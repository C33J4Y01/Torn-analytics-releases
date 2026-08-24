// ==UserScript==
// @name         Torn Analytics
// @namespace    chatgpt.openai.com/torn-tools
// @version      2.17.1
// @description  Persistent Torn log analytics with resumable history, encrypted local storage, metadata-paginated updates, lossless raw-log archiving, and mobile-first analytics dashboards.
// @author       Personal use
// @updateURL    https://raw.githubusercontent.com/C33J4Y01/Torn-analytics-releases/main/torn-analytics.user.js
// @downloadURL  https://raw.githubusercontent.com/C33J4Y01/Torn-analytics-releases/main/torn-analytics.user.js
// @match        https://www.torn.com/*
// @match        https://torn.com/*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_xmlhttpRequest
// @connect      api.torn.com
// @run-at       document-idle
// ==/UserScript==

(() => {
  'use strict';
  // ============================================================
  // VERSION / CONSTANTS
  // ============================================================

  const VERSION = '2.17.1';

  const API_BASE = 'https://api.torn.com/v2';

  const API_LIMIT = 100;

  // Retained for compatibility with older defensive-collector diagnostics.
  // Metadata pagination is now authoritative for completeness.
  const SAFE_SPLIT_THRESHOLD = 90;
  const MAX_PAGINATION_PAGES_PER_RANGE = 64;
  const MAX_RANGE_NETWORK_ATTEMPTS = 512;
  const MAX_RANGE_SPLIT_DEPTH = 24;

  const REQUEST_DELAY_MS = 750;
  const MAX_RETRIES = 5;
  const RETRY_BASE_MS = 1500;

  const SEGMENT_DAYS = 7;
  const UPDATE_OVERLAP_DAYS = 2;

  // Automatic synchronization remains deliberately conservative on mobile:
  // one wake timer, no work while the page is hidden, and the exact same
  // overlap/defensive collector used by the manual update path.
  const AUTO_SYNC_STALE_MS =
    30 * 60 * 1000;

  const AUTO_SYNC_INITIAL_DELAY_MS =
    5 * 1000;

  const AUTO_SYNC_BUSY_RETRY_MS =
    5 * 60 * 1000;

  const AUTO_SYNC_ERROR_BACKOFF_MS =
    15 * 60 * 1000;

  const AUTO_SYNC_LEASE_MS =
    10 * 60 * 1000;
  // ============================================================
  // STORAGE
  // ============================================================

  const API_KEY_STORAGE =
    'tornAnalyticsApiKey';

  const BUTTON_POSITION_KEY =
    'tornAnalyticsButtonPosition';

  // Non-sensitive display preference only. Torn page code could alter this
  // localStorage-backed value without exposing API/history key material.
  const ACTIVITY_TIME_BASIS_STORAGE =
    'tornAnalyticsActivityTimeBasis';

  // Non-sensitive IndexedDB coordination record. It prevents multiple Torn
  // tabs from performing the same automatic API update at once.
  const AUTO_SYNC_LEASE_META_KEY =
    'automatic_log_sync_lease_v1';

  const ITEM_CACHE_KEY =
    'tornAnalyticsItemDictionary';

  const ITEM_CACHE_TIME_KEY =
    'tornAnalyticsItemDictionaryUpdated';

  const ITEM_CACHE_MAX_AGE_MS =
    7 * 24 * 60 * 60 * 1000;

  const DB_NAME =
    'TornAnalyticsDatabase';

  const DB_VERSION = 1;

  const LOG_STORE =
    'logs';

  const META_STORE =
    'metadata';

  const HISTORY_KEY_STORAGE_KEY =
    'tornAnalyticsHistoryDataKeyV1';

  const HISTORY_CANARY_META_KEY =
    'history_security_canary_v1';

  const HISTORY_CRYPTO_VERSION =
    1;

  const HISTORY_CANARY_TEXT =
    'Torn Analytics protected-history canary v1';

  const HISTORY_CANARY_AAD =
    'torn-analytics:history-protection:canary:v1';

  const HISTORY_RECORD_PROTECTION_VERSION =
    1;

  const HISTORY_MIGRATION_META_PREFIX =
    'history_protection_migration_v1:';

  const HISTORY_MIGRATION_BATCH_SIZE =
    100;

  const HISTORY_RECOVERY_META_PREFIX =
    'history_key_recovery_v1:';

  const HISTORY_RECOVERY_VERSION =
    1;

  const HISTORY_RECOVERY_KDF =
    'HKDF-SHA-256';

  const HISTORY_RECOVERY_ALGORITHM =
    'AES-GCM';

  const HISTORY_RECOVERY_INFO =
    'torn-analytics:history-key-recovery:v1';

  const HISTORY_RECOVERY_AAD =
    'torn-analytics:history-key-envelope:v1';
  // ============================================================
  // UI IDS
  // ============================================================

  const BUTTON_ID =
    'torn-analytics-button';

  const MODAL_ID =
    'torn-analytics-modal';

  const STYLE_ID =
    'torn-analytics-style';

  // ============================================================
  // RUNTIME STATE
  // ============================================================

  let running = false;
  let lastRequestStartedAt = 0;
  let currentAccount = null;
  let latestLogs = [];
  let latestItemMap = new Map();
  let latestAnalysis = null;
  let automaticLogSyncRunning = false;
  let automaticLogSyncTimer = null;
  let automaticLogSyncSchedulerInstalled = false;
  let automaticLogSyncLeaseOwner = '';

  // TornPDA replaces this exact documented marker at injection time with
  // the API key already stored by the app. Outside TornPDA the
  // marker remains unchanged and is treated as unavailable.
  const TORN_PDA_API_KEY_SOURCE =
    '###PDA-APIKEY###';

  const injectedPdaApiKey =
    TORN_PDA_API_KEY_SOURCE.includes(
      'PDA-APIKEY'
    )
      ? ''
      : TORN_PDA_API_KEY_SOURCE.trim();

  let sessionApiKey =
    injectedPdaApiKey;

  // A TornPDA-provided key must never coexist with the legacy
  // page-local API-key copy left by pre-security versions.
  if (
    injectedPdaApiKey
  ) {
    try {
      localStorage.removeItem(
        API_KEY_STORAGE
      );
    } catch (_) {}
  }
  // ============================================================
  // BASIC HELPERS
  // ============================================================

  const sleep = ms =>
    new Promise(resolve =>
      setTimeout(resolve, ms)
    );

  function tornPdaRuntimeDetected() {
    return Boolean(
      (
        typeof PDA_storage !== 'undefined' &&
        PDA_storage
      ) ||
      typeof PDA_httpGet === 'function' ||
      globalThis?.flutter_inappwebview
    );
  }

  function userscriptValueStorageAvailable() {
    return (
      typeof GM_getValue === 'function' &&
      typeof GM_setValue === 'function'
    );
  }

  function apiKeyStorageBackend() {
    if (
      typeof PDA_storage !== 'undefined' &&
      PDA_storage &&
      typeof PDA_storage.get === 'function' &&
      typeof PDA_storage.set === 'function'
    ) {
      return 'pda_storage';
    }

    if (
      tornPdaRuntimeDetected()
    ) {
      return null;
    }

    if (
      userscriptValueStorageAvailable()
    ) {
      return 'gm_values';
    }

    return null;
  }

  async function readStoredApiKey(
    backend
  ) {
    if (
      backend === 'pda_storage'
    ) {
      return PDA_storage.get(
        API_KEY_STORAGE,
        ''
      );
    }

    if (
      backend === 'gm_values'
    ) {
      return Promise.resolve(
        GM_getValue(
          API_KEY_STORAGE,
          ''
        )
      );
    }

    return '';
  }

  async function writeStoredApiKey(
    backend,
    value
  ) {
    if (
      backend === 'pda_storage'
    ) {
      await PDA_storage.set(
        API_KEY_STORAGE,
        value
      );
      return;
    }

    if (
      backend === 'gm_values'
    ) {
      await Promise.resolve(
        GM_setValue(
          API_KEY_STORAGE,
          value
        )
      );
    }
  }

  function removeLegacyApiKey() {
    try {
      localStorage.removeItem(
        API_KEY_STORAGE
      );
    } catch (_) {}
  }

  async function loadSecureApiKey() {
    if (
      sessionApiKey
    ) {
      return sessionApiKey;
    }

    removeLegacyApiKey();

    const backend =
      apiKeyStorageBackend();

    if (
      backend
    ) {
      try {
        const stored =
          await readStoredApiKey(
            backend
          );

        if (
          typeof stored === 'string' &&
          stored.trim()
        ) {
          sessionApiKey =
            stored.trim();

          removeLegacyApiKey();

          return sessionApiKey;
        }
      } catch (error) {
        console.warn(
          '[Torn Analytics] Secure API-key read failed:',
          error
        );
      }
    }

    // TornPDA's native store is the only persistent fallback allowed there.
    // Never fall through to its page-local GM compatibility layer.
    if (
      tornPdaRuntimeDetected()
    ) {
      return '';
    }

    try {
      const legacy =
        localStorage.getItem(
          API_KEY_STORAGE
        );

      if (
        legacy?.trim()
      ) {
        sessionApiKey =
          legacy.trim();

        if (backend) {
          try {
            await writeStoredApiKey(
              backend,
              sessionApiKey
            );
          } catch (error) {
            console.warn(
              '[Torn Analytics] Secure API-key migration failed; key will remain session-only:',
              error
            );
          }
        }

        removeLegacyApiKey();

        return sessionApiKey;
      }
    } catch (error) {
      console.warn(
        '[Torn Analytics] Legacy API-key migration failed:',
        error
      );
    }

    return '';
  }

  async function saveSecureApiKey(
    apiKey
  ) {
    const normalized =
      String(
        apiKey ||
        ''
      ).trim();

    if (
      !normalized
    ) {
      return '';
    }

    sessionApiKey =
      normalized;

    removeLegacyApiKey();

    const backend =
      apiKeyStorageBackend();

    if (backend) {
      try {
        await writeStoredApiKey(
          backend,
          sessionApiKey
        );

        const verified =
          await readStoredApiKey(
            backend
          );

        if (
          String(verified || '').trim() !==
          sessionApiKey
        ) {
          throw new Error(
            'saved API key could not be verified'
          );
        }
      } catch (error) {
        console.warn(
          '[Torn Analytics] Secure API-key save failed; key will remain session-only:',
          error
        );
      }
    }

    return sessionApiKey;
  }

  async function clearSecureApiKey() {
    sessionApiKey = '';
    removeLegacyApiKey();

    const backend =
      apiKeyStorageBackend();

    if (
      backend === 'pda_storage'
    ) {
      try {
        await PDA_storage.set(
          API_KEY_STORAGE,
          ''
        );
      } catch (error) {
        console.warn(
          '[Torn Analytics] Secure API-key delete failed:',
          error
        );
      }
    } else if (
      backend === 'gm_values' &&
      typeof GM_deleteValue === 'function'
    ) {
      try {
        await Promise.resolve(
          GM_deleteValue(
            API_KEY_STORAGE
          )
        );
      } catch (error) {
        console.warn(
          '[Torn Analytics] Secure API-key delete failed:',
          error
        );
      }
    }
  }

  function pad2(n) {
    return String(n).padStart(2, '0');
  }

  function localDateString(date) {
    return [
      date.getFullYear(),
      pad2(date.getMonth() + 1),
      pad2(date.getDate())
    ].join('-');
  }

  function parseLocalDate(s) {
    const [y, m, d] =
      s.split('-').map(Number);

    return new Date(
      y,
      m - 1,
      d,
      0,
      0,
      0,
      0
    );
  }

  function addDays(dateString, amount) {
    const d =
      parseLocalDate(dateString);

    d.setDate(
      d.getDate() + amount
    );

    return localDateString(d);
  }

  function todayLocal() {
    return localDateString(
      new Date()
    );
  }

  function startOfDayTimestamp(
    dateString
  ) {
    return Math.floor(
      parseLocalDate(dateString)
        .getTime() / 1000
    );
  }

  function endOfDayTimestamp(
    dateString
  ) {
    const d =
      parseLocalDate(dateString);

    d.setHours(
      23,
      59,
      59,
      999
    );

    return Math.floor(
      d.getTime() / 1000
    );
  }

  function timestampToLocalDate(
    timestamp
  ) {
    return localDateString(
      new Date(
        Number(timestamp) * 1000
      )
    );
  }

  function timestampToIso(
    timestamp
  ) {
    return new Date(
      Number(timestamp) * 1000
    ).toISOString();
  }

  function clamp(
    value,
    min,
    max
  ) {
    return Math.max(
      min,
      Math.min(max, value)
    );
  }

  function makeFloatingButtonMovable(
    button,
    storageKey
  ) {
    if (
      !button ||
      button.dataset.movableReady === '1'
    ) {
      return;
    }

    button.dataset.movableReady = '1';

    const DRAG_THRESHOLD = 7;

    let pointerDown = false;
    let dragging = false;

    let startX = 0;
    let startY = 0;
    let startLeft = 0;
    let startTop = 0;

    function applyPosition(
      left,
      top
    ) {
      const rect =
        button.getBoundingClientRect();

      const maxLeft =
        Math.max(
          0,
          window.innerWidth -
          rect.width
        );

      const maxTop =
        Math.max(
          0,
          window.innerHeight -
          rect.height
        );

      const safeLeft =
        clamp(
          left,
          0,
          maxLeft
        );

      const safeTop =
        clamp(
          top,
          0,
          maxTop
        );

      button.style.left =
        `${safeLeft}px`;

      button.style.top =
        `${safeTop}px`;

      button.style.right =
        'auto';

      button.style.bottom =
        'auto';
    }

    function savePosition() {
      const rect =
        button.getBoundingClientRect();

      try {
        localStorage.setItem(
          storageKey,
          JSON.stringify({
            left: rect.left,
            top: rect.top
          })
        );
      } catch (error) {
        console.warn(
          '[Torn Analytics] Could not save button position:',
          error
        );
      }
    }

    function restorePosition() {
      try {
        const raw =
          localStorage.getItem(
            storageKey
          );

        if (!raw) {
          return;
        }

        const saved =
          JSON.parse(raw);

        const left =
          Number(saved?.left);

        const top =
          Number(saved?.top);

        if (
          Number.isFinite(left) &&
          Number.isFinite(top)
        ) {
          requestAnimationFrame(() => {
            applyPosition(
              left,
              top
            );
          });
        }
      } catch (error) {
        console.warn(
          '[Torn Analytics] Could not restore button position:',
          error
        );
      }
    }

    button.style.touchAction =
      'none';

    button.style.userSelect =
      'none';

    button.style.webkitUserSelect =
      'none';

    button.addEventListener(
      'pointerdown',
      event => {
        if (
          event.button !== undefined &&
          event.button !== 0
        ) {
          return;
        }

        pointerDown = true;
        dragging = false;

        const rect =
          button.getBoundingClientRect();

        startX =
          event.clientX;

        startY =
          event.clientY;

        startLeft =
          rect.left;

        startTop =
          rect.top;

        try {
          button.setPointerCapture(
            event.pointerId
          );
        } catch (_) {}
      }
    );

    button.addEventListener(
      'pointermove',
      event => {
        if (!pointerDown) {
          return;
        }

        const dx =
          event.clientX - startX;

        const dy =
          event.clientY - startY;

        if (
          !dragging &&
          Math.hypot(dx, dy) >=
          DRAG_THRESHOLD
        ) {
          dragging = true;
          button.dataset.dragging = '1';
        }

        if (!dragging) {
          return;
        }

        event.preventDefault();

        applyPosition(
          startLeft + dx,
          startTop + dy
        );
      }
    );

    function finishPointer(event) {
      if (!pointerDown) {
        return;
      }

      pointerDown = false;

      try {
        button.releasePointerCapture(
          event.pointerId
        );
      } catch (_) {}

      if (dragging) {
        savePosition();

        button.dataset.justDragged =
          '1';

        setTimeout(() => {
          delete button.dataset
            .justDragged;
        }, 150);
      }

      dragging = false;

      delete button.dataset
        .dragging;
    }

    button.addEventListener(
      'pointerup',
      finishPointer
    );

    button.addEventListener(
      'pointercancel',
      finishPointer
    );

    button.addEventListener(
      'click',
      event => {
        if (
          button.dataset
            .justDragged === '1'
        ) {
          event.preventDefault();
          event.stopImmediatePropagation();
        }
      },
      true
    );

    window.addEventListener(
      'resize',
      () => {
        const rect =
          button.getBoundingClientRect();

        applyPosition(
          rect.left,
          rect.top
        );

        savePosition();
      }
    );

    restorePosition();
  }

  function money(value) {
    if (
      value === null ||
      value === undefined ||
      !Number.isFinite(Number(value))
    ) {
      return '—';
    }

    const n =
      Math.round(Number(value));

    return (
      `${n < 0 ? '-' : ''}` +
      `$${Math.abs(n).toLocaleString()}`
    );
  }

  function formatDuration(seconds) {
    if (
      !Number.isFinite(seconds) ||
      seconds < 0
    ) {
      return 'Calculating…';
    }

    seconds =
      Math.round(seconds);

    if (seconds < 60) {
      return `${seconds}s`;
    }

    const minutes =
      Math.floor(seconds / 60);

    const sec =
      seconds % 60;

    if (minutes < 60) {
      return sec
        ? `${minutes}m ${sec}s`
        : `${minutes}m`;
    }

    const hours =
      Math.floor(minutes / 60);

    const remMinutes =
      minutes % 60;

    return remMinutes
      ? `${hours}h ${remMinutes}m`
      : `${hours}h`;
  }

  // ============================================================
  // INDEXEDDB
  // ============================================================

  function openDatabase() {
    return new Promise(
      (
        resolve,
        reject
      ) => {

        const request =
          indexedDB.open(
            DB_NAME,
            DB_VERSION
          );

        request.onupgradeneeded =
          event => {

            const db =
              event.target.result;

            if (
              !db.objectStoreNames
                .contains(
                  LOG_STORE
                )
            ) {

              const store =
                db.createObjectStore(
                  LOG_STORE,
                  {
                    keyPath:
                      'cache_key'
                  }
                );

              store.createIndex(
                'account_id',
                'account_id',
                {
                  unique:
                    false
                }
              );

              store.createIndex(
                'timestamp',
                'timestamp',
                {
                  unique:
                    false
                }
              );
            }

            if (
              !db.objectStoreNames
                .contains(
                  META_STORE
                )
            ) {

              db.createObjectStore(
                META_STORE,
                {
                  keyPath:
                    'key'
                }
              );
            }
          };

        request.onsuccess =
          () =>
            resolve(
              request.result
            );

        request.onerror =
          () =>
            reject(
              request.error
            );
      }
    );
  }

  async function dbGetMeta(
    key
  ) {
    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {

        const tx =
          db.transaction(
            META_STORE,
            'readonly'
          );

        const req =
          tx.objectStore(
            META_STORE
          ).get(
            key
          );

        req.onsuccess =
          () => {

            const value =
              req.result
                ?.value ??
              null;

            db.close();

            resolve(
              value
            );
          };

        req.onerror =
          () => {

            db.close();

            reject(
              req.error
            );
          };
      }
    );
  }

  async function dbSetMeta(
    key,
    value
  ) {
    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {

        const tx =
          db.transaction(
            META_STORE,
            'readwrite'
          );

        tx.objectStore(
          META_STORE
        ).put({
          key,
          value
        });

        tx.oncomplete =
          () => {

            db.close();

            resolve();
          };

        tx.onerror =
          () => {

            db.close();

            reject(
              tx.error
            );
          };
      }
    );
  }

  function normalizeStoredAccountId(
    accountId
  ) {
    const normalized =
      Number(
        accountId
      );

    if (
      !Number.isSafeInteger(
        normalized
      ) ||
      normalized <= 0
    ) {
      throw new Error(
        'Invalid Torn account id for persistent storage.'
      );
    }

    return normalized;
  }

  function prepareCachedLog(
    accountId,
    log
  ) {
    const normalizedAccountId =
      Number(
        accountId
      );

    if (
      !Number.isSafeInteger(
        normalizedAccountId
      ) ||
      normalizedAccountId <= 0
    ) {
      throw new Error(
        'Cannot store a Torn log for an invalid account id.'
      );
    }

    const logId =
      canonicalLogId(
        log?.id
      );

    const timestamp =
      Number(
        log?.timestamp
      );

    if (
      !logId
    ) {
      throw new Error(
        'Cannot store a Torn log with an invalid id.'
      );
    }

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp < 0
    ) {
      throw new Error(
        `Cannot store Torn log ${logId} with an invalid timestamp.`
      );
    }

    if (
      Object.prototype.hasOwnProperty.call(
        log || {},
        '_archive'
      )
    ) {
      validateHistoryRawArchiveBinding(
        log
      );
    }

    return {
      ...log,

      id:
        logId,

      timestamp,

      account_id:
        normalizedAccountId,

      cache_key:
        `${normalizedAccountId}:${logId}`
    };
  }

  async function dbLoadCachedRecords(
    accountId
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {

        const tx =
          db.transaction(
            LOG_STORE,
            'readonly'
          );

        const index =
          tx.objectStore(
            LOG_STORE
          ).index(
            'account_id'
          );

        const request =
          index.getAll(
            normalizedAccountId
          );

        request.onsuccess =
          () => {
            const records =
              request.result
                .sort(
                  (
                    a,
                    b
                  ) =>
                    Number(
                      a.timestamp ||
                      0
                    ) -
                    Number(
                      b.timestamp ||
                      0
                    )
                );

            db.close();

            resolve(
              records
            );
          };

        request.onerror =
          () => {
            db.close();

            reject(
              request.error
            );
          };
      }
    );
  }

  async function dbCountAccountLogs(
    accountId
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx =
          db.transaction(
            LOG_STORE,
            'readonly'
          );

        const request =
          tx.objectStore(
            LOG_STORE
          ).index(
            'account_id'
          ).count(
            IDBKeyRange.only(
              normalizedAccountId
            )
          );

        request.onsuccess =
          () => {
            const count =
              Number(
                request.result ||
                0
              );

            db.close();

            resolve(
              count
            );
          };

        request.onerror =
          () => {
            db.close();

            reject(
              request.error
            );
          };
      }
    );
  }

  async function dbLoadCachedRecordsByKeys(
    cacheKeys
  ) {
    const keys =
      [
        ...new Set(
          (cacheKeys || [])
            .map(
              key =>
                String(
                  key ||
                  ''
                )
            )
            .filter(Boolean)
        )
      ];

    if (
      !keys.length
    ) {
      return new Map();
    }

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx =
          db.transaction(
            LOG_STORE,
            'readonly'
          );

        const store =
          tx.objectStore(
            LOG_STORE
          );

        const found =
          new Map();

        for (
          const key
          of keys
        ) {
          const request =
            store.get(
              key
            );

          request.onsuccess =
            () => {
              if (
                request.result
              ) {
                found.set(
                  key,
                  request.result
                );
              }
            };
        }

        tx.oncomplete =
          () => {
            db.close();
            resolve(
              found
            );
          };

        tx.onerror =
          () => {
            db.close();
            reject(
              tx.error
            );
          };

        tx.onabort =
          () => {
            db.close();
            reject(
              tx.error ||
              new Error(
                'Stored Torn log collision lookup was aborted.'
              )
            );
          };
      }
    );
  }

  function stableHistoryJson(
    value
  ) {
    if (
      value === null
    ) {
      return 'null';
    }

    if (
      Array.isArray(
        value
      )
    ) {
      return (
        '[' +
        value.map(
          stableHistoryJson
        ).join(',') +
        ']'
      );
    }

    if (
      typeof value === 'object'
    ) {
      const keys =
        Object.keys(
          value
        ).sort();

      return (
        '{' +
        keys.map(
          key =>
            `${JSON.stringify(key)}:${stableHistoryJson(value[key])}`
        ).join(',') +
        '}'
      );
    }

    if (
      typeof value === 'number' &&
      !Number.isFinite(
        value
      )
    ) {
      throw new Error(
        'A Torn log contains a non-finite numeric value.'
      );
    }

    const encoded =
      JSON.stringify(
        value
      );

    if (
      encoded === undefined
    ) {
      throw new Error(
        'A Torn log contains a value that cannot be compared safely.'
      );
    }

    return encoded;
  }

  function historyLogsEqual(
    left,
    right
  ) {
    return (
      stableHistoryJson(
        left
      ) ===
      stableHistoryJson(
        right
      )
    );
  }

  async function dbPutCachedRecords(
    records
  ) {
    if (
      !records?.length
    ) {
      return;
    }

    for (
      const record
      of records
    ) {
      const normalizedAccountId =
        normalizeStoredAccountId(
          record?.account_id
        );

      const cacheKey =
        String(
          record?.cache_key ||
          ''
        );

      const expectedPrefix =
        `${normalizedAccountId}:`;

      const timestamp =
        Number(
          record?.timestamp
        );

      if (
        !cacheKey.startsWith(
          expectedPrefix
        ) ||
        cacheKey.length <=
          expectedPrefix.length ||
        !Number.isSafeInteger(
          timestamp
        ) ||
        timestamp < 0
      ) {
        throw new Error(
          'Refusing to persist a malformed Torn log cache record.'
        );
      }
    }

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {

        const tx =
          db.transaction(
            LOG_STORE,
            'readwrite'
          );

        const store =
          tx.objectStore(
            LOG_STORE
          );

        for (
          const record
          of records
        ) {
          store.put(
            record
          );
        }

        tx.oncomplete =
          () => {
            db.close();
            resolve();
          };

        tx.onerror =
          () => {
            db.close();
            reject(
              tx.error
            );
          };
      }
    );
  }

  async function dbStoreLogs(
    accountId,
    logs
  ) {
    if (
      !Array.isArray(
        logs
      )
    ) {
      throw new Error(
        'Refusing to store a non-array Torn log batch.'
      );
    }

    if (
      !logs.length
    ) {
      return;
    }

    if (
      logs.some(
        log =>
          !log ||
          typeof log !== 'object' ||
          Array.isArray(
            log
          )
      )
    ) {
      throw new Error(
        'Refusing to store a malformed Torn log batch.'
      );
    }

    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const incoming =
      [];

    const seenKeys =
      new Set();

    for (
      const log
      of logs
    ) {
      const prepared =
        prepareCachedLog(
          normalizedAccountId,
          log
        );

      if (
        seenKeys.has(
          prepared.cache_key
        )
      ) {
        throw new Error(
          `Refusing to store duplicate Torn log identity ${prepared.cache_key} in one batch.`
        );
      }

      seenKeys.add(
        prepared.cache_key
      );

      incoming.push({
        cache_key:
          prepared.cache_key,
        log:
          plaintextLogFromCachedRecord(
            prepared
          )
      });
    }

    // Initialize/verify encryption before examining any existing protected
    // collision. No write occurs until every incoming identity has been checked.
    const verification =
      await verifyHistoryProtectionPersistence();

    if (
      verification.status ===
      'failed'
    ) {
      throw new Error(
        `History protection is unavailable: ${verification.reason || 'persistence verification failed.'}`
      );
    }

    const protectionContext =
      await getHistoryProtectionCryptoContext(
        false
      );

    const existingByKey =
      await dbLoadCachedRecordsByKeys(
        incoming.map(
          row =>
            row.cache_key
        )
      );

    const logsToEncrypt =
      [];

    for (
      const row
      of incoming
    ) {
      const existingRecord =
        existingByKey.get(
          row.cache_key
        );

      if (
        existingRecord
      ) {
        const existingLog =
          isProtectedHistoryRecord(
            existingRecord
          )
            ? await decryptCachedLogRecord(
                existingRecord,
                protectionContext.cryptoKey
              )
            : plaintextLogFromCachedRecord(
                existingRecord
              );

        const comparison =
          compareHistoryLogStoragePayloads(
            existingLog,
            row.log
          );

        if (
          !comparison.compatible
        ) {
          try {
            await recordHistoryDriftAudit(
              normalizedAccountId,
              row.log.id,
              comparison.reason,
              existingLog,
              row.log,
              protectionContext.cryptoKey
            );
          } catch (auditError) {
            throw new Error(
              `Refusing to replace stored Torn log ${row.cache_key} because the API returned different content for an existing identity (${comparison.reason}). ` +
              `Encrypted drift-audit persistence also failed: ${auditError.message}. No conflicting records were written.`
            );
          }

          throw new Error(
            `Refusing to replace stored Torn log ${row.cache_key} because the API returned different content for an existing identity (${comparison.reason}). Encrypted drift evidence was preserved. No conflicting records were written.`
          );
        }

        // An exact protected overlap is already the desired state. A matching
        // legacy protected record is deliberately rewritten once when the API
        // supplies its authenticated raw archive. Legacy plaintext remains an
        // opportunistic encryption target as before.
        if (
          isProtectedHistoryRecord(
            existingRecord
          ) &&
          !comparison.rewrite
        ) {
          continue;
        }
      }

      logsToEncrypt.push(
        row.log
      );
    }

    const records =
      await mapHistoryRecordsInBatches(
        logsToEncrypt,
        log =>
          encryptCachedLogRecord(
            normalizedAccountId,
            log,
            protectionContext.cryptoKey
          )
      );

    await dbPutCachedRecords(
      records
    );
  }

  async function dbLoadLogs(
    accountId
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const records =
      await dbLoadCachedRecords(
        normalizedAccountId
      );

    if (
      !records.length
    ) {
      return [];
    }

    const hasProtected =
      records.some(
        isProtectedHistoryRecord
      );

    let cryptoContext =
      null;

    if (
      hasProtected
    ) {
      const verification =
        await verifyHistoryProtectionPersistence();

      if (
        verification.status ===
        'failed'
      ) {
        throw new Error(
          `History protection is unavailable: ${verification.reason || 'persistence verification failed.'}`
        );
      }

      // A canary created earlier in this same userscript execution is enough to
      // read records written with that immediately round-tripped key. On later
      // executions verifyHistoryProtectionPersistence authenticates the canary.
      cryptoContext =
        await getHistoryProtectionCryptoContext(
          false
        );
    }

    const logs =
      await mapHistoryRecordsInBatches(
        records,
        record =>
          isProtectedHistoryRecord(
            record
          )
            ? decryptCachedLogRecord(
                record,
                cryptoContext.cryptoKey
              )
            : Promise.resolve(
                plaintextLogFromCachedRecord(
                  record
                )
              )
      );

    return logs.sort(
      (
        a,
        b
      ) =>
        Number(
          a.timestamp ||
          0
        ) -
        Number(
          b.timestamp ||
          0
        )
    );
  }

  async function dbClearAccount(
    accountId
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {

        const tx =
          db.transaction(
            LOG_STORE,
            'readwrite'
          );

        const store =
          tx.objectStore(
            LOG_STORE
          );

        const index =
          store.index(
            'account_id'
          );

        const request =
          index.openCursor(
            IDBKeyRange.only(
              normalizedAccountId
            )
          );

        request.onsuccess =
          event => {

            const cursor =
              event.target.result;

            if (
              cursor
            ) {
              cursor.delete();
              cursor.continue();
            }
          };

        tx.oncomplete =
          () => {

            db.close();

            resolve();
          };

        tx.onerror =
          () => {

            db.close();

            reject(
              tx.error
            );
          };
      }
    );
  }
  // ============================================================
  // CACHE METADATA
  // ============================================================

  async function saveAccountCacheMetaSummary(
    account,
    summary,
    source
  ) {
    const count =
      Number(
        summary?.count ||
        0
      );

    const firstTimestamp =
      Number(
        summary?.first_timestamp
      );

    const lastTimestamp =
      Number(
        summary?.last_timestamp
      );

    if (
      !Number.isSafeInteger(
        count
      ) ||
      count <= 0 ||
      !Number.isSafeInteger(
        firstTimestamp
      ) ||
      firstTimestamp < 0 ||
      !Number.isSafeInteger(
        lastTimestamp
      ) ||
      lastTimestamp <
        firstTimestamp
    ) {
      throw new Error(
        'Refusing to save invalid Torn history cache metadata.'
      );
    }

    const meta = {
      account_id:
        account.id,

      account_name:
        account.name,

      signup_timestamp:
        account.signup_timestamp,

      signup_local_date:
        account.signup_local_date,

      first_timestamp:
        firstTimestamp,

      last_timestamp:
        lastTimestamp,

      count:
        count,

      collector_version:
        VERSION,

      cache_schema_version:
        DB_VERSION,

      source,

      updated_at:
        Date.now()
    };

    await dbSetMeta(
      `account:${account.id}`,
      meta
    );

    await dbSetMeta(
      'last_account',
      meta
    );

    return meta;
  }

  async function saveAccountCacheMeta(
    account,
    logs,
    source
  ) {
    if (
      !logs.length
    ) {
      return;
    }

    return saveAccountCacheMetaSummary(
      account,
      {
        first_timestamp:
          Number(
            logs[0]
              .timestamp
          ),

        last_timestamp:
          Number(
            logs[
              logs.length -
              1
            ].timestamp
          ),

        count:
          logs.length
      },
      source
    );
  }

  async function getLastCacheMeta() {
    const meta =
      await dbGetMeta(
        'last_account'
      );

    if (
      !meta ||
      typeof meta !==
        'object'
    ) {
      return meta;
    }

    return {
      ...meta,

      account_name_raw:
        meta.account_name,

      account_name:
        escapeActivityHtml(
          meta.account_name
        )
    };
  }

  async function getBuildState(
    accountId
  ) {
    return dbGetMeta(
      `build:${accountId}`
    );
  }

  async function setBuildState(
    accountId,
    state
  ) {
    return dbSetMeta(
      `build:${accountId}`,
      state
    );
  }

  async function clearBuildState(
    accountId
  ) {
    return dbSetMeta(
      `build:${accountId}`,
      null
    );
  }
  // ============================================================
  // HISTORY PROTECTION
  // ============================================================

  function historyCryptoAvailable() {
    return Boolean(
      globalThis.crypto &&
      globalThis.crypto.subtle &&
      typeof globalThis.crypto.getRandomValues === 'function' &&
      typeof TextEncoder === 'function' &&
      typeof TextDecoder === 'function'
    );
  }

  function historyKeyStorageBackend() {
    if (
      typeof PDA_storage !== 'undefined' &&
      PDA_storage &&
      typeof PDA_storage.get === 'function' &&
      typeof PDA_storage.set === 'function'
    ) {
      return 'pda_storage';
    }

    // TornPDA's GM value compatibility layer is page localStorage. If the
    // native per-script store is missing or incomplete, fail closed instead
    // of ever placing the raw history key into page-readable GM storage.
    if (
      tornPdaRuntimeDetected()
    ) {
      return null;
    }

    if (
      typeof GM_getValue === 'function' &&
      typeof GM_setValue === 'function'
    ) {
      return 'gm_values';
    }

    return null;
  }

  function historyBytesToBase64(
    bytes
  ) {
    let binary = '';

    for (
      let i = 0;
      i < bytes.length;
      i++
    ) {
      binary +=
        String.fromCharCode(
          bytes[i]
        );
    }

    return btoa(
      binary
    );
  }

  function historyBase64ToBytes(
    value
  ) {
    const binary =
      atob(
        String(
          value ||
          ''
        )
      );

    const bytes =
      new Uint8Array(
        binary.length
      );

    for (
      let i = 0;
      i < binary.length;
      i++
    ) {
      bytes[i] =
        binary.charCodeAt(
          i
        );
    }

    return bytes;
  }

  async function historyReadStoredKey(
    backend
  ) {
    if (
      backend ===
      'pda_storage'
    ) {
      return PDA_storage.get(
        HISTORY_KEY_STORAGE_KEY,
        null
      );
    }

    if (
      backend ===
      'gm_values'
    ) {
      return Promise.resolve(
        GM_getValue(
          HISTORY_KEY_STORAGE_KEY,
          null
        )
      );
    }

    return null;
  }

  async function historyWriteStoredKey(
    backend,
    value
  ) {
    if (
      backend ===
      'pda_storage'
    ) {
      await PDA_storage.set(
        HISTORY_KEY_STORAGE_KEY,
        value
      );
      return;
    }

    if (
      backend ===
      'gm_values'
    ) {
      await Promise.resolve(
        GM_setValue(
          HISTORY_KEY_STORAGE_KEY,
          value
        )
      );
      return;
    }

    throw new Error(
      'No protected userscript storage backend is available.'
    );
  }

  async function loadHistoryKeyMaterial(
    createIfMissing = false
  ) {
    if (
      !historyCryptoAvailable()
    ) {
      throw new Error(
        'Web Crypto is unavailable; history protection cannot be enabled.'
      );
    }

    const backend =
      historyKeyStorageBackend();

    if (
      !backend
    ) {
      throw new Error(
        'Protected key storage is unavailable in this userscript manager.'
      );
    }

    const stored =
      await historyReadStoredKey(
        backend
      );

    if (
      stored !== null &&
      stored !== undefined &&
      String(stored).trim()
    ) {
      let rawKey;

      try {
        rawKey =
          historyBase64ToBytes(
            stored
          );
      } catch (_) {
        throw new Error(
          'The stored history-protection key is corrupt.'
        );
      }

      if (
        rawKey.length !== 32
      ) {
        throw new Error(
          'The stored history-protection key has an invalid length.'
        );
      }

      return {
        backend,
        rawKey,
        created:
          false
      };
    }

    if (
      !createIfMissing
    ) {
      return null;
    }

    const rawKey =
      new Uint8Array(
        32
      );

    globalThis.crypto
      .getRandomValues(
        rawKey
      );

    const encoded =
      historyBytesToBase64(
        rawKey
      );

    await historyWriteStoredKey(
      backend,
      encoded
    );

    const verified =
      await historyReadStoredKey(
        backend
      );

    if (
      verified !== encoded
    ) {
      throw new Error(
        'The history-protection key could not be verified after saving.'
      );
    }

    return {
      backend,
      rawKey,
      created:
        true
    };
  }

  async function importHistoryCryptoKey(
    rawKey
  ) {
    return globalThis.crypto
      .subtle
      .importKey(
        'raw',
        rawKey,
        {
          name:
            'AES-GCM'
        },
        false,
        [
          'encrypt',
          'decrypt'
        ]
      );
  }

  async function encryptHistoryCanary(
    rawKey
  ) {
    const iv =
      new Uint8Array(
        12
      );

    globalThis.crypto
      .getRandomValues(
        iv
      );

    const encoder =
      new TextEncoder();

    const key =
      await importHistoryCryptoKey(
        rawKey
      );

    const ciphertext =
      await globalThis.crypto
        .subtle
        .encrypt(
          {
            name:
              'AES-GCM',

            iv,

            additionalData:
              encoder.encode(
                HISTORY_CANARY_AAD
              )
          },
          key,
          encoder.encode(
            HISTORY_CANARY_TEXT
          )
        );

    return {
      version:
        HISTORY_CRYPTO_VERSION,

      algorithm:
        'AES-GCM',

      iv:
        historyBytesToBase64(
          iv
        ),

      ciphertext:
        historyBytesToBase64(
          new Uint8Array(
            ciphertext
          )
        ),

      created_at:
        Date.now()
    };
  }

  async function decryptHistoryCanary(
    rawKey,
    canary
  ) {
    if (
      Number(canary?.version) !==
        HISTORY_CRYPTO_VERSION ||
      canary?.algorithm !==
        'AES-GCM' ||
      !canary?.iv ||
      !canary?.ciphertext
    ) {
      throw new Error(
        'The history-protection canary has an unsupported format.'
      );
    }

    const encoder =
      new TextEncoder();

    const decoder =
      new TextDecoder();

    const key =
      await importHistoryCryptoKey(
        rawKey
      );

    const plaintext =
      await globalThis.crypto
        .subtle
        .decrypt(
          {
            name:
              'AES-GCM',

            iv:
              historyBase64ToBytes(
                canary.iv
              ),

            additionalData:
              encoder.encode(
                HISTORY_CANARY_AAD
              )
          },
          key,
          historyBase64ToBytes(
            canary.ciphertext
          )
        );

    return decoder.decode(
      plaintext
    );
  }

  async function verifyHistoryProtectionPersistence() {
    const existingCanary =
      await dbGetMeta(
        HISTORY_CANARY_META_KEY
      );

    if (
      !existingCanary
    ) {
      const keyRecord =
        await loadHistoryKeyMaterial(
          true
        );

      const canary =
        await encryptHistoryCanary(
          keyRecord.rawKey
        );

      await dbSetMeta(
        HISTORY_CANARY_META_KEY,
        canary
      );

      return {
        status:
          'initialized',

        backend:
          keyRecord.backend,

        logsChanged:
          false
      };
    }

    const keyRecord =
      await loadHistoryKeyMaterial(
        false
      );

    if (
      !keyRecord
    ) {
      return {
        status:
          'failed',

        reason:
          'The canary exists but its encryption key did not survive.',

        logsChanged:
          false
      };
    }

    try {
      const plaintext =
        await decryptHistoryCanary(
          keyRecord.rawKey,
          existingCanary
        );

      if (
        plaintext !==
        HISTORY_CANARY_TEXT
      ) {
        throw new Error(
          'Canary plaintext did not match.'
        );
      }

      return {
        status:
          'verified',

        backend:
          keyRecord.backend,

        logsChanged:
          false
      };

    } catch (error) {
      return {
        status:
          'failed',

        reason:
          `Stored protection key could not decrypt the canary: ${error.message}`,

        logsChanged:
          false
      };
    }
  }

  function isProtectedHistoryRecord(
    record
  ) {
    return Boolean(
      Number(record?.protection_version) ===
        HISTORY_RECORD_PROTECTION_VERSION &&
      record?.protection_algorithm ===
        'AES-GCM' &&
      record?.protection_iv &&
      record?.protection_ciphertext
    );
  }

  function hasHistoryProtectionMetadata(
    record
  ) {
    if (
      !record ||
      typeof record !== 'object'
    ) {
      return false;
    }

    return [
      'protection_version',
      'protection_algorithm',
      'protection_iv',
      'protection_ciphertext'
    ].some(
      key =>
        Object.prototype.hasOwnProperty.call(
          record,
          key
        )
    );
  }

  function plaintextLogFromCachedRecord(
    cached
  ) {
    if (
      isProtectedHistoryRecord(
        cached
      )
    ) {
      throw new Error(
        'Protected records must be decrypted before reading their log payload.'
      );
    }

    if (
      hasHistoryProtectionMetadata(
        cached
      )
    ) {
      throw new Error(
        'A stored Torn log contains partial or malformed history-protection metadata. Refusing to treat it as plaintext.'
      );
    }

    const normalizedAccountId =
      normalizeStoredAccountId(
        cached?.account_id
      );

    const logId =
      canonicalLogId(
        cached?.id
      );

    const timestamp =
      Number(
        cached?.timestamp
      );

    const expectedCacheKey =
      logId
        ? `${normalizedAccountId}:${logId}`
        : '';

    if (
      !logId ||
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp < 0 ||
      String(
        cached?.cache_key ||
        ''
      ) !== expectedCacheKey
    ) {
      throw new Error(
        'A legacy plaintext Torn log failed persistent identity validation.'
      );
    }

    const {
      cache_key,
      account_id,
      ...log
    } =
      cached || {};

    return {
      ...log,
      id:
        logId,
      timestamp
    };
  }

  function historyRecordAad(
    record
  ) {
    return [
      'torn-analytics:history-record',
      `v${HISTORY_RECORD_PROTECTION_VERSION}`,
      String(
        Number(
          record?.account_id
        )
      ),
      String(
        record?.cache_key ||
        ''
      ),
      String(
        Number(
          record?.timestamp ||
          0
        )
      )
    ].join(
      ':'
    );
  }

  async function encryptCachedLogRecord(
    accountId,
    log,
    cryptoKey
  ) {
    if (
      !log?.id
    ) {
      throw new Error(
        'Cannot protect a Torn log without an id.'
      );
    }

    const prepared =
      prepareCachedLog(
        accountId,
        log
      );

    const outer = {
      cache_key:
        prepared.cache_key,

      account_id:
        prepared.account_id,

      timestamp:
        Number(
          log.timestamp ||
          0
        ),

      protection_version:
        HISTORY_RECORD_PROTECTION_VERSION,

      protection_algorithm:
        'AES-GCM'
    };

    const iv =
      new Uint8Array(
        12
      );

    globalThis.crypto
      .getRandomValues(
        iv
      );

    const encoder =
      new TextEncoder();

    const ciphertext =
      await globalThis.crypto
        .subtle
        .encrypt(
          {
            name:
              'AES-GCM',

            iv,

            additionalData:
              encoder.encode(
                historyRecordAad(
                  outer
                )
              )
          },
          cryptoKey,
          encoder.encode(
            JSON.stringify(
              log
            )
          )
        );

    return {
      ...outer,

      protection_iv:
        historyBytesToBase64(
          iv
        ),

      protection_ciphertext:
        historyBytesToBase64(
          new Uint8Array(
            ciphertext
          )
        )
    };
  }

  async function decryptCachedLogRecord(
    record,
    cryptoKey
  ) {
    if (
      !isProtectedHistoryRecord(
        record
      )
    ) {
      return plaintextLogFromCachedRecord(
        record
      );
    }

    const encoder =
      new TextEncoder();

    const decoder =
      new TextDecoder();

    let plaintext;

    try {
      plaintext =
        await globalThis.crypto
          .subtle
          .decrypt(
            {
              name:
                'AES-GCM',

              iv:
                historyBase64ToBytes(
                  record.protection_iv
                ),

              additionalData:
                encoder.encode(
                  historyRecordAad(
                    record
                  )
                )
            },
            cryptoKey,
            historyBase64ToBytes(
              record.protection_ciphertext
            )
          );
    } catch (_) {
      throw new Error(
        `Protected Torn log ${record.cache_key || '(unknown)'} failed authentication.`
      );
    }

    let log;

    try {
      log =
        JSON.parse(
          decoder.decode(
            plaintext
          )
        );
    } catch (_) {
      throw new Error(
        `Protected Torn log ${record.cache_key || '(unknown)'} contained invalid JSON.`
      );
    }

    const expectedCacheKey =
      `${Number(record.account_id)}:${log?.id}`;

    if (
      !log?.id ||
      expectedCacheKey !==
        String(record.cache_key) ||
      Number(log.timestamp || 0) !==
        Number(record.timestamp || 0)
    ) {
      throw new Error(
        `Protected Torn log ${record.cache_key || '(unknown)'} failed identity verification.`
      );
    }

    return log;
  }

  async function getHistoryProtectionCryptoContext(
    requireVerified = true
  ) {
    if (
      requireVerified
    ) {
      const verification =
        await verifyHistoryProtectionPersistence();

      if (
        verification.status ===
        'initialized'
      ) {
        return null;
      }

      if (
        verification.status !==
        'verified'
      ) {
        throw new Error(
          `History protection is unavailable: ${verification.reason || 'persistence verification failed.'}`
        );
      }
    }

    const keyRecord =
      await loadHistoryKeyMaterial(
        false
      );

    if (
      !keyRecord
    ) {
      throw new Error(
        'The protected-history key is missing. Existing encrypted history has not been modified.'
      );
    }

    return {
      ...keyRecord,

      cryptoKey:
        await importHistoryCryptoKey(
          keyRecord.rawKey
        )
    };
  }

  async function mapHistoryRecordsInBatches(
    records,
    mapper,
    batchSize = HISTORY_MIGRATION_BATCH_SIZE
  ) {
    const output = [];

    for (
      let offset = 0;
      offset < records.length;
      offset += batchSize
    ) {
      const batch =
        records.slice(
          offset,
          offset +
          batchSize
        );

      const mapped =
        await Promise.all(
          batch.map(
            mapper
          )
        );

      output.push(
        ...mapped
      );
    }

    return output;
  }

  function historyMigrationMetaKey(
    accountId
  ) {
    return `${HISTORY_MIGRATION_META_PREFIX}${Number(accountId)}`;
  }

  async function getAccountHistoryProtectionStatus(
    accountId
  ) {
    await assertStoredSingleAccountOwner(
      accountId
    );

    const records =
      await dbLoadCachedRecords(
        accountId
      );

    const protectedCount =
      records.filter(
        isProtectedHistoryRecord
      ).length;

    const plaintextCount =
      records.length -
      protectedCount;

    return {
      total:
        records.length,

      protected:
        protectedCount,

      plaintext:
        plaintextCount,

      complete:
        records.length > 0 &&
        plaintextCount === 0,

      metadata:
        await dbGetMeta(
          historyMigrationMetaKey(
            accountId
          )
        )
    };
  }

  async function migrateAccountHistoryProtection(
    accountId,
    onProgress = null
  ) {
    await assertStoredSingleAccountOwner(
      accountId
    );

    const verification =
      await verifyHistoryProtectionPersistence();

    if (
      verification.status !==
      'verified'
    ) {
      throw new Error(
        verification.status ===
        'initialized'
          ? 'History protection must survive one full app/browser restart before log migration is allowed.'
          : `History protection verification failed: ${verification.reason || 'unknown error'}`
      );
    }

    const context =
      await getHistoryProtectionCryptoContext(
        false
      );

    const initialRecords =
      await dbLoadCachedRecords(
        accountId
      );

    const total =
      initialRecords.length;

    if (
      !total
    ) {
      return {
        total:
          0,

        migrated:
          0,

        alreadyProtected:
          0,

        complete:
          true
      };
    }

    const plaintextRecords =
      initialRecords.filter(
        record =>
          !isProtectedHistoryRecord(
            record
          )
      );

    const alreadyProtected =
      total -
      plaintextRecords.length;

    let migrated =
      0;

    const migrationKey =
      historyMigrationMetaKey(
        accountId
      );

    await dbSetMeta(
      migrationKey,
      {
        version:
          HISTORY_RECORD_PROTECTION_VERSION,

        account_id:
          Number(
            accountId
          ),

        status:
          plaintextRecords.length
            ? 'in_progress'
            : 'verifying',

        total,
        already_protected:
          alreadyProtected,

        migrated_this_run:
          0,

        updated_at:
          Date.now()
      }
    );

    for (
      let offset = 0;
      offset < plaintextRecords.length;
      offset += HISTORY_MIGRATION_BATCH_SIZE
    ) {
      const batch =
        plaintextRecords.slice(
          offset,
          offset +
          HISTORY_MIGRATION_BATCH_SIZE
        );

      const encryptedBatch =
        await Promise.all(
          batch.map(
            async cached => {
              const originalLog =
                plaintextLogFromCachedRecord(
                  cached
                );

              const encrypted =
                await encryptCachedLogRecord(
                  accountId,
                  originalLog,
                  context.cryptoKey
                );

              const verifiedLog =
                await decryptCachedLogRecord(
                  encrypted,
                  context.cryptoKey
                );

              if (
                JSON.stringify(
                  verifiedLog
                ) !==
                JSON.stringify(
                  originalLog
                )
              ) {
                throw new Error(
                  `Protected Torn log ${cached.cache_key} failed pre-write verification.`
                );
              }

              return encrypted;
            }
          )
        );

      await dbPutCachedRecords(
        encryptedBatch
      );

      migrated +=
        encryptedBatch.length;

      const protectedNow =
        alreadyProtected +
        migrated;

      await dbSetMeta(
        migrationKey,
        {
          version:
            HISTORY_RECORD_PROTECTION_VERSION,

          account_id:
            Number(
              accountId
            ),

          status:
            'in_progress',

          total,
          already_protected:
            alreadyProtected,

          migrated_this_run:
            migrated,

          protected_total:
            protectedNow,

          plaintext_remaining:
            Math.max(
              0,
              total -
              protectedNow
            ),

          updated_at:
            Date.now()
        }
      );

      if (
        typeof onProgress ===
        'function'
      ) {
        onProgress({
          total,
          protected:
            protectedNow,

          plaintext:
            Math.max(
              0,
              total -
              protectedNow
            ),

          percent:
            total
              ? 100 *
                protectedNow /
                total
              : 100
        });
      }
    }

    const finalRecords =
      await dbLoadCachedRecords(
        accountId
      );

    if (
      finalRecords.length !==
      total
    ) {
      throw new Error(
        `History protection count verification failed: expected ${total}, found ${finalRecords.length}.`
      );
    }

    const unprotected =
      finalRecords.filter(
        record =>
          !isProtectedHistoryRecord(
            record
          )
      );

    if (
      unprotected.length
    ) {
      throw new Error(
        `${unprotected.length} plaintext Torn log records remain. Migration can be resumed safely.`
      );
    }

    await mapHistoryRecordsInBatches(
      finalRecords,
      record =>
        decryptCachedLogRecord(
          record,
          context.cryptoKey
        )
    );

    await dbSetMeta(
      migrationKey,
      {
        version:
          HISTORY_RECORD_PROTECTION_VERSION,

        account_id:
          Number(
            accountId
          ),

        status:
          'complete',

        total,
        protected_total:
          total,

        plaintext_remaining:
          0,

        completed_at:
          Date.now(),

        updated_at:
          Date.now()
      }
    );

    return {
      total,
      migrated,
      alreadyProtected,
      complete:
        true
    };
  }
  // ============================================================
  // HISTORY KEY RECOVERY
  // ============================================================

  function normalizeHistoryRecoveryApiKey(
    apiKey
  ) {
    const normalized =
      String(
        apiKey ||
        ''
      ).trim();

    if (
      !normalized
    ) {
      throw new Error(
        'A Torn API key is required for protected-history key recovery.'
      );
    }

    return normalized;
  }

  function normalizeHistoryRecoveryAccountId(
    accountId
  ) {
    const normalized =
      Number(
        accountId
      );

    if (
      !Number.isSafeInteger(
        normalized
      ) ||
      normalized <= 0
    ) {
      throw new Error(
        'A valid Torn account id is required for protected-history key recovery.'
      );
    }

    return normalized;
  }

  function historyRecoveryMetaKey(
    accountId
  ) {
    return (
      `${HISTORY_RECOVERY_META_PREFIX}` +
      `${normalizeHistoryRecoveryAccountId(accountId)}`
    );
  }

  function historyRecoveryContextString(
    base,
    accountId
  ) {
    return (
      `${base}:` +
      `${normalizeHistoryRecoveryAccountId(accountId)}`
    );
  }

  async function deriveHistoryRecoveryCryptoKey(
    apiKey,
    accountId,
    salt
  ) {
    const normalizedKey =
      normalizeHistoryRecoveryApiKey(
        apiKey
      );

    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    const encoder =
      new TextEncoder();

    const material =
      await globalThis.crypto
        .subtle
        .importKey(
          'raw',
          encoder.encode(
            normalizedKey
          ),
          'HKDF',
          false,
          [
            'deriveKey'
          ]
        );

    return globalThis.crypto
      .subtle
      .deriveKey(
        {
          name:
            'HKDF',

          hash:
            'SHA-256',

          salt,

          info:
            encoder.encode(
              historyRecoveryContextString(
                HISTORY_RECOVERY_INFO,
                normalizedAccountId
              )
            )
        },
        material,
        {
          name:
            'AES-GCM',

          length:
            256
        },
        false,
        [
          'encrypt',
          'decrypt'
        ]
      );
  }

  async function encryptHistoryRecoveryEnvelope(
    apiKey,
    accountId,
    rawHistoryKey
  ) {
    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    if (
      !(rawHistoryKey instanceof Uint8Array) ||
      rawHistoryKey.length !== 32
    ) {
      throw new Error(
        'History recovery requires a valid 256-bit history key.'
      );
    }

    const salt =
      new Uint8Array(
        16
      );

    const iv =
      new Uint8Array(
        12
      );

    globalThis.crypto
      .getRandomValues(
        salt
      );

    globalThis.crypto
      .getRandomValues(
        iv
      );

    const recoveryKey =
      await deriveHistoryRecoveryCryptoKey(
        apiKey,
        normalizedAccountId,
        salt
      );

    const encoder =
      new TextEncoder();

    const ciphertext =
      await globalThis.crypto
        .subtle
        .encrypt(
          {
            name:
              'AES-GCM',

            iv,

            additionalData:
              encoder.encode(
                historyRecoveryContextString(
                  HISTORY_RECOVERY_AAD,
                  normalizedAccountId
                )
              )
          },
          recoveryKey,
          rawHistoryKey
        );

    return {
      version:
        HISTORY_RECOVERY_VERSION,

      account_id:
        normalizedAccountId,

      kdf:
        HISTORY_RECOVERY_KDF,

      algorithm:
        HISTORY_RECOVERY_ALGORITHM,

      salt:
        historyBytesToBase64(
          salt
        ),

      iv:
        historyBytesToBase64(
          iv
        ),

      ciphertext:
        historyBytesToBase64(
          new Uint8Array(
            ciphertext
          )
        ),

      updated_at:
        Date.now()
    };
  }

  async function decryptHistoryRecoveryEnvelope(
    apiKey,
    accountId,
    envelope
  ) {
    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    if (
      Number(envelope?.version) !==
        HISTORY_RECOVERY_VERSION ||
      Number(envelope?.account_id) !==
        normalizedAccountId ||
      envelope?.kdf !==
        HISTORY_RECOVERY_KDF ||
      envelope?.algorithm !==
        HISTORY_RECOVERY_ALGORITHM ||
      !envelope?.salt ||
      !envelope?.iv ||
      !envelope?.ciphertext
    ) {
      throw new Error(
        'The protected-history recovery envelope has an unsupported or mismatched format.'
      );
    }

    let salt;
    let iv;
    let ciphertext;

    try {
      salt =
        historyBase64ToBytes(
          envelope.salt
        );

      iv =
        historyBase64ToBytes(
          envelope.iv
        );

      ciphertext =
        historyBase64ToBytes(
          envelope.ciphertext
        );
    } catch (_) {
      throw new Error(
        'The protected-history recovery envelope is corrupt.'
      );
    }

    if (
      salt.length !== 16 ||
      iv.length !== 12 ||
      !ciphertext.length
    ) {
      throw new Error(
        'The protected-history recovery envelope has invalid parameters.'
      );
    }

    const recoveryKey =
      await deriveHistoryRecoveryCryptoKey(
        apiKey,
        normalizedAccountId,
        salt
      );

    const encoder =
      new TextEncoder();

    let plaintext;

    try {
      plaintext =
        await globalThis.crypto
          .subtle
          .decrypt(
            {
              name:
                'AES-GCM',

              iv,

              additionalData:
                encoder.encode(
                  historyRecoveryContextString(
                    HISTORY_RECOVERY_AAD,
                    normalizedAccountId
                  )
                )
            },
            recoveryKey,
            ciphertext
          );
    } catch (_) {
      throw new Error(
        'The current Torn API key could not unlock this account\'s protected-history recovery envelope.'
      );
    }

    const rawHistoryKey =
      new Uint8Array(
        plaintext
      );

    if (
      rawHistoryKey.length !== 32
    ) {
      throw new Error(
        'The recovered protected-history key has an invalid length.'
      );
    }

    return rawHistoryKey;
  }

  async function historyKeyAuthenticatesCanary(
    rawHistoryKey,
    canary
  ) {
    try {
      const plaintext =
        await decryptHistoryCanary(
          rawHistoryKey,
          canary
        );

      return plaintext ===
        HISTORY_CANARY_TEXT;
    } catch (_) {
      return false;
    }
  }

  async function writeVerifiedRecoveredHistoryKey(
    rawHistoryKey
  ) {
    const backend =
      historyKeyStorageBackend();

    if (
      !backend
    ) {
      throw new Error(
        'Protected key storage is unavailable; the recovered history key was not saved.'
      );
    }

    const encoded =
      historyBytesToBase64(
        rawHistoryKey
      );

    await historyWriteStoredKey(
      backend,
      encoded
    );

    const verified =
      await historyReadStoredKey(
        backend
      );

    if (
      verified !== encoded
    ) {
      throw new Error(
        'The recovered protected-history key could not be verified after saving.'
      );
    }

    return backend;
  }

  async function recoverHistoryKeyFromEnvelope(
    apiKey,
    accountId,
    existingCanary = null
  ) {
    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    const canary =
      existingCanary ||
      await dbGetMeta(
        HISTORY_CANARY_META_KEY
      );

    if (
      !canary
    ) {
      return {
        status:
          'not_initialized',

        recovered:
          false
      };
    }

    const envelope =
      await dbGetMeta(
        historyRecoveryMetaKey(
          normalizedAccountId
        )
      );

    if (
      !envelope
    ) {
      throw new Error(
        'Protected history exists, but no recovery envelope is available for this account\'s encryption key.'
      );
    }

    const rawHistoryKey =
      await decryptHistoryRecoveryEnvelope(
        apiKey,
        normalizedAccountId,
        envelope
      );

    if (
      !await historyKeyAuthenticatesCanary(
        rawHistoryKey,
        canary
      )
    ) {
      throw new Error(
        'The recovered history key did not authenticate the existing protected-history canary.'
      );
    }

    const backend =
      await writeVerifiedRecoveredHistoryKey(
        rawHistoryKey
      );

    return {
      status:
        'recovered',

      recovered:
        true,

      backend,
      rawKey:
        rawHistoryKey
    };
  }

  async function ensureHistoryRecoveryEnvelope(
    apiKey,
    accountId
  ) {
    const normalizedApiKey =
      normalizeHistoryRecoveryApiKey(
        apiKey
      );

    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    const canary =
      await dbGetMeta(
        HISTORY_CANARY_META_KEY
      );

    if (
      !canary
    ) {
      return {
        status:
          'not_initialized',

        recovered:
          false,

        envelopeUpdated:
          false
      };
    }

    let keyRecord =
      null;

    try {
      keyRecord =
        await loadHistoryKeyMaterial(
          false
        );
    } catch (_) {
      keyRecord =
        null;
    }

    if (
      keyRecord &&
      !await historyKeyAuthenticatesCanary(
        keyRecord.rawKey,
        canary
      )
    ) {
      keyRecord =
        null;
    }

    let recovered =
      false;

    if (
      !keyRecord
    ) {
      const recovery =
        await recoverHistoryKeyFromEnvelope(
          normalizedApiKey,
          normalizedAccountId,
          canary
        );

      keyRecord = {
        backend:
          recovery.backend,

        rawKey:
          recovery.rawKey,

        created:
          false
      };

      recovered =
        true;
    }

    const recoveryMetaKey =
      historyRecoveryMetaKey(
        normalizedAccountId
      );

    const existingEnvelope =
      await dbGetMeta(
        recoveryMetaKey
      );

    let envelopeMatches =
      false;

    if (
      existingEnvelope
    ) {
      try {
        const envelopeKey =
          await decryptHistoryRecoveryEnvelope(
            normalizedApiKey,
            normalizedAccountId,
            existingEnvelope
          );

        envelopeMatches =
          envelopeKey.length ===
            keyRecord.rawKey.length &&
          envelopeKey.every(
            (
              value,
              index
            ) =>
              value ===
              keyRecord.rawKey[index]
          );
      } catch (_) {
        envelopeMatches =
          false;
      }
    }

    if (
      !envelopeMatches
    ) {
      const envelope =
        await encryptHistoryRecoveryEnvelope(
          normalizedApiKey,
          normalizedAccountId,
          keyRecord.rawKey
        );

      await dbSetMeta(
        recoveryMetaKey,
        envelope
      );

      const persisted =
        await dbGetMeta(
          recoveryMetaKey
        );

      const verifiedKey =
        await decryptHistoryRecoveryEnvelope(
          normalizedApiKey,
          normalizedAccountId,
          persisted
        );

      if (
        !await historyKeyAuthenticatesCanary(
          verifiedKey,
          canary
        )
      ) {
        throw new Error(
          'The protected-history recovery envelope failed verification after saving.'
        );
      }

      return {
        status:
          recovered
            ? 'recovered_and_refreshed'
            : 'ready',

        recovered,

        envelopeUpdated:
          true,

        backend:
          keyRecord.backend
      };
    }

    return {
      status:
        recovered
          ? 'recovered'
          : 'ready',

      recovered,

      envelopeUpdated:
        false,

      backend:
        keyRecord.backend
    };
  }
  // ============================================================
  // NON-DESTRUCTIVE HISTORY RECOVERY VERIFICATION
  // ============================================================

  function historyKeysEqual(
    left,
    right
  ) {
    if (
      !(left instanceof Uint8Array) ||
      !(right instanceof Uint8Array) ||
      left.length !==
        right.length
    ) {
      return false;
    }

    let difference =
      0;

    for (
      let i = 0;
      i < left.length;
      i++
    ) {
      difference |=
        left[i] ^
        right[i];
    }

    return difference ===
      0;
  }

  async function verifyHistoryRecoveryEnvelope(
    apiKey,
    accountId
  ) {
    const normalizedApiKey =
      normalizeHistoryRecoveryApiKey(
        apiKey
      );

    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    const canary =
      await dbGetMeta(
        HISTORY_CANARY_META_KEY
      );

    if (
      !canary
    ) {
      throw new Error(
        'Protected history has not been initialized yet.'
      );
    }

    const envelope =
      await dbGetMeta(
        historyRecoveryMetaKey(
          normalizedAccountId
        )
      );

    if (
      !envelope
    ) {
      throw new Error(
        'No recovery envelope exists for this Torn account yet. Run Update Logs once to create it.'
      );
    }

    const recoveredKey =
      await decryptHistoryRecoveryEnvelope(
        normalizedApiKey,
        normalizedAccountId,
        envelope
      );

    if (
      !await historyKeyAuthenticatesCanary(
        recoveredKey,
        canary
      )
    ) {
      throw new Error(
        'The recovery envelope decrypted, but its history key did not authenticate the existing canary.'
      );
    }

    let nativeKeyPresent =
      false;

    let matchesNativeKey =
      null;

    try {
      const nativeKey =
        await loadHistoryKeyMaterial(
          false
        );

      if (
        nativeKey?.rawKey
      ) {
        nativeKeyPresent =
          true;

        if (
          !await historyKeyAuthenticatesCanary(
            nativeKey.rawKey,
            canary
          )
        ) {
          throw new Error(
            'The currently stored native history key does not authenticate the existing canary.'
          );
        }

        matchesNativeKey =
          historyKeysEqual(
            recoveredKey,
            nativeKey.rawKey
          );

        if (
          !matchesNativeKey
        ) {
          throw new Error(
            'The recovery envelope key does not match the currently stored native history key.'
          );
        }
      }
    } catch (
      error
    ) {
      if (
        /currently stored native history key|does not match/.test(
          String(
            error?.message ||
            ''
          )
        )
      ) {
        throw error;
      }

      nativeKeyPresent =
        false;

      matchesNativeKey =
        null;
    }

    return {
      status:
        'verified',

      account_id:
        normalizedAccountId,

      native_key_present:
        nativeKeyPresent,

      matches_native_key:
        matchesNativeKey,

      changed:
        false
    };
  }

  async function verifyAuthenticatedHistoryRecoveryEnvelope(
    apiKey,
    accountId
  ) {
    const normalizedApiKey =
      normalizeHistoryRecoveryApiKey(
        apiKey
      );

    const normalizedAccountId =
      normalizeHistoryRecoveryAccountId(
        accountId
      );

    await assertStoredSingleAccountOwner(
      normalizedAccountId
    );

    const accountTracker = {
      setStage() {},
      incrementRequest() {}
    };

    const authenticatedAccount =
      await detectAccount(
        normalizedApiKey,
        accountTracker
      );

    await assertAuthenticatedSingleAccountOwner(
      authenticatedAccount.id
    );

    if (
      Number(authenticatedAccount.id) !==
      normalizedAccountId
    ) {
      throw new Error(
        `Torn account mismatch: recovery verification requested account ${normalizedAccountId}, but the authenticated account is ${authenticatedAccount.id}. Operation blocked.`
      );
    }

    return verifyHistoryRecoveryEnvelope(
      normalizedApiKey,
      normalizedAccountId
    );
  }
  // ============================================================
  // SINGLE-ACCOUNT COMPLIANCE
  // ============================================================

  const SINGLE_ACCOUNT_OWNER_META_KEY =
    'single_account_owner_v1';

  function normalizeSingleAccountId(
    value,
    label = 'Torn account ID'
  ) {
    const id = value;

    if (
      typeof id !== 'number' ||
      !Number.isSafeInteger(id) ||
      id <= 0
    ) {
      throw new Error(
        `${label} must be a positive safe integer.`
      );
    }

    return id;
  }

  async function listStoredTornAccountIds() {
    const db = await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx = db.transaction(
          LOG_STORE,
          'readonly'
        );

        const request = tx.objectStore(
          LOG_STORE
        ).getAll();

        request.onsuccess = () => {
          try {
            const ids = new Set();

            for (
              const record
              of request.result || []
            ) {
              ids.add(
                normalizeSingleAccountId(
                  record?.account_id,
                  'Stored Torn log account ID'
                )
              );
            }

            resolve(
              [...ids].sort((a, b) => a - b)
            );
          } catch (error) {
            reject(error);
          } finally {
            db.close();
          }
        };

        request.onerror = () => {
          db.close();
          reject(request.error);
        };
      }
    );
  }

  async function getSingleAccountOwnerBinding() {
    const binding = await dbGetMeta(
      SINGLE_ACCOUNT_OWNER_META_KEY
    );

    if (!binding) {
      return null;
    }

    return {
      version: Number(binding.version ?? 1),
      account_id: normalizeSingleAccountId(
        binding.account_id,
        'Stored Torn Analytics owner ID'
      ),
      bound_at: Number(binding.bound_at ?? 0) || null
    };
  }

  async function resolveStoredSingleAccountOwner() {
    const binding = await getSingleAccountOwnerBinding();
    const storedIds = await listStoredTornAccountIds();

    if (storedIds.length > 1) {
      throw new Error(
        'Torn Analytics detected stored history for more than one Torn account. Private-history operations are blocked until the installation is safely remediated.'
      );
    }

    const storedId = storedIds.length === 1
      ? storedIds[0]
      : null;

    if (
      binding &&
      storedId &&
      binding.account_id !== storedId
    ) {
      throw new Error(
        'Torn Analytics owner binding conflicts with the encrypted stored-history account. Private-history operations are blocked.'
      );
    }

    if (binding) {
      return binding.account_id;
    }

    if (storedId) {
      await dbSetMeta(
        SINGLE_ACCOUNT_OWNER_META_KEY,
        {
          version: 1,
          account_id: storedId,
          bound_at: Date.now(),
          source: 'existing_single_account_history'
        }
      );

      return storedId;
    }

    return null;
  }

  async function assertAuthenticatedSingleAccountOwner(
    authenticatedAccountId
  ) {
    const authenticatedId = normalizeSingleAccountId(
      authenticatedAccountId,
      'Authenticated Torn account ID'
    );

    const storedOwnerId = await resolveStoredSingleAccountOwner();

    if (
      storedOwnerId !== null &&
      storedOwnerId !== authenticatedId
    ) {
      throw new Error(
        `Torn account mismatch: this Torn Analytics installation is bound to account ${storedOwnerId}, but the authenticated account is ${authenticatedId}. Operation blocked.`
      );
    }

    if (storedOwnerId === null) {
      await dbSetMeta(
        SINGLE_ACCOUNT_OWNER_META_KEY,
        {
          version: 1,
          account_id: authenticatedId,
          bound_at: Date.now(),
          source: 'authenticated_first_owner'
        }
      );
    }

    return authenticatedId;
  }

  async function assertStoredSingleAccountOwner(
    storedAccountId
  ) {
    const requestedId = normalizeSingleAccountId(
      storedAccountId,
      'Stored-history account ID'
    );

    const ownerId = await resolveStoredSingleAccountOwner();

    if (
      ownerId === null ||
      ownerId !== requestedId
    ) {
      throw new Error(
        'Stored-history account does not match the Torn Analytics installation owner. Operation blocked.'
      );
    }

    return ownerId;
  }

  // ============================================================
  // ATOMIC STAGED HISTORY PROMOTION
  // ============================================================

  async function dbPromoteStagedAccountHistory(
    accountId,
    logs
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    if (
      !Array.isArray(
        logs
      ) ||
      !logs.length
    ) {
      throw new Error(
        'Refusing to promote an empty or malformed rebuilt Torn history.'
      );
    }

    const stagedLogs =
      [];

    const stagedById =
      new Map();

    for (
      const log
      of logs
    ) {
      if (
        !log ||
        typeof log !== 'object' ||
        Array.isArray(
          log
        )
      ) {
        throw new Error(
          'Refusing to promote a malformed rebuilt Torn history.'
        );
      }

      const prepared =
        prepareCachedLog(
          normalizedAccountId,
          log
        );

      if (
        stagedById.has(
          prepared.id
        )
      ) {
        throw new Error(
          `Refusing to promote rebuilt Torn history with duplicate identity ${prepared.id}.`
        );
      }

      const plaintext =
        plaintextLogFromCachedRecord(
          prepared
        );

      stagedById.set(
        prepared.id,
        plaintext
      );

      stagedLogs.push(
        plaintext
      );
    }

    // Snapshot the current live records before decrypting/comparing them. The
    // same encrypted snapshot is checked again inside the final read/write
    // transaction so another writer cannot slip a change between verification
    // and promotion.
    const existingRecordSnapshot =
      await dbLoadCachedRecords(
        normalizedAccountId
      );

    const verification =
      await verifyHistoryProtectionPersistence();

    if (
      verification.status ===
      'failed'
    ) {
      throw new Error(
        `History protection is unavailable: ${verification.reason || 'persistence verification failed.'}`
      );
    }

    const protectionContext =
      await getHistoryProtectionCryptoContext(
        false
      );

    const existingLogs =
      await mapHistoryRecordsInBatches(
        existingRecordSnapshot,
        record =>
          isProtectedHistoryRecord(
            record
          )
            ? decryptCachedLogRecord(
                record,
                protectionContext.cryptoKey
              )
            : Promise.resolve(
                plaintextLogFromCachedRecord(
                  record
                )
              )
      );

    // Rebuild is allowed to add newly discovered records and to upgrade a
    // legacy normalized record with its matching raw API archive. It may not
    // erase an existing identity, downgrade an archived record, or accept any
    // normalized/raw content drift. Any conflict preserves the live history.
    for (
      const existingLog
      of existingLogs
    ) {
      const existingId =
        canonicalLogId(
          existingLog?.id
        );

      const replacement =
        existingId
          ? stagedById.get(
              existingId
            )
          : null;

      if (
        !existingId ||
        !replacement
      ) {
        throw new Error(
          `Refusing to promote rebuilt Torn history because existing log ${existingId || '(invalid id)'} is missing from the verified replacement. Existing history was preserved.`
        );
      }

      const comparison =
        compareHistoryLogStoragePayloads(
          existingLog,
          replacement
        );

      if (
        !comparison.compatible
      ) {
        try {
          await recordHistoryDriftAudit(
            normalizedAccountId,
            existingId,
            comparison.reason,
            existingLog,
            replacement,
            protectionContext.cryptoKey
          );
        } catch (auditError) {
          throw new Error(
            `Refusing to promote rebuilt Torn history because existing log ${existingId} changed content (${comparison.reason}). ` +
            `Encrypted drift-audit persistence also failed: ${auditError.message}. Existing history was preserved.`
          );
        }

        throw new Error(
          `Refusing to promote rebuilt Torn history because existing log ${existingId} changed content (${comparison.reason}). Encrypted drift evidence was preserved. Existing history was preserved.`
        );
      }
    }

    const replacementRecords =
      await mapHistoryRecordsInBatches(
        stagedLogs,
        log =>
          encryptCachedLogRecord(
            normalizedAccountId,
            log,
            protectionContext.cryptoKey
          )
      );

    if (
      replacementRecords.length !==
      stagedLogs.length ||
      replacementRecords.some(
        record =>
          !isProtectedHistoryRecord(
            record
          ) ||
          record.account_id !==
            normalizedAccountId ||
          typeof record.cache_key !==
            'string' ||
          !record.cache_key.startsWith(
            `${normalizedAccountId}:`
          )
      )
    ) {
      throw new Error(
        'Refusing to promote rebuilt Torn history because replacement encryption verification failed.'
      );
    }

    const snapshotSignature =
      stableHistoryJson(
        [...existingRecordSnapshot]
          .sort(
            (a, b) =>
              String(
                a.cache_key ||
                ''
              ).localeCompare(
                String(
                  b.cache_key ||
                  ''
                )
              )
          )
      );

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx =
          db.transaction(
            LOG_STORE,
            'readwrite'
          );

        const store =
          tx.objectStore(
            LOG_STORE
          );

        const index =
          store.index(
            'account_id'
          );

        let promotionError =
          null;

        const request =
          index.getAll(
            normalizedAccountId
          );

        request.onsuccess =
          () => {
            const currentRecords =
              [...request.result]
                .sort(
                  (a, b) =>
                    String(
                      a.cache_key ||
                      ''
                    ).localeCompare(
                      String(
                        b.cache_key ||
                        ''
                      )
                    )
                );

            const currentSignature =
              stableHistoryJson(
                currentRecords
              );

            if (
              currentSignature !==
              snapshotSignature
            ) {
              promotionError =
                new Error(
                  'Stored Torn history changed while Full Rebuild was being verified. Existing history was preserved; retry the rebuild.'
                );

              tx.abort();
              return;
            }

            for (
              const record
              of currentRecords
            ) {
              store.delete(
                record.cache_key
              );
            }

            for (
              const record
              of replacementRecords
            ) {
              store.put(
                record
              );
            }
          };

        request.onerror =
          () => {
            promotionError =
              request.error ||
              new Error(
                'Could not verify the live Torn history before staged promotion.'
              );
          };

        tx.oncomplete =
          () => {
            db.close();
            resolve();
          };

        tx.onerror =
          () => {
            db.close();
            reject(
              promotionError ||
              tx.error ||
              new Error(
                'Atomic rebuilt-history promotion failed. Existing history was preserved.'
              )
            );
          };

        tx.onabort =
          () => {
            db.close();
            reject(
              promotionError ||
              tx.error ||
              new Error(
                'Atomic rebuilt-history promotion was aborted. Existing history was preserved.'
              )
            );
          };
      }
    );
  }

  // ============================================================
  // ENCRYPTED SAME-ID HISTORY DRIFT AUDIT
  // ============================================================

  const HISTORY_DRIFT_AUDIT_PREFIX =
    'history_drift_audit_v1:';

  const HISTORY_DRIFT_AUDIT_VERSION =
    1;

  function normalizeHistoryDriftReason(
    reason
  ) {
    const normalized =
      String(
        reason ||
        ''
      );

    if (
      ![
        'normalized_content_drift',
        'raw_api_content_drift',
        'raw_archive_downgrade'
      ].includes(
        normalized
      )
    ) {
      throw new Error(
        'Unsupported Torn history drift audit reason.'
      );
    }

    return normalized;
  }

  function historyDriftAuditAad(
    key,
    record
  ) {
    const accountId =
      normalizeStoredAccountId(
        record?.account_id
      );

    const logId =
      canonicalLogId(
        record?.log_id
      );

    const observedAt =
      Number(
        record?.observed_at
      );

    const reason =
      normalizeHistoryDriftReason(
        record?.reason
      );

    if (
      !logId ||
      !Number.isSafeInteger(
        observedAt
      ) ||
      observedAt <= 0 ||
      Number(
        record?.version
      ) !== HISTORY_DRIFT_AUDIT_VERSION ||
      record?.algorithm !== 'AES-GCM' ||
      typeof key !== 'string' ||
      !key.startsWith(
        `${HISTORY_DRIFT_AUDIT_PREFIX}${accountId}:${encodeURIComponent(logId)}:${observedAt}:`
      )
    ) {
      throw new Error(
        'A Torn history drift audit failed identity verification.'
      );
    }

    return [
      'torn-analytics:history-drift-audit',
      `v${HISTORY_DRIFT_AUDIT_VERSION}`,
      key,
      String(
        accountId
      ),
      logId,
      String(
        observedAt
      ),
      reason
    ].join(
      ':'
    );
  }

  function historyDriftAuditKey(
    accountId,
    logId,
    observedAt
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const normalizedLogId =
      canonicalLogId(
        logId
      );

    const normalizedObservedAt =
      Number(
        observedAt
      );

    if (
      !normalizedLogId ||
      !Number.isSafeInteger(
        normalizedObservedAt
      ) ||
      normalizedObservedAt <= 0
    ) {
      throw new Error(
        'Cannot create a Torn history drift audit for an invalid identity.'
      );
    }

    if (
      !globalThis.crypto ||
      typeof globalThis.crypto.getRandomValues !==
        'function'
    ) {
      throw new Error(
        'Web Crypto is unavailable; history drift evidence cannot be recorded safely.'
      );
    }

    const random =
      new Uint8Array(
        8
      );

    globalThis.crypto
      .getRandomValues(
        random
      );

    const suffix =
      Array.from(
        random,
        byte =>
          byte
            .toString(16)
            .padStart(2, '0')
      ).join('');

    return (
      `${HISTORY_DRIFT_AUDIT_PREFIX}` +
      `${normalizedAccountId}:` +
      `${encodeURIComponent(normalizedLogId)}:` +
      `${normalizedObservedAt}:` +
      suffix
    );
  }

  async function createHistoryDriftAuditRecord(
    accountId,
    logId,
    reason,
    existingLog,
    incomingLog,
    cryptoKey,
    observedAt = Date.now()
  ) {
    const normalizedAccountId =
      normalizeStoredAccountId(
        accountId
      );

    const normalizedLogId =
      canonicalLogId(
        logId
      );

    const normalizedReason =
      normalizeHistoryDriftReason(
        reason
      );

    const normalizedObservedAt =
      Number(
        observedAt
      );

    if (
      !normalizedLogId ||
      !Number.isSafeInteger(
        normalizedObservedAt
      ) ||
      normalizedObservedAt <= 0 ||
      !existingLog ||
      typeof existingLog !== 'object' ||
      Array.isArray(
        existingLog
      ) ||
      !incomingLog ||
      typeof incomingLog !== 'object' ||
      Array.isArray(
        incomingLog
      ) ||
      canonicalLogId(
        existingLog.id
      ) !== normalizedLogId ||
      canonicalLogId(
        incomingLog.id
      ) !== normalizedLogId
    ) {
      throw new Error(
        'Cannot create a Torn history drift audit for an invalid conflicting payload.'
      );
    }

    // Make sure neither conflicting payload contains a value that cannot be
    // represented safely as authenticated JSON before encrypting it.
    stableHistoryJson(
      existingLog
    );

    stableHistoryJson(
      incomingLog
    );

    if (
      !cryptoKey ||
      !globalThis.crypto?.subtle ||
      typeof TextEncoder !== 'function'
    ) {
      throw new Error(
        'History protection crypto is unavailable; drift evidence cannot be recorded safely.'
      );
    }

    const key =
      historyDriftAuditKey(
        normalizedAccountId,
        normalizedLogId,
        normalizedObservedAt
      );

    const outer = {
      version:
        HISTORY_DRIFT_AUDIT_VERSION,
      algorithm:
        'AES-GCM',
      account_id:
        normalizedAccountId,
      log_id:
        normalizedLogId,
      observed_at:
        normalizedObservedAt,
      reason:
        normalizedReason
    };

    const payload = {
      version:
        HISTORY_DRIFT_AUDIT_VERSION,
      account_id:
        normalizedAccountId,
      log_id:
        normalizedLogId,
      observed_at:
        normalizedObservedAt,
      reason:
        normalizedReason,
      existing_log:
        existingLog,
      incoming_log:
        incomingLog
    };

    const iv =
      new Uint8Array(
        12
      );

    globalThis.crypto
      .getRandomValues(
        iv
      );

    const encoder =
      new TextEncoder();

    const ciphertext =
      await globalThis.crypto
        .subtle
        .encrypt(
          {
            name:
              'AES-GCM',
            iv,
            additionalData:
              encoder.encode(
                historyDriftAuditAad(
                  key,
                  outer
                )
              )
          },
          cryptoKey,
          encoder.encode(
            JSON.stringify(
              payload
            )
          )
        );

    return {
      key,
      value: {
        ...outer,
        iv:
          historyBytesToBase64(
            iv
          ),
        ciphertext:
          historyBytesToBase64(
            new Uint8Array(
              ciphertext
            )
          )
      }
    };
  }

  async function decryptHistoryDriftAuditRecord(
    key,
    record,
    cryptoKey
  ) {
    if (
      !record?.iv ||
      !record?.ciphertext ||
      !cryptoKey ||
      !globalThis.crypto?.subtle ||
      typeof TextEncoder !== 'function' ||
      typeof TextDecoder !== 'function'
    ) {
      throw new Error(
        'A Torn history drift audit has an unsupported encrypted format.'
      );
    }

    const encoder =
      new TextEncoder();

    const decoder =
      new TextDecoder();

    let plaintext;

    try {
      plaintext =
        await globalThis.crypto
          .subtle
          .decrypt(
            {
              name:
                'AES-GCM',
              iv:
                historyBase64ToBytes(
                  record.iv
                ),
              additionalData:
                encoder.encode(
                  historyDriftAuditAad(
                    key,
                    record
                  )
                )
            },
            cryptoKey,
            historyBase64ToBytes(
              record.ciphertext
            )
          );
    } catch (_) {
      throw new Error(
        'A Torn history drift audit failed authentication.'
      );
    }

    let payload;

    try {
      payload =
        JSON.parse(
          decoder.decode(
            plaintext
          )
        );
    } catch (_) {
      throw new Error(
        'A Torn history drift audit contained invalid encrypted JSON.'
      );
    }

    const accountId =
      normalizeStoredAccountId(
        record.account_id
      );

    const logId =
      canonicalLogId(
        record.log_id
      );

    const observedAt =
      Number(
        record.observed_at
      );

    const reason =
      normalizeHistoryDriftReason(
        record.reason
      );

    if (
      Number(
        payload?.version
      ) !== HISTORY_DRIFT_AUDIT_VERSION ||
      Number(
        payload?.account_id
      ) !== accountId ||
      canonicalLogId(
        payload?.log_id
      ) !== logId ||
      Number(
        payload?.observed_at
      ) !== observedAt ||
      payload?.reason !== reason ||
      canonicalLogId(
        payload?.existing_log?.id
      ) !== logId ||
      canonicalLogId(
        payload?.incoming_log?.id
      ) !== logId
    ) {
      throw new Error(
        'A Torn history drift audit failed identity verification.'
      );
    }

    return payload;
  }

  async function recordHistoryDriftAudit(
    accountId,
    logId,
    reason,
    existingLog,
    incomingLog,
    cryptoKey,
    observedAt = Date.now()
  ) {
    const created =
      await createHistoryDriftAuditRecord(
        accountId,
        logId,
        reason,
        existingLog,
        incomingLog,
        cryptoKey,
        observedAt
      );

    await dbSetMeta(
      created.key,
      created.value
    );

    return {
      key:
        created.key,
      account_id:
        created.value.account_id,
      log_id:
        created.value.log_id,
      observed_at:
        created.value.observed_at,
      reason:
        created.value.reason,
      persisted:
        true
    };
  }

  // ============================================================
  // PROGRESS
  // ============================================================

  class ProgressTracker {

    constructor(
      callback
    ) {
      this.callback =
        callback;

      this.reset();
    }

    reset() {
      this.startedAt =
        Date.now();

      this.percent =
        0;

      this.stage =
        'Ready';

      this.detail =
        '';

      this.logsCollected =
        0;

      this.apiRequests =
        0;

      this.splitCount =
        0;

      this.render();
    }

    setPercent(
      value
    ) {
      this.percent =
        clamp(
          value,
          0,
          100
        );

      this.render();
    }

    setStage(
      stage,
      detail = ''
    ) {
      this.stage =
        stage;

      this.detail =
        detail;

      this.render();
    }

    setLogs(
      count
    ) {
      this.logsCollected =
        count;

      this.render();
    }

    incrementRequest() {
      this.apiRequests++;
      this.render();
    }

    incrementSplit() {
      this.splitCount++;
      this.render();
    }

    render() {

      const elapsed =
        (
          Date.now() -
          this.startedAt
        ) /
        1000;

      let eta =
        NaN;

      if (
        this.percent >= 2 &&
        this.percent < 100
      ) {

        const estimatedTotal =
          elapsed /
          (
            this.percent /
            100
          );

        eta =
          Math.max(
            0,
            estimatedTotal -
            elapsed
          );
      }

      if (
        this.percent >=
        100
      ) {
        eta = 0;
      }

      this.callback?.({
        percent:
          this.percent,

        stage:
          this.stage,

        detail:
          this.detail,

        logsCollected:
          this.logsCollected,

        apiRequests:
          this.apiRequests,

        splitCount:
          this.splitCount,

        elapsed:
          formatDuration(
            elapsed
          ),

        eta:
          formatDuration(
            eta
          )
      });
    }
  }

  // ============================================================
  // API HELPERS
  // ============================================================

  async function waitForRequestSlot() {

    const elapsed =
      Date.now() -
      lastRequestStartedAt;

    if (
      elapsed <
      REQUEST_DELAY_MS
    ) {

      await sleep(
        REQUEST_DELAY_MS -
        elapsed
      );
    }

    lastRequestStartedAt =
      Date.now();
  }

  function extractApiError(
    json
  ) {

    if (
      !json?.error
    ) {
      return null;
    }

    if (
      typeof json.error ===
      'string'
    ) {
      return json.error;
    }

    return (
      `Torn API error ` +
      `${json.error.code ?? '?'}: ` +
      `${
        json.error.error ??
        json.error.message ??
        'Unknown API error'
      }`
    );
  }

  function validateTornApiUrl(
    url
  ) {
    const parsed =
      new URL(
        url
      );

    if (
      parsed.protocol !== 'https:' ||
      parsed.hostname !== 'api.torn.com' ||
      !parsed.pathname.startsWith('/v2/')
    ) {
      throw new Error(
        'Refusing to send Torn API credentials to an unapproved destination.'
      );
    }

    if (
      parsed.searchParams.has(
        'key'
      )
    ) {
      throw new Error(
        'Torn API keys must not be placed in request URLs.'
      );
    }

    return parsed.toString();
  }

  function consumeRangeAttemptBudget(
    requestBudget
  ) {
    if (
      !requestBudget
    ) {
      return;
    }

    const maxAttempts =
      Number(
        requestBudget.max_attempts ??
        MAX_RANGE_NETWORK_ATTEMPTS
      );

    const attempts =
      Number(
        requestBudget.attempts ||
        0
      );

    if (
      !Number.isFinite(maxAttempts) ||
      maxAttempts < 1
    ) {
      throw new Error(
        'Defensive log collection has an invalid network-attempt budget.'
      );
    }

    if (
      attempts >=
      maxAttempts
    ) {
      throw new Error(
        `Defensive log collection stopped after ${maxAttempts} network attempts. ` +
        'No incomplete range will be stored.'
      );
    }

    requestBudget.attempts =
      attempts + 1;
  }

  function secureUserscriptRequest(
    url,
    apiKey
  ) {
    if (
      typeof GM_xmlhttpRequest !==
      'function'
    ) {
      throw new Error(
        'Secure Torn API transport is unavailable in this userscript manager.'
      );
    }

    return new Promise(
      (
        resolve,
        reject
      ) => {
        GM_xmlhttpRequest({
          method:
            'GET',

          url,

          headers: {
            Authorization:
              `ApiKey ${apiKey}`,

            Accept:
              'application/json'
          },

          timeout:
            30000,

          anonymous:
            true,

          onload:
            resolve,

          onerror:
            () =>
              reject(
                new Error(
                  'Network request failed.'
                )
              ),

          ontimeout:
            () =>
              reject(
                new Error(
                  'Network request timed out.'
                )
              ),

          onabort:
            () =>
              reject(
                new Error(
                  'Network request was aborted.'
                )
              )
        });
      }
    );
  }

  async function apiFetchJson(
    url,
    apiKey,
    tracker,
    attempt = 1,
    requestBudget = null
  ) {

    const safeUrl =
      validateTornApiUrl(
        url
      );

    const normalizedKey =
      String(
        apiKey ||
        ''
      ).trim();

    if (
      !normalizedKey
    ) {
      throw new Error(
        'A Torn API key is required.'
      );
    }

    consumeRangeAttemptBudget(
      requestBudget
    );

    await waitForRequestSlot();

    tracker?.incrementRequest();

    try {

      const response =
        await secureUserscriptRequest(
          safeUrl,
          normalizedKey
        );

      const status =
        Number(
          response?.status ||
          0
        );

      if (
        status &&
        (
          status < 200 ||
          status >= 300
        )
      ) {

        throw new Error(
          `HTTP ${status} ${response?.statusText || ''}`.trim()
        );
      }

      const raw =
        response?.responseText ??
        response?.response ??
        '';

      const json =
        typeof raw === 'string'
          ? JSON.parse(
              raw
            )
          : raw;

      const apiError =
        extractApiError(
          json
        );

      if (
        apiError
      ) {

        throw new Error(
          apiError
        );
      }

      return json;

    } catch (
      error
    ) {

      if (
        attempt >=
        MAX_RETRIES
      ) {

        throw new Error(
          `Request failed after ${MAX_RETRIES} attempts: ${error.message}`
        );
      }

      await sleep(
        RETRY_BASE_MS *
        Math.pow(
          2,
          attempt - 1
        )
      );

      return apiFetchJson(
        safeUrl,
        normalizedKey,
        tracker,
        attempt + 1,
        requestBudget
      );
    }
  }

  // ============================================================
  // ACCOUNT DETECTION
  // ============================================================

  async function detectAccount(
    apiKey,
    tracker
  ) {

    tracker.setStage(
      'Identifying account…',
      'Checking API key'
    );

    const json =
      await apiFetchJson(
        `${API_BASE}/user/profile`,
        apiKey,
        tracker
      );

    const profile =
      json?.profile;

    if (
      !profile?.id ||
      !profile?.name ||
      !profile?.signed_up
    ) {

      throw new Error(
        'Could not determine the account attached to this API key.'
      );
    }

    const signupTimestamp =
      Number(
        profile.signed_up
      );

    return {
      id:
        Number(
          profile.id
        ),

      name:
        profile.name,

      level:
        profile.level ??
        null,

      age_days:
        profile.age ??
        null,

      signup_timestamp:
        signupTimestamp,

      signup_iso:
        timestampToIso(
          signupTimestamp
        ),

      signup_local_date:
        timestampToLocalDate(
          signupTimestamp
        )
    };
  }

  // ============================================================
  // ITEM DICTIONARY
  // ============================================================

  function normalizeItemRecord(
    raw,
    fallbackId = null
  ) {

    if (
      !raw ||
      typeof raw !==
      'object'
    ) {
      return null;
    }

    const id =
      Number(
        raw.id ??
        fallbackId
      );

    if (
      !Number.isFinite(
        id
      )
    ) {
      return null;
    }

    return {
      id,

      name:
        raw.name ??
        raw.item_name ??
        `Item #${id}`,

      type:
        raw.type ??
        raw.category ??
        raw.item_type ??
        null,

      sub_type:
        raw.sub_type ??
        raw.subtype ??
        null,

      market_value:
        Number(
          raw.market_value ??
          raw.marketValue ??
          raw.value?.market ??
          0
        ) ||
        null
    };
  }

  function normalizeItemsResponse(
    json
  ) {

    const source =
      json?.items ??
      json?.torn_items ??
      json?.item ??
      [];

    const map =
      new Map();

    if (
      Array.isArray(
        source
      )
    ) {

      for (
        const raw
        of source
      ) {

        const item =
          normalizeItemRecord(
            raw
          );

        if (
          item
        ) {
          map.set(
            item.id,
            item
          );
        }
      }

    } else if (
      source &&
      typeof source ===
        'object'
    ) {

      for (
        const [
          id,
          raw
        ]
        of Object.entries(
          source
        )
      ) {

        const item =
          normalizeItemRecord(
            raw,
            id
          );

        if (
          item
        ) {

          map.set(
            item.id,
            item
          );
        }
      }
    }

    return map;
  }

  function readItemCache() {

    try {

      const raw =
        localStorage.getItem(
          ITEM_CACHE_KEY
        );

      const updated =
        Number(
          localStorage.getItem(
            ITEM_CACHE_TIME_KEY
          ) ||
          0
        );

      if (
        !raw
      ) {
        return null;
      }

      const parsed =
        JSON.parse(
          raw
        );

      const map =
        new Map();

      for (
        const item
        of parsed
      ) {

        if (
          item?.id
        ) {

          map.set(
            Number(
              item.id
            ),
            item
          );
        }
      }

      return {
        map,

        fresh:
          Date.now() -
          updated <
          ITEM_CACHE_MAX_AGE_MS
      };

    } catch (_) {

      return null;
    }
  }

  function writeItemCache(
    map
  ) {

    try {

      localStorage.setItem(
        ITEM_CACHE_KEY,
        JSON.stringify(
          [
            ...map.values()
          ]
        )
      );

      localStorage.setItem(
        ITEM_CACHE_TIME_KEY,
        String(
          Date.now()
        )
      );

    } catch (
      error
    ) {

      console.warn(
        '[Torn Analytics] Item cache save failed:',
        error
      );
    }
  }

  async function loadItemDictionary(
    apiKey,
    tracker,
    allowApi = true
  ) {

    const cached =
      readItemCache();

    if (
      cached?.map?.size &&
      (
        cached.fresh ||
        !allowApi
      )
    ) {

      return cached.map;
    }

    if (
      !allowApi
    ) {

      return (
        cached?.map ??
        new Map()
      );
    }

    tracker?.setStage(
      'Loading item names…',
      'Refreshing item dictionary'
    );

    const json =
      await apiFetchJson(
        `${API_BASE}/torn/items`,
        apiKey,
        tracker
      );

    const map =
      normalizeItemsResponse(
        json
      );

    if (
      map.size
    ) {

      writeItemCache(
        map
      );

      return map;
    }

    return (
      cached?.map ??
      new Map()
    );
  }

  function itemInfo(
    id,
    map
  ) {

    const numericId =
      Number(
        id
      );

    return (
      map.get(
        numericId
      ) ??
      {
        id:
          numericId,

        name:
          `Item #${numericId}`,

        type:
          null,

        market_value:
          null
      }
    );
  }

  // ============================================================
  // LOG NORMALIZATION / RAW ARCHIVE
  // ============================================================

  const HISTORY_RAW_ARCHIVE_FORMAT =
    'torn-api-v2-user-log-record-v1';

  function canonicalLogId(
    value
  ) {
    if (
      typeof value !== 'string' &&
      typeof value !== 'number'
    ) {
      return null;
    }

    if (
      typeof value === 'number' &&
      !Number.isSafeInteger(
        value
      )
    ) {
      return null;
    }

    const raw =
      String(
        value
      );

    const normalized =
      raw.trim();

    if (
      !normalized ||
      (
        typeof value === 'string' &&
        normalized !== raw
      )
    ) {
      return null;
    }

    return normalized;
  }

  function cloneHistoryRawApiRecord(
    entry
  ) {
    if (
      !entry ||
      typeof entry !== 'object' ||
      Array.isArray(
        entry
      )
    ) {
      throw new Error(
        'A Torn API log record is not a valid JSON object.'
      );
    }

    const canonicalBefore =
      stableHistoryJson(
        entry
      );

    let encoded;
    let cloned;

    try {
      encoded =
        JSON.stringify(
          entry
        );

      if (
        typeof encoded !== 'string'
      ) {
        throw new Error(
          'Record could not be encoded.'
        );
      }

      cloned =
        JSON.parse(
          encoded
        );
    } catch (
      error
    ) {
      throw new Error(
        `A Torn API log record could not be preserved losslessly: ${error.message}`
      );
    }

    if (
      stableHistoryJson(
        cloned
      ) !== canonicalBefore
    ) {
      throw new Error(
        'A Torn API log record changed during lossless archive verification.'
      );
    }

    return cloned;
  }

  function validateHistoryRawArchiveBinding(
    log
  ) {
    if (
      !Object.prototype.hasOwnProperty.call(
        log || {},
        '_archive'
      )
    ) {
      return null;
    }

    const archive =
      log?._archive;

    if (
      !archive ||
      typeof archive !== 'object' ||
      Array.isArray(
        archive
      ) ||
      archive.format !==
        HISTORY_RAW_ARCHIVE_FORMAT ||
      !archive.raw ||
      typeof archive.raw !== 'object' ||
      Array.isArray(
        archive.raw
      )
    ) {
      throw new Error(
        'A Torn history raw archive has an unsupported or malformed format.'
      );
    }

    const normalizedId =
      canonicalLogId(
        log?.id
      );

    const normalizedTimestamp =
      Number(
        log?.timestamp
      );

    const rawId =
      canonicalLogId(
        archive.raw.id
      );

    const rawTimestamp =
      Number(
        archive.raw.timestamp
      );

    if (
      !normalizedId ||
      !rawId ||
      rawId !== normalizedId ||
      !Number.isSafeInteger(
        normalizedTimestamp
      ) ||
      !Number.isSafeInteger(
        rawTimestamp
      ) ||
      rawTimestamp !==
        normalizedTimestamp
    ) {
      throw new Error(
        'A Torn history raw archive does not match the normalized log identity and timestamp.'
      );
    }

    // Re-run the JSON-safety check whenever an archived record crosses a
    // storage comparison boundary. API JSON cannot contain undefined, NaN, or
    // other non-JSON values; accepting those later would make equality claims
    // ambiguous.
    stableHistoryJson(
      archive.raw
    );

    const rawDetails =
      archive.raw.details &&
      typeof archive.raw.details ===
        'object'
        ? archive.raw.details
        : {};

    const rawNumericLogId =
      rawDetails.id === null ||
      rawDetails.id === undefined
        ? null
        : Number(
            rawDetails.id
          );

    const expectedNormalized = {
      id:
        rawId,

      log:
        rawNumericLogId !== null &&
        Number.isSafeInteger(
          rawNumericLogId
        )
          ? rawNumericLogId
          : null,

      title:
        String(
          rawDetails.title ??
          ''
        ),

      timestamp:
        rawTimestamp,

      category:
        String(
          rawDetails.category ??
          ''
        ),

      data:
        archive.raw.data ??
        {},

      params:
        archive.raw.params ??
        {}
    };

    if (
      !historyLogsEqual(
        historyLogWithoutRawArchive(
          log
        ),
        expectedNormalized
      )
    ) {
      throw new Error(
        'A Torn history raw archive does not match the normalized log content.'
      );
    }

    return archive.raw;
  }

  function historyLogWithoutRawArchive(
    log
  ) {
    const {
      _archive,
      ...normalized
    } =
      log || {};

    return normalized;
  }

  function compareHistoryLogStoragePayloads(
    existingLog,
    incomingLog
  ) {
    const existingRaw =
      validateHistoryRawArchiveBinding(
        existingLog
      );

    const incomingRaw =
      validateHistoryRawArchiveBinding(
        incomingLog
      );

    if (
      !historyLogsEqual(
        historyLogWithoutRawArchive(
          existingLog
        ),
        historyLogWithoutRawArchive(
          incomingLog
        )
      )
    ) {
      return {
        compatible:
          false,
        rewrite:
          false,
        reason:
          'normalized_content_drift'
      };
    }

    if (
      existingRaw &&
      incomingRaw
    ) {
      if (
        !historyLogsEqual(
          existingRaw,
          incomingRaw
        )
      ) {
        return {
          compatible:
            false,
          rewrite:
            false,
          reason:
            'raw_api_content_drift'
        };
      }

      return {
        compatible:
          true,
        rewrite:
          false,
        reason:
          'exact_raw_match'
      };
    }

    if (
      !existingRaw &&
      incomingRaw
    ) {
      return {
        compatible:
          true,
        rewrite:
          true,
        reason:
          'raw_archive_upgrade'
      };
    }

    if (
      existingRaw &&
      !incomingRaw
    ) {
      return {
        compatible:
          false,
        rewrite:
          false,
        reason:
          'raw_archive_downgrade'
      };
    }

    return {
      compatible:
        true,
      rewrite:
        false,
      reason:
        'legacy_exact_match'
    };
  }

  function normalizeV2Logs(
    json
  ) {

    const source =
      json?.log ??
      [];

    if (
      !Array.isArray(
        source
      )
    ) {
      return [];
    }

    return source
      .filter(Boolean)
      .map(
        entry => {

          const id =
            canonicalLogId(
              entry.id
            );

          const timestamp =
            Number(
              entry.timestamp
            );

          if (
            !id ||
            !Number.isSafeInteger(
              timestamp
            ) ||
            timestamp < 0
          ) {
            return null;
          }

          let rawArchive;

          try {
            rawArchive =
              cloneHistoryRawApiRecord(
                entry
              );
          } catch (_) {
            return null;
          }

          const details =
            entry.details &&
            typeof entry.details ===
              'object'
              ? entry.details
              : {};

          const numericLogId =
            details.id === null ||
            details.id === undefined
              ? null
              : Number(
                  details.id
                );

          return {
            id,

            log:
              numericLogId !== null &&
              Number.isSafeInteger(
                numericLogId
              )
                ? numericLogId
                : null,

            title:
              String(
                details.title ??
                ''
              ),

            timestamp,

            category:
              String(
                details.category ??
                ''
              ),

            data:
              entry.data ??
              {},

            params:
              entry.params ??
              {},

            _archive: {
              format:
                HISTORY_RAW_ARCHIVE_FORMAT,
              raw:
                rawArchive
            }
          };
        }
      )
      .filter(Boolean);
  }

  function logIdentity(
    log
  ) {

    const id =
      canonicalLogId(
        log?.id
      );

    if (
      id
    ) {
      return id;
    }

    return (
      `${log?.timestamp}|` +
      `${log?.log}|` +
      `${log?.title}|` +
      `${JSON.stringify(log?.data ?? {})}`
    );
  }

  function deduplicateLogs(
    groups
  ) {

    const map =
      new Map();

    for (
      const logs
      of groups
    ) {

      for (
        const log
        of logs ||
        []
      ) {

        if (
          !log
        ) {
          continue;
        }

        const key =
          logIdentity(
            log
          );

        if (
          !map.has(
            key
          )
        ) {

          map.set(
            key,
            log
          );
        }
      }
    }

    return [
      ...map.values()
    ].sort(
      (
        a,
        b
      ) =>
        Number(
          a.timestamp ||
          0
        ) -
        Number(
          b.timestamp ||
          0
        ) ||
        String(
          a.id ??
          ''
        ).localeCompare(
          String(
            b.id ??
            ''
          )
        )
    );
  }

  // ============================================================
  // DEFENSIVE LOG FETCHING
  // ============================================================

  function createRangeSafetyState() {
    return {
      attempts:
        0,

      max_attempts:
        MAX_RANGE_NETWORK_ATTEMPTS
    };
  }

  function createHistoryTargetTraceState(
    targetId,
    targetTimestamp
  ) {
    const normalizedId =
      String(
        targetId ??
        ''
      ).trim();

    const normalizedTimestamp =
      Number(
        targetTimestamp
      );

    if (
      !normalizedId ||
      !Number.isSafeInteger(
        normalizedTimestamp
      ) ||
      normalizedTimestamp < 0
    ) {
      throw new Error(
        'History target tracing requires a valid log ID and timestamp.'
      );
    }

    return {
      target_id:
        normalizedId,

      target_timestamp:
        normalizedTimestamp,

      covering_page_count:
        0,

      page_returned_target_count:
        0,

      split_count:
        0,

      events:
        []
    };
  }

  function summarizeHistoryTargetTrace(
    trace,
    finalLogs = []
  ) {
    if (
      !trace ||
      typeof trace !== 'object' ||
      !Array.isArray(
        trace.events
      )
    ) {
      throw new Error(
        'History target trace state is unavailable.'
      );
    }

    const finalRangeRetainedTarget =
      Array.isArray(
        finalLogs
      ) &&
      finalLogs.some(
        log =>
          String(
            log?.id
          ) ===
          trace.target_id
      );

    const paginationMergeRetainedTarget =
      trace.events.some(
        event =>
          event.stage ===
            'pagination_range_complete' &&
          event.range_contains_target ===
            true &&
          event.retained_target ===
            true
      );

    let classification;

    if (
      finalRangeRetainedTarget
    ) {
      classification =
        'retained';
    } else if (
      Number(
        trace.page_returned_target_count ||
        0
      ) > 0
    ) {
      classification =
        'lost_after_api_response';
    } else if (
      Number(
        trace.covering_page_count ||
        0
      ) > 0
    ) {
      classification =
        'covering_request_did_not_return_target';
    } else {
      classification =
        'no_covering_request';
    }

    return {
      target_id:
        trace.target_id,

      target_timestamp:
        trace.target_timestamp,

      covering_page_count:
        Number(
          trace.covering_page_count ||
          0
        ),

      page_returned_target_count:
        Number(
          trace.page_returned_target_count ||
          0
        ),

      pagination_merge_retained_target:
        paginationMergeRetainedTarget,

      final_range_retained_target:
        finalRangeRetainedTarget,

      split_count:
        Number(
          trace.split_count ||
          0
        ),

      classification,

      events:
        trace.events.map(
          event => ({
            ...event
          })
        )
    };
  }

  async function rawLogRequest(
    apiKey,
    from,
    to,
    tracker,
    requestBudget = null
  ) {

    const normalizedFrom =
      Number(
        from
      );

    const normalizedTo =
      Number(
        to
      );

    if (
      !Number.isSafeInteger(
        normalizedFrom
      ) ||
      !Number.isSafeInteger(
        normalizedTo
      ) ||
      normalizedFrom < 0 ||
      normalizedTo <
        normalizedFrom
    ) {
      throw new Error(
        'Refusing to request an invalid Torn log timestamp range.'
      );
    }

    const url =
      `${API_BASE}/user/log` +
      `?from=${encodeURIComponent(normalizedFrom)}` +
      `&to=${encodeURIComponent(normalizedTo)}` +
      `&limit=${API_LIMIT}`;

    const json =
      await apiFetchJson(
        url,
        apiKey,
        tracker,
        1,
        requestBudget
      );

    const source =
      json?.log;

    if (
      !Array.isArray(
        source
      )
    ) {
      throw new Error(
        'Torn API returned an invalid log response shape. No incomplete range will be stored.'
      );
    }

    const logs =
      normalizeV2Logs(
        json
      );

    if (
      logs.length !==
      source.length
    ) {
      throw new Error(
        'Torn API returned one or more malformed log entries. No incomplete range will be stored.'
      );
    }

    const identities =
      new Set();

    for (
      const log
      of logs
    ) {
      if (
        log.timestamp <
          normalizedFrom ||
        log.timestamp >
          normalizedTo
      ) {
        throw new Error(
          `Torn API returned log ${log.id} outside the requested timestamp range. ` +
          'No incomplete range will be stored.'
        );
      }

      if (
        identities.has(
          log.id
        )
      ) {
        throw new Error(
          `Torn API returned duplicate log identity ${log.id} in one response. ` +
          'No ambiguous range will be stored.'
        );
      }

      identities.add(
        log.id
      );
    }

    return logs;
  }

  function validateTornLogPaginationUrl(
    url,
    from,
    to
  ) {
    if (
      typeof url !== 'string' ||
      !url ||
      url.trim() !== url
    ) {
      throw new Error(
        'Torn API returned an invalid log pagination link. No incomplete range will be stored.'
      );
    }

    let parsed;

    try {
      parsed =
        new URL(
          url
        );
    } catch {
      throw new Error(
        'Torn API returned an invalid log pagination link. No incomplete range will be stored.'
      );
    }

    if (
      parsed.protocol !== 'https:' ||
      parsed.hostname !== 'api.torn.com' ||
      parsed.port ||
      parsed.username ||
      parsed.password ||
      parsed.hash ||
      parsed.pathname !== '/v2/user/log' ||
      parsed.searchParams.has(
        'key'
      )
    ) {
      throw new Error(
        'Torn API returned an unsafe log pagination link. No incomplete range will be stored.'
      );
    }

    const normalizedFrom =
      Number(
        from
      );

    const normalizedTo =
      Number(
        to
      );

    if (
      !Number.isSafeInteger(
        normalizedFrom
      ) ||
      !Number.isSafeInteger(
        normalizedTo
      ) ||
      normalizedFrom < 0 ||
      normalizedTo <
        normalizedFrom
    ) {
      throw new Error(
        'Refusing to validate pagination for an invalid Torn log timestamp range.'
      );
    }

    for (
      const name
      of [
        'log',
        'cat',
        'target'
      ]
    ) {
      const values =
        parsed.searchParams.getAll(
          name
        );

      if (
        values.length > 1 ||
        (
          values.length === 1 &&
          values[0] !== ''
        )
      ) {
        throw new Error(
          'Torn API returned a log pagination link that changed the requested log scope. No incomplete range will be stored.'
        );
      }
    }

    const cursorBounds =
      {};

    for (
      const name
      of [
        'from',
        'to'
      ]
    ) {
      const values =
        parsed.searchParams.getAll(
          name
        );

      if (
        values.length > 1
      ) {
        throw new Error(
          'Torn API returned malformed duplicate log pagination cursor parameters. No incomplete range will be stored.'
        );
      }

      if (
        values.length === 1
      ) {
        const rawValue =
          values[0];

        const actual =
          Number(
            rawValue
          );

        if (
          !rawValue ||
          !Number.isSafeInteger(
            actual
          ) ||
          actual < normalizedFrom ||
          actual > normalizedTo
        ) {
          throw new Error(
            'Torn API returned a log pagination cursor outside the requested timestamp range. No incomplete range will be stored.'
          );
        }

        cursorBounds[name] =
          actual;
      }
    }

    if (
      Number.isSafeInteger(
        cursorBounds.from
      ) &&
      Number.isSafeInteger(
        cursorBounds.to
      ) &&
      cursorBounds.from >
        cursorBounds.to
    ) {
      throw new Error(
        'Torn API returned an inverted log pagination cursor range. No incomplete range will be stored.'
      );
    }

    const limitValues =
      parsed.searchParams.getAll(
        'limit'
      );

    if (
      limitValues.length > 1
    ) {
      throw new Error(
        'Torn API returned malformed duplicate log pagination limit parameters. No incomplete range will be stored.'
      );
    }

    if (
      limitValues.length === 1
    ) {
      const limit =
        Number(
          limitValues[0]
        );

      if (
        !limitValues[0] ||
        !Number.isSafeInteger(
          limit
        ) ||
        limit < 1 ||
        limit > API_LIMIT
      ) {
        throw new Error(
          'Torn API returned an invalid log pagination limit. No incomplete range will be stored.'
        );
      }
    }

    for (
      const name
      of [
        'sort',
        'order'
      ]
    ) {
      const values =
        parsed.searchParams.getAll(
          name
        );

      if (
        values.length > 1
      ) {
        throw new Error(
          'Torn API returned malformed duplicate log pagination ordering parameters. No incomplete range will be stored.'
        );
      }

      if (
        values.length === 1 &&
        values[0] &&
        !/^(asc|desc)$/i.test(
          values[0]
        )
      ) {
        throw new Error(
          'Torn API returned an invalid log pagination ordering value. No incomplete range will be stored.'
        );
      }
    }

    return parsed.toString();
  }

  async function rawLogPageRequest(
    apiKey,
    url,
    from,
    to,
    tracker,
    requestBudget = null
  ) {
    const normalizedFrom =
      Number(
        from
      );

    const normalizedTo =
      Number(
        to
      );

    const safeUrl =
      validateTornLogPaginationUrl(
        url,
        normalizedFrom,
        normalizedTo
      );

    const json =
      await apiFetchJson(
        safeUrl,
        apiKey,
        tracker,
        1,
        requestBudget
      );

    const source =
      json?.log;

    if (
      !Array.isArray(
        source
      )
    ) {
      throw new Error(
        'Torn API returned an invalid log response shape. No incomplete range will be stored.'
      );
    }

    const logs =
      normalizeV2Logs(
        json
      );

    if (
      logs.length !==
      source.length
    ) {
      throw new Error(
        'Torn API returned one or more malformed log entries. No incomplete range will be stored.'
      );
    }

    const identities =
      new Set();

    for (
      const log
      of logs
    ) {
      if (
        log.timestamp <
          normalizedFrom ||
        log.timestamp >
          normalizedTo
      ) {
        throw new Error(
          `Torn API returned log ${log.id} outside the requested timestamp range. ` +
          'No incomplete range will be stored.'
        );
      }

      if (
        identities.has(
          log.id
        )
      ) {
        throw new Error(
          `Torn API returned duplicate log identity ${log.id} in one page. ` +
          'No ambiguous range will be stored.'
        );
      }

      identities.add(
        log.id
      );
    }

    const links =
      json?._metadata?.links;

    if (
      !links ||
      typeof links !== 'object' ||
      Array.isArray(
        links
      ) ||
      !Object.prototype.hasOwnProperty.call(
        links,
        'next'
      ) ||
      !Object.prototype.hasOwnProperty.call(
        links,
        'prev'
      )
    ) {
      throw new Error(
        'Torn API returned log data without required pagination metadata. No incomplete range will be stored.'
      );
    }

    const normalizedLinks =
      {};

    for (
      const name
      of [
        'next',
        'prev'
      ]
    ) {
      const value =
        links[name];

      if (
        value === null
      ) {
        normalizedLinks[name] =
          null;
        continue;
      }

      if (
        typeof value !== 'string' ||
        !value ||
        value.trim() !== value
      ) {
        throw new Error(
          'Torn API returned malformed log pagination metadata. No incomplete range will be stored.'
        );
      }

      normalizedLinks[name] =
        validateTornLogPaginationUrl(
          value,
          normalizedFrom,
          normalizedTo
        );
    }

    const targetTrace =
      requestBudget?.history_target_trace;

    if (
      targetTrace &&
      typeof targetTrace === 'object'
    ) {
      const parsedRequest =
        new URL(
          safeUrl
        );

      const requestFrom =
        parsedRequest.searchParams.has(
          'from'
        )
          ? Number(
              parsedRequest.searchParams.get(
                'from'
              )
            )
          : normalizedFrom;

      const requestTo =
        parsedRequest.searchParams.has(
          'to'
        )
          ? Number(
              parsedRequest.searchParams.get(
                'to'
              )
            )
          : normalizedTo;

      const coversTarget =
        Number.isSafeInteger(
          requestFrom
        ) &&
        Number.isSafeInteger(
          requestTo
        ) &&
        targetTrace.target_timestamp >
          requestFrom &&
        targetTrace.target_timestamp <=
          requestTo;

      const returnedTarget =
        logs.some(
          log =>
            log.id ===
            targetTrace.target_id
        );

      if (
        coversTarget
      ) {
        targetTrace.covering_page_count =
          Number(
            targetTrace.covering_page_count ||
            0
          ) + 1;
      }

      if (
        returnedTarget
      ) {
        targetTrace.page_returned_target_count =
          Number(
            targetTrace.page_returned_target_count ||
            0
          ) + 1;
      }

      if (
        (
          coversTarget ||
          returnedTarget
        ) &&
        targetTrace.events.length < 200
      ) {
        targetTrace.events.push({
          stage:
            'page',
          request_from:
            requestFrom,
          request_to:
            requestTo,
          record_count:
            logs.length,
          covers_target:
            coversTarget,
          returned_target:
            returnedTarget,
          prev_is_null:
            normalizedLinks.prev ===
            null,
          next_is_null:
            normalizedLinks.next ===
            null
        });
      }
    }

    return {
      logs,
      next:
        normalizedLinks.next,
      prev:
        normalizedLinks.prev
    };
  }

  async function fetchPaginatedLogRange(
    apiKey,
    from,
    to,
    tracker,
    safetyState = null
  ) {
    const normalizedFrom =
      Number(
        from
      );

    const normalizedTo =
      Number(
        to
      );

    if (
      !Number.isSafeInteger(
        normalizedFrom
      ) ||
      !Number.isSafeInteger(
        normalizedTo
      ) ||
      normalizedFrom < 0 ||
      normalizedTo <
        normalizedFrom
    ) {
      throw new Error(
        'Refusing to request an invalid Torn log timestamp range.'
      );
    }

    const state =
      safetyState ||
      createRangeSafetyState();

    let pageUrl =
      `${API_BASE}/user/log` +
      `?from=${encodeURIComponent(normalizedFrom)}` +
      `&to=${encodeURIComponent(normalizedTo)}` +
      `&limit=${API_LIMIT}`;

    const seenUrls =
      new Set();

    const recordsById =
      new Map();

    let pageCount =
      0;

    while (
      pageUrl
    ) {
      if (
        pageCount >=
        MAX_PAGINATION_PAGES_PER_RANGE
      ) {
        const error =
          new Error(
            `Torn log pagination exceeded ${MAX_PAGINATION_PAGES_PER_RANGE} pages for one timestamp range; splitting the range defensively.`
          );

        error.code =
          'TORN_HISTORY_RANGE_SPLIT_REQUIRED';

        error.request_count =
          pageCount;

        error.provisional_logs =
          Array.from(
            recordsById.values()
          );

        throw error;
      }

      const safeUrl =
        validateTornLogPaginationUrl(
          pageUrl,
          normalizedFrom,
          normalizedTo
        );

      if (
        seenUrls.has(
          safeUrl
        )
      ) {
        throw new Error(
          'Torn API returned a repeated log pagination link. No ambiguous range will be stored.'
        );
      }

      seenUrls.add(
        safeUrl
      );

      const page =
        await rawLogPageRequest(
          apiKey,
          safeUrl,
          normalizedFrom,
          normalizedTo,
          tracker,
          state
        );

      pageCount++;

      for (
        const log
        of page.logs
      ) {
        const existing =
          recordsById.get(
            log.id
          );

        if (
          existing
        ) {
          if (
            stableHistoryJson(
              existing
            ) !==
            stableHistoryJson(
              log
            )
          ) {
            throw new Error(
              `Torn API returned the same log identity with different content across pagination pages: ${log.id}. ` +
              'No ambiguous range will be stored.'
            );
          }

          continue;
        }

        recordsById.set(
          log.id,
          log
        );
      }

      // Torn's generated pagination chain can move its timestamp cursor
      // past valid records even when those records remain available through a
      // direct narrow /user/log request. Device forensics reproduced this on
      // both 100-record and 99-record multi-second responses. A dense
      // multi-second page therefore cannot prove its range complete. Preserve
      // the validated page, then timestamp-split until direct responses fall
      // below the conservative density threshold.
      //
      // A one-second logical range (from, to] cannot be timestamp-split any
      // further. For that indivisible case, continue through safe metadata
      // pagination when Torn provides it; a full terminal page fails closed
      // below instead of being accepted as complete.
      if (
        page.logs.length >=
          SAFE_SPLIT_THRESHOLD &&
        normalizedTo -
          normalizedFrom >
          1
      ) {
        const targetTrace =
          state?.history_target_trace;

        if (
          targetTrace &&
          targetTrace.target_timestamp >
            normalizedFrom &&
          targetTrace.target_timestamp <=
            normalizedTo &&
          targetTrace.events.length < 200
        ) {
          targetTrace.events.push({
            stage:
              'pagination_split_required',
            reason:
              'saturated_page',
            range_from:
              normalizedFrom,
            range_to:
              normalizedTo,
            page_count:
              pageCount,
            page_returned_target:
              page.logs.some(
                log =>
                  log.id ===
                  targetTrace.target_id
              ),
            retained_before_split:
              recordsById.has(
                targetTrace.target_id
              )
          });
        }

        const error =
          new Error(
            `Torn log request returned a saturated page (${page.logs.length} records); splitting the range defensively.`
          );

        error.code =
          'TORN_HISTORY_RANGE_SPLIT_REQUIRED';

        error.request_count =
          pageCount;

        error.provisional_logs =
          Array.from(
            recordsById.values()
          );

        throw error;
      }

      if (
        page.logs.length >=
          API_LIMIT &&
        normalizedTo -
          normalizedFrom <=
          1 &&
        page.prev ===
          null
      ) {
        throw new Error(
          `Torn returned ${page.logs.length} logs inside indivisible range (${normalizedFrom}, ${normalizedTo}] without another pagination page. Completeness cannot be proven, so no incomplete range will be stored.`
        );
      }

      const targetTraceAfterMerge =
        state?.history_target_trace;

      if (
        targetTraceAfterMerge &&
        targetTraceAfterMerge.target_timestamp >
          normalizedFrom &&
        targetTraceAfterMerge.target_timestamp <=
          normalizedTo &&
        targetTraceAfterMerge.events.length < 200
      ) {
        targetTraceAfterMerge.events.push({
          stage:
            'pagination_page_merge',
          range_from:
            normalizedFrom,
          range_to:
            normalizedTo,
          page_count:
            pageCount,
          retained_target:
            recordsById.has(
              targetTraceAfterMerge.target_id
            )
        });
      }

      if (
        page.prev === null
      ) {
        pageUrl =
          null;
      } else {
        // Torn's generated older-page cursor can step below the oldest
        // returned timestamp. If more than one distinct log shares that
        // boundary second, following the generated cursor verbatim can skip
        // an identity. Validate the metadata link, but overlap the oldest
        // timestamp actually observed and deduplicate by Torn log ID/content.
        if (
          seenUrls.has(
            page.prev
          )
        ) {
          throw new Error(
            'Torn API returned a repeated log pagination link. No ambiguous range will be stored.'
          );
        }

        if (
          page.logs.length === 0
        ) {
          pageUrl =
            page.prev;
        } else {
          let oldestTimestamp =
            page.logs[0].timestamp;

          for (
            const log
            of page.logs
          ) {
            if (
              log.timestamp <
                oldestTimestamp
            ) {
              oldestTimestamp =
                log.timestamp;
            }
          }

          const overlapUrl =
            new URL(
              page.prev
            );

          overlapUrl.searchParams.set(
            'from',
            String(
              normalizedFrom
            )
          );

          overlapUrl.searchParams.set(
            'to',
            String(
              oldestTimestamp
            )
          );

          overlapUrl.searchParams.set(
            'limit',
            String(
              API_LIMIT
            )
          );

          pageUrl =
            validateTornLogPaginationUrl(
              overlapUrl.toString(),
              normalizedFrom,
              normalizedTo
            );
        }
      }
    }

    const logs =
      deduplicateLogs(
        [
          Array.from(
            recordsById.values()
          )
        ]
      );

    if (
      logs.length !==
      recordsById.size
    ) {
      throw new Error(
        'Torn API returned ambiguous duplicate log identities across pagination pages. No incomplete range will be stored.'
      );
    }

    const targetTrace =
      state?.history_target_trace;

    if (
      targetTrace &&
      targetTrace.target_timestamp >
        normalizedFrom &&
      targetTrace.target_timestamp <=
        normalizedTo &&
      targetTrace.events.length < 200
    ) {
      targetTrace.events.push({
        stage:
          'pagination_range_complete',
        range_from:
          normalizedFrom,
        range_to:
          normalizedTo,
        range_contains_target:
          true,
        retained_target:
          recordsById.has(
            targetTrace.target_id
          ),
        result_count:
          logs.length,
        page_count:
          pageCount
      });
    }

    return {
      logs,
      request_count:
        pageCount,
      split_count:
        0,
      unsplittable_near_limit:
        false
    };
  }

  async function fetchCompleteRange(
    apiKey,
    from,
    to,
    tracker,
    safetyState = null,
    splitDepth = 0
  ) {

    if (
      from >
      to
    ) {

      return {
        logs:
          [],

        request_count:
          0,

        split_count:
          0,

        unsplittable_near_limit:
          false
      };
    }

    const state =
      safetyState ||
      createRangeSafetyState();

    if (
      splitDepth >
      MAX_RANGE_SPLIT_DEPTH
    ) {
      throw new Error(
        `Defensive log collection stopped after exceeding ${MAX_RANGE_SPLIT_DEPTH} split levels. ` +
        'No incomplete range will be stored.'
      );
    }

    try {
      return await fetchPaginatedLogRange(
        apiKey,
        from,
        to,
        tracker,
        state
      );
    } catch (
      error
    ) {
      if (
        error?.code !==
        'TORN_HISTORY_RANGE_SPLIT_REQUIRED'
      ) {
        throw error;
      }

      const span =
        to -
        from;

      if (
        span <= 1
      ) {
        throw new Error(
          `Defensive log collection cannot prove completeness for timestamp ${from}: ` +
          'the authoritative pagination chain exceeded its page safety cap. ' +
          'No incomplete range will be stored.'
        );
      }

      tracker?.incrementSplit();

      const targetTrace =
        state?.history_target_trace;

      if (
        targetTrace
      ) {
        targetTrace.split_count =
          Number(
            targetTrace.split_count ||
            0
          ) + 1;

        if (
          targetTrace.target_timestamp >
            from &&
          targetTrace.target_timestamp <=
            to &&
          targetTrace.events.length < 200
        ) {
          targetTrace.events.push({
            stage:
              'range_split',
            range_from:
              from,
            range_to:
              to,
            split_depth:
              splitDepth
          });
        }
      }

      const midpoint =
        Math.floor(
          from +
          span /
          2
        );

      const left =
        await fetchCompleteRange(
          apiKey,
          from,
          midpoint,
          tracker,
          state,
          splitDepth + 1
        );

      // Torn /user/log treats `from` as exclusive and `to` as inclusive.
      // Split the logical range (from, to] as (from, midpoint] plus
      // (midpoint, to]. Advancing the right cursor to midpoint + 1 would
      // silently omit every log whose timestamp equals midpoint + 1.
      const right =
        await fetchCompleteRange(
          apiKey,
          midpoint,
          to,
          tracker,
          state,
          splitDepth + 1
        );

      const mergeSources =
        [
          Array.isArray(
            error.provisional_logs
          )
            ? error.provisional_logs
            : [],
          left.logs,
          right.logs
        ];

      const mergedById =
        new Map();

      for (
        const sourceLogs
        of mergeSources
      ) {
        for (
          const log
          of sourceLogs
        ) {
          const existing =
            mergedById.get(
              log.id
            );

          if (
            existing
          ) {
            if (
              stableHistoryJson(
                existing
              ) !==
              stableHistoryJson(
                log
              )
            ) {
              throw new Error(
                `Torn API returned the same log identity with different content across a defensive range split: ${log.id}. ` +
                'No ambiguous range will be stored.'
              );
            }

            continue;
          }

          mergedById.set(
            log.id,
            log
          );
        }
      }

      const mergedLogs =
        deduplicateLogs([
          Array.from(
            mergedById.values()
          )
        ]);

      const targetTraceAfterSplit =
        state?.history_target_trace;

      if (
        targetTraceAfterSplit &&
        targetTraceAfterSplit.target_timestamp >
          from &&
        targetTraceAfterSplit.target_timestamp <=
          to &&
        targetTraceAfterSplit.events.length < 200
      ) {
        targetTraceAfterSplit.events.push({
          stage:
            'split_merge',
          range_from:
            from,
          range_to:
            to,
          midpoint,
          left_retained_target:
            left.logs.some(
              log =>
                log.id ===
                targetTraceAfterSplit.target_id
            ),
          right_retained_target:
            right.logs.some(
              log =>
                log.id ===
                targetTraceAfterSplit.target_id
            ),
          retained_target:
            mergedLogs.some(
              log =>
                log.id ===
                targetTraceAfterSplit.target_id
            )
        });
      }

      return {
        logs:
          mergedLogs,

        request_count:
          Number(
            error.request_count ||
            0
          ) +
          left.request_count +
          right.request_count,

        split_count:
          1 +
          left.split_count +
          right.split_count,

        unsplittable_near_limit:
          false
      };
    }
  }

  // ============================================================
  // HISTORY SEGMENTS
  // ============================================================

  function createSegments(
    fromDate,
    throughDate
  ) {

    const segments =
      [];

    let start =
      fromDate;

    let index =
      0;

    while (
      start <=
      throughDate
    ) {

      let end =
        addDays(
          start,
          SEGMENT_DAYS -
          1
        );

      if (
        end >
        throughDate
      ) {
        end =
          throughDate;
      }

      segments.push({
        index,
        from_date:
          start,

        to_date:
          end
      });

      if (
        end ===
        throughDate
      ) {
        break;
      }

      start =
        end;

      index++;
    }

    return segments;
  }

  // ============================================================
  // FIRST-RUN / RESUMABLE HISTORY BUILD
  // ============================================================

  async function buildHistory(
    apiKey,
    tracker,
    forceFresh = false
  ) {

    tracker.reset();

    const account =
      await detectAccount(
        apiKey,
        tracker
      );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    currentAccount =
      account;

    // If protected history already exists but its native per-script key was
    // lost, restore it from this account's authenticated recovery envelope
    // before any cached history is read. If the key is healthy, this also
    // refreshes a stale envelope after an API-key rotation.
    await ensureHistoryRecoveryEnvelope(
      apiKey,
      account.id
    );

    latestItemMap =
      await loadItemDictionary(
        apiKey,
        tracker,
        true
      );

    const throughDate =
      todayLocal();

    const segments =
      createSegments(
        account.signup_local_date,
        throughDate
      );

    const collectorCompatibility =
      'v2.8-same-second-pagination-overlap';

    let state =
      await getBuildState(
        account.id
      );

    // Full Rebuild intentionally does not resume or write the normal build
    // checkpoint while collecting. The live encrypted history remains the
    // authoritative generation until the complete replacement is verified and
    // atomically promoted at the end.
    if (
      forceFresh
    ) {
      state =
        null;
    }

    let nextSegment =
      0;

    if (
      !forceFresh &&
      state?.in_progress &&
      state?.collector_compatibility ===
        collectorCompatibility
    ) {

      nextSegment =
        Number(
          state.next_segment ||
          0
        );
    }

    if (
      !forceFresh &&
      (
        !state ||
        !state.in_progress ||
        state.collector_compatibility !==
          collectorCompatibility
      )
    ) {

      state = {
        account_id:
          account.id,

        in_progress:
          true,

        collector_compatibility:
          collectorCompatibility,

        started_at:
          Date.now(),

        next_segment:
          0,

        segment_count:
          segments.length,

        completed_through:
          null
      };

      await setBuildState(
        account.id,
        state
      );
    }

    const existing =
      await dbLoadLogs(
        account.id
      );

    tracker.setLogs(
      existing.length
    );

    let stagedLogs =
      forceFresh
        ? []
        : null;

    let anyUnsplittable =
      false;

    for (
      let i =
        nextSegment;
      i <
      segments.length;
      i++
    ) {

      const segment =
        segments[i];

      // Keep the hard network-attempt cap, but scope it to this independently
      // bounded weekly segment. A complete account rebuild can legitimately
      // require more than 512 requests across all dense weeks combined.
      const collectionSafetyState =
        createRangeSafetyState();

      tracker.setStage(
        forceFresh
          ? 'Rebuilding history safely…'
          : (
              i === nextSegment &&
              nextSegment > 0
                ? 'Resuming history build…'
                : 'Building history…'
            ),

        `${segment.from_date} → ${segment.to_date}`
      );

      // Torn API `from` is exclusive. Start one second before the
      // authenticated signup timestamp so logs emitted at the exact signup
      // second (including account-creation records) are not omitted.
      const from =
        Math.max(
          startOfDayTimestamp(
            segment.from_date
          ),
          account.signup_timestamp - 1
        );

      const to =
        segment.to_date ===
        todayLocal()
          ? Math.floor(
              Date.now() /
              1000
            )
          : endOfDayTimestamp(
              segment.to_date
            );

      const result =
        await fetchCompleteRange(
          apiKey,
          from,
          to,
          tracker,
          collectionSafetyState
        );

      anyUnsplittable ||=
        result.unsplittable_near_limit;

      if (
        forceFresh
      ) {
        stagedLogs =
          deduplicateLogs([
            stagedLogs,
            result.logs
          ]);

        tracker.setLogs(
          stagedLogs.length
        );
      } else {
        await dbStoreLogs(
          account.id,
          result.logs
        );

        // The first encrypted write initializes the history key/canary. Create
        // this account's recovery envelope immediately afterward so a new
        // installation does not depend on native key storage as its only path.
        await ensureHistoryRecoveryEnvelope(
          apiKey,
          account.id
        );

        const currentLogs =
          await dbLoadLogs(
            account.id
          );

        tracker.setLogs(
          currentLogs.length
        );

        state = {
          ...state,

          next_segment:
            i + 1,

          completed_through:
            segment.to_date,

          last_checkpoint_at:
            Date.now()
        };

        await setBuildState(
          account.id,
          state
        );
      }

      const completed =
        i + 1;

      tracker.setPercent(
        5 +
        90 *
        (
          completed /
          segments.length
        )
      );
    }

    if (
      forceFresh
    ) {
      if (
        !stagedLogs.length
      ) {
        throw new Error(
          'Full Rebuild collected no Torn logs. Existing history was preserved.'
        );
      }

      tracker.setStage(
        'Verifying rebuilt history…',
        `${stagedLogs.length.toLocaleString()} staged logs; existing history remains untouched`
      );

      tracker.setPercent(
        96
      );

      await dbPromoteStagedAccountHistory(
        account.id,
        stagedLogs
      );

      await ensureHistoryRecoveryEnvelope(
        apiKey,
        account.id
      );
    }

    latestLogs =
      await dbLoadLogs(
        account.id
      );

    if (
      forceFresh &&
      latestLogs.length !==
        stagedLogs.length
    ) {
      throw new Error(
        'Full Rebuild promotion verification found an unexpected stored-log count mismatch.'
      );
    }

    await saveAccountCacheMeta(
      account,
      latestLogs,
      forceFresh
        ? 'history_rebuild'
        : 'history_build'
    );

    await clearBuildState(
      account.id
    );

    tracker.setPercent(
      97
    );

    tracker.setStage(
      'Building analytics…',
      `${latestLogs.length.toLocaleString()} stored logs`
    );

    latestAnalysis =
      buildBasicAnalysis(
        latestLogs,
        latestItemMap
      );

    latestAnalysis.resource_flow =
      buildResourceFlow(
        latestLogs
      );

    tracker.setPercent(
      100
    );

    tracker.setStage(
      'History ready',
      `${latestLogs.length.toLocaleString()} logs saved permanently`
    );

    return {
      account,
      logs:
        latestLogs,

      integrity:
        anyUnsplittable
          ? 'review_required'
          : 'complete'
    };
  }

  // ============================================================
  // INCREMENTAL UPDATES
  // ============================================================

  async function fetchIncrementalLogBatch(
    apiKey,
    account,
    lastTimestamp,
    tracker
  ) {
    const normalizedLastTimestamp =
      Number(
        lastTimestamp
      );

    if (
      !Number.isSafeInteger(
        normalizedLastTimestamp
      ) ||
      normalizedLastTimestamp <
        Number(
          account?.signup_timestamp
        )
    ) {
      throw new Error(
        'Stored history has an invalid latest timestamp. Incremental collection was not attempted.'
      );
    }

    const overlapStart =
      Math.max(
        account.signup_timestamp,

        normalizedLastTimestamp -
        UPDATE_OVERLAP_DAYS *
        86400
      );

    const now =
      Math.floor(
        Date.now() /
        1000
      );

    const collectionSafetyState =
      createRangeSafetyState();

    tracker.setStage(
      'Updating logs…',
      `${timestampToLocalDate(overlapStart)} → now`
    );

    tracker.setPercent(
      20
    );

    const result =
      await fetchCompleteRange(
        apiKey,
        overlapStart,
        now,
        tracker,
        collectionSafetyState
      );

    return {
      ...result,
      overlap_start:
        overlapStart,
      through_timestamp:
        now
    };
  }

  async function updateLogs(
    apiKey,
    tracker
  ) {

    tracker.reset();

    const account =
      await detectAccount(
        apiKey,
        tracker
      );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    currentAccount =
      account;

    // Recover a missing native history key, or refresh this account's
    // recovery envelope after an API-key rotation, before cached history is read.
    await ensureHistoryRecoveryEnvelope(
      apiKey,
      account.id
    );

    latestItemMap =
      await loadItemDictionary(
        apiKey,
        tracker,
        true
      );

    const existing =
      await dbLoadLogs(
        account.id
      );

    if (
      !existing.length
    ) {

      throw new Error(
        'No stored history exists yet. Build your history first.'
      );
    }

    const lastTimestamp =
      Number(
        existing[
          existing.length -
          1
        ].timestamp
      );

    const result =
      await fetchIncrementalLogBatch(
        apiKey,
        account,
        lastTimestamp,
        tracker
      );

    tracker.setPercent(
      70
    );

    await dbStoreLogs(
      account.id,
      result.logs
    );

    await ensureHistoryRecoveryEnvelope(
      apiKey,
      account.id
    );

    latestLogs =
      await dbLoadLogs(
        account.id
      );

    const added =
      latestLogs.length -
      existing.length;

    await saveAccountCacheMeta(
      account,
      latestLogs,
      'incremental_update'
    );

    tracker.setLogs(
      latestLogs.length
    );

    tracker.setStage(
      'Building analytics…',
      `${added.toLocaleString()} new unique logs`
    );

    tracker.setPercent(
      90
    );

    latestAnalysis =
      buildBasicAnalysis(
        latestLogs,
        latestItemMap
      );

    latestAnalysis.resource_flow =
      buildResourceFlow(
        latestLogs
      );

    tracker.setPercent(
      100
    );

    tracker.setStage(
      'Update complete',
      `${added.toLocaleString()} new logs added`
    );

    return {
      account,
      added,
      logs:
        latestLogs
    };
  }
  // ============================================================
  // LIGHTWEIGHT AUTOMATIC LOG SYNCHRONIZATION
  // ============================================================

  const AUTOMATIC_LOG_SYNC_STATE_EVENT =
    'ta-automatic-log-sync-state';

  function automaticLogSyncPageActive() {
    const visible =
      typeof document ===
        'undefined' ||
      !document.visibilityState ||
      document.visibilityState ===
        'visible';

    const online =
      typeof navigator ===
        'undefined' ||
      navigator.onLine !==
        false;

    return (
      visible &&
      online
    );
  }

  function automaticLogSyncHistoryAvailable(
    meta
  ) {
    const accountId =
      Number(
        meta?.account_id
      );

    const count =
      Number(
        meta?.count
      );

    return (
      Number.isSafeInteger(
        accountId
      ) &&
      accountId > 0 &&
      Number.isSafeInteger(
        count
      ) &&
      count > 0
    );
  }

  function automaticLogSyncDue(
    meta,
    now = Date.now()
  ) {
    if (
      !automaticLogSyncHistoryAvailable(
        meta
      )
    ) {
      return false;
    }

    const updatedAt =
      Number(
        meta.updated_at ||
        0
      );

    return (
      !updatedAt ||
      updatedAt >
        Number(now) ||
      Math.max(
        0,
        Number(now) -
        updatedAt
      ) >=
        AUTO_SYNC_STALE_MS
    );
  }

  function automaticLogSyncDueDelay(
    meta,
    now = Date.now()
  ) {
    if (
      automaticLogSyncDue(
        meta,
        now
      )
    ) {
      return 0;
    }

    const updatedAt =
      Number(
        meta?.updated_at ||
        0
      );

    if (
      !updatedAt
    ) {
      return AUTO_SYNC_STALE_MS;
    }

    return Math.max(
      AUTO_SYNC_INITIAL_DELAY_MS,
      AUTO_SYNC_STALE_MS -
        Math.max(
          0,
          Number(now) -
          updatedAt
        )
    );
  }

  function automaticLogSyncStatusText(
    meta,
    syncRunning = automaticLogSyncRunning
  ) {
    if (
      syncRunning
    ) {
      return 'Updating recent logs now. Dashboard analysis remains deferred until the tool is open.';
    }

    if (
      !automaticLogSyncHistoryAvailable(
        meta
      )
    ) {
      return 'Automatic updates begin after the initial history build.';
    }

    const updatedAt =
      Number(
        meta.updated_at ||
        0
      );

    const lastUpdate =
      updatedAt
        ? new Date(
            updatedAt
          ).toLocaleString()
        : 'not recorded yet';

    return (
      'On while Torn is active. Checks when history is at least 30 minutes old; ' +
      `last history update: ${lastUpdate}.`
    );
  }

  function automaticLogSyncOwnerToken() {
    if (
      automaticLogSyncLeaseOwner
    ) {
      return automaticLogSyncLeaseOwner;
    }

    const randomPart =
      typeof globalThis?.crypto
        ?.randomUUID ===
        'function'
        ? globalThis.crypto
            .randomUUID()
        : `${Date.now()}-${Math.random()}`;

    automaticLogSyncLeaseOwner =
      `torn-analytics-${randomPart}`;

    return automaticLogSyncLeaseOwner;
  }

  async function tryAcquireAutomaticLogSyncLease(
    owner,
    now = Date.now()
  ) {
    const normalizedOwner =
      String(
        owner ||
        ''
      ).trim();

    if (
      !normalizedOwner
    ) {
      throw new Error(
        'Automatic synchronization requires a valid lease owner.'
      );
    }

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx =
          db.transaction(
            META_STORE,
            'readwrite'
          );

        const store =
          tx.objectStore(
            META_STORE
          );

        const request =
          store.get(
            AUTO_SYNC_LEASE_META_KEY
          );

        let acquired = false;

        request.onsuccess =
          () => {
            const lease =
              request.result
                ?.value;

            const activeOtherLease =
              lease?.owner &&
              lease.owner !==
                normalizedOwner &&
              Number(
                lease.expires_at ||
                0
              ) >
                Number(now);

            if (
              activeOtherLease
            ) {
              return;
            }

            acquired = true;

            store.put({
              key:
                AUTO_SYNC_LEASE_META_KEY,

              value: {
                owner:
                  normalizedOwner,
                acquired_at:
                  Number(now),
                expires_at:
                  Number(now) +
                  AUTO_SYNC_LEASE_MS
              }
            });
          };

        tx.oncomplete =
          () => {
            db.close();
            resolve(
              acquired
            );
          };

        tx.onerror =
          () => {
            db.close();
            reject(
              tx.error
            );
          };

        tx.onabort =
          () => {
            db.close();
            reject(
              tx.error ||
              new Error(
                'Automatic synchronization lease acquisition was aborted.'
              )
            );
          };
      }
    );
  }

  async function releaseAutomaticLogSyncLease(
    owner
  ) {
    const normalizedOwner =
      String(
        owner ||
        ''
      ).trim();

    if (
      !normalizedOwner
    ) {
      return false;
    }

    const db =
      await openDatabase();

    return new Promise(
      (
        resolve,
        reject
      ) => {
        const tx =
          db.transaction(
            META_STORE,
            'readwrite'
          );

        const store =
          tx.objectStore(
            META_STORE
          );

        const request =
          store.get(
            AUTO_SYNC_LEASE_META_KEY
          );

        let released = false;

        request.onsuccess =
          () => {
            if (
              request.result
                ?.value
                ?.owner !==
              normalizedOwner
            ) {
              return;
            }

            released = true;

            store.delete(
              AUTO_SYNC_LEASE_META_KEY
            );
          };

        tx.oncomplete =
          () => {
            db.close();
            resolve(
              released
            );
          };

        tx.onerror =
          () => {
            db.close();
            reject(
              tx.error
            );
          };

        tx.onabort =
          () => {
            db.close();
            reject(
              tx.error ||
              new Error(
                'Automatic synchronization lease release was aborted.'
              )
            );
          };
      }
    );
  }

  function dispatchAutomaticLogSyncState(
    running,
    detail = {}
  ) {
    automaticLogSyncRunning =
      running ===
      true;

    if (
      typeof document ===
        'undefined'
    ) {
      return;
    }

    const eventDetail = {
      ...detail,
      running:
        automaticLogSyncRunning
    };

    let event =
      null;

    if (
      typeof CustomEvent ===
        'function'
    ) {
      event =
        new CustomEvent(
          AUTOMATIC_LOG_SYNC_STATE_EVENT,
          {
            detail:
              eventDetail
          }
        );
    } else if (
      typeof document.createEvent ===
        'function'
    ) {
      event =
        document.createEvent(
          'CustomEvent'
        );

      event.initCustomEvent(
        AUTOMATIC_LOG_SYNC_STATE_EVENT,
        false,
        false,
        eventDetail
      );
    }

    if (
      event
    ) {
      document.dispatchEvent(
        event
      );
    }
  }

  async function synchronizeLogsInBackground(
    apiKey,
    tracker,
    cachedMeta = null
  ) {
    tracker.reset();

    const cached =
      cachedMeta ||
      await getLastCacheMeta();

    if (
      !automaticLogSyncHistoryAvailable(
        cached
      )
    ) {
      throw new Error(
        'No stored history exists yet. Build your history first.'
      );
    }

    await assertStoredSingleAccountOwner(
      cached.account_id
    );

    const account =
      await detectAccount(
        apiKey,
        tracker
      );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    if (
      Number(
        account.id
      ) !==
      Number(
        cached.account_id
      )
    ) {
      throw new Error(
        `Torn account mismatch: stored history belongs to ${cached.account_id}, but the authenticated account is ${account.id}. Operation blocked.`
      );
    }

    // Keep the same recovery and authenticated-overlap protections as the
    // manual update path. Only analysis and item-name work are deferred.
    await ensureHistoryRecoveryEnvelope(
      apiKey,
      account.id
    );

    const result =
      await fetchIncrementalLogBatch(
        apiKey,
        account,
        cached.last_timestamp,
        tracker
      );

    tracker.setPercent(
      70
    );

    await dbStoreLogs(
      account.id,
      result.logs
    );

    await ensureHistoryRecoveryEnvelope(
      apiKey,
      account.id
    );

    const storedCount =
      await dbCountAccountLogs(
        account.id
      );

    const priorCount =
      Number(
        cached.count
      );

    if (
      !Number.isSafeInteger(
        storedCount
      ) ||
      storedCount <
        priorCount
    ) {
      throw new Error(
        'Automatic synchronization detected an invalid stored-log count. Cache metadata was not changed.'
      );
    }

    const fetchedLastTimestamp =
      result.logs.reduce(
        (
          latest,
          log
        ) =>
          Math.max(
            latest,
            Number(
              log?.timestamp ||
              0
            )
          ),
        Number(
          cached.last_timestamp
        )
      );

    const savedMeta =
      await saveAccountCacheMetaSummary(
        account,
        {
          first_timestamp:
            Number(
              cached.first_timestamp
            ),
          last_timestamp:
            fetchedLastTimestamp,
          count:
            storedCount
        },
        'automatic_incremental_update'
      );

    const added =
      storedCount -
      priorCount;

    tracker.setLogs(
      storedCount
    );

    tracker.setPercent(
      100
    );

    tracker.setStage(
      'Automatic update complete',
      `${added.toLocaleString()} new logs added`
    );

    return {
      account,
      added,
      count:
        storedCount,
      meta:
        savedMeta
    };
  }

  function clearAutomaticLogSyncTimer() {
    if (
      automaticLogSyncTimer !==
        null &&
      typeof clearTimeout ===
        'function'
    ) {
      clearTimeout(
        automaticLogSyncTimer
      );
    }

    automaticLogSyncTimer =
      null;
  }

  function scheduleAutomaticLogSync(
    delay = AUTO_SYNC_INITIAL_DELAY_MS
  ) {
    clearAutomaticLogSyncTimer();

    if (
      !automaticLogSyncPageActive() ||
      typeof setTimeout !==
        'function'
    ) {
      return;
    }

    automaticLogSyncTimer =
      setTimeout(
        () => {
          automaticLogSyncTimer =
            null;

          void runAutomaticLogSyncIfDue()
            .catch(
              error => {
                console.warn(
                  '[Torn Analytics] Automatic log synchronization check failed:',
                  error
                );

                scheduleAutomaticLogSync(
                  AUTO_SYNC_ERROR_BACKOFF_MS
                );
              }
            );
        },
        Math.max(
          AUTO_SYNC_INITIAL_DELAY_MS,
          Number(delay) ||
          0
        )
      );
  }

  async function runAutomaticLogSyncIfDue() {
    if (
      !automaticLogSyncPageActive()
    ) {
      clearAutomaticLogSyncTimer();

      return {
        status:
          'inactive'
      };
    }

    if (
      automaticLogSyncRunning ||
      running ||
      document.getElementById(
        MODAL_ID
      )
    ) {
      scheduleAutomaticLogSync(
        AUTO_SYNC_BUSY_RETRY_MS
      );

      return {
        status:
          'busy'
      };
    }

    const cached =
      await getLastCacheMeta();

    if (
      !automaticLogSyncHistoryAvailable(
        cached
      )
    ) {
      scheduleAutomaticLogSync(
        AUTO_SYNC_STALE_MS
      );

      return {
        status:
          'no_history'
      };
    }

    if (
      !automaticLogSyncDue(
        cached
      )
    ) {
      scheduleAutomaticLogSync(
        automaticLogSyncDueDelay(
          cached
        )
      );

      return {
        status:
          'fresh'
      };
    }

    const apiKey =
      await loadSecureApiKey();

    if (
      !apiKey
    ) {
      scheduleAutomaticLogSync(
        AUTO_SYNC_ERROR_BACKOFF_MS
      );

      return {
        status:
          'no_api_key'
      };
    }

    const leaseOwner =
      automaticLogSyncOwnerToken();

    const acquired =
      await tryAcquireAutomaticLogSyncLease(
        leaseOwner
      );

    if (
      !acquired
    ) {
      scheduleAutomaticLogSync(
        AUTO_SYNC_BUSY_RETRY_MS
      );

      return {
        status:
          'leased_elsewhere'
      };
    }

    let started = false;
    let nextDelay =
      AUTO_SYNC_STALE_MS;

    try {
      // Another tab may have completed while this tab waited for the lease.
      const refreshed =
        await getLastCacheMeta();

      if (
        !automaticLogSyncDue(
          refreshed
        )
      ) {
        nextDelay =
          automaticLogSyncDueDelay(
            refreshed
          );

        return {
          status:
            'fresh_after_lease'
        };
      }

      started = true;

      dispatchAutomaticLogSyncState(
        true,
        {
          status:
            'updating'
        }
      );

      const tracker =
        new ProgressTracker();

      const result =
        await synchronizeLogsInBackground(
          apiKey,
          tracker,
          refreshed
        );

      console.info(
        '[Torn Analytics] Automatic log update complete:',
        `${result.added} new logs; ${result.count} stored.`
      );

      return {
        status:
          'updated',
        ...result
      };
    } catch (
      error
    ) {
      nextDelay =
        AUTO_SYNC_ERROR_BACKOFF_MS;

      console.warn(
        '[Torn Analytics] Automatic log update deferred:',
        error
      );

      return {
        status:
          'failed',
        error
      };
    } finally {
      if (
        started
      ) {
        dispatchAutomaticLogSyncState(
          false,
          {
            status:
              nextDelay ===
                AUTO_SYNC_ERROR_BACKOFF_MS
                ? 'failed'
                : 'complete'
          }
        );
      }

      try {
        await releaseAutomaticLogSyncLease(
          leaseOwner
        );
      } catch (
        error
      ) {
        console.warn(
          '[Torn Analytics] Automatic synchronization lease cleanup failed:',
          error
        );
      }

      scheduleAutomaticLogSync(
        nextDelay
      );
    }
  }

  function handleAutomaticLogSyncWake() {
    if (
      automaticLogSyncPageActive()
    ) {
      scheduleAutomaticLogSync(
        AUTO_SYNC_INITIAL_DELAY_MS
      );
    } else {
      clearAutomaticLogSyncTimer();
    }
  }

  function installAutomaticLogSyncScheduler() {
    if (
      automaticLogSyncSchedulerInstalled
    ) {
      return;
    }

    automaticLogSyncSchedulerInstalled =
      true;

    if (
      typeof document !==
        'undefined'
    ) {
      document.addEventListener(
        'visibilitychange',
        handleAutomaticLogSyncWake,
        { passive: true }
      );
    }

    if (
      typeof window !==
        'undefined'
    ) {
      for (
        const eventName
        of [
          'pageshow',
          'focus',
          'online'
        ]
      ) {
        window.addEventListener(
          eventName,
          handleAutomaticLogSyncWake,
          { passive: true }
        );
      }

      window.addEventListener(
        'pagehide',
        clearAutomaticLogSyncTimer,
        { passive: true }
      );
    }

    scheduleAutomaticLogSync(
      AUTO_SYNC_INITIAL_DELAY_MS
    );
  }
  // ============================================================
  // LOAD / ANALYZE STORED DATA
  // ============================================================

  async function analyzeStoredLogs(
    tracker,
    apiKey = ''
  ) {

    tracker.reset();

    tracker.setStage(
      'Loading stored history…',
      'No historical API requests'
    );

    const meta =
      await getLastCacheMeta();

    if (
      !meta?.account_id
    ) {

      throw new Error(
        'No stored history was found.'
      );
    }

    await assertStoredSingleAccountOwner(
      meta.account_id
    );

    tracker.setPercent(
      25
    );

    latestLogs =
      await dbLoadLogs(
        meta.account_id
      );

    if (
      !latestLogs.length
    ) {

      throw new Error(
        'Cache metadata exists, but no logs were found.'
      );
    }

    currentAccount = {
      id:
        meta.account_id,

      name:
        meta.account_name_raw ??
        meta.account_name,

      signup_timestamp:
        meta.signup_timestamp,

      signup_local_date:
        meta.signup_local_date
    };

    tracker.setLogs(
      latestLogs.length
    );

    latestItemMap =
      await loadItemDictionary(
        '',
        tracker,
        false
      );

    tracker.setPercent(
      60
    );

    tracker.setStage(
      'Analyzing history…',
      `${latestLogs.length.toLocaleString()} cached logs`
    );

    latestAnalysis =
      buildBasicAnalysis(
        latestLogs,
        latestItemMap
      );

    latestAnalysis.resource_flow =
      buildResourceFlow(
        latestLogs
      );

    latestAnalysis.resource_bars =
      await loadResourceBarsSnapshot(
        apiKey,
        tracker
      );

    latestAnalysis.training_cooldowns =
      await loadTrainingCooldownsSnapshot(
        apiKey,
        tracker
      );

    latestAnalysis.activity =
      buildOverallActivity(
        latestLogs,
        activityTimeBasisPreference()
      );

    latestAnalysis.stat_growth =
      buildStatGrowth(
        latestLogs,
        activityTimeBasisPreference()
      );

    latestAnalysis.training_readiness =
      buildTrainingReadiness(
        latestAnalysis.stat_growth,
        latestAnalysis.resource_bars,
        latestAnalysis.training_cooldowns,
        Date.now(),
        typeof location !== 'undefined'
          ? location.href
          : ''
      );

    const analysisHost =
      document.getElementById(
        'ta-status'
      );

    if (
      analysisHost
    ) {
      analysisHost.innerHTML =
        renderStoredAnalysisDashboards(
          latestAnalysis
        );

      bindStoredAnalysisDashboardInteractions(
        analysisHost,
        latestAnalysis
      );
    }

    tracker.setPercent(
      100
    );

    tracker.setStage(
      'Analysis ready',
      'No full export required'
    );

    return {
      account:
        currentAccount,

      logs:
        latestLogs,

      analysis:
        latestAnalysis
    };
  }
  // ============================================================
  // BASIC ITEM ANALYTICS
  // ============================================================

  function addItemEvent(
    map,
    id,
    event
  ) {

    id =
      Number(
        id
      );

    if (
      !Number.isFinite(
        id
      )
    ) {
      return;
    }

    if (
      !map.has(
        id
      )
    ) {

      const info =
        itemInfo(
          id,
          latestItemMap
        );

      map.set(
        id,
        {
          id,

          name:
            info.name,

          type:
            info.type,

          acquired:
            0,

          disposed:
            0,

          events:
            []
        }
      );
    }

    const item =
      map.get(
        id
      );

    item.events.push(
      event
    );

    if (
      event.direction ===
      'IN'
    ) {

      item.acquired +=
        Number(
          event.qty ||
          0
        );
    }

    if (
      event.direction ===
      'OUT'
    ) {

      item.disposed +=
        Number(
          event.qty ||
          0
        );
    }
  }

  function buildBasicAnalysis(
    logs,
    itemMap
  ) {

    latestItemMap =
      itemMap;

    const items =
      new Map();

    for (
      const log
      of logs
    ) {

      const title =
        String(
          log.title ||
          ''
        ).toLowerCase();

      const d =
        log.data ||
        {};

      const itemsArray =
        Array.isArray(
          d.items
        )
          ? d.items
          : [];

      if (
        title ===
          'item market buy' ||
        title ===
          'bazaar buy'
      ) {

        for (
          const row
          of itemsArray
        ) {

          addItemEvent(
            items,
            row.id,
            {
              timestamp:
                log.timestamp,

              direction:
                'IN',

              qty:
                Number(
                  row.qty ||
                  0
                ),

              type:
                'PURCHASE',

              source:
                title,

              cash_total:
                Number(
                  d.cost_each ||
                  0
                ) *
                Number(
                  row.qty ||
                  0
                )
            }
          );
        }
      }

      else if (
        title ===
          'item market sell' ||
        title ===
          'bazaar sell'
      ) {

        for (
          const row
          of itemsArray
        ) {

          addItemEvent(
            items,
            row.id,
            {
              timestamp:
                log.timestamp,

              direction:
                'OUT',

              qty:
                Number(
                  row.qty ||
                  0
                ),

              type:
                'SALE',

              source:
                title,

              cash_total:
                Number(
                  d.cost_each ||
                  0
                ) *
                Number(
                  row.qty ||
                  0
                )
            }
          );
        }
      }

      else if (
        title ===
        'item abroad buy'
      ) {

        addItemEvent(
          items,
          d.item,
          {
            timestamp:
              log.timestamp,

            direction:
              'IN',

            qty:
              Number(
                d.quantity ||
                d.qty ||
                0
              ),

            type:
              'PURCHASE',

            source:
              'Foreign shop',

            cash_total:
              Number(
                d.cost_total ||
                0
              )
          }
        );
      }

      else if (
        title.startsWith(
          'item use '
        ) &&
        Number(
          d.faction ||
          0
        ) === 0
      ) {

        addItemEvent(
          items,
          d.item,
          {
            timestamp:
              log.timestamp,

            direction:
              'OUT',

            qty:
              1,

            type:
              'CONSUME',

            source:
              'Personal inventory',

            cash_total:
              null
          }
        );
      }

      else if (
        title ===
          'crime success item gain (new)' &&
        d.items_gained &&
        typeof d.items_gained ===
          'object'
      ) {

        for (
          const [
            id,
            qty
          ]
          of Object.entries(
            d.items_gained
          )
        ) {

          addItemEvent(
            items,
            id,
            {
              timestamp:
                log.timestamp,

              direction:
                'IN',

              qty:
                Number(
                  qty
                ),

              type:
                'REWARD',

              source:
                'Crime',

              cash_total:
                0
            }
          );
        }
      }

      else if (
        title ===
        'trade items outgoing'
      ) {

        for (
          const row
          of itemsArray
        ) {

          addItemEvent(
            items,
            row.id,
            {
              timestamp:
                log.timestamp,

              direction:
                'OUT',

              qty:
                Number(
                  row.qty ||
                  0
                ),

              type:
                'TRADE',

              source:
                'Trade',

              cash_total:
                null,

              trade_id:
                d.parsed_trade_id ??
                null
            }
          );
        }
      }

      else if (
        title ===
        'trade items incoming'
      ) {

        for (
          const row
          of itemsArray
        ) {

          addItemEvent(
            items,
            row.id,
            {
              timestamp:
                log.timestamp,

              direction:
                'IN',

              qty:
                Number(
                  row.qty ||
                  0
                ),

              type:
                'TRADE',

              source:
                'Trade',

              cash_total:
                null,

              trade_id:
                d.parsed_trade_id ??
                null
            }
          );
        }
      }
    }

    for (
      const item
      of items.values()
    ) {

      item.net_quantity =
        item.acquired -
        item.disposed;
    }

    return {
      items
    };
  }

  // ============================================================
  // OVERALL ACTIVITY ANALYTICS
  // ============================================================

  function activityDayNumber(
    dateString
  ) {
    const [
      year,
      month,
      day
    ] =
      String(
        dateString ||
        ''
      )
        .split('-')
        .map(Number);

    return Math.floor(
      Date.UTC(
        year,
        month - 1,
        day
      ) /
      86400000
    );
  }

  function activityHourLabel(
    hour
  ) {
    const normalized =
      Number(hour) % 24;

    const suffix =
      normalized >= 12
        ? 'PM'
        : 'AM';

    const display =
      normalized % 12 ||
      12;

    return `${display} ${suffix}`;
  }

  function normalizeActivityTimeBasis(
    value
  ) {
    return String(
      value ||
      ''
    ).toLowerCase() === 'tct'
      ? 'tct'
      : 'local';
  }

  function activityTimeBasisPreference() {
    try {
      return normalizeActivityTimeBasis(
        localStorage.getItem(
          ACTIVITY_TIME_BASIS_STORAGE
        )
      );
    } catch (_) {
      return 'local';
    }
  }

  function saveActivityTimeBasisPreference(
    value
  ) {
    const normalized =
      normalizeActivityTimeBasis(
        value
      );

    try {
      localStorage.setItem(
        ACTIVITY_TIME_BASIS_STORAGE,
        normalized
      );
    } catch (_) {}

    return normalized;
  }

  function activityDateKeyForBasis(
    date,
    timeBasis = 'local'
  ) {
    const basis =
      normalizeActivityTimeBasis(
        timeBasis
      );

    if (
      basis === 'tct'
    ) {
      return [
        date.getUTCFullYear(),
        pad2(
          date.getUTCMonth() +
          1
        ),
        pad2(
          date.getUTCDate()
        )
      ].join('-');
    }

    return localDateString(
      date
    );
  }

  function activityHourForBasis(
    date,
    timeBasis = 'local'
  ) {
    return normalizeActivityTimeBasis(
      timeBasis
    ) === 'tct'
      ? date.getUTCHours()
      : date.getHours();
  }

  function activityMinuteForBasis(
    date,
    timeBasis = 'local'
  ) {
    return normalizeActivityTimeBasis(
      timeBasis
    ) === 'tct'
      ? date.getUTCMinutes()
      : date.getMinutes();
  }

  function buildOverallActivity(
    logs,
    timeBasis = 'local'
  ) {
    const normalizedTimeBasis =
      normalizeActivityTimeBasis(
        timeBasis
      );

    const byDay =
      new Map();

    const byCategory =
      new Map();

    const hourlyCounts =
      Array.from(
        { length: 24 },
        () => 0
      );

    let validLogCount = 0;
    let firstTimestamp = null;
    let lastTimestamp = null;

    for (
      const log
      of logs || []
    ) {
      const timestamp =
        Number(
          log?.timestamp
        );

      if (
        !Number.isFinite(
          timestamp
        ) ||
        timestamp <= 0
      ) {
        continue;
      }

      validLogCount++;

      if (
        firstTimestamp === null ||
        timestamp < firstTimestamp
      ) {
        firstTimestamp =
          timestamp;
      }

      if (
        lastTimestamp === null ||
        timestamp > lastTimestamp
      ) {
        lastTimestamp =
          timestamp;
      }

      const date =
        new Date(
          timestamp * 1000
        );

      const dateKey =
        activityDateKeyForBasis(
          date,
          normalizedTimeBasis
        );

      const category =
        String(
          log?.category ||
          'Uncategorized'
        ).trim() ||
        'Uncategorized';

      const day =
        byDay.get(
          dateKey
        ) || {
          date:
            dateKey,
          count:
            0,
          first_timestamp:
            timestamp,
          last_timestamp:
            timestamp,
          categories:
            new Map()
        };

      day.count++;

      day.first_timestamp =
        Math.min(
          day.first_timestamp,
          timestamp
        );

      day.last_timestamp =
        Math.max(
          day.last_timestamp,
          timestamp
        );

      day.categories.set(
        category,
        (
          day.categories.get(
            category
          ) ||
          0
        ) +
        1
      );

      byDay.set(
        dateKey,
        day
      );

      byCategory.set(
        category,
        (
          byCategory.get(
            category
          ) ||
          0
        ) +
        1
      );

      hourlyCounts[
        activityHourForBasis(
          date,
          normalizedTimeBasis
        )
      ]++;
    }

    if (
      !validLogCount
    ) {
      return {
        time_basis:
          normalizedTimeBasis,
        total_logs:
          0,
        first_timestamp:
          null,
        last_timestamp:
          null,
        first_date:
          null,
        last_date:
          null,
        span_days:
          0,
        active_days:
          0,
        inactive_days:
          0,
        average_logs_per_active_day:
          0,
        average_logs_per_calendar_day:
          0,
        longest_active_streak:
          null,
        ending_active_streak:
          null,
        peak_day:
          null,
        peak_hour:
          null,
        largest_inactive_gap:
          null,
        inactive_gaps:
          [],
        categories:
          [],
        hours:
          [],
        days:
          [],
        recent_7_days:
          []
      };
    }

    const days =
      Array.from(
        byDay.values()
      )
        .map(
          day => {
            const topCategory =
              Array.from(
                day.categories.entries()
              )
                .sort(
                  (
                    a,
                    b
                  ) =>
                    b[1] -
                    a[1] ||
                    a[0].localeCompare(
                      b[0]
                    )
                )[0] ||
              null;

            return {
              date:
                day.date,
              count:
                day.count,
              first_timestamp:
                day.first_timestamp,
              last_timestamp:
                day.last_timestamp,
              top_category:
                topCategory
                  ? {
                      name:
                        topCategory[0],
                      count:
                        topCategory[1]
                    }
                  : null
            };
          }
        )
        .sort(
          (
            a,
            b
          ) =>
            activityDayNumber(
              a.date
            ) -
            activityDayNumber(
              b.date
            )
        );

    const firstDate =
      days[0].date;

    const lastDate =
      days[
        days.length - 1
      ].date;

    const firstDayNumber =
      activityDayNumber(
        firstDate
      );

    const lastDayNumber =
      activityDayNumber(
        lastDate
      );

    const spanDays =
      lastDayNumber -
      firstDayNumber +
      1;

    const categories =
      Array.from(
        byCategory.entries()
      )
        .map(
          ([
            name,
            count
          ]) => ({
            name,
            count,
            percent:
              count /
              validLogCount *
              100
          })
        )
        .sort(
          (
            a,
            b
          ) =>
            b.count -
            a.count ||
            a.name.localeCompare(
              b.name
            )
        );

    const hours =
      hourlyCounts.map(
        (
          count,
          hour
        ) => ({
          hour,
          label:
            activityHourLabel(
              hour
            ),
          count,
          percent:
            count /
            validLogCount *
            100
        })
      );

    const peakDay =
      days.reduce(
        (
          best,
          day
        ) =>
          !best ||
          day.count > best.count
            ? day
            : best,
        null
      );

    const peakHour =
      hours.reduce(
        (
          best,
          hour
        ) =>
          !best ||
          hour.count > best.count
            ? hour
            : best,
        null
      );

    const inactiveGaps =
      [];

    let longestActiveStreak =
      null;

    let streakStartIndex =
      0;

    for (
      let i = 0;
      i < days.length;
      i++
    ) {
      if (
        i > 0
      ) {
        const previousDayNumber =
          activityDayNumber(
            days[i - 1].date
          );

        const currentDayNumber =
          activityDayNumber(
            days[i].date
          );

        const difference =
          currentDayNumber -
          previousDayNumber;

        if (
          difference > 1
        ) {
          const streakDays =
            i -
            streakStartIndex;

          if (
            !longestActiveStreak ||
            streakDays >
              longestActiveStreak.days
          ) {
            longestActiveStreak = {
              days:
                streakDays,
              start_date:
                days[
                  streakStartIndex
                ].date,
              end_date:
                days[
                  i - 1
                ].date
            };
          }

          inactiveGaps.push({
            start_date:
              addDays(
                days[i - 1].date,
                1
              ),
            end_date:
              addDays(
                days[i].date,
                -1
              ),
            days:
              difference -
              1
          });

          streakStartIndex =
            i;
        }
      }
    }

    const endingStreakDays =
      days.length -
      streakStartIndex;

    const endingActiveStreak = {
      days:
        endingStreakDays,
      start_date:
        days[
          streakStartIndex
        ].date,
      end_date:
        days[
          days.length - 1
        ].date
    };

    if (
      !longestActiveStreak ||
      endingStreakDays >
        longestActiveStreak.days
    ) {
      longestActiveStreak =
        endingActiveStreak;
    }

    const largestInactiveGap =
      inactiveGaps.reduce(
        (
          best,
          gap
        ) =>
          !best ||
          gap.days > best.days
            ? gap
            : best,
        null
      );

    const dayLookup =
      new Map(
        days.map(
          day => [
            activityDayNumber(
              day.date
            ),
            day
          ]
        )
      );

    const recent7Days =
      [];

    for (
      let offset = 6;
      offset >= 0;
      offset--
    ) {
      const dayNumber =
        lastDayNumber -
        offset;

      const activeDay =
        dayLookup.get(
          dayNumber
        );

      recent7Days.push({
        date:
          activeDay?.date ||
          addDays(
            lastDate,
            -offset
          ),
        count:
          activeDay?.count ||
          0
      });
    }

    return {
      time_basis:
        normalizedTimeBasis,
      total_logs:
        validLogCount,
      first_timestamp:
        firstTimestamp,
      last_timestamp:
        lastTimestamp,
      first_date:
        firstDate,
      last_date:
        lastDate,
      span_days:
        spanDays,
      active_days:
        days.length,
      inactive_days:
        Math.max(
          0,
          spanDays -
          days.length
        ),
      average_logs_per_active_day:
        validLogCount /
        days.length,
      average_logs_per_calendar_day:
        validLogCount /
        spanDays,
      longest_active_streak:
        longestActiveStreak,
      ending_active_streak:
        endingActiveStreak,
      peak_day:
        peakDay,
      peak_hour:
        peakHour,
      largest_inactive_gap:
        largestInactiveGap,
      inactive_gaps:
        inactiveGaps,
      categories,
      hours,
      days,
      recent_7_days:
        recent7Days
    };
  }

  function escapeActivityHtml(
    value
  ) {
    return String(
      value ??
      ''
    )
      .replace(
        /&/g,
        '&amp;'
      )
      .replace(
        /</g,
        '&lt;'
      )
      .replace(
        />/g,
        '&gt;'
      )
      .replace(
        /"/g,
        '&quot;'
      )
      .replace(
        /'/g,
        '&#39;'
      );
  }

  function renderOverallActivitySummary(
    activity
  ) {
    if (
      !activity?.total_logs
    ) {
      return `
        <div class="panel">
          <b>Overall Activity</b>
          <div class="small">
            No timestamped logs were available for activity analysis.
          </div>
        </div>
      `;
    }

    const categoryLines =
      activity.categories
        .slice(
          0,
          5
        )
        .map(
          row =>
            `${escapeActivityHtml(row.name)}: ` +
            `${Number(row.count).toLocaleString()} ` +
            `(${row.percent.toFixed(1)}%)`
        )
        .join('<br>');

    const recentLines =
      activity.recent_7_days
        .map(
          row =>
            `${escapeActivityHtml(row.date)}: ` +
            `${Number(row.count).toLocaleString()}`
        )
        .join('<br>');

    const gapLine =
      activity.largest_inactive_gap
        ? `${activity.largest_inactive_gap.days} days ` +
          `(${escapeActivityHtml(activity.largest_inactive_gap.start_date)} → ` +
          `${escapeActivityHtml(activity.largest_inactive_gap.end_date)})`
        : 'None between recorded active days';

    return `
      <div class="panel">
        <b>Overall Activity</b>

        <div class="small">
          ${Number(activity.total_logs).toLocaleString()} timestamped logs
          across ${Number(activity.span_days).toLocaleString()} calendar days.
          Times use ${activity.time_basis === 'tct' ? 'Torn City Time (UTC)' : "this device's local timezone"}.
        </div>

        <div class="stats">
          <div>
            Active days:
            <b>${Number(activity.active_days).toLocaleString()}</b>
          </div>

          <div>
            Inactive days:
            <b>${Number(activity.inactive_days).toLocaleString()}</b>
          </div>

          <div>
            Avg / active day:
            <b>${activity.average_logs_per_active_day.toFixed(1)}</b>
          </div>

          <div>
            Avg / calendar day:
            <b>${activity.average_logs_per_calendar_day.toFixed(1)}</b>
          </div>

          <div>
            Longest streak:
            <b>${activity.longest_active_streak?.days || 0} days</b>
          </div>

          <div>
            Ending streak:
            <b>${activity.ending_active_streak?.days || 0} days</b>
          </div>
        </div>

        <div class="small">
          <b>Range:</b>
          ${escapeActivityHtml(activity.first_date)}
          →
          ${escapeActivityHtml(activity.last_date)}
          <br>

          <b>Peak day:</b>
          ${escapeActivityHtml(activity.peak_day?.date || '—')}
          —
          ${Number(activity.peak_day?.count || 0).toLocaleString()} logs
          <br>

          <b>Peak hour:</b>
          ${escapeActivityHtml(activity.peak_hour?.label || '—')}
          —
          ${Number(activity.peak_hour?.count || 0).toLocaleString()} logs
          <br>

          <b>Largest inactive gap:</b>
          ${gapLine}
        </div>

        <div class="small">
          <b>Top categories</b>
          <br>
          ${categoryLines || 'None'}
        </div>

        <div class="small">
          <b>Most recent 7 calendar days in stored history</b>
          <br>
          ${recentLines}
        </div>
      </div>
    `;
  }

  // ============================================================
  // OVERALL ACTIVITY DASHBOARD
  // ============================================================

  function activityDashboardIsLandscape() {
    const width =
      Number(
        typeof window !== 'undefined'
          ? window.innerWidth || 0
          : 0
      );

    const height =
      Number(
        typeof window !== 'undefined'
          ? window.innerHeight || 0
          : 0
      );

    if (
      width > 0 &&
      height > 0
    ) {
      return width > height;
    }

    try {
      return typeof matchMedia === 'function' &&
        matchMedia('(orientation: landscape)').matches;
    } catch (_) {
      return false;
    }
  }

  function activityDashboardLayout(
    isLandscape = activityDashboardIsLandscape()
  ) {
    return isLandscape
      ? {
          orientation: 'landscape',
          recent_days: 14,
          hour_bucket_hours: 2,
          hour_bars: 12
        }
      : {
          orientation: 'portrait',
          recent_days: 7,
          hour_bucket_hours: 4,
          hour_bars: 6
        };
  }

  function activityDashboardHourMinuteLabel(
    hour,
    minute = 0
  ) {
    const normalizedHour =
      (
        (
          Math.floor(
            Number(hour) ||
            0
          ) %
          24
        ) +
        24
      ) %
      24;

    const normalizedMinute =
      Math.max(
        0,
        Math.min(
          59,
          Math.floor(
            Number(minute) ||
            0
          )
        )
      );

    const suffix =
      normalizedHour >= 12
        ? 'PM'
        : 'AM';

    const displayHour =
      normalizedHour % 12 ||
      12;

    return `${displayHour}:${pad2(normalizedMinute)} ${suffix}`;
  }

  function activityDashboardHourRange(
    startHour,
    bucketHours = 1
  ) {
    const safeBucketHours =
      [
        1,
        2,
        4
      ].includes(
        Number(bucketHours)
      )
        ? Number(bucketHours)
        : 1;

    const normalizedStart =
      (
        (
          Math.floor(
            Number(startHour) ||
            0
          ) %
          24
        ) +
        24
      ) %
      24;

    const endHour =
      (
        normalizedStart +
        safeBucketHours -
        1
      ) %
      24;

    const startLabel =
      activityDashboardHourMinuteLabel(
        normalizedStart,
        0
      );

    const endLabel =
      activityDashboardHourMinuteLabel(
        endHour,
        59
      );

    const compactStartLabel =
      startLabel.replace(
        ':00 ',
        ' '
      );

    const compactEndLabel =
      endLabel;

    return {
      start_hour:
        normalizedStart,
      end_hour:
        endHour,
      bucket_hours:
        safeBucketHours,
      start_label:
        startLabel,
      end_label:
        endLabel,
      compact_start_label:
        compactStartLabel,
      compact_end_label:
        compactEndLabel,
      compact_label:
        `${compactStartLabel}–${compactEndLabel}`,
      label:
        `${startLabel}–${endLabel}`
    };
  }

  function activityDashboardUtcOffsetLabel(
    date = new Date()
  ) {
    const offsetMinutes =
      -Number(
        date?.getTimezoneOffset?.() ||
        0
      );

    const sign =
      offsetMinutes >= 0
        ? '+'
        : '−';

    const absolute =
      Math.abs(
        offsetMinutes
      );

    const hours =
      Math.floor(
        absolute /
        60
      );

    const minutes =
      absolute %
      60;

    return `UTC${sign}${hours}${minutes ? `:${pad2(minutes)}` : ''}`;
  }

  function activityDashboardTimezoneContext(
    date = new Date(),
    timeBasis = 'local'
  ) {
    const normalizedTimeBasis =
      normalizeActivityTimeBasis(
        timeBasis
      );

    if (
      normalizedTimeBasis === 'tct'
    ) {
      return {
        short_name:
          'TCT',
        zone_name:
          'UTC',
        offset:
          'UTC',
        label:
          'TCT (UTC)'
      };
    }

    let shortName = '';
    let zoneName = '';

    try {
      const formatter =
        new Intl.DateTimeFormat(
          undefined,
          {
            timeZoneName:
              'short'
          }
        );

      shortName =
        formatter
          .formatToParts(
            date
          )
          .find(
            part =>
              part.type ===
              'timeZoneName'
          )
          ?.value ||
        '';
    } catch (_) {}

    try {
      zoneName =
        Intl.DateTimeFormat()
          .resolvedOptions()
          .timeZone ||
        '';
    } catch (_) {}

    const offset =
      activityDashboardUtcOffsetLabel(
        date
      );

    return {
      short_name:
        shortName,
      zone_name:
        zoneName,
      offset,
      label:
        shortName
          ? `${shortName} (${offset})`
          : zoneName
            ? `${zoneName} (${offset})`
            : offset
    };
  }

  function activityDashboardLongDate(
    value
  ) {
    const date =
      parseLocalDate(
        String(
          value ||
          ''
        )
      );

    if (
      Number.isNaN(
        date.getTime()
      )
    ) {
      return String(
        value ||
        ''
      );
    }

    const weekdays = [
      'Sunday',
      'Monday',
      'Tuesday',
      'Wednesday',
      'Thursday',
      'Friday',
      'Saturday'
    ];

    const months = [
      'Jan',
      'Feb',
      'Mar',
      'Apr',
      'May',
      'Jun',
      'Jul',
      'Aug',
      'Sep',
      'Oct',
      'Nov',
      'Dec'
    ];

    return `${weekdays[date.getDay()]}, ${months[date.getMonth()]} ${date.getDate()}, ${date.getFullYear()}`;
  }

  function activityDashboardMonthDay(
    value,
    includeYear = false
  ) {
    const date =
      parseLocalDate(
        String(
          value ||
          ''
        )
      );

    if (
      Number.isNaN(
        date.getTime()
      )
    ) {
      return String(
        value ||
        ''
      );
    }

    const months = [
      'Jan',
      'Feb',
      'Mar',
      'Apr',
      'May',
      'Jun',
      'Jul',
      'Aug',
      'Sep',
      'Oct',
      'Nov',
      'Dec'
    ];

    return `${months[date.getMonth()]} ${date.getDate()}${includeYear ? `, ${date.getFullYear()}` : ''}`;
  }

  function activityDashboardPartialTodayContext(
    activity,
    now = new Date()
  ) {
    const timeBasis =
      normalizeActivityTimeBasis(
        activity?.time_basis
      );

    const today =
      activityDateKeyForBasis(
        now,
        timeBasis
      );

    const isPartialToday =
      Boolean(
        activity?.last_date &&
        activity.last_date ===
          today
      );

    const lastTimestamp =
      Number(
        activity?.last_timestamp ||
        0
      );

    let latestStoredTime = '';

    if (
      isPartialToday &&
      Number.isFinite(
        lastTimestamp
      ) &&
      lastTimestamp > 0
    ) {
      const lastDate =
        new Date(
          lastTimestamp *
          1000
        );

      if (
        activityDateKeyForBasis(
          lastDate,
          timeBasis
        ) ===
        today
      ) {
        latestStoredTime =
          activityDashboardHourMinuteLabel(
            activityHourForBasis(
              lastDate,
              timeBasis
            ),
            activityMinuteForBasis(
              lastDate,
              timeBasis
            )
          );
      }
    }

    return {
      time_basis:
        timeBasis,
      today,
      is_partial_today:
        isPartialToday,
      latest_stored_time:
        latestStoredTime
    };
  }

  function activityDashboardRecentDays(
    activity,
    length = 14
  ) {
    if (
      !activity?.last_date
    ) {
      return [];
    }

    const requestedLength =
      Math.floor(
        Number(length) ||
        14
      );

    const safeLength =
      Math.max(
        1,
        Math.min(
          30,
          requestedLength
        )
      );

    const dayLookup =
      new Map(
        (activity.days || [])
          .map(
            row => [
              row.date,
              row
            ]
          )
      );

    const rows = [];

    for (
      let offset = safeLength - 1;
      offset >= 0;
      offset--
    ) {
      const date =
        addDays(
          activity.last_date,
          -offset
        );

      rows.push({
        date,
        count:
          Number(
            dayLookup.get(
              date
            )?.count ||
            0
          )
      });
    }

    return rows;
  }

  function activityDashboardHourBuckets(
    activity,
    bucketHours = 2
  ) {
    const hours =
      Array.isArray(
        activity?.hours
      )
        ? activity.hours
        : [];

    const safeBucketHours =
      Number(bucketHours) === 4
        ? 4
        : 2;

    const totalLogs =
      Math.max(
        0,
        Number(
          activity?.total_logs ||
          0
        )
      );

    const rows = [];

    for (
      let start = 0;
      start < 24;
      start += safeBucketHours
    ) {
      let count = 0;

      for (
        let offset = 0;
        offset < safeBucketHours;
        offset++
      ) {
        count +=
          Number(
            hours[start + offset]?.count ||
            0
          );
      }

      const range =
        activityDashboardHourRange(
          start,
          safeBucketHours
        );

      rows.push({
        hour:
          start,
        label:
          activityHourLabel(
            start
          ),
        count,
        percent:
          totalLogs > 0
            ? count /
              totalLogs *
              100
            : 0,
        bucket_hours:
          safeBucketHours,
        range_label:
          range.label,
        range_start_label:
          range.start_label,
        range_end_label:
          range.end_label,
        compact_range_start_label:
          range.compact_start_label,
        compact_range_end_label:
          range.compact_end_label
      });
    }

    return rows;
  }

  function activityDashboardPercent(
    value,
    maximum,
    minimum = 4
  ) {
    const numericValue =
      Math.max(
        0,
        Number(value) ||
        0
      );

    const numericMaximum =
      Math.max(
        0,
        Number(maximum) ||
        0
      );

    if (
      numericMaximum <= 0 ||
      numericValue <= 0
    ) {
      return 0;
    }

    return Math.max(
      minimum,
      Math.min(
        100,
        Math.round(
          numericValue /
          numericMaximum *
          100
        )
      )
    );
  }

  function activityDashboardShortDate(
    value
  ) {
    const text =
      String(
        value ||
        ''
      );

    if (
      text.length >= 10
    ) {
      return `${text.slice(5, 7)}/${text.slice(8, 10)}`;
    }

    return text;
  }

  function renderActivityTimeBasisControl(
    activity
  ) {
    const basis =
      normalizeActivityTimeBasis(
        activity?.time_basis ??
        activityTimeBasisPreference()
      );

    const localTimezone =
      activityDashboardTimezoneContext(
        new Date(),
        'local'
      );

    const context =
      basis === 'tct'
        ? 'TCT uses UTC calendar-day and clock-hour boundaries.'
        : `Device Local uses ${localTimezone.label}.`;

    return `
      <div class="ta-time-basis-control">
        <div class="ta-time-basis-topline">
          <span>Time basis</span>
          <div class="ta-time-basis-options" role="group" aria-label="Activity time basis">
            <button
              type="button"
              data-ta-time-basis="local"
              aria-pressed="${basis === 'local' ? 'true' : 'false'}"
              class="${basis === 'local' ? 'ta-time-basis-active' : ''}"
            >Device Local</button>
            <button
              type="button"
              data-ta-time-basis="tct"
              aria-pressed="${basis === 'tct' ? 'true' : 'false'}"
              class="${basis === 'tct' ? 'ta-time-basis-active' : ''}"
            >TCT (UTC)</button>
          </div>
        </div>
        <div class="ta-time-basis-context">
          ${escapeActivityHtml(context)}
        </div>
      </div>
    `;
  }

  function activityDashboardApplyTimeBasis(
    root,
    value
  ) {
    const nextBasis =
      saveActivityTimeBasisPreference(
        value
      );

    if (
      !root ||
      !Array.isArray(
        latestLogs
      ) ||
      !latestLogs.length ||
      !latestAnalysis
    ) {
      return nextBasis;
    }

    latestAnalysis.activity =
      buildOverallActivity(
        latestLogs,
        nextBasis
      );

    latestAnalysis.stat_growth =
      buildStatGrowth(
        latestLogs,
        nextBasis
      );

    root.innerHTML =
      renderStoredAnalysisDashboards(
        latestAnalysis
      );

    bindStoredAnalysisDashboardInteractions(
      root,
      latestAnalysis
    );

    return nextBasis;
  }

  function activityDashboardMetric(
    label,
    value,
    note = ''
  ) {
    return `
      <div class="ta-metric-card">
        <div class="ta-metric-label">
          ${escapeActivityHtml(label)}
        </div>

        <div class="ta-metric-value">
          ${escapeActivityHtml(value)}
        </div>

        ${
          note
            ? `
              <div class="ta-metric-note">
                ${escapeActivityHtml(note)}
              </div>
            `
            : ''
        }
      </div>
    `;
  }

  function renderActivityDailyChart(
    activity
  ) {
    const layout =
      activityDashboardLayout();

    const partialContext =
      activityDashboardPartialTodayContext(
        activity
      );

    const rows =
      activityDashboardRecentDays(
        activity,
        layout.recent_days
      );

    const windowTotal =
      rows.reduce(
        (
          total,
          row
        ) =>
          total +
          Number(
            row.count ||
            0
          ),
        0
      );

    const maximum =
      Math.max(
        0,
        ...rows.map(
          row =>
            Number(
              row.count ||
              0
            )
        )
      );

    const bars =
      rows.map(row => {
        const count =
          Number(
            row.count ||
            0
          );

        const height =
          activityDashboardPercent(
            count,
            maximum
          );

        const isPartial =
          partialContext.is_partial_today &&
          row.date ===
            partialContext.today;

        const windowPercent =
          windowTotal > 0
            ? count /
              windowTotal *
              100
            : 0;

        const partialText =
          isPartial
            ? partialContext.latest_stored_time
              ? ` · Today · partial · latest stored log ${partialContext.latest_stored_time}`
              : ' · Today · partial'
            : '';

        const detail =
          `${activityDashboardLongDate(row.date)} · ` +
          `${count.toLocaleString()} logs · ` +
          `${windowPercent.toFixed(1)}% of displayed ${layout.recent_days}-day activity${partialText}`;

        return `
          <div
            class="ta-chart-column${isPartial ? ' ta-chart-column-partial' : ''}"
            role="button"
            tabindex="0"
            data-ta-detail="${escapeActivityHtml(detail)}"
            aria-label="${escapeActivityHtml(detail)}"
            title="${escapeActivityHtml(detail)}"
          >
            <div class="ta-chart-value">${count.toLocaleString()}</div>
            <div class="ta-chart-rail"><div class="ta-chart-bar" style="height:${height}%"></div></div>
            <div class="ta-chart-label">
              ${escapeActivityHtml(activityDashboardShortDate(row.date))}
              ${isPartial ? '<span class="ta-chart-partial-badge">partial</span>' : ''}
            </div>
          </div>
        `;
      }).join('');

    const firstRow =
      rows[0] ||
      null;

    const lastRow =
      rows[
        rows.length -
        1
      ] ||
      null;

    const firstYear =
      String(
        firstRow?.date ||
        ''
      ).slice(
        0,
        4
      );

    const lastYear =
      String(
        lastRow?.date ||
        ''
      ).slice(
        0,
        4
      );

    const dateWindow =
      firstRow &&
      lastRow
        ? `${activityDashboardMonthDay(firstRow.date, firstYear !== lastYear)}–${activityDashboardMonthDay(lastRow.date, firstYear !== lastYear)}`
        : '';

    const partialHeading =
      partialContext.is_partial_today
        ? ' · includes partial today'
        : '';

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Recent activity</span>
          <span>Last ${layout.recent_days} calendar days · ${escapeActivityHtml(dateWindow)}${partialHeading}</span>
        </div>
        <div class="ta-chart-scroll">
          <div class="ta-chart-columns ta-chart-columns-daily" style="grid-template-columns:repeat(${rows.length},minmax(0,1fr))">
            ${bars}
          </div>
        </div>
        <div class="ta-chart-detail" data-ta-chart-detail-output>
          Tap a day for its full date, exact count, and share of this chart window.
        </div>
      </div>
    `;
  }

  function renderActivityHourlyChart(
    activity
  ) {
    const layout =
      activityDashboardLayout();

    const timezone =
      activityDashboardTimezoneContext(
        new Date(),
        activity?.time_basis
      );

    const rows =
      activityDashboardHourBuckets(
        activity,
        layout.hour_bucket_hours
      );

    const maximum =
      Math.max(
        0,
        ...rows.map(
          row =>
            Number(
              row.count ||
              0
            )
        )
      );

    const bars =
      rows.map(row => {
        const count =
          Number(
            row.count ||
            0
          );

        const height =
          activityDashboardPercent(
            count,
            maximum
          );

        const detail =
          `${row.range_label} · ` +
          `${count.toLocaleString()} logs · ` +
          `${Number(row.percent || 0).toFixed(1)}% of all timestamped activity · ` +
          `${timezone.label}`;

        return `
          <div
            class="ta-chart-column"
            role="button"
            tabindex="0"
            data-ta-detail="${escapeActivityHtml(detail)}"
            aria-label="${escapeActivityHtml(detail)}"
            title="${escapeActivityHtml(detail)}"
          >
            <div class="ta-chart-value">${count.toLocaleString()}</div>
            <div class="ta-chart-rail"><div class="ta-chart-bar" style="height:${height}%"></div></div>
            <div class="ta-chart-label ta-chart-range-label">
              <span>${escapeActivityHtml(row.compact_range_start_label)}</span>
              <span>–${escapeActivityHtml(row.compact_range_end_label)}</span>
            </div>
          </div>
        `;
      }).join('');

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Time-of-day profile</span>
          <span>${layout.hour_bucket_hours}-hour buckets · ${escapeActivityHtml(timezone.label)}</span>
        </div>
        <div class="ta-chart-scroll">
          <div class="ta-chart-columns ta-chart-columns-hourly" style="grid-template-columns:repeat(${rows.length},minmax(0,1fr))">
            ${bars}
          </div>
        </div>
        <div class="ta-chart-detail" data-ta-chart-detail-output>
          Tap a bucket for its exact time range, count, and share of all activity.
        </div>
      </div>
    `;
  }

  function bindActivityDashboardInteractions(
    root
  ) {
    if (
      !root?.querySelectorAll
    ) {
      return;
    }

    const timeBasisButtons =
      Array.from(
        root.querySelectorAll(
          '[data-ta-time-basis]'
        )
      );

    for (
      const button
      of timeBasisButtons
    ) {
      button.addEventListener(
        'click',
        () => {
          const requested =
            button.getAttribute(
              'data-ta-time-basis'
            );

          const current =
            normalizeActivityTimeBasis(
              latestAnalysis?.activity?.time_basis
            );

          const next =
            normalizeActivityTimeBasis(
              requested
            );

          if (
            next === current
          ) {
            return;
          }

          activityDashboardApplyTimeBasis(
            root,
            next
          );
        }
      );
    }

    const columns =
      Array.from(
        root.querySelectorAll(
          '.ta-chart-column[data-ta-detail]'
        )
      );

    const activate =
      column => {
        const card =
          column?.closest?.(
            '.ta-chart-card'
          );

        if (
          !card
        ) {
          return;
        }

        const output =
          card.querySelector(
            '[data-ta-chart-detail-output]'
          );

        if (
          output
        ) {
          output.textContent =
            column.getAttribute(
              'data-ta-detail'
            ) ||
            '';
        }

        for (
          const candidate
          of card.querySelectorAll(
            '.ta-chart-column[data-ta-detail]'
          )
        ) {
          candidate.classList.toggle(
            'ta-chart-column-active',
            candidate === column
          );
        }
      };

    for (
      const column
      of columns
    ) {
      column.addEventListener(
        'click',
        () =>
          activate(
            column
          )
      );

      column.addEventListener(
        'keydown',
        event => {
          if (
            event.key !== 'Enter' &&
            event.key !== ' '
          ) {
            return;
          }

          event.preventDefault();
          activate(
            column
          );
        }
      );
    }
  }

  function renderActivityCategoryBars(
    activity
  ) {
    const rows =
      (activity?.categories || [])
        .slice(
          0,
          5
        );

    if (
      !rows.length
    ) {
      return '';
    }

    const maximum =
      Math.max(
        ...rows.map(
          row =>
            Number(
              row.count ||
              0
            )
        ),
        1
      );

    const bars =
      rows
        .map(
          row => {
            const count =
              Number(
                row.count ||
                0
              );

            const width =
              activityDashboardPercent(
                count,
                maximum,
                3
              );

            return `
              <div class="ta-category-row">
                <div class="ta-category-topline">
                  <span>
                    ${escapeActivityHtml(row.name)}
                  </span>

                  <span>
                    ${count.toLocaleString()} · ${Number(row.percent || 0).toFixed(1)}%
                  </span>
                </div>

                <div class="ta-category-track">
                  <div
                    class="ta-category-fill"
                    style="width:${width}%"
                  ></div>
                </div>
              </div>
            `;
          }
        )
        .join('');

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Top categories</span>
          <span>Share of timestamped logs</span>
        </div>

        <div class="ta-category-list">
          ${bars}
        </div>
      </div>
    `;
  }

  function renderOverallActivityDashboard(
    activity
  ) {
    if (
      !activity?.total_logs
    ) {
      return `
        <details class="ta-section">
          <summary class="ta-section-summary-row">
            <span class="ta-section-title">
              Overall Activity
            </span>

            <span class="ta-section-meta">
              No activity data
            </span>
          </summary>

          <div class="ta-section-body">
            <div class="small">
              No timestamped logs were available for activity analysis.
            </div>
          </div>
        </details>
      `;
    }

    const longestStreak =
      Number(
        activity.longest_active_streak?.days ||
        0
      );

    const endingStreak =
      Number(
        activity.ending_active_streak?.days ||
        0
      );

    const gapText =
      activity.largest_inactive_gap
        ? `${activity.largest_inactive_gap.days} days · ` +
          `${activity.largest_inactive_gap.start_date} → ${activity.largest_inactive_gap.end_date}`
        : 'None between recorded active days';

    const peakHourRange =
      activity.peak_hour
        ? activityDashboardHourRange(
            activity.peak_hour.hour,
            1
          ).label
        : '—';

    const timezone =
      activityDashboardTimezoneContext(
        new Date(),
        activity?.time_basis
      );

    const partialContext =
      activityDashboardPartialTodayContext(
        activity
      );

    const metrics = [
      activityDashboardMetric(
        'Timestamped logs',
        Number(activity.total_logs).toLocaleString(),
        `${Number(activity.span_days).toLocaleString()} calendar days`
      ),
      activityDashboardMetric(
        'Active days',
        `${Number(activity.active_days).toLocaleString()} / ${Number(activity.span_days).toLocaleString()}`,
        `${Number(activity.inactive_days).toLocaleString()} inactive`
      ),
      activityDashboardMetric(
        'Average / day',
        activity.average_logs_per_calendar_day.toFixed(1),
        `${activity.average_logs_per_active_day.toFixed(1)} per active day`
      ),
      activityDashboardMetric(
        'Longest streak',
        `${longestStreak} days`,
        `${activity.longest_active_streak?.start_date || '—'} → ${activity.longest_active_streak?.end_date || '—'}`
      ),
      activityDashboardMetric(
        'Peak day',
        Number(activity.peak_day?.count || 0).toLocaleString(),
        activity.peak_day?.date || '—'
      ),
      activityDashboardMetric(
        'Peak hour',
        peakHourRange,
        `${Number(activity.peak_hour?.count || 0).toLocaleString()} logs · single-hour statistic`
      )
    ].join('');

    const partialIntro =
      partialContext.is_partial_today
        ? partialContext.latest_stored_time
          ? ` Today is partial; latest stored activity is ${partialContext.latest_stored_time}.`
          : ' Today is partial.'
        : '';

    return `
      <details class="ta-section ta-activity-section">
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">
            Overall Activity
          </span>

          <span class="ta-section-meta">
            ${Number(activity.total_logs).toLocaleString()} logs · ${Number(activity.active_days).toLocaleString()} active days
          </span>
        </summary>

        <div class="ta-section-body">
          <div class="ta-section-intro">
            Activity patterns from your locally stored Torn history.
            Time basis: ${escapeActivityHtml(timezone.label)}.${escapeActivityHtml(partialIntro)}
          </div>

          <div class="ta-metric-grid">
            ${metrics}
          </div>

          ${renderActivityDailyChart(activity)}

          ${renderActivityHourlyChart(activity)}

          ${renderActivityCategoryBars(activity)}

          <div class="ta-detail-grid">
            <div>
              <span>Stored range</span>
              <b>
                ${escapeActivityHtml(activity.first_date)} → ${escapeActivityHtml(activity.last_date)}
              </b>
            </div>

            <div>
              <span>Time basis</span>
              <b>${escapeActivityHtml(timezone.label)}</b>
            </div>

            <div>
              <span>Ending streak</span>
              <b>${endingStreak} days</b>
            </div>

            <div>
              <span>Largest inactive gap</span>
              <b>${escapeActivityHtml(gapText)}</b>
            </div>
          </div>
        </div>
      </details>
    `;
  }
  // ============================================================
  // NON-SENSITIVE UI RESTORE STATE
  // ============================================================

  const UI_SESSION_STORAGE_KEY =
    'tornAnalyticsUiRestoreV3';

  const UI_RESTORE_MAX_AGE_MS =
    5 * 60 * 1000;

  const UI_ORIENTATION_HANDOFF_STORAGE_KEY =
    'tornAnalyticsOrientationHandoffV1';

  const UI_ORIENTATION_HANDOFF_MAX_AGE_MS =
    30 * 1000;

  function uiSessionOrientation() {
    const width =
      Number(
        typeof window !== 'undefined'
          ? window.innerWidth || 0
          : 0
      );

    const height =
      Number(
        typeof window !== 'undefined'
          ? window.innerHeight || 0
          : 0
      );

    return width > height
      ? 'landscape'
      : 'portrait';
  }

  function uiRestoreStorage() {
    try {
      // sessionStorage is scoped to one top-level Torn tab. Using it keeps
      // same-tab reload/orientation restoration without allowing a newly
      // opened TornPDA tab to inherit an already-open dashboard.
      return typeof sessionStorage !==
        'undefined'
          ? sessionStorage
          : null;
    } catch (_) {
      // Automatic modal restoration is optional. Fail closed when the
      // per-tab store is unavailable so a new page starts with the launcher.
      return null;
    }
  }

  function uiOrientationHandoffStorage() {
    try {
      // TornPDA may create a fresh top-level page context during rotation,
      // which can discard sessionStorage. localStorage is used only for a
      // short-lived orientation handoff, never for normal modal persistence.
      return typeof localStorage !==
        'undefined'
          ? localStorage
          : null;
    } catch (_) {
      return null;
    }
  }

  function clearUiOrientationHandoff() {
    try {
      uiOrientationHandoffStorage()?.removeItem(
        UI_ORIENTATION_HANDOFF_STORAGE_KEY
      );
    } catch (_) {}
  }

  function uiSessionOptionalBoolean(
    value
  ) {
    return value === true
      ? true
      : value === false
        ? false
        : null;
  }

  function uiSessionTrainingFocus(
    value
  ) {
    return [
      'recent',
      'most_trained',
      'strength',
      'defense',
      'speed',
      'dexterity'
    ].includes(
      value
    )
      ? value
      : 'recent';
  }
  function uiSessionStatGainScope(
    value
  ) {
    return value ===
      'all'
        ? 'all'
        : 'selected';
  }

  function writeUiOrientationHandoff(
    state
  ) {
    if (
      !state?.modal_open
    ) {
      clearUiOrientationHandoff();
      return null;
    }

    const handoff = {
      modal_open:
        true,
      analysis_visible:
        state.analysis_visible ===
        true,
      scroll_top:
        Math.max(
          0,
          Number(
            state.scroll_top
          ) ||
          0
        ),
      orientation:
        state.orientation ===
        'landscape'
          ? 'landscape'
          : 'portrait',
      orientation_refresh_pending:
        true,
      training_workspace_open:
        uiSessionOptionalBoolean(
          state.training_workspace_open
        ),
      training_readiness_open:
        uiSessionOptionalBoolean(
          state.training_readiness_open
        ),
      stat_growth_open:
        uiSessionOptionalBoolean(
          state.stat_growth_open
        ),
      stat_growth_focus:
        uiSessionTrainingFocus(
          state.stat_growth_focus
        ),
      stat_growth_scope:
        uiSessionStatGainScope(
          state.stat_growth_scope
        ),
      updated_at:
        Date.now()
    };

    try {
      uiOrientationHandoffStorage()?.setItem(
        UI_ORIENTATION_HANDOFF_STORAGE_KEY,
        JSON.stringify(
          handoff
        )
      );
    } catch (_) {}

    return handoff;
  }

  function readUiOrientationHandoff() {
    try {
      const raw =
        uiOrientationHandoffStorage()?.getItem(
          UI_ORIENTATION_HANDOFF_STORAGE_KEY
        );

      if (
        !raw
      ) {
        return null;
      }

      const parsed =
        JSON.parse(
          raw
        );

      if (
        !parsed ||
        typeof parsed !==
          'object' ||
        Array.isArray(
          parsed
        ) ||
        parsed.modal_open !==
          true
      ) {
        return null;
      }

      return {
        modal_open:
          true,
        analysis_visible:
          parsed.analysis_visible ===
          true,
        scroll_top:
          Math.max(
            0,
            Number(
              parsed.scroll_top
            ) ||
            0
          ),
        orientation:
          parsed.orientation ===
          'landscape'
            ? 'landscape'
            : 'portrait',
        orientation_refresh_pending:
          true,
        training_workspace_open:
          uiSessionOptionalBoolean(
            parsed.training_workspace_open
          ),
        training_readiness_open:
          uiSessionOptionalBoolean(
            parsed.training_readiness_open
          ),
        stat_growth_open:
          uiSessionOptionalBoolean(
            parsed.stat_growth_open
          ),
        stat_growth_focus:
          uiSessionTrainingFocus(
            parsed.stat_growth_focus
          ),
        stat_growth_scope:
          uiSessionStatGainScope(
            parsed.stat_growth_scope
          ),
        updated_at:
          Math.max(
            0,
            Number(
              parsed.updated_at
            ) ||
            0
          )
      };
    } catch (_) {
      return null;
    }
  }

  function defaultUiSessionState() {
    return {
      modal_open:
        false,
      analysis_visible:
        false,
      scroll_top:
        0,
      orientation:
        uiSessionOrientation(),
      orientation_refresh_pending:
        false,
      training_workspace_open:
        null,
      training_readiness_open:
        null,
      stat_growth_open:
        null,
      stat_growth_focus:
        'recent',
      stat_growth_scope:
        'selected',
      updated_at:
        0
    };
  }

  function readUiSessionState() {
    try {
      const storage =
        uiRestoreStorage();

      const raw =
        storage?.getItem(
          UI_SESSION_STORAGE_KEY
        );

      if (
        !raw
      ) {
        return defaultUiSessionState();
      }

      const parsed =
        JSON.parse(
          raw
        );

      if (
        !parsed ||
        typeof parsed !==
          'object' ||
        Array.isArray(
          parsed
        )
      ) {
        return defaultUiSessionState();
      }

      return {
        modal_open:
          parsed.modal_open ===
          true,
        analysis_visible:
          parsed.analysis_visible ===
          true,
        scroll_top:
          Math.max(
            0,
            Number(
              parsed.scroll_top
            ) ||
            0
          ),
        orientation:
          parsed.orientation ===
          'landscape'
            ? 'landscape'
            : 'portrait',
        orientation_refresh_pending:
          parsed.orientation_refresh_pending ===
          true,
        training_workspace_open:
          uiSessionOptionalBoolean(
            parsed.training_workspace_open
          ),
        training_readiness_open:
          uiSessionOptionalBoolean(
            parsed.training_readiness_open
          ),
        stat_growth_open:
          uiSessionOptionalBoolean(
            parsed.stat_growth_open
          ),
        stat_growth_focus:
          uiSessionTrainingFocus(
            parsed.stat_growth_focus
          ),
        stat_growth_scope:
          uiSessionStatGainScope(
            parsed.stat_growth_scope
          ),
        updated_at:
          Math.max(
            0,
            Number(
              parsed.updated_at
            ) ||
            0
          )
      };

    } catch (_) {
      return defaultUiSessionState();
    }
  }

  function writeUiSessionState(
    patch = {}
  ) {
    const current =
      readUiSessionState();

    const next = {
      ...current,
      ...patch,
      orientation:
        Object.prototype.hasOwnProperty.call(
          patch,
          'orientation'
        )
          ? patch.orientation
          : uiSessionOrientation(),
      updated_at:
        Date.now()
    };

    try {
      uiRestoreStorage()?.setItem(
        UI_SESSION_STORAGE_KEY,
        JSON.stringify(
          next
        )
      );
    } catch (_) {}

    if (
      next.modal_open !==
      true
    ) {
      clearUiOrientationHandoff();
    }

    return next;
  }

  function markUiModalOpened(
    restoreState = null
  ) {
    const opened =
      writeUiSessionState({
        modal_open:
          true,
        analysis_visible:
          restoreState?.analysis_visible ===
          true,
        scroll_top:
          Math.max(
            0,
            Number(
              restoreState?.scroll_top
            ) ||
            0
          ),
        orientation_refresh_pending:
          false
      });

    // TornPDA can replace the entire page context during rotation without
    // first delivering resize, orientationchange, or pagehide. Seed the
    // short-lived cross-context handoff as soon as the modal opens so that
    // path still restores. A same-orientation new tab remains fail-closed.
    writeUiOrientationHandoff(
      opened
    );

    return opened;
  }

  function markUiOrientationRefreshPending() {
    const current =
      readUiSessionState();

    if (
      !current.modal_open
    ) {
      clearUiOrientationHandoff();
      return false;
    }

    const pending =
      writeUiSessionState({
        orientation_refresh_pending:
          true,
        // Preserve the last stable orientation. The resize/orientation event
        // may fire after window dimensions already reflect the new layout.
        orientation:
          current.orientation
      });

    writeUiOrientationHandoff(
      pending
    );

    return true;
  }

  function consumeUiOrientationRestoreState() {
    const current =
      readUiSessionState();

    const orientation =
      uiSessionOrientation();

    const sessionAgeMs =
      current.updated_at > 0
        ? Date.now() -
          current.updated_at
        : Number.POSITIVE_INFINITY;

    const sessionFresh =
      sessionAgeMs >= 0 &&
      sessionAgeMs <
        UI_RESTORE_MAX_AGE_MS;

    const sessionRestore =
      current.modal_open &&
      sessionFresh;

    const handoff =
      readUiOrientationHandoff();

    const handoffAgeMs =
      handoff?.updated_at > 0
        ? Date.now() -
          handoff.updated_at
        : Number.POSITIVE_INFINITY;

    const handoffFresh =
      handoffAgeMs >= 0 &&
      handoffAgeMs <
        UI_ORIENTATION_HANDOFF_MAX_AGE_MS;

    // A persistent handoff is accepted only when orientation actually
    // changed. This lets TornPDA survive a replaced page context without
    // causing a normal same-orientation new tab to inherit the modal.
    const orientationRestore =
      !sessionRestore &&
      handoff?.modal_open &&
      handoffFresh &&
      handoff.orientation !==
        orientation;

    const source =
      sessionRestore
        ? current
        : orientationRestore
          ? handoff
          : null;

    clearUiOrientationHandoff();

    const restoreState =
      source
        ? {
            ...source
          }
        : null;

    writeUiSessionState({
      modal_open:
        Boolean(
          source
        ),
      analysis_visible:
        source?.analysis_visible ===
        true,
      scroll_top:
        source
          ? source.scroll_top
          : 0,
      orientation,
      orientation_refresh_pending:
        false,
      training_workspace_open:
        uiSessionOptionalBoolean(
          source?.training_workspace_open
        ),
      training_readiness_open:
        uiSessionOptionalBoolean(
          source?.training_readiness_open
        ),
      stat_growth_open:
        uiSessionOptionalBoolean(
          source?.stat_growth_open
        ),
      stat_growth_focus:
        uiSessionTrainingFocus(
          source?.stat_growth_focus
        ),
      stat_growth_scope:
        uiSessionStatGainScope(
          source?.stat_growth_scope
        )
    });

    return restoreState;
  }
  // ============================================================
  // STAT GROWTH ANALYTICS
  // ============================================================

  function gymTrainingSpec(
    logId
  ) {
    switch (
      Number(
        logId
      )
    ) {
      case 5300:
        return {
          log_id: 5300,
          stat: 'strength',
          label: 'Strength'
        };

      case 5301:
        return {
          log_id: 5301,
          stat: 'defense',
          label: 'Defense'
        };

      case 5302:
        return {
          log_id: 5302,
          stat: 'speed',
          label: 'Speed'
        };

      case 5303:
        return {
          log_id: 5303,
          stat: 'dexterity',
          label: 'Dexterity'
        };

      default:
        return null;
    }
  }

  function statGrowthFiniteNumber(
    value
  ) {
    if (
      typeof value === 'number'
    ) {
      return Number.isFinite(
        value
      )
        ? value
        : null;
    }

    if (
      typeof value !== 'string'
    ) {
      return null;
    }

    const normalized =
      value.trim();

    if (
      !normalized ||
      !/^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(
        normalized
      )
    ) {
      return null;
    }

    const number =
      Number(
        normalized
      );

    return Number.isFinite(
      number
    )
      ? number
      : null;
  }

  function statGrowthPositiveInteger(
    value
  ) {
    const number =
      statGrowthFiniteNumber(
        value
      );

    return Number.isSafeInteger(
      number
    ) &&
    number > 0
      ? number
      : null;
  }

  function statGrowthOptionalNonNegativeInteger(
    value
  ) {
    const number =
      statGrowthFiniteNumber(
        value
      );

    return Number.isSafeInteger(
      number
    ) &&
    number >= 0
      ? number
      : null;
  }

  function statGrowthNearlyEqual(
    left,
    right
  ) {
    if (
      !Number.isFinite(left) ||
      !Number.isFinite(right)
    ) {
      return false;
    }

    const scale =
      Math.max(
        1,
        Math.abs(left),
        Math.abs(right)
      );

    return Math.abs(
      left -
      right
    ) <=
      1e-8 *
      scale;
  }

  function inspectGymTrainingLog(
    log
  ) {
    const spec =
      gymTrainingSpec(
        log?.log ??
        log?.details?.id
      );

    if (
      !spec
    ) {
      return {
        recognized: false,
        valid: false,
        reason: 'not_gym_training',
        record: null
      };
    }

    const timestamp =
      Number(
        log?.timestamp
      );

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_timestamp',
        record: null
      };
    }

    const data =
      log?.data;

    if (
      !data ||
      typeof data !== 'object' ||
      Array.isArray(data)
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_data',
        record: null
      };
    }

    const trains =
      statGrowthPositiveInteger(
        data.trains
      );

    if (
      trains === null
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_trains',
        record: null
      };
    }

    const energyUsed =
      statGrowthPositiveInteger(
        data.energy_used
      );

    if (
      energyUsed === null
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_energy_used',
        record: null
      };
    }

    const beforeField =
      `${spec.stat}_before`;

    const afterField =
      `${spec.stat}_after`;

    const increasedField =
      `${spec.stat}_increased`;

    const before =
      statGrowthFiniteNumber(
        data[beforeField]
      );

    const after =
      statGrowthFiniteNumber(
        data[afterField]
      );

    const increased =
      statGrowthFiniteNumber(
        data[increasedField]
      );

    if (
      before === null ||
      before < 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_stat_before',
        record: null
      };
    }

    if (
      after === null ||
      after < 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_stat_after',
        record: null
      };
    }

    if (
      increased === null ||
      increased <= 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_stat_increase',
        record: null
      };
    }

    const observedDelta =
      after -
      before;

    if (
      observedDelta <= 0 ||
      !statGrowthNearlyEqual(
        observedDelta,
        increased
      )
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'inconsistent_stat_delta',
        record: null
      };
    }

    const warnings =
      [];

    const rawHappyUsed =
      data.happy_used;

    const happyUsed =
      statGrowthOptionalNonNegativeInteger(
        rawHappyUsed
      );

    if (
      rawHappyUsed !== null &&
      rawHappyUsed !== undefined &&
      rawHappyUsed !== '' &&
      happyUsed === null
    ) {
      warnings.push(
        'invalid_happy_used'
      );
    }

    const rawGym =
      data.gym;

    const gym =
      statGrowthPositiveInteger(
        rawGym
      );

    if (
      rawGym !== null &&
      rawGym !== undefined &&
      rawGym !== '' &&
      gym === null
    ) {
      warnings.push(
        'invalid_gym'
      );
    }

    return {
      recognized: true,
      valid: true,
      reason: null,
      record: {
        id:
          String(
            log?.id ??
            ''
          ),
        log_id:
          spec.log_id,
        title:
          String(
            log?.title ??
            ''
          ),
        timestamp,
        stat:
          spec.stat,
        stat_label:
          spec.label,
        trains,
        energy_used:
          energyUsed,
        energy_per_train:
          energyUsed /
          trains,
        happy_used:
          happyUsed,
        gym,
        stat_before:
          before,
        stat_after:
          after,
        stat_increased:
          increased,
        gain_per_energy:
          increased /
          energyUsed,
        warnings
      }
    };
  }

  function parseGymTrainingLog(
    log
  ) {
    const inspection =
      inspectGymTrainingLog(
        log
      );

    return inspection.valid
      ? inspection.record
      : null;
  }

  function statGrowthBlankStat(
    stat,
    label
  ) {
    return {
      stat,
      label,
      actions: 0,
      trains: 0,
      energy_used: 0,
      happy_used: 0,
      happy_known_actions: 0,
      gain: 0,
      gain_per_energy: 0,
      first_timestamp: null,
      last_timestamp: null,
      first_before: null,
      last_after: null
    };
  }

  function statGrowthBlankStatTotals() {
    return {
      strength:
        statGrowthBlankStat(
          'strength',
          'Strength'
        ),
      defense:
        statGrowthBlankStat(
          'defense',
          'Defense'
        ),
      speed:
        statGrowthBlankStat(
          'speed',
          'Speed'
        ),
      dexterity:
        statGrowthBlankStat(
          'dexterity',
          'Dexterity'
        )
    };
  }

  function statGrowthFocusStat(
    growth,
    focus = 'recent'
  ) {
    if (
      [
        'strength',
        'defense',
        'speed',
        'dexterity'
      ].includes(
        focus
      )
    ) {
      return focus;
    }

    const rows =
      Object.values(
        growth?.stats || {}
      )
        .filter(
          row =>
            row &&
            Number(row.actions || 0) > 0 &&
            Number.isSafeInteger(
              Number(row.last_timestamp)
            )
        );

    if (
      !rows.length
    ) {
      return null;
    }

    rows.sort(
      (
        left,
        right
      ) => {
        if (
          focus ===
          'most_trained'
        ) {
          return Number(right.trains || 0) -
            Number(left.trains || 0) ||
            Number(right.last_timestamp || 0) -
            Number(left.last_timestamp || 0) ||
            String(left.stat).localeCompare(
              String(right.stat)
            );
        }

        return Number(right.last_timestamp || 0) -
          Number(left.last_timestamp || 0) ||
          Number(right.trains || 0) -
          Number(left.trains || 0) ||
          String(left.stat).localeCompare(
            String(right.stat)
          );
      }
    );

    return rows[0].stat ||
      null;
  }

  function statGrowthCumulativeSamples(
    growth,
    stat,
    limit = 12
  ) {
    const normalizedStat =
      String(
        stat ||
        ''
      );

    const safeLimit =
      Math.max(
        1,
        Math.min(
          60,
          Math.floor(
            Number(limit) ||
            12
          )
        )
      );

    return (growth?.training_actions || [])
      .filter(
        action =>
          action?.stat ===
          normalizedStat
      )
      .slice()
      .sort(
        (
          left,
          right
        ) =>
          Number(left.timestamp || 0) -
            Number(right.timestamp || 0) ||
          String(left.id || '').localeCompare(
            String(right.id || '')
        )
      )
      .slice(
        -safeLimit
      );
  }

  function statGrowthAddToStat(
    target,
    action
  ) {
    target.actions++;
    target.trains +=
      action.trains;
    target.energy_used +=
      action.energy_used;
    target.gain +=
      action.stat_increased;

    if (
      action.happy_used !== null
    ) {
      target.happy_used +=
        action.happy_used;
      target.happy_known_actions++;
    }

    if (
      target.first_timestamp === null ||
      action.timestamp <
        target.first_timestamp ||
      (
        action.timestamp ===
          target.first_timestamp &&
        (
          target.first_before === null ||
          action.stat_before <
            target.first_before
        )
      )
    ) {
      target.first_timestamp =
        action.timestamp;
      target.first_before =
        action.stat_before;
    }

    if (
      target.last_timestamp === null ||
      action.timestamp >
        target.last_timestamp ||
      (
        action.timestamp ===
          target.last_timestamp &&
        action.stat_after >
          target.last_after
      )
    ) {
      target.last_timestamp =
        action.timestamp;
      target.last_after =
        action.stat_after;
    }

    target.gain_per_energy =
      target.energy_used > 0
        ? target.gain /
          target.energy_used
        : 0;
  }

  function statGrowthDayNumber(
    dateString
  ) {
    const [
      year,
      month,
      day
    ] =
      String(
        dateString ||
        ''
      )
        .split('-')
        .map(Number);

    return Math.floor(
      Date.UTC(
        year,
        month - 1,
        day
      ) /
      86400000
    );
  }

  function statGrowthWindow(
    days,
    windowDays,
    endDateOverride = null
  ) {
    const endDate =
      endDateOverride ||
      days?.[
        days.length - 1
      ]?.date ||
      null;

    if (
      !endDate
    ) {
      return {
        days: windowDays,
        start_date: null,
        end_date: null,
        actions: 0,
        trains: 0,
        energy_used: 0,
        happy_used: 0,
        gain: 0,
        gain_per_energy: 0,
        stats:
          statGrowthBlankStatTotals()
      };
    }

    const endDayNumber =
      statGrowthDayNumber(
        endDate
      );

    const startDayNumber =
      endDayNumber -
      windowDays +
      1;

    const selected =
      (days || []).filter(
        row => {
          const dayNumber =
            statGrowthDayNumber(
              row.date
            );

          return dayNumber >=
            startDayNumber &&
            dayNumber <=
            endDayNumber;
        }
      );

    const stats =
      statGrowthBlankStatTotals();

    let actions = 0;
    let trains = 0;
    let energyUsed = 0;
    let happyUsed = 0;
    let gain = 0;

    for (
      const day
      of selected
    ) {
      actions +=
        day.actions;
      trains +=
        day.trains;
      energyUsed +=
        day.energy_used;
      happyUsed +=
        day.happy_used;
      gain +=
        day.gain;

      for (
        const stat
        of Object.keys(
          stats
        )
      ) {
        const source =
          day.stats[stat];

        stats[stat].actions +=
          source.actions;
        stats[stat].trains +=
          source.trains;
        stats[stat].energy_used +=
          source.energy_used;
        stats[stat].happy_used +=
          source.happy_used;
        stats[stat].happy_known_actions +=
          source.happy_known_actions;
        stats[stat].gain +=
          source.gain;

        stats[stat].gain_per_energy =
          stats[stat].energy_used > 0
            ? stats[stat].gain /
              stats[stat].energy_used
            : 0;
      }
    }

    return {
      days:
        windowDays,
      start_date:
        new Date(
          startDayNumber *
          86400000
        )
          .toISOString()
          .slice(0, 10),
      end_date:
        endDate,
      actions,
      trains,
      energy_used:
        energyUsed,
      happy_used:
        happyUsed,
      gain,
      gain_per_energy:
        energyUsed > 0
          ? gain /
            energyUsed
          : 0,
      stats
    };
  }

  function buildStatGrowth(
    logs,
    timeBasis = 'local'
  ) {
    const normalizedTimeBasis =
      normalizeActivityTimeBasis(
        timeBasis
      );

    const actions =
      [];

    let recognizedLogs = 0;
    let historyLastTimestamp = null;

    const rejectionReasons =
      {};

    const warningReasons =
      {};

    for (
      const log
      of logs || []
    ) {
      const candidateTimestamp =
        Number(
          log?.timestamp
        );

      if (
        Number.isSafeInteger(
          candidateTimestamp
        ) &&
        candidateTimestamp > 0 &&
        (
          historyLastTimestamp === null ||
          candidateTimestamp >
            historyLastTimestamp
        )
      ) {
        historyLastTimestamp =
          candidateTimestamp;
      }

      const inspection =
        inspectGymTrainingLog(
          log
        );

      if (
        !inspection.recognized
      ) {
        continue;
      }

      recognizedLogs++;

      if (
        !inspection.valid
      ) {
        rejectionReasons[
          inspection.reason
        ] =
          (
            rejectionReasons[
              inspection.reason
            ] ||
            0
          ) +
          1;
        continue;
      }

      for (
        const warning
        of inspection.record.warnings
      ) {
        warningReasons[
          warning
        ] =
          (
            warningReasons[
              warning
            ] ||
            0
          ) +
          1;
      }

      actions.push(
        inspection.record
      );
    }

    actions.sort(
      (
        left,
        right
      ) =>
        left.timestamp -
          right.timestamp ||
        left.id.localeCompare(
          right.id
        )
    );

    const stats =
      statGrowthBlankStatTotals();

    const byDay =
      new Map();

    const byGym =
      new Map();

    let totalTrains = 0;
    let totalEnergyUsed = 0;
    let totalHappyUsed = 0;
    let happyKnownActions = 0;
    let totalGain = 0;

    for (
      const action
      of actions
    ) {
      totalTrains +=
        action.trains;
      totalEnergyUsed +=
        action.energy_used;
      totalGain +=
        action.stat_increased;

      if (
        action.happy_used !== null
      ) {
        totalHappyUsed +=
          action.happy_used;
        happyKnownActions++;
      }

      statGrowthAddToStat(
        stats[action.stat],
        action
      );

      const date =
        new Date(
          action.timestamp *
          1000
        );

      const dateKey =
        activityDateKeyForBasis(
          date,
          normalizedTimeBasis
        );

      const day =
        byDay.get(
          dateKey
        ) || {
          date:
            dateKey,
          actions: 0,
          trains: 0,
          energy_used: 0,
          happy_used: 0,
          happy_known_actions: 0,
          gain: 0,
          gain_per_energy: 0,
          stats:
            statGrowthBlankStatTotals()
        };

      day.actions++;
      day.trains +=
        action.trains;
      day.energy_used +=
        action.energy_used;
      day.gain +=
        action.stat_increased;

      if (
        action.happy_used !== null
      ) {
        day.happy_used +=
          action.happy_used;
        day.happy_known_actions++;
      }

      day.gain_per_energy =
        day.energy_used > 0
          ? day.gain /
            day.energy_used
          : 0;

      statGrowthAddToStat(
        day.stats[action.stat],
        action
      );

      byDay.set(
        dateKey,
        day
      );

      const gymKey =
        action.gym === null
          ? 'unknown'
          : String(
              action.gym
            );

      const gym =
        byGym.get(
          gymKey
        ) || {
          gym_id:
            action.gym,
          actions: 0,
          trains: 0,
          energy_used: 0,
          happy_used: 0,
          happy_known_actions: 0,
          gain: 0,
          gain_per_energy: 0,
          first_timestamp: null,
          last_timestamp: null,
          stats:
            statGrowthBlankStatTotals()
        };

      gym.actions++;
      gym.trains +=
        action.trains;
      gym.energy_used +=
        action.energy_used;
      gym.gain +=
        action.stat_increased;

      if (
        action.happy_used !== null
      ) {
        gym.happy_used +=
          action.happy_used;
        gym.happy_known_actions++;
      }

      gym.gain_per_energy =
        gym.energy_used > 0
          ? gym.gain /
            gym.energy_used
          : 0;

      gym.first_timestamp =
        gym.first_timestamp === null
          ? action.timestamp
          : Math.min(
              gym.first_timestamp,
              action.timestamp
            );

      gym.last_timestamp =
        gym.last_timestamp === null
          ? action.timestamp
          : Math.max(
              gym.last_timestamp,
              action.timestamp
            );

      statGrowthAddToStat(
        gym.stats[action.stat],
        action
      );

      byGym.set(
        gymKey,
        gym
      );
    }

    const days =
      Array.from(
        byDay.values()
      ).sort(
        (
          left,
          right
        ) =>
          statGrowthDayNumber(
            left.date
          ) -
          statGrowthDayNumber(
            right.date
          )
      );

    const gyms =
      Array.from(
        byGym.values()
      ).sort(
        (
          left,
          right
        ) =>
          (
            left.first_timestamp ||
            0
          ) -
          (
            right.first_timestamp ||
            0
          ) ||
          Number(
            left.gym_id ||
            0
          ) -
          Number(
            right.gym_id ||
            0
          )
      );

    const historyLastDate =
      historyLastTimestamp === null
        ? null
        : activityDateKeyForBasis(
            new Date(
              historyLastTimestamp *
              1000
            ),
            normalizedTimeBasis
          );

    const bestDayByGain =
      days.reduce(
        (
          best,
          day
        ) =>
          !best ||
          day.gain >
            best.gain
            ? day
            : best,
        null
      );

    return {
      time_basis:
        normalizedTimeBasis,
      recognized_logs:
        recognizedLogs,
      valid_logs:
        actions.length,
      rejected_logs:
        recognizedLogs -
        actions.length,
      rejection_reasons:
        rejectionReasons,
      warning_reasons:
        warningReasons,
      actions:
        actions.length,
      training_actions:
        actions,
      trains:
        totalTrains,
      energy_used:
        totalEnergyUsed,
      happy_used:
        totalHappyUsed,
      happy_known_actions:
        happyKnownActions,
      gain:
        totalGain,
      gain_per_energy:
        totalEnergyUsed > 0
          ? totalGain /
            totalEnergyUsed
          : 0,
      training_days:
        days.length,
      history_last_timestamp:
        historyLastTimestamp,
      history_last_date:
        historyLastDate,
      first_timestamp:
        actions[0]?.timestamp ||
        null,
      last_timestamp:
        actions[
          actions.length - 1
        ]?.timestamp ||
        null,
      first_date:
        days[0]?.date ||
        null,
      last_date:
        days[
          days.length - 1
        ]?.date ||
        null,
      best_day_by_gain:
        bestDayByGain,
      stats,
      days,
      gyms,
      recent_7_days:
        statGrowthWindow(
          days,
          7,
          historyLastDate
        ),
      recent_14_days:
        statGrowthWindow(
          days,
          14,
          historyLastDate
        ),
      recent_30_days:
        statGrowthWindow(
          days,
          30,
          historyLastDate
        )
    };
  }
  // ============================================================
  // TRAINING READINESS
  // ============================================================

  function normalizeTrainingCooldownsResponse(
    json,
    fetchedAt = Date.now()
  ) {
    const source = json?.cooldowns;

    if (!source || typeof source !== 'object' || Array.isArray(source)) {
      throw new Error('Torn API returned an invalid cooldowns response.');
    }

    const normalize = value => {
      const seconds = Number(value);
      return Number.isSafeInteger(seconds) &&
        seconds >= 0 &&
        seconds <= 30 * 24 * 60 * 60
        ? seconds
        : null;
    };

    const drug = normalize(source.drug);
    const booster = normalize(source.booster);

    if (drug === null || booster === null) {
      throw new Error('Torn API returned invalid drug or booster cooldown data.');
    }

    const safeFetchedAt = Number.isFinite(Number(fetchedAt))
      ? Number(fetchedAt)
      : Date.now();

    return {
      status: 'available',
      fetched_at: safeFetchedAt,
      drug_ready_at: Math.ceil(safeFetchedAt / 1000) + drug,
      booster_ready_at: Math.ceil(safeFetchedAt / 1000) + booster
    };
  }

  async function fetchTrainingCooldownsSnapshot(
    apiKey,
    tracker
  ) {
    const json = await apiFetchJson(
      `${API_BASE}/user/cooldowns`,
      apiKey,
      tracker
    );

    return normalizeTrainingCooldownsResponse(json, Date.now());
  }

  async function loadTrainingCooldownsSnapshot(
    apiKey,
    tracker
  ) {
    const normalizedKey = String(apiKey || '').trim();

    if (!normalizedKey) {
      return {
        status: 'unavailable',
        reason: 'api_key_unavailable',
        fetched_at: null
      };
    }

    tracker?.setStage(
      'Refreshing training cooldowns…',
      'One live Torn API request'
    );

    try {
      return await fetchTrainingCooldownsSnapshot(normalizedKey, tracker);
    } catch (error) {
      console.warn('Training cooldown refresh failed.', error);
      return {
        status: 'unavailable',
        reason: 'api_request_failed',
        fetched_at: null
      };
    }
  }

  function trainingReadinessQuarterHour(
    nowMs = Date.now()
  ) {
    const safeNow = Number.isFinite(Number(nowMs))
      ? Number(nowMs)
      : Date.now();
    const intervalMs = 15 * 60 * 1000;
    const nextMs = Math.floor(safeNow / intervalMs + 1) * intervalMs;

    return {
      next_timestamp: Math.floor(nextMs / 1000),
      seconds_until: Math.max(0, Math.ceil((nextMs - safeNow) / 1000))
    };
  }

  function trainingReadinessQuantile(
    values,
    proportion
  ) {
    const sorted = (values || [])
      .map(Number)
      .filter(value => Number.isFinite(value) && value >= 0)
      .sort((left, right) => left - right);

    if (!sorted.length) {
      return null;
    }

    const position = Math.max(0, Math.min(1, Number(proportion) || 0)) *
      (sorted.length - 1);
    const lower = Math.floor(position);
    const upper = Math.ceil(position);

    if (lower === upper) {
      return sorted[lower];
    }

    return sorted[lower] +
      (sorted[upper] - sorted[lower]) *
      (position - lower);
  }

  function trainingReadinessModel(
    actions,
    stat,
    gymId
  ) {
    const comparable = (actions || [])
      .filter(action =>
        action?.stat === stat &&
        (
          gymId === null ||
          Number(action?.gym) === Number(gymId)
        ) &&
        Number.isFinite(Number(action?.gain_per_energy)) &&
        Number(action.gain_per_energy) > 0
      )
      .sort((left, right) =>
        Number(right.timestamp || 0) - Number(left.timestamp || 0)
      )
      .slice(0, 12);

    const rates = comparable.map(action => Number(action.gain_per_energy));
    const observations = comparable
      .slice()
      .reverse()
      .map(action => ({
        timestamp: Number(action.timestamp || 0),
        rate: Number(action.gain_per_energy)
      }));
    const samples = rates.length;

    return {
      stat,
      gym_id: gymId,
      samples,
      observations,
      confidence:
        samples >= 8
          ? 'High'
          : samples >= 4
            ? 'Medium'
            : samples >= 2
              ? 'Low'
              : 'Insufficient',
      rate_low:
        samples >= 2
          ? trainingReadinessQuantile(rates, 0.25)
          : null,
      rate_mid:
        samples >= 2
          ? trainingReadinessQuantile(rates, 0.5)
          : null,
      rate_high:
        samples >= 2
          ? trainingReadinessQuantile(rates, 0.75)
          : null
    };
  }

  function buildTrainingReadiness(
    growth,
    bars,
    cooldowns,
    nowMs = Date.now(),
    pageUrl = ''
  ) {
    const actions = Array.isArray(growth?.training_actions)
      ? growth.training_actions
      : [];
    const latest = actions.length
      ? actions[actions.length - 1]
      : null;
    const gymId = Number.isSafeInteger(Number(latest?.gym)) &&
      Number(latest.gym) > 0
      ? Number(latest.gym)
      : null;
    const defaultStat =
      ['strength', 'defense', 'speed', 'dexterity'].includes(latest?.stat)
        ? latest.stat
        : 'strength';
    const effectiveUrl = String(
      pageUrl ||
      (typeof location !== 'undefined' ? location.href : '')
    );
    const energy = bars?.status === 'available'
      ? Number(bars?.energy?.current)
      : null;
    const happiness = bars?.status === 'available'
      ? Number(bars?.happiness?.current)
      : null;
    const happinessMaximum = bars?.status === 'available'
      ? Number(bars?.happiness?.maximum)
      : null;
    const models = {};

    for (const stat of ['strength', 'defense', 'speed', 'dexterity']) {
      models[stat] = trainingReadinessModel(actions, stat, gymId);
    }

    return {
      page_is_gym: /(?:^|\/)gym\.php(?:[?#]|$)/i.test(effectiveUrl),
      default_stat: defaultStat,
      gym_id: gymId,
      last_training_timestamp: latest?.timestamp || null,
      energy: Number.isFinite(energy) ? energy : null,
      happiness: Number.isFinite(happiness) ? happiness : null,
      happiness_maximum: Number.isFinite(happinessMaximum)
        ? happinessMaximum
        : null,
      over_happiness:
        Number.isFinite(happiness) &&
        Number.isFinite(happinessMaximum) &&
        happiness > happinessMaximum,
      drug_ready_at:
        cooldowns?.status === 'available' &&
        Number.isSafeInteger(Number(cooldowns.drug_ready_at))
          ? Number(cooldowns.drug_ready_at)
          : null,
      booster_ready_at:
        cooldowns?.status === 'available' &&
        Number.isSafeInteger(Number(cooldowns.booster_ready_at))
          ? Number(cooldowns.booster_ready_at)
          : null,
      quarter_hour: trainingReadinessQuarterHour(nowMs),
      models
    };
  }

  function trainingReadinessProjection(
    model,
    plannedEnergy
  ) {
    const energy = Math.max(
      1,
      Math.min(5000, Math.floor(Number(plannedEnergy) || 0))
    );

    if (
      !model ||
      Number(model.samples) < 2 ||
      !Number.isFinite(Number(model.rate_low)) ||
      !Number.isFinite(Number(model.rate_high))
    ) {
      return {
        energy,
        available: false,
        low: null,
        high: null
      };
    }

    return {
      energy,
      available: true,
      low: Number(model.rate_low) * energy,
      high: Number(model.rate_high) * energy
    };
  }

  function trainingReadinessStatLabel(
    stat
  ) {
    return {
      strength: 'Strength',
      defense: 'Defense',
      speed: 'Speed',
      dexterity: 'Dexterity'
    }[stat] || 'Strength';
  }

  function trainingReadinessFormatDuration(
    seconds
  ) {
    const safe = Math.max(0, Math.floor(Number(seconds) || 0));
    const hours = Math.floor(safe / 3600);
    const minutes = Math.floor(safe / 60);
    const remainder = safe % 60;

    if (hours > 0) {
      return `${hours}h ${Math.floor((safe % 3600) / 60)}m`;
    }

    return `${minutes}m ${remainder}s`;
  }

  function trainingReadinessHistoryChart(
    observations,
    stat
  ) {
    const points = (Array.isArray(observations) ? observations : [])
      .map(observation => ({
        timestamp: Number(observation?.timestamp),
        rate: Number(observation?.rate)
      }))
      .filter(observation =>
        Number.isFinite(observation.timestamp) &&
        observation.timestamp > 0 &&
        Number.isFinite(observation.rate) &&
        observation.rate > 0
      )
      .slice(-12);

    if (points.length < 2) {
      return '<div class="ta-section-intro">Not enough comparable observations to draw a history graph yet.</div>';
    }

    const width = 320;
    const height = 128;
    const left = 38;
    const right = 10;
    const top = 12;
    const bottom = 24;
    const rates = points.map(point => point.rate);
    const rawMin = Math.min(...rates);
    const rawMax = Math.max(...rates);
    const spread = rawMax - rawMin;
    const padding = spread > 0 ? spread * 0.15 : Math.max(rawMax * 0.08, 0.01);
    const minRate = Math.max(0, rawMin - padding);
    const maxRate = rawMax + padding;
    const range = Math.max(maxRate - minRate, 0.000001);
    const plotWidth = width - left - right;
    const plotHeight = height - top - bottom;
    const xFor = index =>
      left + (points.length === 1 ? 0 : (index / (points.length - 1)) * plotWidth);
    const yFor = rate =>
      top + ((maxRate - rate) / range) * plotHeight;
    const polyline = points
      .map((point, index) => `${xFor(index).toFixed(1)},${yFor(point.rate).toFixed(1)}`)
      .join(' ');
    const circles = points
      .map((point, index) =>
        `<circle cx="${xFor(index).toFixed(1)}" cy="${yFor(point.rate).toFixed(1)}" r="2.8" fill="currentColor"><title>${escapeActivityHtml(new Date(point.timestamp * 1000).toLocaleString())}: ${escapeActivityHtml(statGrowthFormatNumber(point.rate, 4))} gain/E</title></circle>`
      )
      .join('');
    const median = trainingReadinessQuantile(rates, 0.5);
    const medianY = yFor(median).toFixed(1);
    const firstDate = new Date(points[0].timestamp * 1000)
      .toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
    const lastDate = new Date(points[points.length - 1].timestamp * 1000)
      .toLocaleDateString(undefined, { month: 'short', day: 'numeric' });

    return `
      <div class="ta-section-intro">${escapeActivityHtml(trainingReadinessStatLabel(stat))} · gain per Energy · same observed gym</div>
      <svg viewBox="0 0 ${width} ${height}" role="img" aria-label="Observed ${escapeActivityHtml(trainingReadinessStatLabel(stat))} gain per Energy over recent comparable training actions" style="display:block;width:100%;height:auto;max-height:180px;overflow:visible;color:inherit">
        <line x1="${left}" y1="${top}" x2="${left}" y2="${height - bottom}" stroke="currentColor" opacity="0.25" />
        <line x1="${left}" y1="${height - bottom}" x2="${width - right}" y2="${height - bottom}" stroke="currentColor" opacity="0.25" />
        <line x1="${left}" y1="${medianY}" x2="${width - right}" y2="${medianY}" stroke="currentColor" opacity="0.35" stroke-dasharray="4 4" />
        <polyline points="${polyline}" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" />
        ${circles}
        <text x="2" y="${top + 4}" fill="currentColor" opacity="0.7" font-size="9">${escapeActivityHtml(statGrowthFormatNumber(rawMax, 3))}</text>
        <text x="2" y="${height - bottom}" fill="currentColor" opacity="0.7" font-size="9">${escapeActivityHtml(statGrowthFormatNumber(rawMin, 3))}</text>
        <text x="${left}" y="${height - 7}" fill="currentColor" opacity="0.7" font-size="9">${escapeActivityHtml(firstDate)}</text>
        <text x="${width - right}" y="${height - 7}" fill="currentColor" opacity="0.7" font-size="9" text-anchor="end">${escapeActivityHtml(lastDate)}</text>
      </svg>
      <div class="ta-section-intro">Dashed line = median. Points are real recorded observations; no Happiness prediction is applied.</div>
    `;
  }

  function renderTrainingReadinessDashboard(
    readiness,
    renderOptions
  ) {
    if (!readiness) {
      return '';
    }

    const safeRenderOptions =
      renderOptions &&
      typeof renderOptions === 'object'
        ? renderOptions
        : {};

    const defaultModel = readiness.models?.[readiness.default_stat];
    const plannedEnergy = Math.max(1, Math.floor(Number(readiness.energy) || 250));
    const projection = trainingReadinessProjection(defaultModel, plannedEnergy);

    const options = ['strength', 'defense', 'speed', 'dexterity']
      .map(stat => {
        const model = readiness.models?.[stat] || {};
        const encodedObservations = encodeURIComponent(
          JSON.stringify(model.observations || [])
        );
        return `<option value="${stat}" ${stat === readiness.default_stat ? 'selected' : ''} data-samples="${Number(model.samples || 0)}" data-confidence="${escapeActivityHtml(model.confidence || 'Insufficient')}" data-rate-low="${Number.isFinite(Number(model.rate_low)) ? Number(model.rate_low) : ''}" data-rate-high="${Number.isFinite(Number(model.rate_high)) ? Number(model.rate_high) : ''}" data-observations="${encodedObservations}">${trainingReadinessStatLabel(stat)}</option>`;
      })
      .join('');

    const projectionText = projection.available
      ? `${statGrowthFormatNumber(projection.low, 2)}–${statGrowthFormatNumber(projection.high, 2)} observed gain`
      : 'Not enough comparable training samples yet';
    const sampleText =
      `${Number(defaultModel?.samples || 0)} comparable samples · ${defaultModel?.confidence || 'Insufficient'} confidence`;
    const resetDuration = trainingReadinessFormatDuration(
      readiness.quarter_hour?.seconds_until
    );
    const recommendation = readiness.energy === null
      ? 'Live Energy is unavailable. Historical estimates still work.'
      : readiness.energy <= 0
        ? 'Wait for Energy before training.'
        : 'Ready to train. For a happiness boost, use a booster just after a TCT quarter-hour and train before the next one.';
    const recommendationHtml =
      readiness.over_happiness && readiness.energy !== null && readiness.energy > 0
        ? `Train before the next quarter-hour reset (<span data-ta-quarter-countdown>${escapeActivityHtml(resetDuration)}</span>).`
        : escapeActivityHtml(recommendation);

    const sectionOpen =
      safeRenderOptions.open === true ||
      (
        safeRenderOptions.open !== false &&
        readiness.page_is_gym
      );

    const quarterHourMetric = `
      <div class="ta-metric-card">
        <div class="ta-metric-label">Quarter-hour</div>
        <div class="ta-metric-value">
          Next TCT quarter-hour in
          <span data-ta-quarter-countdown>${escapeActivityHtml(resetDuration)}</span>
        </div>
        <div class="ta-metric-note">TCT (UTC)</div>
      </div>
    `;

    const cooldownMetric = (label, readyAt) => {
      const available =
        readyAt !== null &&
        readyAt !== undefined &&
        Number.isSafeInteger(Number(readyAt)) &&
        Number(readyAt) > 0;
      const remaining = available
        ? Math.max(0, Number(readyAt) - Math.floor(Date.now() / 1000))
        : null;

      return `
        <div class="ta-metric-card">
          <div class="ta-metric-label">${escapeActivityHtml(label)}</div>
          <div class="ta-metric-value" ${available ? `data-ta-cooldown-ready-at="${Number(readyAt)}"` : ''}>
            ${available ? (remaining <= 0 ? 'Ready' : escapeActivityHtml(trainingReadinessFormatDuration(remaining))) : '—'}
          </div>
          <div class="ta-metric-note">${available ? 'Live from Torn' : 'Live cooldown unavailable'}</div>
        </div>
      `;
    };

    return `
      <details class="ta-section ta-training-readiness-section" ${sectionOpen ? 'open' : ''}>
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">Training Readiness</span>
          <span class="ta-section-meta">${readiness.energy === null ? 'Historical only' : `${Number(readiness.energy).toLocaleString()} E`}</span>
        </summary>

        <div class="ta-section-body">
          <div class="ta-section-intro">
            Read-only guidance from live bars and your own observed gym history. Estimates are historical ranges, not Torn formula guarantees.
          </div>

          <div class="ta-training-status" data-ta-training-recommendation>${recommendationHtml}</div>

          <div class="ta-metric-grid">
            ${activityDashboardMetric('Live Energy', readiness.energy === null ? '—' : Number(readiness.energy).toLocaleString(), readiness.energy === null ? 'Live Energy unavailable' : 'Live from Torn')}
            ${activityDashboardMetric('Live Happiness', readiness.happiness === null ? '—' : Number(readiness.happiness).toLocaleString(), readiness.happiness === null ? 'Live Happiness unavailable' : readiness.happiness_maximum === null ? 'Live from Torn' : `${Number(readiness.happiness_maximum).toLocaleString()} maximum`)}
            ${activityDashboardMetric('Last observed gym', statGrowthGymName(readiness.gym_id), readiness.last_training_timestamp ? 'From your latest valid gym log' : 'No valid gym log yet')}
            ${quarterHourMetric}
            ${cooldownMetric('Drug cooldown', readiness.drug_ready_at)}
            ${cooldownMetric('Booster cooldown', readiness.booster_ready_at)}
          </div>

          <div class="ta-training-controls">
            <label>
              <span>Target stat</span>
              <select data-ta-training-stat>${options}</select>
            </label>
            <label>
              <span>Planned Energy</span>
              <input data-ta-training-energy type="number" min="1" max="5000" step="5" value="${plannedEnergy}">
            </label>
          </div>

          <div class="ta-training-projection">
            <strong data-ta-training-projection>${escapeActivityHtml(projectionText)}</strong>
            <span data-ta-training-samples>${escapeActivityHtml(sampleText)}</span>
          </div>

          <details class="ta-section" style="margin-top:10px">
            <summary class="ta-section-summary-row">
              <span class="ta-section-title">Observed gain history</span>
              <span class="ta-section-meta">Last ${Number(defaultModel?.samples || 0)} samples</span>
            </summary>
            <div class="ta-section-body" data-ta-training-history>
              ${trainingReadinessHistoryChart(defaultModel?.observations, readiness.default_stat)}
            </div>
          </details>
        </div>
      </details>
    `;
  }

  function bindTrainingReadinessInteractions(
    root
  ) {
    const section = root?.querySelector?.('.ta-training-readiness-section');

    if (!section) {
      return;
    }

    const select = section.querySelector('[data-ta-training-stat]');
    const input = section.querySelector('[data-ta-training-energy]');
    const output = section.querySelector('[data-ta-training-projection]');
    const samples = section.querySelector('[data-ta-training-samples]');
    const history = section.querySelector('[data-ta-training-history]');
    const historyMeta = history
      ?.closest('details')
      ?.querySelector('.ta-section-meta');

    const refreshQuarterHour = () => {
      if (!section.isConnected) {
        return;
      }

      const duration = trainingReadinessFormatDuration(
        trainingReadinessQuarterHour(Date.now()).seconds_until
      );

      for (const clock of section.querySelectorAll('[data-ta-quarter-countdown]')) {
        clock.textContent = duration;
      }

      for (const cooldown of section.querySelectorAll('[data-ta-cooldown-ready-at]')) {
        const readyAt = Number(
          cooldown.getAttribute('data-ta-cooldown-ready-at')
        );
        const remaining = Math.max(
          0,
          readyAt - Math.floor(Date.now() / 1000)
        );

        cooldown.textContent = remaining <= 0
          ? 'Ready'
          : trainingReadinessFormatDuration(remaining);
      }

      setTimeout(
        refreshQuarterHour,
        1000 - (Date.now() % 1000) + 20
      );
    };

    const refresh = () => {
      const option = select?.selectedOptions?.[0];
      let observations = [];

      try {
        observations = JSON.parse(
          decodeURIComponent(option?.dataset?.observations || '%5B%5D')
        );
      } catch {
        observations = [];
      }

      const model = {
        samples: Number(option?.dataset?.samples || 0),
        confidence: option?.dataset?.confidence || 'Insufficient',
        rate_low: option?.dataset?.rateLow
          ? Number(option.dataset.rateLow)
          : null,
        rate_high: option?.dataset?.rateHigh
          ? Number(option.dataset.rateHigh)
          : null,
        observations
      };
      const projection = trainingReadinessProjection(model, input?.value);

      if (output) {
        output.textContent = projection.available
          ? `${statGrowthFormatNumber(projection.low, 2)}–${statGrowthFormatNumber(projection.high, 2)} observed gain`
          : 'Not enough comparable training samples yet';
      }

      if (samples) {
        samples.textContent = `${model.samples} comparable samples · ${model.confidence} confidence`;
      }

      if (history) {
        history.innerHTML = trainingReadinessHistoryChart(
          model.observations,
          option?.value || 'strength'
        );
      }

      if (historyMeta) {
        historyMeta.textContent = `Last ${model.samples} samples`;
      }
    };

    select?.addEventListener('change', refresh);
    input?.addEventListener('input', refresh);
    refreshQuarterHour();
  }
  // ============================================================
  // STAT GROWTH DASHBOARD
  // ============================================================

  function statGrowthGymName(
    gymId
  ) {
    const names = {
      1: 'Premier Fitness',
      2: 'Average Joes',
      3: "Woody's Workout",
      4: 'Beach Bods',
      5: 'Silver Gym',
      6: 'Pour Femme',
      7: 'Davies Den',
      8: 'Global Gym',
      9: 'Knuckle Heads',
      10: 'Pioneer Fitness',
      11: 'Anabolic Anomalies',
      12: 'Core',
      13: 'Racing Fitness',
      14: 'Complete Cardio',
      15: 'Legs, Bums and Tums',
      16: 'Deep Burn',
      17: 'Apollo Gym',
      18: 'Gun Shop',
      19: 'Force Training',
      20: "Cha Cha's",
      21: 'Atlas',
      22: 'Last Round',
      23: 'The Edge',
      24: "George's",
      25: 'Balboas Gym',
      26: 'Frontline Fitness',
      27: 'Gym 3000',
      28: 'Mr. Isoyamas',
      29: 'Total Rebound',
      30: 'Elites',
      31: 'The Sports Science Lab',
      32: 'Jail Gym'
    };

    const numericId =
      Number(
        gymId
      );

    if (
      Number.isSafeInteger(
        numericId
      ) &&
      numericId > 0
    ) {
      return names[numericId] ||
        `Gym #${numericId}`;
    }

    return 'Unknown gym';
  }

  function statGrowthFormatNumber(
    value,
    maximumFractionDigits = 2
  ) {
    const number =
      Number(
        value
      );

    if (
      !Number.isFinite(
        number
      )
    ) {
      return '—';
    }

    return number.toLocaleString(
      undefined,
      {
        maximumFractionDigits:
          Math.max(
            0,
            Math.min(
              6,
              Number(
                maximumFractionDigits
              ) ||
              0
            )
          )
      }
    );
  }

  function statGrowthFormatGain(
    value
  ) {
    const number =
      Number(
        value
      );

    if (
      !Number.isFinite(
        number
      )
    ) {
      return '—';
    }

    return `${number >= 0 ? '+' : ''}${statGrowthFormatNumber(number, 2)}`;
  }

  function statGrowthFormatRate(
    value
  ) {
    return statGrowthFormatNumber(
      value,
      4
    );
  }

  function statGrowthTimeBasisLabel(
    growth
  ) {
    return activityDashboardTimezoneContext(
      new Date(),
      growth?.time_basis
    ).label;
  }

  function statGrowthRecentDays(
    growth,
    length = 14
  ) {
    const endDate =
      growth?.history_last_date ||
      growth?.last_date ||
      null;

    if (
      !endDate
    ) {
      return [];
    }

    const safeLength =
      Math.max(
        1,
        Math.min(
          30,
          Math.floor(
            Number(length) ||
            14
          )
        )
      );

    const lookup =
      new Map(
        (growth.days || [])
          .map(
            day => [
              day.date,
              day
            ]
          )
      );

    const rows =
      [];

    for (
      let offset =
        safeLength - 1;
      offset >= 0;
      offset--
    ) {
      const date =
        addDays(
          endDate,
          -offset
        );

      const day =
        lookup.get(
          date
        );

      rows.push(
        day || {
          date,
          actions: 0,
          trains: 0,
          energy_used: 0,
          happy_used: 0,
          happy_known_actions: 0,
          gain: 0,
          gain_per_energy: 0,
          stats:
            statGrowthBlankStatTotals()
        }
      );
    }

    return rows;
  }

  function statGrowthDayDetail(
    day,
    growth,
    windowDays
  ) {
    const timezone =
      statGrowthTimeBasisLabel(
        growth
      );

    const statParts =
      [
        'strength',
        'defense',
        'speed',
        'dexterity'
      ]
        .map(
          stat => {
            const row =
              day?.stats?.[stat];

            if (
              !row?.gain
            ) {
              return null;
            }

            return `${row.label} ${statGrowthFormatGain(row.gain)}`;
          }
        )
        .filter(Boolean)
        .join(' · ');

    return `${activityDashboardLongDate(day.date)} · ` +
      `${statGrowthFormatGain(day.gain)} observed gain · ` +
      `${Number(day.energy_used || 0).toLocaleString()} energy · ` +
      `${Number(day.trains || 0).toLocaleString()} trains · ` +
      `${Number(day.actions || 0).toLocaleString()} actions` +
      `${statParts ? ` · ${statParts}` : ''} · ` +
      `${timezone} · displayed ${windowDays}-day window`;
  }

  function statGrowthCumulativeFocusLabel(
    focus
  ) {
    return {
      recent: 'Most recent',
      most_trained: 'Most trained',
      strength: 'Strength',
      defense: 'Defense',
      speed: 'Speed',
      dexterity: 'Dexterity'
    }[
      uiSessionTrainingFocus(
        focus
      )
    ];
  }

  function renderStatGrowthFocusControl(
    focus
  ) {
    const selected =
      uiSessionTrainingFocus(
        focus
      );

    return `
      <div class="ta-stat-total-controls">
        <label>
          <span>Stat</span>
          <select data-ta-stat-total-focus>
            ${[
              'recent',
              'most_trained',
              'strength',
              'defense',
              'speed',
              'dexterity'
            ].map(
              option => `
                <option
                  value="${option}"
                  ${option === selected ? 'selected' : ''}
                >${escapeActivityHtml(statGrowthCumulativeFocusLabel(option))}</option>
              `
            ).join('')}
          </select>
        </label>
      </div>
    `;
  }
  function statGrowthCumulativeSampleDetail(
    action
  ) {
    const date =
      new Date(
        Number(action?.timestamp || 0) *
        1000
      ).toLocaleString();

    return `${date} · ${action?.stat_label || 'Stat'} ` +
      `${statGrowthFormatGain(action?.stat_increased)} · ` +
      `${Number(action?.energy_used || 0).toLocaleString()} energy · ` +
      `${Number(action?.trains || 0).toLocaleString()} trains · ` +
      `${statGrowthGymName(action?.gym)} · ` +
      `total after ${statGrowthFormatNumber(action?.stat_after, 2)}`;
  }

  function renderStatGrowthCumulativeChart(
    growth,
    focus = 'recent'
  ) {
    const stat =
      statGrowthFocusStat(
        growth,
        focus
      );

    const samples =
      statGrowthCumulativeSamples(
        growth,
        stat,
        12
      );

    const label =
      stat &&
      samples[0]?.stat_label
        ? samples[0].stat_label
        : 'Stat';

    if (
      !samples.length
    ) {
      return `
        <div class="ta-chart-card ta-stat-total-chart" data-ta-stat-total-card>
          <div class="ta-chart-heading">
            <span>Observed total &amp; session gain</span>
            <span>No selected-stat observations</span>
          </div>

          ${renderStatGrowthFocusControl(focus)}
        </div>
      `;
    }

    const width =
      620;

    const height =
      230;

    const left =
      54;

    const right =
      54;

    const top =
      20;

    const bottom =
      38;

    const plotWidth =
      width -
      left -
      right;

    const plotHeight =
      height -
      top -
      bottom;

    const totals =
      samples.map(
        action =>
          Number(
            action.stat_after ||
            0
          )
      );

    const gains =
      samples.map(
        action =>
          Number(
            action.stat_increased ||
            0
          )
      );

    const minimumTotal =
      Math.min(
        ...totals
      );

    const maximumTotal =
      Math.max(
        ...totals
      );

    const totalRange =
      Math.max(
        1,
        maximumTotal -
        minimumTotal
      );

    const maximumGain =
      Math.max(
        1,
        ...gains
      );

    const pointX =
      index =>
        samples.length === 1
          ? left +
            plotWidth / 2
          : left +
            index /
              (samples.length - 1) *
              plotWidth;

    const pointY =
      total =>
        top +
        (
          1 -
          (total -
            minimumTotal) /
            totalRange
        ) *
          plotHeight;

    const line =
      samples.map(
        (
          action,
          index
        ) =>
          `${index ? 'L' : 'M'}${pointX(index).toFixed(2)} ${pointY(Number(action.stat_after || 0)).toFixed(2)}`
      ).join(' ');

    const barWidth =
      Math.max(
        5,
        Math.min(
          20,
          plotWidth /
            samples.length *
            .56
        )
      );

    const bars =
      samples.map(
        (
          action,
          index
        ) => {
          const gain =
            Number(
              action.stat_increased ||
              0
            );

          const barHeight =
            Math.max(
              2,
              gain /
                maximumGain *
                plotHeight *
                .36
            );

          return `<rect x="${(pointX(index) - barWidth / 2).toFixed(2)}" y="${(top + plotHeight - barHeight).toFixed(2)}" width="${barWidth.toFixed(2)}" height="${barHeight.toFixed(2)}" rx="2" class="ta-stat-total-bar"></rect>`;
        }
      ).join('');

    const points =
      samples.map(
        (
          action,
          index
        ) => {
          const detail =
            statGrowthCumulativeSampleDetail(
              action
            );

          return `
            <circle
              cx="${pointX(index).toFixed(2)}"
              cy="${pointY(Number(action.stat_after || 0)).toFixed(2)}"
              r="8"
              class="ta-stat-total-hit"
              data-ta-stat-total-detail="${escapeActivityHtml(detail)}"
              role="button"
              tabindex="0"
              aria-label="${escapeActivityHtml(detail)}"
            ></circle>
            <circle
              cx="${pointX(index).toFixed(2)}"
              cy="${pointY(Number(action.stat_after || 0)).toFixed(2)}"
              r="3.7"
              class="ta-stat-total-point"
            ></circle>
          `;
        }
      ).join('');

    const firstDate =
      new Date(
        Number(samples[0].timestamp || 0) *
        1000
      ).toLocaleDateString(
        undefined,
        {
          month: 'short',
          day: 'numeric'
        }
      );

    const lastDate =
      new Date(
        Number(samples[samples.length - 1].timestamp || 0) *
        1000
      ).toLocaleDateString(
        undefined,
        {
          month: 'short',
          day: 'numeric'
        }
      );

    const firstDetail =
      statGrowthCumulativeSampleDetail(
        samples[
          samples.length - 1
        ]
      );

    return `
      <div class="ta-chart-card ta-stat-total-chart" data-ta-stat-total-card>
        <div class="ta-chart-heading">
          <span>Observed total &amp; session gain</span>
          <span>${escapeActivityHtml(label)} · last ${samples.length} observations</span>
        </div>

        ${renderStatGrowthFocusControl(focus)}

        <svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${escapeActivityHtml(label)} observed total line with session gain bars" class="ta-stat-total-svg">
          <line x1="${left}" y1="${top}" x2="${left}" y2="${top + plotHeight}" class="ta-stat-total-axis"></line>
          <line x1="${left}" y1="${top + plotHeight}" x2="${left + plotWidth}" y2="${top + plotHeight}" class="ta-stat-total-axis"></line>
          <line x1="${left}" y1="${top + plotHeight / 2}" x2="${left + plotWidth}" y2="${top + plotHeight / 2}" class="ta-stat-total-guide"></line>
          ${bars}
          <path d="${line}" class="ta-stat-total-line"></path>
          ${points}
          <text x="0" y="${top + 4}" class="ta-stat-total-label">${escapeActivityHtml(statGrowthFormatNumber(maximumTotal, 2))}</text>
          <text x="0" y="${top + plotHeight}" class="ta-stat-total-label">${escapeActivityHtml(statGrowthFormatNumber(minimumTotal, 2))}</text>
          <text x="${width}" y="${top + 4}" text-anchor="end" class="ta-stat-total-label">+${escapeActivityHtml(statGrowthFormatNumber(maximumGain, 2))}</text>
          <text x="${width}" y="${top + plotHeight}" text-anchor="end" class="ta-stat-total-label">0</text>
          <text x="${left}" y="${height - 8}" class="ta-stat-total-label">${escapeActivityHtml(firstDate)}</text>
          <text x="${left + plotWidth}" y="${height - 8}" text-anchor="end" class="ta-stat-total-label">${escapeActivityHtml(lastDate)}</text>
        </svg>

        <div class="ta-stat-total-legend">
          <span><i class="ta-stat-total-line-key"></i>Total stat</span>
          <span><i class="ta-stat-total-bar-key"></i>Session gain</span>
        </div>

        <div class="ta-chart-detail" data-ta-stat-total-detail-output>
          ${escapeActivityHtml(firstDetail)}
        </div>
      </div>
    `;
  }

  function renderStatGrowthRecentChart(
    growth
  ) {
    const layout =
      activityDashboardLayout();

    const rows =
      statGrowthRecentDays(
        growth,
        layout.recent_days
      );

    const maximum =
      Math.max(
        0,
        ...rows.map(
          row =>
            Number(
              row.gain ||
              0
            )
        )
      );

    const partial =
      activityDashboardPartialTodayContext({
        time_basis:
          growth?.time_basis,
        last_date:
          growth?.history_last_date ||
          growth?.last_date ||
          null,
        last_timestamp:
          growth?.history_last_timestamp ||
          growth?.last_timestamp ||
          null
      });

    const bars =
      rows
        .map(
          row => {
            const gain =
              Number(
                row.gain ||
                0
              );

            const height =
              activityDashboardPercent(
                gain,
                maximum
              );

            const isPartial =
              partial.is_partial_today &&
              row.date ===
                partial.today;

            const detail =
              statGrowthDayDetail(
                row,
                growth,
                layout.recent_days
              );

            return `
              <div
                class="ta-chart-column${isPartial ? ' ta-chart-column-partial' : ''}"
                role="button"
                tabindex="0"
                data-ta-stat-detail="${escapeActivityHtml(detail)}"
                aria-label="${escapeActivityHtml(detail)}"
                title="${escapeActivityHtml(detail)}"
              >
                <div class="ta-chart-value">
                  ${escapeActivityHtml(statGrowthFormatGain(gain))}
                </div>
                <div class="ta-chart-rail">
                  <div
                    class="ta-chart-bar"
                    style="height:${height}%"
                  ></div>
                </div>
                <div class="ta-chart-label">
                  ${escapeActivityHtml(activityDashboardShortDate(row.date))}
                  ${isPartial ? '<span class="ta-chart-partial-badge">partial</span>' : ''}
                </div>
              </div>
            `;
          }
        )
        .join('');

    const first =
      rows[0] ||
      null;

    const last =
      rows[
        rows.length - 1
      ] ||
      null;

    const dateWindow =
      first &&
      last
        ? `${activityDashboardMonthDay(first.date)}–${activityDashboardMonthDay(last.date)}`
        : '';

    return `
      <div class="ta-chart-card ta-stat-growth-chart">
        <div class="ta-chart-heading">
          <span>Recent stat growth</span>
          <span>Last ${layout.recent_days} calendar days · ${escapeActivityHtml(dateWindow)}</span>
        </div>

        <div class="ta-chart-scroll">
          <div
            class="ta-chart-columns ta-chart-columns-daily"
            style="grid-template-columns:repeat(${rows.length},minmax(0,1fr))"
          >
            ${bars}
          </div>
        </div>

        <div
          class="ta-chart-detail"
          data-ta-stat-detail-output
        >
          Tap a day for observed gain, energy, trains, and stat breakdown.
        </div>
      </div>
    `;
  }

  function renderStatGrowthStatCards(
    growth
  ) {
    const order = [
      'strength',
      'defense',
      'speed',
      'dexterity'
    ];

    const cards =
      order
        .map(
          stat => {
            const row =
              growth?.stats?.[stat] ||
              statGrowthBlankStat(
                stat,
                stat
              );

            const lastObserved =
              row.last_after === null
                ? '—'
                : statGrowthFormatNumber(
                    row.last_after,
                    2
                  );

            return `
              <div class="ta-stat-card">
                <div class="ta-stat-card-title">
                  ${escapeActivityHtml(row.label)}
                </div>

                <div class="ta-stat-card-gain">
                  ${escapeActivityHtml(statGrowthFormatGain(row.gain))}
                </div>

                <div class="ta-stat-card-grid">
                  <div>
                    <span>Energy</span>
                    <b>${Number(row.energy_used || 0).toLocaleString()}</b>
                  </div>
                  <div>
                    <span>Gain / E</span>
                    <b>${escapeActivityHtml(statGrowthFormatRate(row.gain_per_energy))}</b>
                  </div>
                  <div>
                    <span>Trains</span>
                    <b>${Number(row.trains || 0).toLocaleString()}</b>
                  </div>
                  <div>
                    <span>After last train</span>
                    <b>${escapeActivityHtml(lastObserved)}</b>
                  </div>
                </div>
              </div>
            `;
          }
        )
        .join('');

    return `
      <div class="ta-stat-grid">
        ${cards}
      </div>
    `;
  }

  function renderStatGrowthWindows(
    growth
  ) {
    const windows = [
      ['7 days', growth?.recent_7_days],
      ['14 days', growth?.recent_14_days],
      ['30 days', growth?.recent_30_days]
    ];

    return `
      <div class="ta-stat-window-grid">
        ${
          windows
            .map(
              ([
                label,
                row
              ]) => `
                <div class="ta-stat-window-card">
                  <div class="ta-stat-window-title">
                    ${escapeActivityHtml(label)}
                  </div>
                  <div class="ta-stat-window-gain">
                    ${escapeActivityHtml(statGrowthFormatGain(row?.gain || 0))}
                  </div>
                  <div class="ta-stat-window-note">
                    ${Number(row?.energy_used || 0).toLocaleString()} E ·
                    ${Number(row?.trains || 0).toLocaleString()} trains ·
                    ${escapeActivityHtml(statGrowthFormatRate(row?.gain_per_energy || 0))} gain/E
                  </div>
                </div>
              `
            )
            .join('')
        }
      </div>
    `;
  }

  function renderStatGrowthEnergyAllocation(
    growth
  ) {
    const totalEnergy =
      Number(
        growth?.energy_used ||
        0
      );

    if (
      totalEnergy <= 0
    ) {
      return '';
    }

    const rows =
      [
        'strength',
        'defense',
        'speed',
        'dexterity'
      ]
        .map(
          stat =>
            growth.stats[stat]
        );

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Energy allocation</span>
          <span>Share of observed gym energy</span>
        </div>

        <div class="ta-category-list">
          ${
            rows
              .map(
                row => {
                  const energy =
                    Number(
                      row.energy_used ||
                      0
                    );

                  const percent =
                    energy /
                    totalEnergy *
                    100;

                  return `
                    <div class="ta-category-row">
                      <div class="ta-category-topline">
                        <span>${escapeActivityHtml(row.label)}</span>
                        <span>${energy.toLocaleString()} E · ${percent.toFixed(1)}%</span>
                      </div>
                      <div class="ta-category-track">
                        <div
                          class="ta-category-fill"
                          style="width:${activityDashboardPercent(energy, totalEnergy, 2)}%"
                        ></div>
                      </div>
                    </div>
                  `;
                }
              )
              .join('')
          }
        </div>
      </div>
    `;
  }

  function renderStatGrowthGymBreakdown(
    growth
  ) {
    const gyms =
      Array.isArray(
        growth?.gyms
      )
        ? growth.gyms
        : [];

    if (
      !gyms.length
    ) {
      return '';
    }

    const rows =
      gyms
        .map(
          gym => {
            const name =
              statGrowthGymName(
                gym.gym_id
              );

            const energyPerTrain =
              Number(gym.trains || 0) > 0
                ? Number(gym.energy_used || 0) /
                  Number(gym.trains)
                : 0;

            const statParts =
              [
                'strength',
                'defense',
                'speed',
                'dexterity'
              ]
                .map(
                  stat => {
                    const row =
                      gym.stats?.[stat];

                    return row?.gain
                      ? `${row.label.slice(0, 3).toUpperCase()} ${statGrowthFormatGain(row.gain)}`
                      : null;
                  }
                )
                .filter(Boolean)
                .join(' · ');

            return `
              <div class="ta-stat-gym-row">
                <div class="ta-stat-gym-topline">
                  <span>${escapeActivityHtml(name)}</span>
                  <span>
                    ${Number(gym.energy_used || 0).toLocaleString()} E ·
                    ${Number(gym.trains || 0).toLocaleString()} trains
                  </span>
                </div>

                <div class="ta-stat-gym-values">
                  <span>
                    Observed gain ${escapeActivityHtml(statGrowthFormatGain(gym.gain))}
                  </span>
                  <span>
                    ${escapeActivityHtml(statGrowthFormatRate(gym.gain_per_energy))} gain/E ·
                    ${escapeActivityHtml(statGrowthFormatNumber(energyPerTrain, 2))} avg E/train
                  </span>
                </div>

                ${
                  statParts
                    ? `<div class="ta-stat-gym-note">${escapeActivityHtml(statParts)}</div>`
                    : ''
                }
              </div>
            `;
          }
        )
        .join('');

    return `
      <details class="ta-stat-subsection">
        <summary>
          Growth by gym
          <span>${gyms.length.toLocaleString()} gyms observed</span>
        </summary>
        <div class="ta-stat-subsection-body">
          ${rows}
        </div>
      </details>
    `;
  }

  function renderStatGrowthDataQuality(
    growth
  ) {
    const rejected =
      Number(
        growth?.rejected_logs ||
        0
      );

    const warnings =
      Object.values(
        growth?.warning_reasons ||
        {}
      ).reduce(
        (
          total,
          value
        ) =>
          total +
          Number(
            value ||
            0
          ),
        0
      );

    const status =
      rejected > 0
        ? `${rejected.toLocaleString()} recognized gym logs rejected by defensive validation`
        : 'All recognized gym training logs passed defensive validation';

    return `
      <details class="ta-stat-subsection ta-stat-quality${rejected ? ' ta-stat-quality-warning' : ''}">
        <summary>
          Data quality
          <span>${Number(growth?.valid_logs || 0).toLocaleString()} / ${Number(growth?.recognized_logs || 0).toLocaleString()} parsed</span>
        </summary>
        <div class="ta-stat-subsection-body">
          <div class="ta-stat-quality-line">
            ${escapeActivityHtml(status)}.
          </div>
          <div class="ta-stat-quality-line">
            Happiness-consumed data was valid for
            ${Number(growth?.happy_known_actions || 0).toLocaleString()} /
            ${Number(growth?.valid_logs || 0).toLocaleString()} parsed actions.
          </div>
          ${
            warnings
              ? `<div class="ta-stat-quality-line">${warnings.toLocaleString()} optional metadata warnings were retained without discarding otherwise valid observed gains.</div>`
              : ''
          }
        </div>
      </details>
    `;
  }

  function statGrowthScopedGainSummary(
    growth,
    focus = 'recent',
    scope = 'selected'
  ) {
    const normalizedFocus =
      [
        'recent',
        'most_trained',
        'strength',
        'defense',
        'speed',
        'dexterity'
      ].includes(
        focus
      )
        ? focus
        : 'recent';

    const normalizedScope =
      scope ===
      'all'
        ? 'all'
        : 'selected';

    const stat =
      statGrowthFocusStat(
        growth,
        normalizedFocus
      );

    const selected =
      stat
        ? growth?.stats?.[stat]
        : null;

    const row =
      normalizedScope ===
        'all' ||
      !selected
        ? growth
        : selected;

    return {
      focus:
        normalizedFocus,
      scope:
        normalizedScope,
      stat,
      label:
        normalizedScope ===
        'all'
          ? 'All stats'
          : selected?.label ||
            'Selected stat',
      gain:
        Number(
          row?.gain ||
          0
        ),
      actions:
        Number(
          row?.actions ??
          row?.valid_logs ??
          0
        )
    };
  }

  function renderStatGrowthScopedGainSummary(
    growth,
    focus = 'recent',
    scope = 'selected'
  ) {
    const summary =
      statGrowthScopedGainSummary(
        growth,
        focus,
        scope
      );

    return `
      <div class="ta-stat-gain-scope" data-ta-stat-gain-scope>
        <div class="ta-stat-gain-scope-controls" role="group" aria-label="Observed gain summary scope">
          ${
            [
              ['selected', 'Selected stat'],
              ['all', 'All stats']
            ].map(
              ([value, label]) => `
                <button
                  type="button"
                  class="${value === summary.scope ? 'ta-stat-gain-scope-active' : ''}"
                  data-ta-stat-gain-scope-option="${value}"
                  aria-pressed="${value === summary.scope ? 'true' : 'false'}"
                >${label}</button>
              `
            ).join('')
          }
        </div>

        <div class="ta-metric-card ta-stat-gain-primary">
          <div class="ta-metric-label">Observed stat gain</div>
          <div class="ta-metric-value">${escapeActivityHtml(statGrowthFormatGain(summary.gain))}</div>
          <div class="ta-metric-note">
            ${escapeActivityHtml(summary.label)} · ${summary.actions.toLocaleString()} training actions
          </div>
        </div>
      </div>
    `;
  }

  function renderStatGrowthDashboard(
    growth,
    options
  ) {
    const safeOptions =
      options &&
      typeof options === 'object'
        ? options
        : {};

    const sectionOpen =
      safeOptions.open === true;

    const focus =
      uiSessionTrainingFocus(
        safeOptions.focus
      );

    const scope =
      safeOptions.scope ===
      'all'
        ? 'all'
        : 'selected';

    if (
      !growth?.valid_logs
    ) {
      return `
        <details class="ta-section ta-stat-growth-section" ${sectionOpen ? 'open' : ''}>
          <summary class="ta-section-summary-row">
            <span class="ta-section-title">Stat Growth</span>
            <span class="ta-section-meta">No gym training data</span>
          </summary>
          <div class="ta-section-body">
            <div class="ta-section-intro">
              No valid Torn gym-training logs were found in the stored history.
            </div>
            ${
              growth?.rejected_logs
                ? renderStatGrowthDataQuality(growth)
                : ''
            }
          </div>
        </details>
      `;
    }

    const timeBasis =
      statGrowthTimeBasisLabel(
        growth
      );

    const bestDay =
      growth.best_day_by_gain;

    const metrics = [
      activityDashboardMetric(
        'Energy trained',
        Number(growth.energy_used).toLocaleString(),
        `${Number(growth.trains).toLocaleString()} individual trains · all stats`
      ),
      activityDashboardMetric(
        'Gain / energy',
        statGrowthFormatRate(
          growth.gain_per_energy
        ),
        'Observed across all gym logs · all stats'
      ),
      activityDashboardMetric(
        'Training days',
        Number(growth.training_days).toLocaleString(),
        `${growth.first_date || '—'} → ${growth.last_date || '—'}`
      ),
      activityDashboardMetric(
        'Best growth day',
        bestDay
          ? statGrowthFormatGain(
              bestDay.gain
            )
          : '—',
        bestDay?.date ||
          '—'
      ),
      activityDashboardMetric(
        'Happiness consumed',
        Number(growth.happy_used).toLocaleString(),
        `${Number(growth.happy_known_actions).toLocaleString()} / ${Number(growth.valid_logs).toLocaleString()} actions with valid data`
      )
    ].join('');

    return `
      <details class="ta-section ta-stat-growth-section" ${sectionOpen ? 'open' : ''}>
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">Stat Growth</span>
          <span class="ta-section-meta">
            ${escapeActivityHtml(statGrowthFormatGain(growth.gain))} · ${Number(growth.energy_used).toLocaleString()} E
          </span>
        </summary>

        <div class="ta-section-body">
          <div class="ta-section-intro">
            Observed gym-training history from Torn logs. Daily grouping follows
            ${escapeActivityHtml(timeBasis)} selected in Settings. All-time gain and energy totals do not change with the time basis.
          </div>

          ${renderStatGrowthCumulativeChart(growth, focus)}

          ${renderStatGrowthScopedGainSummary(growth, focus, scope)}

          <details class="ta-stat-subsection ta-stat-more-details">
            <summary>
              More growth details
              <span>Metrics, breakdowns &amp; diagnostics</span>
            </summary>
            <div class="ta-stat-subsection-body">
              <div class="ta-metric-grid">
                ${metrics}
              </div>

              ${renderStatGrowthStatCards(growth)}

              ${renderStatGrowthWindows(growth)}

              ${renderStatGrowthRecentChart(growth)}

              ${renderStatGrowthEnergyAllocation(growth)}

              ${renderStatGrowthGymBreakdown(growth)}

              ${renderStatGrowthDataQuality(growth)}
            </div>
          </details>
        </div>
      </details>
    `;
  }

  function bindStatGrowthDashboardInteractions(
    root,
    growth = null
  ) {
    if (
      !root?.querySelectorAll
    ) {
      return;
    }

    const uiState =
      readUiSessionState();

    root.__taStatGrowth =
      growth ||
      root.__taStatGrowth ||
      null;

    root.__taStatGrowthFocus =
      uiSessionTrainingFocus(
        uiState.stat_growth_focus
      );

    root.__taStatGrowthScope =
      uiState.stat_growth_scope ===
      'all'
        ? 'all'
        : 'selected';

    const columns =
      Array.from(
        root.querySelectorAll(
          '.ta-chart-column[data-ta-stat-detail]'
        )
      );

    const activate =
      column => {
        const card =
          column?.closest?.(
            '.ta-chart-card'
          );

        if (
          !card
        ) {
          return;
        }

        const output =
          card.querySelector(
            '[data-ta-stat-detail-output]'
          );

        if (
          output
        ) {
          output.textContent =
            column.getAttribute(
              'data-ta-stat-detail'
            ) ||
            '';
        }

        for (
          const candidate
          of card.querySelectorAll(
            '.ta-chart-column[data-ta-stat-detail]'
          )
        ) {
          candidate.classList.toggle(
            'ta-chart-column-active',
            candidate === column
          );
        }
      };

    for (
      const column
      of columns
    ) {
      column.addEventListener(
        'click',
        () =>
          activate(
            column
          )
      );

      column.addEventListener(
        'keydown',
        event => {
          if (
            event.key !== 'Enter' &&
            event.key !== ' '
          ) {
            return;
          }

          event.preventDefault();
          activate(
            column
          );
        }
      );
    }

    const bindCumulativeInteractions =
      scope => {
        const card =
          scope?.matches?.(
            '[data-ta-stat-total-card]'
          )
            ? scope
            : scope?.querySelector?.(
              '[data-ta-stat-total-card]'
            );

        if (
          !card
        ) {
          return;
        }

        const activatePoint =
          point => {
            const output =
              card.querySelector(
                '[data-ta-stat-total-detail-output]'
              );

            if (
              output
            ) {
              output.textContent =
                point.getAttribute(
                  'data-ta-stat-total-detail'
                ) ||
                '';
            }
          };

        for (
          const point
          of card.querySelectorAll(
            '[data-ta-stat-total-detail]'
          )
        ) {
          point.addEventListener(
            'click',
            () =>
              activatePoint(
                point
              )
          );

          point.addEventListener(
            'keydown',
            event => {
              if (
                event.key !== 'Enter' &&
                event.key !== ' '
              ) {
                return;
              }

              event.preventDefault();
              activatePoint(
                point
              );
            }
          );
        }

        const select =
          card.querySelector(
            '[data-ta-stat-total-focus]'
          );

        select?.addEventListener(
          'change',
          () => {
            root.__taStatGrowthFocus =
              uiSessionTrainingFocus(
                select.value
              );

            writeUiSessionState({
              stat_growth_focus:
                root.__taStatGrowthFocus
            });

            card.outerHTML =
              renderStatGrowthCumulativeChart(
                root.__taStatGrowth ||
                {},
                root.__taStatGrowthFocus
              );

            refreshScopedGainSummary();

            bindCumulativeInteractions(
              root
            );
          }
        );
      };

    const refreshScopedGainSummary =
      () => {
        const current =
          root.querySelector(
            '[data-ta-stat-gain-scope]'
          );

        if (
          !current
        ) {
          return;
        }

        current.outerHTML =
          renderStatGrowthScopedGainSummary(
            root.__taStatGrowth ||
            {},
            root.__taStatGrowthFocus,
            root.__taStatGrowthScope
          );

        bindScopedGainInteractions();
      };

    const bindScopedGainInteractions =
      () => {
        const panel =
          root.querySelector(
            '[data-ta-stat-gain-scope]'
          );

        if (
          !panel
        ) {
          return;
        }

        for (
          const button
          of panel.querySelectorAll(
            '[data-ta-stat-gain-scope-option]'
          )
        ) {
          button.addEventListener(
            'click',
            () => {
              root.__taStatGrowthScope =
                button.getAttribute(
                  'data-ta-stat-gain-scope-option'
                ) ===
                'all'
                  ? 'all'
                  : 'selected';

              writeUiSessionState({
                stat_growth_scope:
                  root.__taStatGrowthScope
              });

              refreshScopedGainSummary();
            }
          );
        }
      };

    bindCumulativeInteractions(
      root
    );

    bindScopedGainInteractions();
  }

  function renderTrainingWorkspace(
    readiness,
    growth
  ) {
    if (
      !readiness &&
      !growth
    ) {
      return '';
    }

    const state =
      readUiSessionState();

    const defaultOpen =
      readiness?.page_is_gym ===
      true;

    const workspaceOpen =
      state.training_workspace_open ===
      null
        ? defaultOpen
        : state.training_workspace_open;

    const readinessOpen =
      state.training_readiness_open ===
      null
        ? defaultOpen
        : state.training_readiness_open;

    const statGrowthOpen =
      state.stat_growth_open ===
      true;

    const focus =
      uiSessionTrainingFocus(
        state.stat_growth_focus
      );

    const scope =
      state.stat_growth_scope ===
      'all'
        ? 'all'
        : 'selected';

    const meta = [
      readiness?.energy === null ||
      readiness?.energy === undefined
        ? 'Historical readiness'
        : `${Number(readiness.energy).toLocaleString()} E`,
      growth?.valid_logs
        ? `${Number(growth.valid_logs).toLocaleString()} actions`
        : null
    ].filter(Boolean).join(' · ');

    return `
      <details class="ta-section ta-training-workspace-section" ${workspaceOpen ? 'open' : ''}>
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">Training</span>
          <span class="ta-section-meta">${escapeActivityHtml(meta)}</span>
        </summary>

        <div class="ta-section-body ta-training-workspace-body">
          ${renderTrainingReadinessDashboard(readiness, { open: readinessOpen })}
          ${renderStatGrowthDashboard(growth, {
            open: statGrowthOpen,
            focus,
            scope
          })}
        </div>
      </details>
    `;
  }

  function bindTrainingWorkspaceInteractions(
    root
  ) {
    const bindings = [
      [
        '.ta-training-workspace-section',
        'training_workspace_open'
      ],
      [
        '.ta-training-readiness-section',
        'training_readiness_open'
      ],
      [
        '.ta-stat-growth-section',
        'stat_growth_open'
      ]
    ];

    for (
      const [selector, key]
      of bindings
    ) {
      const section =
        root?.querySelector?.(
          selector
        );

      section?.addEventListener(
        'toggle',
        () => {
          writeUiSessionState({
            [key]:
              section.open ===
              true
          });
        }
      );
    }
  }

  function renderStoredAnalysisDashboards(
    analysis
  ) {
    return (
      renderResourceDashboard(
        analysis?.resource_flow,
        analysis?.resource_bars
      ) +
      renderTrainingWorkspace(
        analysis?.training_readiness,
        analysis?.stat_growth
      ) +
      renderOverallActivityDashboard(
        analysis?.activity
      )
    );
  }

  function bindStoredAnalysisDashboardInteractions(
    root,
    analysis = null
  ) {
    bindResourceDashboardInteractions(
      root
    );

    bindTrainingWorkspaceInteractions(
      root
    );

    bindTrainingReadinessInteractions(
      root
    );

    bindActivityDashboardInteractions(
      root
    );

    bindStatGrowthDashboardInteractions(
      root,
      analysis?.stat_growth
    );
  }
  // ============================================================
  // ENERGY / NERVE / HAPPINESS RESOURCE-FLOW FOUNDATION
  // ============================================================

  function resourceFlowFiniteNumber(
    value
  ) {
    if (
      typeof value === 'number'
    ) {
      return Number.isFinite(
        value
      )
        ? value
        : null;
    }

    if (
      typeof value !== 'string'
    ) {
      return null;
    }

    const normalized =
      value.trim();

    if (
      !normalized ||
      !/^[+-]?\d+$/.test(
        normalized
      )
    ) {
      return null;
    }

    const number =
      Number(
        normalized
      );

    return Number.isFinite(
      number
    )
      ? number
      : null;
  }

  function resourceFlowPositiveAmount(
    value
  ) {
    const number =
      resourceFlowFiniteNumber(
        value
      );

    return Number.isSafeInteger(
      number
    ) &&
    number > 0
      ? number
      : null;
  }

  function resourceFlowNonNegativeAmount(
    value
  ) {
    const number =
      resourceFlowFiniteNumber(
        value
      );

    return Number.isSafeInteger(
      number
    ) &&
    number >= 0
      ? number
      : null;
  }

  function resourceFlowObservedSpecs(
    logId
  ) {
    const id =
      Number(
        logId
      );

    switch (
      id
    ) {
      case 4900:
        return [{
          field: 'energy_increased',
          resource: 'energy',
          flow: 'in',
          kind: 'gain',
          category: 'point_refill',
          detail: 'points'
        }];

      case 4905:
        return [{
          field: 'nerve_increased',
          resource: 'nerve',
          flow: 'in',
          kind: 'gain',
          category: 'point_refill',
          detail: 'points'
        }];

      case 7850:
        return [{
          field: 'energy_received',
          resource: 'energy',
          flow: 'in',
          kind: 'gain',
          category: 'mission_reward',
          detail: 'mission'
        }];

      // Torn currently names this payload field energy_received even though
      // log type 7851 explicitly describes a Nerve reward.
      case 7851:
        return [{
          field: 'energy_received',
          resource: 'nerve',
          flow: 'in',
          kind: 'gain',
          category: 'mission_reward',
          detail: 'mission'
        }];

      case 2030:
        return [{
          field: 'nerve_increased',
          resource: 'nerve',
          flow: 'in',
          kind: 'gain',
          category: 'consumable',
          detail: 'alcohol'
        }];

      case 2200:
        return [{
          field: 'nerve_increased',
          resource: 'nerve',
          flow: 'in',
          kind: 'gain',
          category: 'drug',
          detail: 'cannabis'
        }];

      case 2020:
        return [{
          field: 'happy_increased',
          resource: 'happiness',
          flow: 'in',
          kind: 'gain',
          category: 'consumable',
          detail: 'candy'
        }];

      case 2180:
        return [{
          field: 'happy_increased',
          resource: 'happiness',
          flow: 'in',
          kind: 'gain',
          category: 'consumable',
          detail: 'erotic_dvd'
        }];

      case 2210:
        return [{
          field: 'happy_increased',
          resource: 'happiness',
          flow: 'in',
          kind: 'gain',
          category: 'drug',
          detail: 'ecstasy'
        }];

      case 2280:
        return [{
          field: 'happy_increased',
          resource: 'happiness',
          flow: 'in',
          kind: 'gain',
          category: 'drug',
          detail: 'vicodin'
        }];

      case 6005:
        return [{
          field: 'happy_increased',
          resource: 'happiness',
          flow: 'in',
          kind: 'gain',
          category: 'rehab',
          detail: null,
          allow_zero: true
        }];

      case 2291:
        return [
          {
            field: 'energy_decreased',
            resource: 'energy',
            flow: 'out',
            kind: 'loss',
            category: 'overdose',
            detail: 'xanax',
            allow_zero: true
          },
          {
            field: 'nerve_decreased',
            resource: 'nerve',
            flow: 'out',
            kind: 'loss',
            category: 'overdose',
            detail: 'xanax',
            allow_zero: true
          },
          {
            field: 'happy_decreased',
            resource: 'happiness',
            flow: 'out',
            kind: 'loss',
            category: 'overdose',
            detail: 'xanax',
            allow_zero: true
          }
        ];

      case 1404:
        return [{
          field: 'energy_used',
          resource: 'energy',
          flow: 'out',
          kind: 'use',
          category: 'dump_search',
          detail: null
        }];

      case 5300:
      case 5301:
      case 5302:
      case 5303:
        return [
          {
            field: 'energy_used',
            resource: 'energy',
            flow: 'out',
            kind: 'use',
            category: 'gym_training',
            detail: null
          },
          {
            field: 'happy_used',
            resource: 'happiness',
            flow: 'out',
            kind: 'use',
            category: 'gym_training',
            detail: null,
            allow_zero: true
          }
        ];

      case 5362:
        return [{
          field: 'nerve_used',
          resource: 'nerve',
          flow: 'out',
          kind: 'use',
          category: 'bust',
          detail: null
        }];

      case 8100:
      case 8105:
      case 8110:
      case 8115:
      case 8140:
      case 8145:
      case 8150:
      case 8155:
        return [{
          field: 'energy_used',
          resource: 'energy',
          flow: 'out',
          kind: 'use',
          category: 'attack',
          detail: null
        }];

      case 9010:
      case 9015:
      case 9020:
      case 9027:
      case 9050:
      case 9052:
      case 9055:
      case 9056:
      case 9060:
      case 9150:
      case 9154:
      case 9155:
      case 9158:
      case 9160:
      case 9163:
        return [{
          field: 'nerve',
          resource: 'nerve',
          flow: 'out',
          kind: 'use',
          category: 'crime',
          detail: null
        }];

      default:
        return [];
    }
  }

  function resourceFlowDerivedSpec(
    logId
  ) {
    switch (
      Number(
        logId
      )
    ) {
      case 2290:
        return {
          resource: 'energy',
          flow: 'in',
          kind: 'gain',
          category: 'drug',
          detail: 'xanax',
          amount: 250,
          expected_item_id: 206,
          rule: 'successful_xanax_standard_energy'
        };

      case 6020:
        return {
          resource: 'energy',
          flow: 'out',
          kind: 'use',
          category: 'hunting',
          detail: null,
          amount: 10,
          expected_item_id: null,
          rule: 'standard_hunting_energy_cost'
        };

      default:
        return null;
    }
  }

  function resourceFlowCandidateFields(
    data,
    logId = null
  ) {
    if (
      !data ||
      typeof data !== 'object' ||
      Array.isArray(
        data
      )
    ) {
      return [];
    }

    const knownNonFlowFields =
      new Set([
        'maximum_energy_before',
        'maximum_energy_after',
        'maximum_nerve_before',
        'maximum_nerve_after',
        'maximum_happy_before',
        'maximum_happy_after'
      ]);

    switch (
      Number(
        logId
      )
    ) {
      case 5900:
      case 5905:
      case 5910:
      case 5927:
      case 5928:
      case 5933:
      case 5936:
      case 5938:
        knownNonFlowFields.add(
          'happy'
        );
        break;

      default:
        break;
    }

    return Object.keys(
      data
    ).filter(
      field =>
        /(^|_)(energy|nerve|happy|happiness)(_|$)/i.test(
          field
        ) &&
        !knownNonFlowFields.has(
          field
        )
    ).sort();
  }

  function inspectHappinessMaximumLog(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );

    if (
      logId !== 8844
    ) {
      return {
        recognized: false,
        valid: true,
        reason: null,
        event: null
      };
    }

    const timestamp =
      Number(
        log?.timestamp
      );

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_timestamp',
        event: null
      };
    }

    const before =
      resourceFlowPositiveAmount(
        log?.data?.maximum_happy_before
      );

    const after =
      resourceFlowPositiveAmount(
        log?.data?.maximum_happy_after
      );

    if (
      before === null ||
      after === null ||
      after < before
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_happiness_maximum_change',
        event: null
      };
    }

    return {
      recognized: true,
      valid: true,
      reason: null,
      event: {
        id:
          String(
            log?.id ??
            ''
          ),
        log_id: logId,
        timestamp,
        before,
        after,
        basis: 'observed_exact'
      }
    };
  }

  function buildHappinessMaximumHistory(
    logs
  ) {
    const events =
      [];

    const rejectionReasons =
      {};

    let recognizedLogs = 0;
    let validLogs = 0;
    let rejectedLogs = 0;

    for (
      const log
      of logs || []
    ) {
      const inspected =
        inspectHappinessMaximumLog(
          log
        );

      if (
        !inspected.recognized
      ) {
        continue;
      }

      recognizedLogs++;

      if (
        !inspected.valid
      ) {
        rejectedLogs++;

        rejectionReasons[
          inspected.reason
        ] =
          (
            rejectionReasons[
              inspected.reason
            ] ||
            0
          ) +
          1;

        continue;
      }

      validLogs++;
      events.push(
        inspected.event
      );
    }

    events.sort(
      (
        left,
        right
      ) =>
        left.timestamp -
          right.timestamp ||
        left.id.localeCompare(
          right.id
        )
    );

    let continuityBreaks = 0;

    for (
      let index = 1;
      index < events.length;
      index++
    ) {
      if (
        events[index - 1].after !==
        events[index].before
      ) {
        continuityBreaks++;
      }
    }

    return {
      events,
      first_known_maximum:
        events.length
          ? events[0].before
          : null,
      latest_known_maximum:
        events.length
          ? events[events.length - 1].after
          : null,
      quality: {
        recognized_logs:
          recognizedLogs,
        valid_logs:
          validLogs,
        rejected_logs:
          rejectedLogs,
        continuity_breaks:
          continuityBreaks,
        rejection_reasons:
          rejectionReasons
      }
    };
  }

  function happinessMaximumAt(
    history,
    timestamp
  ) {
    const target =
      Number(
        timestamp
      );

    const events =
      history?.events;

    if (
      !Number.isSafeInteger(
        target
      ) ||
      target <= 0 ||
      !Array.isArray(
        events
      ) ||
      !events.length ||
      Number(
        history?.quality?.continuity_breaks ||
        0
      ) > 0
    ) {
      return null;
    }

    let maximum =
      events[0].before;

    for (
      const event
      of events
    ) {
      if (
        event.timestamp > target
      ) {
        break;
      }

      maximum =
        event.after;
    }

    return maximum;
  }

  function resourceFlowEvent(
    log,
    spec,
    amount,
    basis
  ) {
    const itemId =
      resourceFlowPositiveAmount(
        log?.data?.item
      );

    return {
      id:
        String(
          log?.id ??
          ''
        ),
      log_id:
        Number(
          log?.log
        ),
      title:
        String(
          log?.title ??
          ''
        ),
      timestamp:
        Number(
          log?.timestamp
        ),
      resource:
        spec.resource,
      flow:
        spec.flow,
      kind:
        spec.kind,
      category:
        spec.category,
      detail:
        spec.detail ??
        null,
      amount,
      basis,
      rule:
        spec.rule ??
        null,
      item_id:
        itemId
    };
  }

  function inspectResourceFlowLog(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );

    const observedSpecs =
      resourceFlowObservedSpecs(
        logId
      );

    const derivedSpec =
      resourceFlowDerivedSpec(
        logId
      );

    const data =
      log?.data;

    if (
      !observedSpecs.length &&
      !derivedSpec
    ) {
      const candidateFields =
        resourceFlowCandidateFields(
          data,
          logId
        );

      return {
        recognized: false,
        resource_candidate:
          candidateFields.length > 0,
        valid:
          candidateFields.length === 0,
        reason:
          candidateFields.length
            ? 'unsupported_resource_schema'
            : null,
        candidate_fields:
          candidateFields,
        events: []
      };
    }

    const timestamp =
      Number(
        log?.timestamp
      );

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0
    ) {
      return {
        recognized: true,
        resource_candidate: true,
        valid: false,
        reason: 'invalid_timestamp',
        candidate_fields: [],
        events: []
      };
    }

    if (
      !data ||
      typeof data !== 'object' ||
      Array.isArray(
        data
      )
    ) {
      return {
        recognized: true,
        resource_candidate: true,
        valid: false,
        reason: 'invalid_data',
        candidate_fields: [],
        events: []
      };
    }

    const candidateFields =
      resourceFlowCandidateFields(
        data,
        logId
      );

    const expectedFields =
      new Set(
        observedSpecs.map(
          spec =>
            spec.field
        )
      );

    const unexpectedFields =
      candidateFields.filter(
        field =>
          !expectedFields.has(
            field
          )
      );

    if (
      unexpectedFields.length
    ) {
      return {
        recognized: true,
        resource_candidate: true,
        valid: false,
        reason: 'unexpected_resource_fields',
        candidate_fields:
          unexpectedFields,
        events: []
      };
    }

    const events =
      [];

    for (
      const spec
      of observedSpecs
    ) {
      const amount =
        spec.allow_zero
          ? resourceFlowNonNegativeAmount(
              data[spec.field]
            )
          : resourceFlowPositiveAmount(
              data[spec.field]
            );

      if (
        amount === null
      ) {
        return {
          recognized: true,
          resource_candidate: true,
          valid: false,
          reason: 'invalid_resource_amount',
          candidate_fields: [
            spec.field
          ],
          events: []
        };
      }

      if (
        amount > 0
      ) {
        events.push(
          resourceFlowEvent(
            log,
            spec,
            amount,
            'observed_exact'
          )
        );
      }
    }

    if (
      derivedSpec
    ) {
      if (
        derivedSpec.expected_item_id !== null &&
        resourceFlowPositiveAmount(
          data.item
        ) !==
          derivedSpec.expected_item_id
      ) {
        return {
          recognized: true,
          resource_candidate: true,
          valid: false,
          reason: 'invalid_derived_rule_binding',
          candidate_fields: [],
          events: []
        };
      }

      events.push(
        resourceFlowEvent(
          log,
          derivedSpec,
          derivedSpec.amount,
          'derived_rule'
        )
      );
    }

    return {
      recognized: true,
      resource_candidate: true,
      valid: true,
      reason: null,
      candidate_fields:
        candidateFields,
      events
    };
  }

  function resourceFlowBlankResource(
    resource
  ) {
    return {
      resource,
      in_total: 0,
      out_total: 0,
      gain_total: 0,
      use_total: 0,
      loss_total: 0,
      observed_in: 0,
      observed_out: 0,
      derived_in: 0,
      derived_out: 0,
      event_count: 0,
      categories: {}
    };
  }

  function resourceFlowAddEvent(
    target,
    event
  ) {
    target.event_count++;

    if (
      event.flow === 'in'
    ) {
      target.in_total +=
        event.amount;

      if (
        event.basis === 'observed_exact'
      ) {
        target.observed_in +=
          event.amount;
      } else {
        target.derived_in +=
          event.amount;
      }
    } else {
      target.out_total +=
        event.amount;

      if (
        event.basis === 'observed_exact'
      ) {
        target.observed_out +=
          event.amount;
      } else {
        target.derived_out +=
          event.amount;
      }
    }

    if (
      event.kind === 'gain'
    ) {
      target.gain_total +=
        event.amount;
    } else if (
      event.kind === 'use'
    ) {
      target.use_total +=
        event.amount;
    } else if (
      event.kind === 'loss'
    ) {
      target.loss_total +=
        event.amount;
    }

    const category =
      target.categories[
        event.category
      ] || {
        amount: 0,
        events: 0
      };

    category.amount +=
      event.amount;
    category.events++;

    target.categories[
      event.category
    ] =
      category;
  }

  function buildResourceFlow(
    logs
  ) {
    const events =
      [];

    const energy =
      resourceFlowBlankResource(
        'energy'
      );

    const nerve =
      resourceFlowBlankResource(
        'nerve'
      );

    const happiness =
      resourceFlowBlankResource(
        'happiness'
      );

    const happinessMaximum =
      buildHappinessMaximumHistory(
        logs
      );

    const unsupportedLogIds =
      new Set();

    const rejectionReasons =
      {};

    let recognizedLogs = 0;
    let validLogs = 0;
    let rejectedLogs = 0;
    let unsupportedCandidateLogs = 0;
    let ignoredLogs = 0;
    let observedExactEvents = 0;
    let derivedRuleEvents = 0;

    for (
      const log
      of logs || []
    ) {
      const inspected =
        inspectResourceFlowLog(
          log
        );

      if (
        !inspected.recognized
      ) {
        if (
          inspected.resource_candidate
        ) {
          unsupportedCandidateLogs++;

          const logId =
            Number(
              log?.log ??
              log?.details?.id
            );

          if (
            Number.isSafeInteger(
              logId
            )
          ) {
            unsupportedLogIds.add(
              logId
            );
          }
        } else {
          ignoredLogs++;
        }

        continue;
      }

      recognizedLogs++;

      if (
        !inspected.valid
      ) {
        rejectedLogs++;

        rejectionReasons[
          inspected.reason
        ] =
          (
            rejectionReasons[
              inspected.reason
            ] ||
            0
          ) +
          1;

        continue;
      }

      validLogs++;

      for (
        const event
        of inspected.events
      ) {
        events.push(
          event
        );

        if (
          event.basis === 'observed_exact'
        ) {
          observedExactEvents++;
        } else {
          derivedRuleEvents++;
        }

        resourceFlowAddEvent(
          event.resource === 'energy'
            ? energy
            : event.resource === 'nerve'
              ? nerve
              : happiness,
          event
        );
      }
    }

    events.sort(
      (
        left,
        right
      ) =>
        left.timestamp -
          right.timestamp ||
        left.id.localeCompare(
          right.id
        ) ||
        left.resource.localeCompare(
          right.resource
        )
    );

    return {
      events,
      energy,
      nerve,
      happiness,
      happiness_maximum:
        happinessMaximum,
      quality: {
        input_logs:
          Array.isArray(logs)
            ? logs.length
            : 0,
        recognized_logs:
          recognizedLogs,
        valid_logs:
          validLogs,
        rejected_logs:
          rejectedLogs,
        ignored_logs:
          ignoredLogs,
        observed_exact_events:
          observedExactEvents,
        derived_rule_events:
          derivedRuleEvents,
        unsupported_candidate_logs:
          unsupportedCandidateLogs,
        unsupported_log_ids:
          [...unsupportedLogIds].sort(
            (
              left,
              right
            ) =>
              left -
              right
          ),
        rejection_reasons:
          rejectionReasons
      },
      limitations: {
        natural_regeneration:
          'not_observable_from_log_history',
        current_bar_state:
          'not_reconstructable_from_flows_alone'
      }
    };
  }
  // ============================================================
  // BEGINNER-FIRST ENERGY / NERVE / HAPPINESS DASHBOARD
  // ============================================================

  function escapeResourceDashboardHtml(
    value
  ) {
    return String(
      value ??
      ''
    )
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  function resourceDashboardNonNegativeInteger(
    value
  ) {
    return Number.isSafeInteger(
      value
    ) &&
    value >= 0
      ? value
      : null;
  }

  function normalizeResourceDashboardBar(
    bar,
    resource
  ) {
    if (
      !bar ||
      typeof bar !== 'object' ||
      Array.isArray(bar)
    ) {
      throw new Error(
        `Torn API returned an invalid ${resource} bar.`
      );
    }

    const normalized =
      {};

    for (
      const field
      of [
        'current',
        'maximum',
        'increment',
        'interval',
        'tick_time',
        'full_time'
      ]
    ) {
      const value =
        resourceDashboardNonNegativeInteger(
          bar[field]
        );

      if (
        value === null
      ) {
        throw new Error(
          `Torn API returned an invalid ${resource} ${field} value.`
        );
      }

      normalized[field] =
        value;
    }

    if (
      normalized.maximum < 1
    ) {
      throw new Error(
        `Torn API returned an inconsistent ${resource} bar.`
      );
    }

    return normalized;
  }

  function normalizeResourceBarsResponse(
    json,
    fetchedAt = Date.now()
  ) {
    const bars =
      json?.bars;

    if (
      !bars ||
      typeof bars !== 'object' ||
      Array.isArray(bars)
    ) {
      throw new Error(
        'Torn API returned an invalid bars response.'
      );
    }

    const timestamp =
      Number(
        fetchedAt
      );

    if (
      !Number.isFinite(timestamp) ||
      timestamp <= 0
    ) {
      throw new Error(
        'Live resource refresh time is invalid.'
      );
    }

    return {
      status: 'available',
      source: 'torn_api_v2_user_bars',
      fetched_at: timestamp,
      energy:
        normalizeResourceDashboardBar(
          bars.energy,
          'Energy'
        ),
      nerve:
        normalizeResourceDashboardBar(
          bars.nerve,
          'Nerve'
        ),
      happiness:
        normalizeResourceDashboardBar(
          bars.happy,
          'Happiness'
        )
    };
  }

  async function fetchResourceBarsSnapshot(
    apiKey,
    tracker
  ) {
    const json =
      await apiFetchJson(
        `${API_BASE}/user/bars`,
        apiKey,
        tracker
      );

    return normalizeResourceBarsResponse(
      json,
      Date.now()
    );
  }

  async function loadResourceBarsSnapshot(
    apiKey,
    tracker
  ) {
    const normalizedKey =
      String(
        apiKey ||
        ''
      ).trim();

    if (
      !normalizedKey
    ) {
      return {
        status: 'unavailable',
        reason: 'api_key_unavailable',
        fetched_at: null
      };
    }

    tracker?.setStage(
      'Refreshing Energy, Nerve, and Happiness…',
      'One live Torn API request'
    );

    try {
      return await fetchResourceBarsSnapshot(
        normalizedKey,
        tracker
      );
    } catch (
      error
    ) {
      console.warn(
        'Live resource refresh failed.',
        error
      );

      return {
        status: 'unavailable',
        reason: 'api_request_failed',
        message:
          String(
            error?.message ||
            'Live Torn API data is unavailable.'
          ),
        fetched_at: null
      };
    }
  }

  function resourceDashboardFormatNumber(
    value
  ) {
    const number =
      Number(
        value
      );

    return Number.isFinite(
      number
    )
      ? number.toLocaleString()
      : '—';
  }

  function resourceDashboardFormatPercentage(
    amount,
    total
  ) {
    const normalizedAmount =
      Number(
        amount
      );

    const normalizedTotal =
      Number(
        total
      );

    if (
      !Number.isFinite(normalizedAmount) ||
      !Number.isFinite(normalizedTotal) ||
      normalizedAmount < 0 ||
      normalizedTotal <= 0
    ) {
      return '0%';
    }

    const percentage =
      Math.max(
        0,
        Math.min(
          100,
          (
            normalizedAmount /
            normalizedTotal
          ) *
            100
        )
      );

    return (
      Number(
        percentage.toFixed(
          1
        )
      ).toLocaleString() +
      '%'
    );
  }

  function resourceDashboardFormatDuration(
    seconds
  ) {
    const remaining =
      Math.max(
        0,
        Math.ceil(
          Number(seconds) ||
          0
        )
      );

    if (
      remaining === 0
    ) {
      return 'Full now';
    }

    const hours =
      Math.floor(
        remaining /
        3600
      );

    const minutes =
      Math.floor(
        (
          remaining %
          3600
        ) /
        60
      );

    const secondsPart =
      remaining %
      60;

    if (
      hours > 0
    ) {
      return `${hours}h ${minutes}m`;
    }

    if (
      minutes > 0
    ) {
      return `${minutes}m ${secondsPart}s`;
    }

    return `${secondsPart}s`;
  }

  function resourceDashboardFullClockTime(
    fullAt
  ) {
    const date =
      new Date(
        Number(fullAt)
      );

    if (
      !Number.isFinite(
        date.getTime()
      )
    ) {
      return '';
    }

    return date.toLocaleTimeString(
      undefined,
      {
        hour: 'numeric',
        minute: '2-digit'
      }
    );
  }

  function resourceDashboardEtaText(
    fullAt,
    now = Date.now()
  ) {
    const remainingSeconds =
      Math.max(
        0,
        Math.ceil(
          (
            Number(fullAt) -
            Number(now)
          ) /
          1000
        )
      );

    if (
      remainingSeconds === 0
    ) {
      return 'Full now';
    }

    return (
      `Full in ${resourceDashboardFormatDuration(remainingSeconds)}` +
      ` · ${resourceDashboardFullClockTime(fullAt)}`
    );
  }

  function resourceDashboardLiveStatusText(
    current,
    maximum,
    fullAt,
    now = Date.now()
  ) {
    const normalizedCurrent =
      Number(
        current
      );

    const normalizedMaximum =
      Number(
        maximum
      );

    const overMaximum =
      normalizedCurrent -
      normalizedMaximum;

    if (
      Number.isFinite(overMaximum) &&
      overMaximum > 0
    ) {
      return (
        'Over maximum by ' +
        resourceDashboardFormatNumber(
          overMaximum
        )
      );
    }

    if (
      Number.isFinite(normalizedCurrent) &&
      Number.isFinite(normalizedMaximum) &&
      normalizedCurrent >= normalizedMaximum
    ) {
      return 'Full now';
    }

    const etaText =
      resourceDashboardEtaText(
        fullAt,
        now
      );

    if (
      etaText === 'Full now' &&
      Number.isFinite(normalizedCurrent) &&
      Number.isFinite(normalizedMaximum) &&
      normalizedCurrent < normalizedMaximum
    ) {
      return 'Expected full now · refresh to confirm';
    }

    return etaText;
  }

  function resourceDashboardSourceLabel(
    event
  ) {
    const labels = {
      point_refill: 'Point refill',
      mission_reward: 'Mission reward',
      consumable: 'Consumable',
      drug: 'Drug',
      rehab: 'Rehab',
      overdose: 'Overdose',
      dump_search: 'Dump searching',
      gym_training: 'Gym training',
      bust: 'Busts',
      attack: 'Attacks',
      crime: 'Crimes',
      hunting: 'Hunting'
    };

    const detailLabels = {
      xanax: 'Xanax',
      cannabis: 'Cannabis',
      alcohol: 'Alcohol',
      candy: 'Candy',
      erotic_dvd: 'Erotic DVD',
      ecstasy: 'Ecstasy',
      vicodin: 'Vicodin',
      points: 'Point refill',
      mission: 'Mission reward'
    };

    if (
      event?.category ===
      'overdose'
    ) {
      const item =
        detailLabels[
          event?.detail
        ];

      return item
        ? `${item} overdose`
        : 'Overdose';
    }

    return detailLabels[
      event?.detail
    ] ||
      labels[event?.category] ||
      String(
        event?.category ||
        'Other activity'
      ).replace(
        /_/g,
        ' '
      );
  }

  function resourceDashboardBreakdown(
    events,
    resource,
    flow,
    kind = ''
  ) {
    const grouped =
      new Map();

    for (
      const event
      of events || []
    ) {
      if (
        event?.resource !== resource ||
        event?.flow !== flow ||
        (
          kind &&
          event?.kind !== kind
        )
      ) {
        continue;
      }

      const label =
        resourceDashboardSourceLabel(
          event
        );

      const current =
        grouped.get(
          label
        ) || {
          label,
          amount: 0,
          events: 0
        };

      current.amount +=
        Number(
          event.amount
        ) ||
        0;

      current.events++;

      grouped.set(
        label,
        current
      );
    }

    return [...grouped.values()]
      .sort(
        (
          left,
          right
        ) =>
          right.amount -
            left.amount ||
          left.label.localeCompare(
            right.label
          )
      );
  }

  function renderResourceDashboardBreakdown(
    rows,
    emptyText,
    tone = 'neutral'
  ) {
    const positiveRows =
      (
        rows ||
        []
      ).filter(
        row =>
          Number.isFinite(
            Number(
              row?.amount
            )
          ) &&
          Number(
            row.amount
          ) > 0
      );

    if (
      !positiveRows.length
    ) {
      return `
        <div class="ta-resource-empty">
          ${escapeResourceDashboardHtml(emptyText)}
        </div>
      `;
    }

    const safeTone =
      [
        'gain',
        'use',
        'loss'
      ].includes(
        tone
      )
        ? tone
        : 'neutral';

    const total =
      positiveRows.reduce(
        (
          sum,
          row
        ) =>
          sum +
          Number(
            row.amount
          ),
        0
      );

    const categoryText =
      positiveRows.length === 1
        ? 'category'
        : 'categories';

    return `
      <div class="ta-resource-breakdown ta-resource-breakdown-${safeTone}">
        <div class="ta-resource-breakdown-summary">
          <span>${positiveRows.length} ranked ${categoryText}</span>
          <b>${resourceDashboardFormatNumber(total)} total</b>
        </div>
        <div class="ta-resource-breakdown-list">
          ${positiveRows.map(
            (
              row,
              index
            ) => {
              const share =
                Math.max(
                  0,
                  Math.min(
                    100,
                    (
                      Number(row.amount) /
                      total
                    ) *
                      100
                  )
                );

              const eventCount =
                Number(
                  row.events
                ) ||
                0;

              return `
                <div class="ta-resource-breakdown-row">
                  <div class="ta-resource-breakdown-rank">${index + 1}</div>
                  <div class="ta-resource-breakdown-main">
                    <div class="ta-resource-breakdown-topline">
                      <span class="ta-resource-breakdown-label">${escapeResourceDashboardHtml(row.label)}</span>
                      <span class="ta-resource-breakdown-values">
                        <b>${resourceDashboardFormatNumber(row.amount)}</b>
                        <span>${resourceDashboardFormatPercentage(row.amount, total)}</span>
                      </span>
                    </div>
                    <div class="ta-resource-breakdown-track">
                      <div style="width:${share.toFixed(2)}%"></div>
                    </div>
                    <div class="ta-resource-breakdown-events">
                      ${resourceDashboardFormatNumber(eventCount)} recorded ${eventCount === 1 ? 'event' : 'events'}
                    </div>
                  </div>
                </div>
              `;
            }
          ).join('')}
        </div>
      </div>
    `;
  }

  function renderResourceDashboardLiveCard(
    resource,
    bar,
    fetchedAt
  ) {
    const title =
      resource === 'energy'
        ? 'Energy'
        : resource === 'nerve'
          ? 'Nerve'
          : 'Happiness';

    const percentage =
      Math.max(
        0,
        Math.min(
          100,
          (
            bar.current /
            bar.maximum
          ) *
          100
        )
      );

    const fullAt =
      Number(fetchedAt) +
      bar.full_time *
      1000;

    const rateText =
      bar.increment > 0 &&
      bar.interval > 0
        ? '+' +
          resourceDashboardFormatNumber(
            bar.increment
          ) +
          ' every ' +
          resourceDashboardFormatDuration(
            bar.interval
          )
        : 'No natural refill rate reported';

    const statusText =
      resourceDashboardLiveStatusText(
        bar.current,
        bar.maximum,
        fullAt
      );

    return `
      <div class="ta-resource-live-card">
        <div class="ta-resource-live-topline">
          <span>${title}</span>
          <b>${resourceDashboardFormatNumber(bar.current)} / ${resourceDashboardFormatNumber(bar.maximum)}</b>
        </div>
        <div class="ta-resource-live-track">
          <div style="width:${percentage.toFixed(2)}%"></div>
        </div>
        <div
          class="ta-resource-eta"
          data-ta-resource-full-at="${fullAt}"
          data-ta-resource-current="${bar.current}"
          data-ta-resource-maximum="${bar.maximum}"
        >
          ${escapeResourceDashboardHtml(statusText)}
        </div>
        <div class="ta-resource-rate">
          ${rateText} · Live from Torn
        </div>
      </div>
    `;
  }

  function renderResourceDashboardHistoryCard(
    flow,
    resource
  ) {
    const summary =
      flow?.[resource] ||
      resourceFlowBlankResource(
        resource
      );

    const title =
      resource === 'energy'
        ? 'Energy history'
        : resource === 'nerve'
          ? 'Nerve history'
          : 'Happiness history';

    const incoming =
      resourceDashboardBreakdown(
        flow?.events,
        resource,
        'in',
        'gain'
      );

    const outgoing =
      resourceDashboardBreakdown(
        flow?.events,
        resource,
        'out',
        'use'
      );

    const setbacks =
      resourceDashboardBreakdown(
        flow?.events,
        resource,
        'out',
        'loss'
      );

    return `
      <div class="ta-resource-history-card">
        <div class="ta-resource-history-title">
          ${title}
        </div>
        <div class="ta-metric-grid ta-resource-metric-grid">
          <div class="ta-metric-card ta-resource-metric-gain">
            <div class="ta-metric-label">Gained</div>
            <div class="ta-metric-value">${resourceDashboardFormatNumber(summary.gain_total)}</div>
          </div>
          <div class="ta-metric-card ta-resource-metric-use">
            <div class="ta-metric-label">Used</div>
            <div class="ta-metric-value">${resourceDashboardFormatNumber(summary.use_total)}</div>
          </div>
          <div class="ta-metric-card ta-resource-metric-loss">
            <div class="ta-metric-label">Lost to setbacks</div>
            <div class="ta-metric-value">${resourceDashboardFormatNumber(summary.loss_total)}</div>
          </div>
        </div>
        <div class="ta-resource-list-heading ta-resource-list-heading-gain">Where it came from</div>
        ${renderResourceDashboardBreakdown(incoming, `No recorded ${resource} gains yet.`, 'gain')}
        <div class="ta-resource-list-heading ta-resource-list-heading-use">Where it went</div>
        ${renderResourceDashboardBreakdown(outgoing, `No recorded ${resource} uses yet.`, 'use')}
        ${
          Number(summary.loss_total) > 0
            ? `
              <div class="ta-resource-list-heading ta-resource-list-heading-loss">Setbacks</div>
              ${renderResourceDashboardBreakdown(setbacks, `No recorded ${resource} setbacks yet.`, 'loss')}
            `
            : ''
        }
      </div>
    `;
  }

  function renderResourceDashboard(
    flow,
    barsSnapshot
  ) {
    if (
      !flow
    ) {
      return '';
    }

    const totalEvents =
      Number(
        flow?.events?.length ||
        0
      );

    const liveAvailable =
      barsSnapshot?.status ===
      'available';

    const liveHtml =
      liveAvailable
        ? `
          <div class="ta-resource-live-grid">
            ${renderResourceDashboardLiveCard('energy', barsSnapshot.energy, barsSnapshot.fetched_at)}
            ${renderResourceDashboardLiveCard('nerve', barsSnapshot.nerve, barsSnapshot.fetched_at)}
            ${renderResourceDashboardLiveCard('happiness', barsSnapshot.happiness, barsSnapshot.fetched_at)}
          </div>
          <div class="ta-resource-freshness">
            Refreshed ${escapeResourceDashboardHtml(new Date(barsSnapshot.fetched_at).toLocaleTimeString())}.
            Analyze Stored Logs again for a fresh API reading.
          </div>
        `
        : `
          <div class="ta-resource-live-unavailable">
            <b>Live resources unavailable</b>
            <span>
              Historical totals still work. A valid saved API key is needed for current bars and refill times.
            </span>
          </div>
        `;

    return `
      <details class="ta-section ta-resource-section">
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">Energy, Nerve &amp; Happiness</span>
          <span class="ta-section-meta">
            ${resourceDashboardFormatNumber(totalEvents)} recorded events
          </span>
        </summary>
        <div class="ta-section-body">
          <div class="ta-section-intro">
            See what you have now, when it will refill, and how your recorded Energy, Nerve, and Happiness moved over time.
          </div>
          ${liveHtml}
          <div class="ta-resource-history-grid">
            ${renderResourceDashboardHistoryCard(flow, 'energy')}
            ${renderResourceDashboardHistoryCard(flow, 'nerve')}
            ${renderResourceDashboardHistoryCard(flow, 'happiness')}
          </div>
          <div class="ta-resource-limit-note">
            Natural regeneration is not included in historical gains because Torn does not record it in personal log history. Actions without a recorded resource amount are not guessed. Live bars and refill times above come directly from Torn's API.
          </div>
        </div>
      </details>
    `;
  }

  function bindResourceDashboardInteractions(
    root
  ) {
    const countdowns =
      root?.querySelectorAll?.(
        '[data-ta-resource-full-at]'
      ) ||
      [];

    if (
      !countdowns.length
    ) {
      return;
    }

    const update =
      () => {
        if (
          !root.isConnected
        ) {
          return;
        }

        let stillCounting =
          false;

        for (
          const output
          of countdowns
        ) {
          const fullAt =
            Number(
              output.getAttribute(
                'data-ta-resource-full-at'
              )
            );

          const current =
            Number(
              output.getAttribute(
                'data-ta-resource-current'
              )
            );

          const maximum =
            Number(
              output.getAttribute(
                'data-ta-resource-maximum'
              )
            );

          output.textContent =
            resourceDashboardLiveStatusText(
              current,
              maximum,
              fullAt
            );

          if (
            fullAt >
            Date.now()
          ) {
            stillCounting =
              true;
          }
        }

        if (
          stillCounting
        ) {
          setTimeout(
            update,
            1000
          );
        }
      };

    update();
  }
  // ============================================================
  // LIVE RESOURCE FAILURE DIAGNOSTICS
  // ============================================================

  const renderResourceDashboardWithoutDiagnostics =
    renderResourceDashboard;

  function resourceDashboardDiagnosticText(
    snapshot
  ) {
    const reason =
      String(
        snapshot?.reason ||
        'unknown'
      );

    if (
      reason ===
      'api_key_unavailable'
    ) {
      return 'No API key reached the /user/bars request.';
    }

    const raw =
      String(
        snapshot?.message ||
        ''
      ).trim();

    if (
      !raw
    ) {
      return `Bars failure reason: ${reason}.`;
    }

    const redacted =
      raw
        .replace(
          /ApiKey\s+[^\s<>&]+/gi,
          'ApiKey [redacted]'
        )
        .replace(
          /(\bkey=)[^&\s<]+/gi,
          '$1[redacted]'
        );

    return `${reason}: ${redacted}`
      .slice(
        0,
        220
      );
  }

  renderResourceDashboard =
    function renderResourceDashboardWithDiagnostics(
      flow,
      barsSnapshot
    ) {
      const html =
        renderResourceDashboardWithoutDiagnostics(
          flow,
          barsSnapshot
        );

      if (
        !html ||
        barsSnapshot?.status ===
          'available'
      ) {
        return html;
      }

      const oldText =
        'Historical totals still work. A valid saved API key is needed for current bars and refill times.';

      if (
        !html.includes(
          oldText
        )
      ) {
        return html;
      }

      const diagnostic =
        escapeResourceDashboardHtml(
          resourceDashboardDiagnosticText(
            barsSnapshot
          )
        );

      return html.replace(
        oldText,
        'Historical totals still work. The live /user/bars reading failed, while other analytics remain available.' +
          `<br><b>Diagnostic:</b> ${diagnostic}`
      );
    };
  // ============================================================
  // VERIFIED READABLE HISTORY SERIALIZATION
  // ============================================================

  const HISTORY_EXPORT_FORMAT =
    'torn-analytics-readable-history';

  const HISTORY_EXPORT_FORMAT_VERSION =
    2;

  function normalizeHistoryExportAccount(
    account
  ) {
    const id = normalizeSingleAccountId(
      account?.id,
      'Authenticated Torn account ID'
    );

    const name = String(account?.name ?? '').trim();

    if (!name) {
      throw new Error(
        'Readable history export requires a valid authenticated Torn account.'
      );
    }

    return { id, name };
  }

  function historyExportFilename(
    accountId,
    date = new Date()
  ) {
    const id = normalizeSingleAccountId(
      accountId,
      'History export account ID'
    );

    const day = date.toISOString().slice(0, 10);
    return `TornAnalytics-${id}-history-${day}.json`;
  }

  async function historyExportSha256Hex(
    text
  ) {
    if (
      !globalThis.crypto?.subtle ||
      typeof TextEncoder !== 'function'
    ) {
      throw new Error(
        'SHA-256 is unavailable; refusing to create an unverifiable readable history export.'
      );
    }

    const digest = await globalThis.crypto.subtle.digest(
      'SHA-256',
      new TextEncoder().encode(String(text))
    );

    return Array.from(
      new Uint8Array(digest),
      byte => byte.toString(16).padStart(2, '0')
    ).join('');
  }

  function summarizeHistoryArchiveProvenance(
    records
  ) {
    if (
      !Array.isArray(
        records
      )
    ) {
      throw new Error(
        'Readable history export provenance requires a verified record array.'
      );
    }

    let rawRecordCount =
      0;

    let legacyNormalizedCount =
      0;

    for (
      const record
      of records
    ) {
      const raw =
        validateHistoryRawArchiveBinding(
          record
        );

      if (
        raw
      ) {
        rawRecordCount++;
      } else {
        legacyNormalizedCount++;
      }
    }

    return {
      raw_record_format:
        HISTORY_RAW_ARCHIVE_FORMAT,
      raw_record_count:
        rawRecordCount,
      legacy_normalized_count:
        legacyNormalizedCount,
      lossless_raw_complete:
        records.length > 0 &&
        rawRecordCount === records.length &&
        legacyNormalizedCount === 0
    };
  }

  function validateHistoryExportRecordSet(
    accountId,
    cachedRecords,
    logs
  ) {
    const id = normalizeSingleAccountId(
      accountId,
      'History export account ID'
    );

    if (!Array.isArray(cachedRecords) || !cachedRecords.length) {
      throw new Error(
        `No stored Torn history exists for authenticated account ${id}.`
      );
    }

    if (!Array.isArray(logs) || logs.length !== cachedRecords.length) {
      throw new Error(
        'Readable history export verification failed because stored-record and decrypted-log counts do not match.'
      );
    }

    const prefix = `${id}:`;

    for (const record of cachedRecords) {
      let recordAccountId;

      try {
        recordAccountId = normalizeSingleAccountId(
          record?.account_id,
          'Stored export record account ID'
        );
      } catch {
        throw new Error(
          'Readable history export blocked because a stored record failed authenticated account binding.'
        );
      }

      if (
        recordAccountId !== id ||
        typeof record?.cache_key !== 'string' ||
        !record.cache_key.startsWith(prefix)
      ) {
        throw new Error(
          'Readable history export blocked because a stored record failed authenticated account binding.'
        );
      }
    }

    const seen = new Set();

    for (const log of logs) {
      const prepared = prepareCachedLog(id, log);

      if (seen.has(prepared.id)) {
        throw new Error(
          `Readable history export blocked because duplicate Torn log identity ${prepared.id} was found.`
        );
      }

      seen.add(prepared.id);
    }

    return [...logs].sort(
      (a, b) =>
        Number(a.timestamp) - Number(b.timestamp) ||
        String(a.id).localeCompare(String(b.id))
    );
  }

  async function buildReadableHistoryExport(
    authenticatedAccount
  ) {
    const account = normalizeHistoryExportAccount(authenticatedAccount);
    const protection = await getAccountHistoryProtectionStatus(account.id);

    if (!protection.complete || protection.plaintext !== 0) {
      throw new Error(
        'Readable history export is available only after all stored Torn logs are protected by Local History Protection.'
      );
    }

    const cachedRecords = await dbLoadCachedRecords(account.id);

    if (cachedRecords.some(record => !isProtectedHistoryRecord(record))) {
      throw new Error(
        'Readable history export blocked because an unprotected stored Torn log was detected.'
      );
    }

    const logs = await dbLoadLogs(account.id);
    const records = validateHistoryExportRecordSet(
      account.id,
      cachedRecords,
      logs
    );

    const archiveProvenance =
      summarizeHistoryArchiveProvenance(
        records
      );

    const firstTimestamp = Number(records[0]?.timestamp);
    const lastTimestamp = Number(records[records.length - 1]?.timestamp);

    if (
      !Number.isSafeInteger(firstTimestamp) ||
      !Number.isSafeInteger(lastTimestamp) ||
      firstTimestamp < 0 ||
      lastTimestamp < firstTimestamp
    ) {
      throw new Error(
        'Readable history export verification failed because the history coverage is invalid.'
      );
    }

    const payload = {
      format: HISTORY_EXPORT_FORMAT,
      format_version: HISTORY_EXPORT_FORMAT_VERSION,
      account: {
        id: account.id,
        name: account.name
      },
      coverage: {
        first_timestamp: firstTimestamp,
        first_iso: timestampToIso(firstTimestamp),
        last_timestamp: lastTimestamp,
        last_iso: timestampToIso(lastTimestamp),
        record_count: records.length
      },
      archive_provenance:
        archiveProvenance,
      collector: {
        name: 'Torn Analytics',
        version: VERSION,
        source: 'authenticated-account-scoped encrypted local history'
      },
      exported_at: new Date().toISOString(),
      records
    };

    const digest = await historyExportSha256Hex(
      stableHistoryJson(payload)
    );

    const output = {
      ...payload,
      integrity: {
        algorithm: 'SHA-256',
        canonicalization: 'stable-json-v1',
        scope: 'all top-level fields except integrity',
        digest
      }
    };

    return {
      account,
      filename: historyExportFilename(account.id),
      record_count: records.length,
      first_timestamp: firstTimestamp,
      last_timestamp: lastTimestamp,
      archive_provenance:
        archiveProvenance,
      digest,
      json: JSON.stringify(output, null, 2)
    };
  }

  async function buildAuthenticatedReadableHistoryExport(
    apiKey,
    tracker = null
  ) {
    const accountTracker = tracker || {
      setStage() {},
      incrementRequest() {}
    };

    const account = await detectAccount(
      apiKey,
      accountTracker
    );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    return buildReadableHistoryExport(
      account
    );
  }

  // ============================================================
  // EPHEMERAL READABLE HISTORY DOWNLOAD
  // ============================================================

  function triggerReadableHistoryDownload(
    result
  ) {
    if (
      !result ||
      typeof result.json !== 'string' ||
      !result.json.length ||
      typeof result.filename !== 'string' ||
      !/^TornAnalytics-[1-9]\d*-history-\d{4}-\d{2}-\d{2}\.json$/.test(
        result.filename
      )
    ) {
      throw new Error(
        'Readable history download refused an invalid verified export result.'
      );
    }

    if (
      typeof Blob !== 'function' ||
      !globalThis.URL?.createObjectURL ||
      !globalThis.URL?.revokeObjectURL
    ) {
      throw new Error(
        'This browser cannot create a local readable history download safely.'
      );
    }

    const blob = new Blob(
      [result.json],
      {
        type: 'application/json;charset=utf-8'
      }
    );

    const objectUrl =
      URL.createObjectURL(
        blob
      );

    const anchor =
      document.createElement(
        'a'
      );

    anchor.href =
      objectUrl;

    anchor.download =
      result.filename;

    anchor.rel =
      'noopener';

    anchor.style.display =
      'none';

    try {
      // Keep the object URL out of Torn's page DOM. A detached anchor is
      // sufficient for standards-compliant browsers and avoids exposing the
      // temporary readable-history URL to page-level DOM observers.
      anchor.click();
    } finally {
      anchor.remove();

      setTimeout(
        () => {
          URL.revokeObjectURL(
            objectUrl
          );
        },
        1000
      );
    }

    return {
      account: {
        id: result.account.id,
        name: result.account.name
      },
      filename: result.filename,
      record_count: result.record_count,
      first_timestamp: result.first_timestamp,
      last_timestamp: result.last_timestamp,
      digest: result.digest
    };
  }

  function sharePreparedHistoryExport(
    result
  ) {
    if (
      !result ||
      typeof result.json !== 'string' ||
      !result.json.length ||
      typeof result.filename !== 'string' ||
      !/^TornAnalytics-[1-9]\d*-history-\d{4}-\d{2}-\d{2}\.json$/.test(
        result.filename
      )
    ) {
      throw new Error(
        'Native history share refused an invalid verified export result.'
      );
    }

    if (
      typeof File !== 'function' ||
      typeof globalThis.navigator?.share !== 'function'
    ) {
      throw new Error(
        'Native file sharing is unavailable in this TornPDA/iOS browser. No readable export was exposed to the page.'
      );
    }

    const file = new File(
      [result.json],
      result.filename,
      {
        type: 'application/json;charset=utf-8'
      }
    );

    const shareData = {
      files: [file]
    };

    if (
      typeof navigator.canShare === 'function' &&
      !navigator.canShare(shareData)
    ) {
      throw new Error(
        'This TornPDA/iOS browser cannot safely share the prepared JSON file.'
      );
    }

    const receipt = {
      account: {
        id: result.account.id,
        name: result.account.name
      },
      filename: result.filename,
      record_count: result.record_count,
      first_timestamp: result.first_timestamp,
      last_timestamp: result.last_timestamp,
      digest: result.digest
    };

    // navigator.share() is intentionally invoked synchronously before this
    // function yields so the direct Save Export File tap retains user
    // activation in WebKit/WKWebView.
    const shareResult = navigator.share(
      shareData
    );

    if (
      !shareResult ||
      typeof shareResult.then !== 'function'
    ) {
      throw new Error(
        'Native file sharing did not start correctly.'
      );
    }

    return shareResult.then(
      () => receipt
    );
  }

  async function exportAuthenticatedHistoryToDownload(
    apiKey,
    tracker = null
  ) {
    const result =
      await buildAuthenticatedReadableHistoryExport(
        apiKey,
        tracker
      );

    return triggerReadableHistoryDownload(
      result
    );
  }

  // ============================================================
  // READ-ONLY HISTORY FORENSICS
  // ============================================================

  function historyForensicWindowConfig() {
    return {
      from:
        1782991800,

      to:
        1782991920,

      target_id:
        'zEna1LjCEgf6Idhd1agH',

      target_timestamp:
        1782991856
    };
  }

  async function runHistoryForensicWindowCheck(
    apiKey,
    tracker = null,
    requestedTargetId = null
  ) {
    const defaultConfig =
      historyForensicWindowConfig();

    const account =
      await detectAccount(
        apiKey,
        tracker
      );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    // Deliberately do not create/refresh recovery metadata or write any cache
    // state here. This diagnostic must be read-only with respect to history.
    const storedLogs =
      await dbLoadLogs(
        account.id
      );

    const config =
      requestedTargetId ===
      null
        ? defaultConfig
        : (() => {
            const target =
              resolveStoredHistoryTraceTarget(
                storedLogs,
                requestedTargetId
              );

            return {
              from:
                target.timestamp -
                60,
              to:
                target.timestamp +
                60,
              target_id:
                target.id,
              target_timestamp:
                target.timestamp
            };
          })();

    tracker?.setStage(
      'Running forensic history check…',
      `${config.from} → ${config.to}; read-only direct Torn v2 comparison`
    );

    const url =
      `${API_BASE}/user/log` +
      `?from=${encodeURIComponent(config.from)}` +
      `&to=${encodeURIComponent(config.to)}` +
      `&limit=${API_LIMIT}`;

    const json =
      await apiFetchJson(
        url,
        apiKey,
        tracker,
        1,
        createRangeSafetyState()
      );

    const source =
      json?.log;

    if (
      !Array.isArray(
        source
      )
    ) {
      throw new Error(
        'The forensic Torn v2 response did not contain a valid log array.'
      );
    }

    const links =
      json?._metadata?.links;

    if (
      source.length >=
        API_LIMIT ||
      !links ||
      typeof links !== 'object' ||
      Array.isArray(
        links
      ) ||
      !Object.prototype.hasOwnProperty.call(
        links,
        'prev'
      ) ||
      !Object.prototype.hasOwnProperty.call(
        links,
        'next'
      ) ||
      links.prev !== null ||
      links.next !== null
    ) {
      throw new Error(
        'The forensic window is saturated or paginated, so one direct request cannot independently prove this window. No conclusion was drawn.'
      );
    }

    const liveLogs =
      normalizeV2Logs(
        json
      );

    if (
      liveLogs.length !==
      source.length
    ) {
      throw new Error(
        'The forensic Torn v2 response contained a malformed log entry.'
      );
    }

    for (
      const log
      of liveLogs
    ) {
      if (
        !Number.isSafeInteger(
          log.timestamp
        ) ||
        log.timestamp <=
          config.from ||
        log.timestamp >
          config.to
      ) {
        throw new Error(
          `The forensic Torn v2 response returned log ${log.id} outside the exact diagnostic window.`
        );
      }
    }

    const storedWindow =
      storedLogs.filter(
        log =>
          Number.isSafeInteger(
            log?.timestamp
          ) &&
          log.timestamp >
            config.from &&
          log.timestamp <=
            config.to
      );

    const storedById =
      new Map(
        storedWindow.map(
          log => [
            String(
              log.id
            ),
            log
          ]
        )
      );

    const liveById =
      new Map(
        liveLogs.map(
          log => [
            String(
              log.id
            ),
            log
          ]
        )
      );

    const storedOnlyIds =
      [];

    const apiOnlyIds =
      [];

    const conflictIds =
      [];

    let confirmedCurrent =
      0;

    for (
      const [
        id,
        storedLog
      ]
      of storedById
    ) {
      const liveLog =
        liveById.get(
          id
        );

      if (
        !liveLog
      ) {
        storedOnlyIds.push(
          id
        );
        continue;
      }

      if (
        historyLogsEqual(
          historyLogWithoutRawArchive(
            storedLog
          ),
          historyLogWithoutRawArchive(
            liveLog
          )
        )
      ) {
        confirmedCurrent++;
      } else {
        conflictIds.push(
          id
        );
      }
    }

    for (
      const id
      of liveById.keys()
    ) {
      if (
        !storedById.has(
          id
        )
      ) {
        apiOnlyIds.push(
          id
        );
      }
    }

    storedOnlyIds.sort();
    apiOnlyIds.sort();
    conflictIds.sort();

    const targetStored =
      storedById.get(
        config.target_id
      ) ||
      null;

    const targetLive =
      liveById.get(
        config.target_id
      ) ||
      null;

    let targetStatus =
      'absent_both';

    if (
      targetStored &&
      targetLive
    ) {
      targetStatus =
        historyLogsEqual(
          historyLogWithoutRawArchive(
            targetStored
          ),
          historyLogWithoutRawArchive(
            targetLive
          )
        )
          ? 'confirmed_current'
          : 'conflict';
    } else if (
      targetStored
    ) {
      targetStatus =
        'stored_only';
    } else if (
      targetLive
    ) {
      targetStatus =
        'api_only';
    }

    const result = {
      account: {
        id:
          account.id,

        name:
          String(
            account.name ??
            ''
          )
      },

      window: {
        from:
          config.from,

        to:
          config.to
      },

      counts: {
        stored:
          storedWindow.length,

        fresh_v2:
          liveLogs.length,

        confirmed_current:
          confirmedCurrent,

        stored_only:
          storedOnlyIds.length,

        api_only:
          apiOnlyIds.length,

        conflicts:
          conflictIds.length
      },

      target: {
        id:
          config.target_id,

        timestamp:
          config.target_timestamp,

        stored_present:
          Boolean(
            targetStored
          ),

        fresh_v2_present:
          Boolean(
            targetLive
          ),

        status:
          targetStatus
      },

      stored_only_ids:
        storedOnlyIds,

      api_only_ids:
        apiOnlyIds,

      conflict_ids:
        conflictIds
    };

    tracker?.setStage(
      'Forensic check complete',
      `Stored ${result.counts.stored} · fresh v2 ${result.counts.fresh_v2} · target ${result.target.status}`
    );

    return result;
  }

  function formatHistoryForensicResult(
    result
  ) {
    const targetStatus =
      String(
        result?.target?.status ??
        'unknown'
      )
        .replaceAll(
          '_',
          ' '
        )
        .toUpperCase();

    const storedOnlyPreview =
      result.stored_only_ids.length
        ? result.stored_only_ids
            .slice(
              0,
              8
            )
            .join(', ')
        : 'None';

    const apiOnlyPreview =
      result.api_only_ids.length
        ? result.api_only_ids
            .slice(
              0,
              8
            )
            .join(', ')
        : 'None';

    const conflictPreview =
      result.conflict_ids.length
        ? result.conflict_ids
            .slice(
              0,
              8
            )
            .join(', ')
        : 'None';

    return (
      'Read-only history forensic check complete.\n\n' +
      `Window: ${result.window.from} → ${result.window.to}\n` +
      `Stored records: ${result.counts.stored}\n` +
      `Fresh Torn v2 records: ${result.counts.fresh_v2}\n` +
      `Confirmed current: ${result.counts.confirmed_current}\n` +
      `Stored-only: ${result.counts.stored_only}\n` +
      `Fresh-only: ${result.counts.api_only}\n` +
      `Conflicts: ${result.counts.conflicts}\n\n` +
      `Target ${result.target.id}\n` +
      `Stored: ${result.target.stored_present ? 'YES' : 'NO'}\n` +
      `Fresh Torn v2: ${result.target.fresh_v2_present ? 'YES' : 'NO'}\n` +
      `Status: ${targetStatus}\n\n` +
      `Stored-only IDs: ${storedOnlyPreview}\n` +
      `Fresh-only IDs: ${apiOnlyPreview}\n` +
      `Conflict IDs: ${conflictPreview}\n\n` +
      'No stored history was modified.'
    );
  }

  function resolveStoredHistoryTraceTarget(
    storedLogs,
    requestedTargetId
  ) {
    const targetId =
      String(
        requestedTargetId ??
        ''
      ).trim();

    if (
      !targetId
    ) {
      throw new Error(
        'Enter the exact Torn log ID reported as missing by Full Rebuild.'
      );
    }

    const storedTarget =
      storedLogs.find(
        log =>
          String(
            log?.id
          ) ===
          targetId
      );

    const targetTimestamp =
      Number(
        storedTarget?.timestamp
      );

    if (
      !storedTarget ||
      !Number.isSafeInteger(
        targetTimestamp
      ) ||
      targetTimestamp <= 0
    ) {
      throw new Error(
        `Stored history does not contain a valid log with ID ${targetId}.`
      );
    }

    return {
      id:
        targetId,
      timestamp:
        targetTimestamp
    };
  }

  async function runHistoryTargetCollectorTrace(
    apiKey,
    tracker = null,
    requestedTargetId = null
  ) {

    const account =
      await detectAccount(
        apiKey,
        tracker
      );

    await assertAuthenticatedSingleAccountOwner(
      account.id
    );

    const storedLogs =
      await dbLoadLogs(
        account.id
      );

    const target =
      resolveStoredHistoryTraceTarget(
        storedLogs,
        requestedTargetId
      );

    const throughDate =
      todayLocal();

    const segments =
      createSegments(
        account.signup_local_date,
        throughDate
      );

    let tracedSegment =
      null;
    let tracedFrom =
      null;
    let tracedTo =
      null;

    for (
      const segment
      of segments
    ) {
      const from =
        Math.max(
          startOfDayTimestamp(
            segment.from_date
          ),
          account.signup_timestamp - 1
        );

      const to =
        segment.to_date ===
        throughDate
          ? Math.floor(
              Date.now() /
              1000
            )
          : endOfDayTimestamp(
              segment.to_date
            );

      if (
        target.timestamp >
          from &&
        target.timestamp <=
          to
      ) {
        tracedSegment =
          segment;
        tracedFrom =
          from;
        tracedTo =
          to;
        break;
      }
    }

    if (
      !tracedSegment
    ) {
      throw new Error(
        'The target Torn log does not fall inside any current history-build segment.'
      );
    }

    tracker?.setStage(
      'Tracing rebuild collector…',
      `${tracedSegment.from_date} → ${tracedSegment.to_date}; read-only exact collector path`
    );

    const safetyState =
      createRangeSafetyState();

    safetyState.history_target_trace =
      createHistoryTargetTraceState(
        target.id,
        target.timestamp
      );

    const result =
      await fetchCompleteRange(
        apiKey,
        tracedFrom,
        tracedTo,
        tracker,
        safetyState
      );

    const trace =
      summarizeHistoryTargetTrace(
        safetyState.history_target_trace,
        result.logs
      );

    const storedTarget =
      storedLogs.some(
        log =>
          String(
            log?.id
          ) ===
          target.id
      );

    const output = {
      account: {
        id:
          account.id,
        name:
          String(
            account.name ??
            ''
          )
      },
      segment: {
        from_date:
          tracedSegment.from_date,
        to_date:
          tracedSegment.to_date,
        from_timestamp:
          tracedFrom,
        to_timestamp:
          tracedTo
      },
      stored_target_present:
        storedTarget,
      collector_result_count:
        result.logs.length,
      collector_request_count:
        result.request_count,
      collector_split_count:
        result.split_count,
      trace
    };

    tracker?.setStage(
      'Collector trace complete',
      `Target ${trace.classification} · ${result.request_count} requests · ${result.split_count} splits`
    );

    return output;
  }

  function formatHistoryTargetCollectorTrace(
    result
  ) {
    const trace =
      result.trace;

    const keyEvents =
      trace.events
        .filter(
          event =>
            event.stage === 'page' ||
            event.stage === 'pagination_split_required' ||
            event.stage === 'pagination_range_complete' ||
            event.stage === 'split_merge'
        )
        .slice(
          -12
        )
        .map(
          event => {
            if (
              event.stage === 'page'
            ) {
              return (
                `PAGE ${event.request_from}→${event.request_to} ` +
                `n=${event.record_count} covers=${event.covers_target ? 'Y' : 'N'} ` +
                `target=${event.returned_target ? 'Y' : 'N'}`
              );
            }

            if (
              event.stage === 'pagination_split_required'
            ) {
              return (
                `SPLIT REQUIRED ${event.range_from}→${event.range_to} ` +
                `target-on-page=${event.page_returned_target ? 'Y' : 'N'} ` +
                `retained-before=${event.retained_before_split ? 'Y' : 'N'}`
              );
            }

            if (
              event.stage === 'pagination_range_complete'
            ) {
              return (
                `RANGE COMPLETE ${event.range_from}→${event.range_to} ` +
                `target=${event.retained_target ? 'Y' : 'N'}`
              );
            }

            return (
              `SPLIT MERGE ${event.range_from}→${event.range_to} ` +
              `target=${event.retained_target ? 'Y' : 'N'}`
            );
          }
        )
        .join('\n');

    return (
      'Read-only rebuild collector trace complete.\n\n' +
      `Segment: ${result.segment.from_date} → ${result.segment.to_date}\n` +
      `Stored target present: ${result.stored_target_present ? 'YES' : 'NO'}\n` +
      `Weekly collector records: ${result.collector_result_count}\n` +
      `API requests: ${result.collector_request_count}\n` +
      `Range splits: ${result.collector_split_count}\n\n` +
      `Target: ${trace.target_id}\n` +
      `Covering API pages: ${trace.covering_page_count}\n` +
      `Pages that returned target: ${trace.page_returned_target_count}\n` +
      `Pagination merge retained target: ${trace.pagination_merge_retained_target ? 'YES' : 'NO'}\n` +
      `Final weekly result retained target: ${trace.final_range_retained_target ? 'YES' : 'NO'}\n` +
      `Classification: ${trace.classification.toUpperCase().replaceAll('_', ' ')}\n\n` +
      'Last relevant trace events:\n' +
      `${keyEvents || 'None'}\n\n` +
      'No stored history was modified.'
    );
  }

  // ============================================================
  // CSS
  // ============================================================

  function injectStyles() {

    if (
      document.getElementById(
        STYLE_ID
      )
    ) {
      return;
    }

    const style =
      document.createElement(
        'style'
      );

    style.id =
      STYLE_ID;

    style.textContent = `

      #${BUTTON_ID} {
        position: fixed;
        right: 12px;
        bottom: 90px;
        z-index: 999999;
        padding: 10px 13px;
        border: 0;
        border-radius: 8px;
        background: #222;
        color: white;
        font-weight: 700;
        box-shadow: 0 2px 10px rgba(0,0,0,.45);
        cursor: grab;
        touch-action: none;
        user-select: none;
        -webkit-user-select: none;
      }

      #${BUTTON_ID}[data-dragging="1"] {
        cursor: grabbing;
      }

      #${MODAL_ID} {
        position: fixed;
        inset: 0;
        z-index: 1000000;
        display: flex;
        justify-content: center;
        align-items: center;
        padding: 12px;
        background: rgba(0,0,0,.84);
      }

      #${MODAL_ID} .card {
        display: flex;
        flex-direction: column;
        width: min(720px,100%);
        height: 94vh;
        max-height: 94vh;
        overflow: hidden;
        padding: 0;
        border-radius: 12px;
        background: #181818;
        color: #eee;
      }

      #${MODAL_ID} h2 {
        margin: 0;
        font-size: 18px;
      }

      #${MODAL_ID} .ta-modal-header {
        flex: 0 0 auto;
        display: flex;
        align-items: center;
        gap: 12px;
        padding: 12px 16px;
        border-bottom: 1px solid #333;
        background: #202020;
      }

      #${MODAL_ID} .ta-modal-header h2 {
        flex: 1;
      }

      #${MODAL_ID} .ta-modal-close {
        width: auto;
        min-width: 72px;
        min-height: 38px;
        margin: 0;
        padding: 7px 12px;
      }

      #${MODAL_ID} .ta-modal-scroll {
        min-height: 0;
        overflow-x: hidden;
        overflow-y: auto;
        padding: 16px;
        overscroll-behavior: contain;
        -webkit-overflow-scrolling: touch;
      }

      #${MODAL_ID} .sub {
        margin-bottom: 12px;
        font-size: 13px;
        line-height: 1.5;
        opacity: .75;
      }

      #${MODAL_ID} .panel {
        padding: 10px;
        margin-bottom: 10px;
        border: 1px solid #333;
        border-radius: 8px;
        background: #101010;
      }

      #${MODAL_ID} button,
      #${MODAL_ID} input,
      #${MODAL_ID} select {
        box-sizing: border-box;
        width: 100%;
        min-height: 42px;
        margin: 6px 0 9px;
        padding: 9px;
        border: 1px solid #555;
        border-radius: 7px;
        background: #111;
        color: #fff;
      }

      #${MODAL_ID} button {
        background: #333;
        font-weight: 700;
      }

      #${MODAL_ID} button:disabled {
        opacity: .4;
      }

      #${MODAL_ID} .actions {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 8px;
      }

      #${MODAL_ID} .top {
        display: flex;
        justify-content: space-between;
        gap: 10px;
        font-weight: 700;
      }

      #${MODAL_ID} .track {
        height: 12px;
        margin: 8px 0;
        border-radius: 999px;
        overflow: hidden;
        background: #292929;
      }

      #${MODAL_ID} .fill {
        width: 0%;
        height: 100%;
        background: #aaa;
        transition: width .2s ease;
      }

      #${MODAL_ID} .stats {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 5px 12px;
        font-size: 12px;
      }

      #${MODAL_ID} .small {
        margin: 6px 0;
        font-size: 12px;
        opacity: .78;
      }

      #${MODAL_ID} .setup {
        padding: 12px;
        margin-bottom: 10px;
        border: 1px solid #555;
        border-radius: 8px;
      }

      #${MODAL_ID} .ta-section {
        margin: 12px 0;
        overflow: hidden;
        border: 1px solid #3a3a3a;
        border-radius: 10px;
        background: #101010;
      }

      #${MODAL_ID} .ta-section-summary-row {
        display: flex;
        align-items: center;
        gap: 10px;
        min-height: 46px;
        padding: 11px 12px;
        cursor: pointer;
        list-style: none;
        user-select: none;
        -webkit-user-select: none;
      }

      #${MODAL_ID} .ta-section-summary-row::-webkit-details-marker {
        display: none;
      }

      #${MODAL_ID} .ta-section-summary-row::after {
        content: '▾';
        margin-left: 2px;
        font-size: 13px;
        opacity: .7;
        transition: transform .15s ease;
      }

      #${MODAL_ID} .ta-section:not([open]) .ta-section-summary-row::after {
        transform: rotate(-90deg);
      }

      #${MODAL_ID} .ta-section-title {
        font-size: 15px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-section-meta {
        margin-left: auto;
        text-align: right;
        font-size: 12px;
        opacity: .65;
      }

      #${MODAL_ID} .ta-section-body {
        padding: 0 12px 12px;
      }

      #${MODAL_ID} .ta-training-workspace-body {
        padding-top: 2px;
      }

      #${MODAL_ID} .ta-training-workspace-body > .ta-section {
        margin: 8px 0;
        border-color: #303030;
        background: #0c0c0c;
      }

      #${MODAL_ID} .ta-training-workspace-body > .ta-section:last-child {
        margin-bottom: 0;
      }

      #${MODAL_ID} .ta-training-workspace-body > .ta-section .ta-section-title {
        font-size: 14px;
      }

      #${MODAL_ID} .ta-settings-section .ta-section-body {
        padding-top: 2px;
      }

      #${MODAL_ID} .ta-settings-section.ta-automatic-sync-busy .ta-section-body {
        opacity: .68;
        pointer-events: none;
      }

      #${MODAL_ID} .ta-settings-group + .ta-settings-group {
        margin-top: 12px;
        padding-top: 12px;
        border-top: 1px solid #303030;
      }

      #${MODAL_ID} .ta-settings-label {
        display: block;
        margin-bottom: 4px;
        font-size: 12px;
        font-weight: 800;
        opacity: .75;
      }

      #${MODAL_ID} .ta-section-intro {
        margin: 0 0 12px;
        font-size: 12px;
        line-height: 1.5;
        opacity: .65;
      }

      #${MODAL_ID} .ta-training-status,
      #${MODAL_ID} .ta-training-projection {
        margin: 0 0 12px;
        padding: 10px;
        border: 1px solid #303030;
        border-radius: 8px;
        background: #151515;
        line-height: 1.4;
      }

      #${MODAL_ID} .ta-training-controls {
        display: grid;
        grid-template-columns: repeat(2, minmax(0, 1fr));
        gap: 10px;
        margin: 12px 0;
      }

      #${MODAL_ID} .ta-training-controls label,
      #${MODAL_ID} .ta-training-projection {
        display: grid;
        gap: 5px;
      }

      #${MODAL_ID} .ta-training-controls label > span,
      #${MODAL_ID} .ta-training-projection > span {
        font-size: 11px;
        opacity: .68;
      }

      #${MODAL_ID} .ta-training-controls select,
      #${MODAL_ID} .ta-training-controls input {
        box-sizing: border-box;
        width: 100%;
        min-height: 40px;
        padding: 8px;
        border: 1px solid #555;
        border-radius: 7px;
        background: #202020;
        color: #fff;
        font: inherit;
      }

      @media (max-width: 520px) {
        #${MODAL_ID} .ta-training-controls {
          grid-template-columns: 1fr;
        }
      }

      #${MODAL_ID} .ta-time-basis-control {
        margin: 0 0 12px;
        padding: 10px;
        border: 1px solid #303030;
        border-radius: 8px;
        background: #151515;
      }

      #${MODAL_ID} .ta-time-basis-topline {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 10px;
      }

      #${MODAL_ID} .ta-time-basis-topline > span {
        flex: 0 0 auto;
        font-size: 12px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-time-basis-options {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 6px;
        width: min(320px, 70%);
      }

      #${MODAL_ID} .ta-time-basis-options button {
        width: 100%;
        min-height: 36px;
        margin: 0;
        padding: 7px 9px;
        border-color: #444;
        font-size: 12px;
        opacity: .72;
      }

      #${MODAL_ID} .ta-time-basis-options button.ta-time-basis-active {
        border-color: #aaa;
        background: #444;
        opacity: 1;
      }

      #${MODAL_ID} .ta-time-basis-context {
        margin-top: 7px;
        font-size: 11px;
        line-height: 1.4;
        opacity: .7;
      }

      #${MODAL_ID} .ta-metric-grid {
        display: grid;
        grid-template-columns: repeat(3, minmax(0, 1fr));
        gap: 7px;
        margin-bottom: 10px;
      }

      #${MODAL_ID} .ta-metric-card {
        min-width: 0;
        padding: 9px;
        border: 1px solid #2f2f2f;
        border-radius: 8px;
        background: #161616;
      }

      #${MODAL_ID} .ta-metric-label {
        font-size: 11px;
        text-transform: uppercase;
        letter-spacing: .04em;
        opacity: .55;
      }

      #${MODAL_ID} .ta-metric-value {
        margin-top: 3px;
        font-size: 17px;
        font-weight: 800;
        line-height: 1.1;
        overflow-wrap: anywhere;
      }

      #${MODAL_ID} .ta-metric-note {
        margin-top: 5px;
        font-size: 11px;
        line-height: 1.25;
        opacity: .58;
        overflow-wrap: anywhere;
      }

      #${MODAL_ID} .ta-chart-card {
        margin-top: 8px;
        padding: 9px;
        border: 1px solid #2f2f2f;
        border-radius: 8px;
        background: #141414;
      }

      #${MODAL_ID} .ta-chart-heading {
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        gap: 8px;
        margin-bottom: 8px;
      }

      #${MODAL_ID} .ta-chart-heading span:first-child {
        font-size: 13px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-chart-heading span:last-child {
        text-align: right;
        font-size: 11px;
        opacity: .55;
      }

      #${MODAL_ID} .ta-chart-scroll {
        overflow: hidden;
        padding-bottom: 2px;
      }

      #${MODAL_ID} .ta-chart-columns {
        display: grid;
        align-items: end;
        gap: 4px;
        width: 100%;
        min-width: 0;
        min-height: 126px;
      }

      #${MODAL_ID} .ta-chart-columns-daily,
      #${MODAL_ID} .ta-chart-columns-hourly {
        width: 100%;
        min-width: 0;
      }

      #${MODAL_ID} .ta-chart-column {
        display: flex;
        flex-direction: column;
        justify-content: flex-end;
        min-width: 0;
        height: 132px;
        border-radius: 5px;
        text-align: center;
      }

      #${MODAL_ID} .ta-chart-column[data-ta-detail] {
        cursor: pointer;
        touch-action: manipulation;
      }

      #${MODAL_ID} .ta-chart-column[data-ta-detail]:focus-visible {
        outline: 1px solid #888;
        outline-offset: 1px;
      }

      #${MODAL_ID} .ta-chart-column-active .ta-chart-rail {
        outline: 1px solid #888;
        outline-offset: 1px;
      }

      #${MODAL_ID} .ta-chart-column-partial .ta-chart-rail {
        border: 1px dashed #666;
      }

      #${MODAL_ID} .ta-chart-value {
        min-height: 16px;
        margin-bottom: 3px;
        font-size: 10px;
        opacity: .62;
      }

      #${MODAL_ID} .ta-chart-rail {
        display: flex;
        align-items: flex-end;
        justify-content: center;
        height: 78px;
        overflow: hidden;
        border-radius: 4px;
        background: #1d1d1d;
      }

      #${MODAL_ID} .ta-chart-bar {
        width: 68%;
        min-height: 0;
        border-radius: 3px 3px 0 0;
        background: #999;
      }

      #${MODAL_ID} .ta-chart-label {
        margin-top: 4px;
        font-size: 10px;
        line-height: 1.2;
        white-space: nowrap;
        opacity: .58;
      }

      #${MODAL_ID} .ta-chart-range-label {
        min-height: 25px;
        font-size: 9px;
        white-space: normal;
      }

      #${MODAL_ID} .ta-chart-range-label span {
        display: block;
      }

      #${MODAL_ID} .ta-chart-partial-badge {
        display: block;
        margin-top: 2px;
        font-size: 8px;
        font-weight: 700;
        letter-spacing: .02em;
        text-transform: uppercase;
        opacity: .72;
      }

      #${MODAL_ID} .ta-chart-detail {
        min-height: 20px;
        margin-top: 8px;
        padding: 8px 10px;
        border: 1px solid #292929;
        border-radius: 6px;
        background: #111;
        font-size: 11px;
        line-height: 1.45;
        opacity: .78;
      }

      #${MODAL_ID} .ta-stat-total-controls {
        margin: 0 0 8px;
      }

      #${MODAL_ID} .ta-stat-total-controls label {
        display: grid;
        grid-template-columns: minmax(68px, auto) minmax(0, 1fr);
        align-items: center;
        gap: 8px;
        font-size: 11px;
        opacity: .8;
      }

      #${MODAL_ID} .ta-stat-total-controls select {
        min-height: 34px;
        padding: 6px 8px;
        border: 1px solid #444;
        border-radius: 6px;
        background: #171717;
        color: inherit;
        font: inherit;
      }
      #${MODAL_ID} .ta-stat-gain-scope {
        display: grid;
        gap: 8px;
        margin: 10px 0;
      }

      #${MODAL_ID} .ta-stat-gain-scope-controls {
        display: grid;
        grid-template-columns: repeat(2, minmax(0, 1fr));
        gap: 6px;
      }

      #${MODAL_ID} .ta-stat-gain-scope-controls button {
        min-height: 34px;
        margin: 0;
        padding: 6px 8px;
        border-color: #444;
        font-size: 11px;
        opacity: .7;
      }

      #${MODAL_ID} .ta-stat-gain-scope-controls button.ta-stat-gain-scope-active {
        border-color: #ddd;
        background: #3a3a3a;
        opacity: 1;
      }

      #${MODAL_ID} .ta-stat-gain-primary {
        min-height: 74px;
      }

      #${MODAL_ID} .ta-stat-more-details {
        margin-top: 10px;
      }

      #${MODAL_ID} .ta-stat-total-controls button {
        min-height: 34px;
        margin: 0;
        padding: 6px 8px;
        border-color: #444;
        font-size: 11px;
        opacity: .7;
      }

      #${MODAL_ID} .ta-stat-total-controls button.ta-stat-total-focus-active {
        border-color: #ddd;
        background: #3a3a3a;
        opacity: 1;
      }

      #${MODAL_ID} .ta-stat-total-svg {
        display: block;
        width: 100%;
        height: auto;
        overflow: visible;
      }

      #${MODAL_ID} .ta-stat-total-axis {
        stroke: #555;
        stroke-width: 1;
      }

      #${MODAL_ID} .ta-stat-total-guide {
        stroke: #454545;
        stroke-width: 1;
        stroke-dasharray: 5 5;
      }

      #${MODAL_ID} .ta-stat-total-bar {
        fill: #dba854;
        opacity: .72;
      }

      #${MODAL_ID} .ta-stat-total-line {
        fill: none;
        stroke: #f2f2f2;
        stroke-width: 3;
        stroke-linecap: round;
        stroke-linejoin: round;
      }

      #${MODAL_ID} .ta-stat-total-point {
        fill: #f2f2f2;
        pointer-events: none;
      }

      #${MODAL_ID} .ta-stat-total-hit {
        fill: transparent;
        cursor: pointer;
        touch-action: manipulation;
      }

      #${MODAL_ID} .ta-stat-total-hit:focus-visible {
        fill: rgba(255, 255, 255, .16);
        outline: none;
      }

      #${MODAL_ID} .ta-stat-total-label {
        fill: #aaa;
        font-size: 11px;
      }

      #${MODAL_ID} .ta-stat-total-legend {
        display: flex;
        flex-wrap: wrap;
        gap: 10px;
        margin-top: 4px;
        font-size: 11px;
        opacity: .68;
      }

      #${MODAL_ID} .ta-stat-total-legend span {
        display: inline-flex;
        align-items: center;
        gap: 5px;
      }

      #${MODAL_ID} .ta-stat-total-legend i {
        display: inline-block;
      }

      #${MODAL_ID} .ta-stat-total-line-key {
        width: 16px;
        height: 3px;
        border-radius: 9px;
        background: #f2f2f2;
      }

      #${MODAL_ID} .ta-stat-total-bar-key {
        width: 10px;
        height: 10px;
        border-radius: 2px;
        background: #dba854;
      }

      #${MODAL_ID} .ta-category-list {
        display: grid;
        gap: 8px;
      }

      #${MODAL_ID} .ta-category-topline {
        display: flex;
        justify-content: space-between;
        gap: 10px;
        margin-bottom: 4px;
        font-size: 11px;
      }

      #${MODAL_ID} .ta-category-topline span:first-child {
        min-width: 0;
        overflow: hidden;
        text-overflow: ellipsis;
        white-space: nowrap;
      }

      #${MODAL_ID} .ta-category-topline span:last-child {
        flex: 0 0 auto;
        opacity: .58;
      }

      #${MODAL_ID} .ta-category-track {
        height: 7px;
        overflow: hidden;
        border-radius: 999px;
        background: #222;
      }

      #${MODAL_ID} .ta-category-fill {
        height: 100%;
        border-radius: inherit;
        background: #888;
      }

      #${MODAL_ID} .ta-detail-grid {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 7px;
        margin-top: 8px;
      }

      #${MODAL_ID} .ta-detail-grid > div {
        padding: 8px;
        border: 1px solid #2b2b2b;
        border-radius: 7px;
        background: #131313;
      }

      #${MODAL_ID} .ta-detail-grid span,
      #${MODAL_ID} .ta-detail-grid b {
        display: block;
      }

      #${MODAL_ID} .ta-detail-grid span {
        margin-bottom: 4px;
        font-size: 11px;
        opacity: .5;
      }

      #${MODAL_ID} .ta-detail-grid b {
        font-size: 12px;
        line-height: 1.35;
        overflow-wrap: anywhere;
      }

      #${MODAL_ID} .ta-stat-grid {
        display: grid;
        grid-template-columns: repeat(2, minmax(0, 1fr));
        gap: 8px;
        margin: 10px 0;
      }

      #${MODAL_ID} .ta-stat-card {
        min-width: 0;
        padding: 10px;
        border: 1px solid #303030;
        border-radius: 8px;
        background: #151515;
      }

      #${MODAL_ID} .ta-stat-card-title {
        font-size: 13px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-stat-card-gain {
        margin: 5px 0 9px;
        font-size: 19px;
        font-weight: 800;
        line-height: 1.1;
      }

      #${MODAL_ID} .ta-stat-card-grid {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 7px 10px;
      }

      #${MODAL_ID} .ta-stat-card-grid span,
      #${MODAL_ID} .ta-stat-card-grid b {
        display: block;
      }

      #${MODAL_ID} .ta-stat-card-grid span {
        margin-bottom: 2px;
        font-size: 11px;
        opacity: .55;
      }

      #${MODAL_ID} .ta-stat-card-grid b {
        font-size: 12px;
        line-height: 1.3;
        overflow-wrap: anywhere;
      }

      #${MODAL_ID} .ta-stat-window-grid {
        display: grid;
        grid-template-columns: repeat(3, minmax(0, 1fr));
        gap: 7px;
        margin: 10px 0;
      }

      #${MODAL_ID} .ta-stat-window-card {
        min-width: 0;
        padding: 9px;
        border: 1px solid #2f2f2f;
        border-radius: 8px;
        background: #141414;
      }

      #${MODAL_ID} .ta-stat-window-title {
        font-size: 11px;
        font-weight: 800;
        opacity: .7;
      }

      #${MODAL_ID} .ta-stat-window-gain {
        margin-top: 4px;
        font-size: 16px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-stat-window-note {
        margin-top: 5px;
        font-size: 11px;
        line-height: 1.4;
        opacity: .6;
      }

      #${MODAL_ID} .ta-stat-subsection {
        margin-top: 9px;
        border: 1px solid #2e2e2e;
        border-radius: 8px;
        background: #131313;
      }

      #${MODAL_ID} .ta-stat-subsection > summary {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 10px;
        min-height: 42px;
        padding: 9px 10px;
        cursor: pointer;
        font-size: 12px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-stat-subsection > summary span {
        text-align: right;
        font-size: 11px;
        font-weight: 400;
        opacity: .58;
      }

      #${MODAL_ID} .ta-stat-subsection-body {
        padding: 0 10px 10px;
      }

      #${MODAL_ID} .ta-stat-gym-row {
        padding: 9px 0;
        border-top: 1px solid #292929;
      }

      #${MODAL_ID} .ta-stat-gym-row:first-child {
        border-top: 0;
      }

      #${MODAL_ID} .ta-stat-gym-topline,
      #${MODAL_ID} .ta-stat-gym-values {
        display: flex;
        justify-content: space-between;
        gap: 10px;
      }

      #${MODAL_ID} .ta-stat-gym-topline {
        font-size: 12px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-stat-gym-topline span:last-child,
      #${MODAL_ID} .ta-stat-gym-values span:last-child {
        flex: 0 0 auto;
        text-align: right;
      }

      #${MODAL_ID} .ta-stat-gym-values {
        margin-top: 5px;
        font-size: 11px;
        line-height: 1.35;
        opacity: .68;
      }

      #${MODAL_ID} .ta-stat-gym-note {
        margin-top: 5px;
        font-size: 11px;
        line-height: 1.35;
        opacity: .55;
      }

      #${MODAL_ID} .ta-stat-quality-line {
        margin-top: 6px;
        font-size: 11px;
        line-height: 1.45;
        opacity: .72;
      }

      #${MODAL_ID} .ta-stat-quality-warning {
        border-color: #665;
      }

      #${MODAL_ID} .ta-resource-live-grid,
      #${MODAL_ID} .ta-resource-history-grid {
        display: grid;
        grid-template-columns: repeat(3, minmax(0, 1fr));
        gap: 8px;
      }

      #${MODAL_ID} .ta-resource-live-grid {
        margin-bottom: 6px;
      }

      #${MODAL_ID} .ta-resource-live-card,
      #${MODAL_ID} .ta-resource-history-card,
      #${MODAL_ID} .ta-resource-live-unavailable,
      #${MODAL_ID} .ta-resource-limit-note {
        min-width: 0;
        padding: 10px;
        border: 1px solid #303030;
        border-radius: 8px;
        background: #151515;
      }

      #${MODAL_ID} .ta-resource-live-topline {
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        gap: 8px;
      }

      #${MODAL_ID} .ta-resource-live-topline span,
      #${MODAL_ID} .ta-resource-history-title {
        font-size: 13px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-resource-live-topline b {
        text-align: right;
        font-size: 16px;
      }

      #${MODAL_ID} .ta-resource-live-track {
        height: 9px;
        margin: 9px 0;
        overflow: hidden;
        border-radius: 999px;
        background: #292929;
      }

      #${MODAL_ID} .ta-resource-live-track > div {
        height: 100%;
        border-radius: inherit;
        background: #aaa;
      }

      #${MODAL_ID} .ta-resource-eta {
        font-size: 13px;
        font-weight: 800;
        line-height: 1.35;
      }

      #${MODAL_ID} .ta-resource-rate,
      #${MODAL_ID} .ta-resource-freshness,
      #${MODAL_ID} .ta-resource-live-unavailable span,
      #${MODAL_ID} .ta-resource-limit-note,
      #${MODAL_ID} .ta-resource-empty {
        font-size: 11px;
        line-height: 1.45;
        opacity: .65;
      }

      #${MODAL_ID} .ta-resource-rate {
        margin-top: 5px;
      }

      #${MODAL_ID} .ta-resource-freshness {
        margin-bottom: 10px;
        text-align: right;
      }

      #${MODAL_ID} .ta-resource-live-unavailable {
        margin-bottom: 10px;
      }

      #${MODAL_ID} .ta-resource-live-unavailable b,
      #${MODAL_ID} .ta-resource-live-unavailable span {
        display: block;
      }

      #${MODAL_ID} .ta-resource-live-unavailable span {
        margin-top: 4px;
      }

      #${MODAL_ID} .ta-resource-history-title {
        margin-bottom: 8px;
      }

      #${MODAL_ID} .ta-resource-metric-grid {
        grid-template-columns: repeat(3, minmax(0, 1fr));
      }

      #${MODAL_ID} .ta-resource-metric-gain,
      #${MODAL_ID} .ta-resource-metric-use,
      #${MODAL_ID} .ta-resource-metric-loss {
        box-shadow: inset 0 3px 0 var(--ta-resource-accent);
      }

      #${MODAL_ID} .ta-resource-metric-gain {
        --ta-resource-accent: #72b98e;
      }

      #${MODAL_ID} .ta-resource-metric-use {
        --ta-resource-accent: #d1a05f;
      }

      #${MODAL_ID} .ta-resource-metric-loss {
        --ta-resource-accent: #cf7474;
      }

      #${MODAL_ID} .ta-resource-metric-gain .ta-metric-value,
      #${MODAL_ID} .ta-resource-metric-use .ta-metric-value,
      #${MODAL_ID} .ta-resource-metric-loss .ta-metric-value {
        color: var(--ta-resource-accent);
      }

      #${MODAL_ID} .ta-resource-list-heading {
        display: flex;
        align-items: center;
        gap: 6px;
        margin: 13px 0 7px;
        font-size: 11px;
        font-weight: 800;
        text-transform: uppercase;
        letter-spacing: .03em;
        color: var(--ta-resource-accent, #aaa);
      }

      #${MODAL_ID} .ta-resource-list-heading::before {
        width: 7px;
        height: 7px;
        flex: 0 0 auto;
        border-radius: 999px;
        background: currentColor;
        content: '';
      }

      #${MODAL_ID} .ta-resource-list-heading-gain {
        --ta-resource-accent: #72b98e;
      }

      #${MODAL_ID} .ta-resource-list-heading-use {
        --ta-resource-accent: #d1a05f;
      }

      #${MODAL_ID} .ta-resource-list-heading-loss {
        --ta-resource-accent: #cf7474;
      }

      #${MODAL_ID} .ta-resource-breakdown {
        --ta-resource-accent: #aaa;
      }

      #${MODAL_ID} .ta-resource-breakdown-gain {
        --ta-resource-accent: #72b98e;
      }

      #${MODAL_ID} .ta-resource-breakdown-use {
        --ta-resource-accent: #d1a05f;
      }

      #${MODAL_ID} .ta-resource-breakdown-loss {
        --ta-resource-accent: #cf7474;
      }

      #${MODAL_ID} .ta-resource-breakdown-summary {
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        gap: 8px;
        margin-bottom: 7px;
        font-size: 10px;
        line-height: 1.35;
        opacity: .7;
      }

      #${MODAL_ID} .ta-resource-breakdown-summary b {
        flex: 0 0 auto;
        color: var(--ta-resource-accent);
        font-size: 11px;
      }

      #${MODAL_ID} .ta-resource-breakdown-list {
        display: grid;
        gap: 6px;
      }

      #${MODAL_ID} .ta-resource-breakdown-row {
        display: grid;
        grid-template-columns: 24px minmax(0, 1fr);
        gap: 8px;
        min-width: 0;
        padding: 8px;
        border: 1px solid #292929;
        border-radius: 7px;
        background: #111;
      }

      #${MODAL_ID} .ta-resource-breakdown-rank {
        display: flex;
        align-items: center;
        justify-content: center;
        width: 24px;
        height: 24px;
        border: 1px solid var(--ta-resource-accent);
        border-radius: 999px;
        color: var(--ta-resource-accent);
        font-size: 10px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-resource-breakdown-main {
        min-width: 0;
      }

      #${MODAL_ID} .ta-resource-breakdown-topline {
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        gap: 8px;
      }

      #${MODAL_ID} .ta-resource-breakdown-label {
        min-width: 0;
        overflow: hidden;
        font-size: 11px;
        font-weight: 700;
        line-height: 1.35;
        text-overflow: ellipsis;
        white-space: nowrap;
      }

      #${MODAL_ID} .ta-resource-breakdown-values {
        display: flex;
        flex: 0 0 auto;
        align-items: center;
        gap: 5px;
        font-size: 11px;
      }

      #${MODAL_ID} .ta-resource-breakdown-values > span {
        min-width: 35px;
        padding: 2px 5px;
        border: 1px solid var(--ta-resource-accent);
        border-radius: 999px;
        color: var(--ta-resource-accent);
        text-align: center;
        font-size: 9px;
        font-weight: 800;
      }

      #${MODAL_ID} .ta-resource-breakdown-track {
        height: 5px;
        margin-top: 6px;
        overflow: hidden;
        border-radius: 999px;
        background: #262626;
      }

      #${MODAL_ID} .ta-resource-breakdown-track > div {
        height: 100%;
        min-width: 2px;
        border-radius: inherit;
        background: var(--ta-resource-accent);
      }

      #${MODAL_ID} .ta-resource-breakdown-events {
        margin-top: 4px;
        font-size: 9px;
        line-height: 1.3;
        opacity: .55;
      }

      #${MODAL_ID} .ta-resource-limit-note {
        margin-top: 10px;
      }
      @media(max-width:520px) {

        #${MODAL_ID} .actions,
        #${MODAL_ID} .stats {
          grid-template-columns: 1fr;
        }

        #${MODAL_ID} .ta-metric-grid {
          grid-template-columns: repeat(2, minmax(0, 1fr));
        }

        #${MODAL_ID} .ta-detail-grid {
          grid-template-columns: 1fr;
        }

        #${MODAL_ID} .ta-section-meta {
          max-width: 48%;
        }

        #${MODAL_ID} .ta-stat-grid,
        #${MODAL_ID} .ta-stat-window-grid,
        #${MODAL_ID} .ta-resource-live-grid,
        #${MODAL_ID} .ta-resource-history-grid {
          grid-template-columns: 1fr;
        }

        #${MODAL_ID} .ta-stat-gym-topline,
        #${MODAL_ID} .ta-stat-gym-values {
          align-items: flex-start;
          flex-direction: column;
          gap: 3px;
        }

        #${MODAL_ID} .ta-stat-gym-topline span:last-child,
        #${MODAL_ID} .ta-stat-gym-values span:last-child {
          text-align: left;
        }

        #${MODAL_ID} .ta-resource-breakdown-topline {
          align-items: flex-start;
        }
      }

    `;

    document.head.appendChild(
      style
    );
  }
  // ============================================================
  // MODAL
  // ============================================================

  function shouldRestoreStoredAnalysis(
    restoreState,
    cached,
    analyzeButton
  ) {
    void restoreState;

    return Boolean(
      cached?.account_id &&
      cached.count &&
      analyzeButton &&
      !automaticLogSyncRunning
    );
  }

  function storedHistorySummaryHtml(
    cached
  ) {
    if (
      !cached?.account_id ||
      !cached.count
    ) {
      return '';
    }

    return `
      ${cached.account_name}
      [${cached.account_id}]
      <br>
      ${cached.count.toLocaleString()}
      logs
      <br>
      ${timestampToLocalDate(cached.first_timestamp)}
      →
      ${timestampToLocalDate(cached.last_timestamp)}
    `;
  }

  async function openModal(
    options = {}
  ) {

    if (
      document.getElementById(
        MODAL_ID
      )
    ) {
      return;
    }

    injectStyles();

    const cached =
      await getLastCacheMeta();

    const buildState =
      cached?.account_id
        ? await getBuildState(
            cached.account_id
          )
        : null;

    const savedKey =
      await loadSecureApiKey();

    const modal =
      document.createElement(
        'div'
      );

    modal.id =
      MODAL_ID;

    let historySection;

    if (
      cached?.account_id &&
      cached.count
    ) {

      historySection = `

        <div class="panel">

          <b>
            Stored history
          </b>

          <div
            id="ta-stored-history-summary"
            class="small"
          >
            ${storedHistorySummaryHtml(cached)}
          </div>

        </div>

      `;

    } else {

      historySection = `

        <div class="setup">

          <b>
            Initial setup required
          </b>

          <div class="small">

            No stored history exists on this device yet.

            Your first history build will download your Torn
            personal logs and save each completed section
            immediately.

            After this, future analytics updates will normally
            use the stored history instead of downloading
            everything again.

          </div>

        </div>

      `;
    }

    modal.innerHTML = `

      <div class="card">

        <div class="ta-modal-header">
          <h2>
            Torn Analytics v${VERSION}
          </h2>

          <button
            id="ta-close"
            class="ta-modal-close"
            type="button"
          >
            Close
          </button>
        </div>

        <div class="ta-modal-scroll">

        <div class="sub">

          Your raw Torn log history is stored locally in IndexedDB
          and remains available when the userscript code is replaced
          by future compatible versions.

        </div>

        ${historySection}

        <details class="ta-section ta-settings-section">
          <summary class="ta-section-summary-row">
            <span class="ta-section-title">Settings</span>
            <span class="ta-section-meta">Actions &amp; preferences</span>
          </summary>

          <div class="ta-section-body">
            <div class="ta-settings-group">
              <b>
                Automatic log updates
              </b>

              <div
                id="ta-automatic-sync-status"
                class="small"
              >
                ${automaticLogSyncStatusText(cached)}
              </div>
            </div>

            <div class="ta-settings-group">
              <label class="ta-settings-label" for="ta-key">
                API key
              </label>

              <input
                id="ta-key"
                type="password"
                autocomplete="off"
                value=""
                placeholder="${savedKey ? 'Saved securely — leave blank to reuse' : 'Enter Torn API key'}"
              >
            </div>

            <div class="ta-settings-group">
              ${renderActivityTimeBasisControl()}
            </div>

            <div
              id="ta-main-actions"
              class="actions ta-settings-group"
            >

          ${
            cached?.account_id
              ? `
                <button id="ta-analyze">
                  Analyze Stored Logs
                </button>

                <button id="ta-update">
                  Update Logs
                </button>

                <button
                  id="ta-export-history"
                  style="grid-column:1/-1"
                >
                  Export History JSON
                </button>

                <button
                  id="ta-save-export"
                  style="grid-column:1/-1;display:none"
                >
                  Save Export File
                </button>

                <button
                  id="ta-forensic-history"
                  style="grid-column:1/-1"
                >
                  Run History Diagnostic
                </button>

                <button
                  id="ta-trace-history"
                  style="grid-column:1/-1"
                >
                  Trace Rebuild Collector
                </button>

                <div
                  class="small"
                  style="grid-column:1/-1"
                >
                  Export creates a readable decrypted JSON copy of
                  your Torn history. Keep the file private. The export
                  does not include your API key or Torn Analytics
                  encryption/recovery keys.
                </div>
              `
              : `
                <button
                  id="ta-build"
                  style="grid-column:1/-1"
                >
                  Build My History
                </button>
              `
          }

            </div>

            ${
              cached?.account_id
                ? `
                  <div class="ta-settings-group">
                    <div class="small">
                      Advanced: Rebuild Full History safely recollects the complete
                      history from account creation, verifies it against the current
                      stored generation, then atomically promotes the replacement.
                    </div>

                    <button id="ta-rebuild">
                      Rebuild Full History
                    </button>
                  </div>
                `
                : ''
            }
          </div>
        </details>

        <div class="panel">

          <div class="top">

            <span id="ta-stage">
              Ready
            </span>

            <span id="ta-percent">
              0%
            </span>

          </div>

          <div class="track">

            <div
              id="ta-fill"
              class="fill"
            ></div>

          </div>

          <div
            id="ta-detail"
            class="small"
          >

            ${
              cached?.account_id
                ? 'Stored history is ready.'
                : 'Enter your API key and build your history once.'
            }

          </div>

          <div class="stats">

            <div>
              Logs:
              <b id="ta-logs">
                ${cached?.count?.toLocaleString() ?? '0'}
              </b>
            </div>

            <div>
              ETA:
              <b id="ta-eta">
                —
              </b>
            </div>

            <div>
              Elapsed:
              <b id="ta-elapsed">
                0s
              </b>
            </div>

            <div>
              API requests:
              <b id="ta-requests">
                0
              </b>
            </div>

            <div>
              Range splits:
              <b id="ta-splits">
                0
              </b>
            </div>

          </div>

        </div>

        <div id="ta-status"></div>

        </div>

      </div>
    `;

    document.body.appendChild(
      modal
    );

    const $ =
      selector =>
        modal.querySelector(
          selector
        );

    const keyInput =
      $('#ta-key');

    const closeButton =
      $('#ta-close');

    const scrollContainer =
      $('.ta-modal-scroll');

    const analysisHost =
      $('#ta-status');

    for (
      const button
      of modal.querySelectorAll(
        '[data-ta-time-basis]'
      )
    ) {
      button.addEventListener(
        'click',
        () => {
          const next =
            activityDashboardApplyTimeBasis(
              analysisHost,
              button.getAttribute(
                'data-ta-time-basis'
              )
            );

          for (
            const option
            of modal.querySelectorAll(
              '[data-ta-time-basis]'
            )
          ) {
            const active =
              option.getAttribute(
                'data-ta-time-basis'
              ) === next;

            option.classList.toggle(
              'ta-time-basis-active',
              active
            );

            option.setAttribute(
              'aria-pressed',
              active
                ? 'true'
                : 'false'
            );
          }

          const timeBasisContext =
            modal.querySelector(
              '.ta-settings-section .ta-time-basis-context'
            );

          if (
            timeBasisContext
          ) {
            const localTimezone =
              activityDashboardTimezoneContext(
                new Date(),
                'local'
              );

            timeBasisContext.textContent =
              next === 'tct'
                ? 'TCT uses UTC calendar-day and clock-hour boundaries.'
                : `Device Local uses ${localTimezone.label}.`;
          }
        }
      );
    }

    let pendingHistoryExport =
      null;

    const settingsSection =
      $('.ta-settings-section');

    let restoreAnalysisAfterAutomaticSync =
      Boolean(
        automaticLogSyncRunning &&
        cached?.account_id &&
        cached.count
      );

    function applyAutomaticLogSyncModalState(
      syncRunning = automaticLogSyncRunning
    ) {
      settingsSection?.classList.toggle(
        'ta-automatic-sync-busy',
        syncRunning ===
          true
      );

      settingsSection?.setAttribute(
        'aria-busy',
        syncRunning
          ? 'true'
          : 'false'
      );
    }

    function refreshAutomaticLogSyncStatus(
      meta
    ) {
      const status =
        $('#ta-automatic-sync-status');

      if (
        status
      ) {
        status.textContent =
          automaticLogSyncStatusText(
            meta
          );
      }
    }

    async function refreshStoredHistorySummary() {
      const refreshedCached =
        await getLastCacheMeta();

      const storedHistorySummary =
        $('#ta-stored-history-summary');

      if (
        storedHistorySummary &&
        refreshedCached?.account_id &&
        refreshedCached.count
      ) {
        storedHistorySummary.innerHTML =
          storedHistorySummaryHtml(
            refreshedCached
          );
      }

      refreshAutomaticLogSyncStatus(
        refreshedCached
      );

      modal.dispatchEvent(
        new Event(
          'ta-history-updated'
        )
      );

      return refreshedCached;
    }

    const automaticLogSyncStateListener =
      event => {
        const syncRunning =
          event?.detail?.running ===
          true;

        applyAutomaticLogSyncModalState(
          syncRunning
        );

        refreshAutomaticLogSyncStatus(
          cached
        );

        if (
          syncRunning
        ) {
          return;
        }

        void (async () => {
          const refreshed =
            await refreshStoredHistorySummary();

          refreshAutomaticLogSyncStatus(
            refreshed
          );

          if (
            restoreAnalysisAfterAutomaticSync
          ) {
            restoreAnalysisAfterAutomaticSync =
              false;

            await runStoredAnalysis(
              false,
              null
            );
          }
        })().catch(
          error => {
            console.warn(
              '[Torn Analytics] Could not refresh the modal after automatic synchronization:',
              error
            );
          }
        );
      };

    document.addEventListener(
      AUTOMATIC_LOG_SYNC_STATE_EVENT,
      automaticLogSyncStateListener
    );

    applyAutomaticLogSyncModalState();

    const restoreState =
      options?.restoreState ||
      null;

    markUiModalOpened(
      restoreState
    );

    if (
      scrollContainer
    ) {
      let scrollSavePending = false;

      scrollContainer.addEventListener(
        'scroll',
        () => {
          if (
            scrollSavePending
          ) {
            return;
          }

          scrollSavePending = true;

          requestAnimationFrame(
            () => {
              scrollSavePending = false;
              writeUiSessionState({
                scroll_top: scrollContainer.scrollTop
              });
            }
          );
        },
        { passive: true }
      );
    }

    const tracker =
      new ProgressTracker(
        info => {

          $('#ta-stage')
            .textContent =
            info.stage;

          $('#ta-percent')
            .textContent =
            `${Math.round(info.percent)}%`;

          $('#ta-fill')
            .style.width =
            `${info.percent}%`;

          $('#ta-detail')
            .textContent =
            info.detail ||
            '';

          $('#ta-logs')
            .textContent =
            Number(
              info.logsCollected
            ).toLocaleString();

          $('#ta-eta')
            .textContent =
            info.percent >=
            100
              ? 'Complete'
              : info.eta;

          $('#ta-elapsed')
            .textContent =
            info.elapsed;

          $('#ta-requests')
            .textContent =
            Number(
              info.apiRequests
            ).toLocaleString();

          $('#ta-splits')
            .textContent =
            Number(
              info.splitCount
            ).toLocaleString();
        }
      );

    function setBusy(
      busy
    ) {

      running =
        busy;

      for (
        const button
        of modal.querySelectorAll(
          'button'
        )
      ) {

        if (
          button.id !==
          'ta-close'
        ) {
          button.disabled =
            busy;
        }
      }

      keyInput.disabled =
        busy;

      closeButton.disabled =
        busy;
    }

    async function getApiKey() {

      const enteredKey =
        keyInput.value
          .trim();

      const apiKey =
        enteredKey ||
        await loadSecureApiKey();

      if (
        !apiKey
      ) {

        alert(
          'Enter your Torn API key.'
        );

        return null;
      }

      if (
        enteredKey
      ) {
        await saveSecureApiKey(
          enteredKey
        );
      }

      keyInput.value =
        '';

      return apiKey;
    }

    async function getOptionalApiKey() {
      const enteredKey =
        keyInput.value
          .trim();

      if (
        enteredKey
      ) {
        await saveSecureApiKey(
          enteredKey
        );

        keyInput.value =
          '';

        return enteredKey;
      }

      return await loadSecureApiKey();
    }

    const buildButton =
      $('#ta-build');

    if (
      buildButton
    ) {

      buildButton.onclick =
        async () => {

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          setBusy(
            true
          );

          try {

            const account =
              await detectAccount(
                apiKey,
                tracker
              );

            const existingState =
              await getBuildState(
                account.id
              );

            if (
              existingState
                ?.in_progress
            ) {

              const resume =
                confirm(
                  `An unfinished history build was found.\n\n` +
                  `Completed through: ${existingState.completed_through ?? 'unknown'}\n\n` +
                  `Resume where it left off?`
                );

              if (
                !resume
              ) {

                const restart =
                  confirm(
                    'Start over from account creation instead?'
                  );

                if (
                  !restart
                ) {
                  return;
                }

                await buildHistory(
                  apiKey,
                  tracker,
                  true
                );

              } else {

                await buildHistory(
                  apiKey,
                  tracker,
                  false
                );
              }

            } else {

              await buildHistory(
                apiKey,
                tracker,
                false
              );
            }

            alert(
              'History build complete.\n\n' +
              'Your logs are now saved locally and can be reused by future compatible script updates.'
            );

          } catch (
            error
          ) {

            console.error(
              error
            );

            tracker.setStage(
              'Build interrupted',
              error.message
            );

            alert(
              `History build stopped:\n\n${error.message}\n\n` +
              `Completed segments were already saved. You can resume later.`
            );

          } finally {

            setBusy(
              false
            );
          }
        };
    }

    const analyzeButton =
      $('#ta-analyze');

    async function runStoredAnalysis(
      showCompletionAlert = true,
      restoreScrollTop = null
    ) {
      setBusy(
        true
      );

      try {
        const optionalApiKey =
          await getOptionalApiKey();

        await analyzeStoredLogs(
          tracker,
          optionalApiKey
        );

        await refreshStoredHistorySummary();

        writeUiSessionState({
          analysis_visible: true,
          orientation_refresh_pending: false
        });

        if (
          scrollContainer &&
          restoreScrollTop !== null
        ) {
          requestAnimationFrame(
            () => {
              scrollContainer.scrollTop =
                Math.max(
                  0,
                  Number(restoreScrollTop) ||
                  0
                );
            }
          );
        }

        if (
          showCompletionAlert
        ) {
          alert(
            `${latestLogs.length.toLocaleString()} stored logs analyzed.\n\nNo full export was needed.`
          );
        }

        return true;

      } catch (
        error
      ) {
        writeUiSessionState({
          analysis_visible:
            showCompletionAlert
              ? false
              : true
        });

        tracker.setStage(
          'Analysis failed',
          error.message
        );

        if (
          showCompletionAlert
        ) {
          alert(
            error.message
          );
        } else {
          console.error(
            error
          );
        }

        return false;

      } finally {
        setBusy(
          false
        );
      }
    }

    if (
      analyzeButton
    ) {
      analyzeButton.onclick =
        () =>
          runStoredAnalysis(
            true,
            null
          );
    }

    const updateButton =
      $('#ta-update');

    if (
      updateButton
    ) {

      updateButton.onclick =
        async () => {

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          setBusy(
            true
          );

          try {

            const result =
              await updateLogs(
                apiKey,
                tracker
              );

            await refreshStoredHistorySummary();

            const analysisRefreshed =
              await runStoredAnalysis(
                false,
                null
              );

            alert(
              `Update complete.\n\n` +
              `${result.added.toLocaleString()} new logs added.\n` +
              `${result.logs.length.toLocaleString()} stored total.\n` +
              (
                analysisRefreshed
                  ? 'Dashboard refreshed automatically.'
                  : 'Logs were saved, but the dashboard refresh failed.'
              )
            );

          } catch (
            error
          ) {

            tracker.setStage(
              'Update failed',
              error.message
            );

            alert(
              error.message
            );

          } finally {

            setBusy(
              false
            );
          }
        };
    }

    const exportButton =
      $('#ta-export-history');

    const saveExportButton =
      $('#ta-save-export');

    if (
      exportButton
    ) {
      exportButton.onclick =
        async () => {
          const confirmed =
            confirm(
              'Export History JSON creates a readable decrypted copy of your Torn activity history.\n\n' +
              'Keep this file private. It will not include your Torn API key or Torn Analytics encryption/recovery keys.\n\n' +
              'The export will freshly authenticate your Torn account and bind the filename and manifest to that verified Torn ID.\n\n' +
              'Continue?'
            );

          if (
            !confirmed
          ) {
            return;
          }

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          pendingHistoryExport =
            null;

          if (
            saveExportButton
          ) {
            saveExportButton.style.display =
              'none';
          }

          setBusy(
            true
          );

          try {
            tracker.setStage(
              'Preparing export…',
              'Freshly authenticating your Torn account and verifying protected local history...'
            );

            const result =
              await buildAuthenticatedReadableHistoryExport(
                apiKey,
                tracker
              );

            pendingHistoryExport =
              result;

            if (
              saveExportButton
            ) {
              saveExportButton.style.display =
                '';
            }

            tracker.setStage(
              'Export prepared',
              `${result.record_count.toLocaleString()} logs · Torn ID ${result.account.id} · tap Save Export File`
            );

            alert(
              `History JSON prepared securely.\n\n` +
              `Torn ID: ${result.account.id}\n` +
              `Records: ${result.record_count.toLocaleString()}\n` +
              `Filename: ${result.filename}\n\n` +
              `Tap Save Export File next. iOS should open its share sheet; choose Save to Files.\n\n` +
              `The readable JSON remains in memory only until that save step.`
            );
          } catch (
            error
          ) {
            pendingHistoryExport =
              null;

            tracker.setStage(
              'Export failed',
              error.message
            );

            alert(
              error.message
            );
          } finally {
            setBusy(
              false
            );
          }
        };
    }

    if (
      saveExportButton
    ) {
      saveExportButton.onclick =
        () => {
          const prepared =
            pendingHistoryExport;

          if (
            !prepared
          ) {
            alert(
              'Prepare the history export first.'
            );
            return;
          }

          let sharePromise;

          try {
            // This call must remain directly inside the click handler with no
            // await before it. WebKit requires transient user activation for
            // navigator.share().
            sharePromise =
              sharePreparedHistoryExport(
                prepared
              );
          } catch (
            error
          ) {
            pendingHistoryExport =
              null;
            saveExportButton.style.display =
              'none';

            tracker.setStage(
              'Save failed',
              error.message
            );

            alert(
              error.message
            );
            return;
          }

          pendingHistoryExport =
            null;
          saveExportButton.style.display =
            'none';

          tracker.setStage(
            'iOS share sheet opened',
            'Choose Save to Files to keep the account-bound JSON export.'
          );

          Promise.resolve(
            sharePromise
          ).then(
            receipt => {
              tracker.setStage(
                'Export saved/shared',
                `${receipt.record_count.toLocaleString()} logs · Torn ID ${receipt.account.id}`
              );

              alert(
                `History JSON handed to iOS.\n\n` +
                `Torn ID: ${receipt.account.id}\n` +
                `Records: ${receipt.record_count.toLocaleString()}\n` +
                `Filename: ${receipt.filename}\n\n` +
                `If you chose Save to Files, upload that unchanged JSON for verification.`
              );
            }
          ).catch(
            error => {
              tracker.setStage(
                'Save cancelled or failed',
                error.message
              );

              alert(
                `The prepared export was not saved.\n\n${error.message}`
              );
            }
          );
        };
    }

    const forensicButton =
      $('#ta-forensic-history');

    if (
      forensicButton
    ) {
      forensicButton.onclick =
        async () => {
          const requestedTargetId =
            prompt(
              'Enter the exact Torn log ID to check directly against Torn v2.\n\n' +
              'This diagnostic is read-only and will not modify stored history.',
              ''
            );

          if (
            requestedTargetId ===
            null
          ) {
            return;
          }

          const normalizedTargetId =
            String(
              requestedTargetId
            ).trim();

          if (
            !normalizedTargetId
          ) {
            alert(
              'Enter the exact Torn log ID.'
            );
            return;
          }

          const confirmed =
            confirm(
              `Directly check Torn v2 for log ${normalizedTargetId}?\n\n` +
              'This makes one read-only request for the two-minute window around its stored timestamp. It will not rebuild, replace, merge, delete, or modify stored history.\n\n' +
              'Continue?'
            );

          if (
            !confirmed
          ) {
            return;
          }

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          setBusy(
            true
          );

          try {
            const result =
              await runHistoryForensicWindowCheck(
                apiKey,
                tracker,
                normalizedTargetId
              );

            alert(
              formatHistoryForensicResult(
                result
              )
            );
          } catch (
            error
          ) {
            tracker.setStage(
              'Forensic check failed',
              error.message
            );

            alert(
              `Forensic history check failed:\n\n${error.message}\n\nNo stored history was modified.`
            );
          } finally {
            setBusy(
              false
            );
          }
        };
    }

    const traceButton =
      $('#ta-trace-history');

    if (
      traceButton
    ) {
      traceButton.onclick =
        async () => {
          const requestedTargetId =
            prompt(
              'Enter the exact Torn log ID reported as missing by Full Rebuild.\n\n' +
              'This trace is read-only and will not modify stored history.',
              ''
            );

          if (
            requestedTargetId ===
            null
          ) {
            return;
          }

          const normalizedTargetId =
            String(
              requestedTargetId
            ).trim();

          if (
            !normalizedTargetId
          ) {
            alert(
              'Enter the exact missing Torn log ID.'
            );
            return;
          }

          const confirmed =
            confirm(
              `Trace Full Rebuild for missing log ${normalizedTargetId}?\n\n` +
              'This is read-only. It may make many Torn API requests because it uses the same pagination and defensive splitting path as Full Rebuild, but it will not replace, merge, delete, or modify stored history.\n\n' +
              'Continue?'
            );

          if (
            !confirmed
          ) {
            return;
          }

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          setBusy(
            true
          );

          try {
            const result =
              await runHistoryTargetCollectorTrace(
                apiKey,
                tracker,
                normalizedTargetId
              );

            alert(
              formatHistoryTargetCollectorTrace(
                result
              )
            );
          } catch (
            error
          ) {
            tracker.setStage(
              'Collector trace failed',
              error.message
            );

            alert(
              `Rebuild collector trace failed:\n\n${error.message}\n\nNo stored history was modified.`
            );
          } finally {
            setBusy(
              false
            );
          }
        };
    }

    const rebuildButton =
      $('#ta-rebuild');

    if (
      rebuildButton
    ) {

      rebuildButton.onclick =
        async () => {

          const apiKey =
            await getApiKey();

          if (
            !apiKey
          ) {
            return;
          }

          const confirmed =
            confirm(
              'Full Rebuild will collect a complete replacement from account creation while keeping your current stored history intact.\n\n' +
              'Torn Analytics will replace the stored history only after the replacement is complete and verified. If collection or verification fails, the current stored history stays unchanged.\n\n' +
              'Use this mainly when the collector changes or you intentionally want a complete validation run.\n\n' +
              'Continue?'
            );

          if (
            !confirmed
          ) {
            return;
          }

          setBusy(
            true
          );

          try {

            await buildHistory(
              apiKey,
              tracker,
              true
            );

            await refreshStoredHistorySummary();

            alert(
              'Full history rebuild complete.'
            );

          } catch (
            error
          ) {

            tracker.setStage(
              'Build interrupted',
              error.message
            );

            alert(
              `Build interrupted:\n\n${error.message}\n\n` +
              `Your existing stored history remains intact. No partial rebuild was promoted.`
            );

          } finally {

            setBusy(
              false
            );
          }
        };
    }

    if (
      shouldRestoreStoredAnalysis(
        restoreState,
        cached,
        analyzeButton
      )
    ) {
      tracker.setStage(
        'Restoring dashboard',
        'Loading stored history and refreshing live resources...'
      );

      await runStoredAnalysis(
        false,
        restoreState?.scroll_top ?? null
      );
    } else if (
      scrollContainer &&
      restoreState?.scroll_top
    ) {
      requestAnimationFrame(
        () => {
          scrollContainer.scrollTop =
            Math.max(
              0,
              Number(
                restoreState.scroll_top
              ) ||
              0
            );
        }
      );
    }

    closeButton.onclick =
      () => {

        if (
          running
        ) {
          return;
        }

        writeUiSessionState({
          modal_open: false,
          analysis_visible: false,
          scroll_top: 0,
          orientation_refresh_pending: false
        });

        document.removeEventListener(
          AUTOMATIC_LOG_SYNC_STATE_EVENT,
          automaticLogSyncStateListener
        );

        modal.remove();

        scheduleAutomaticLogSync(
          AUTO_SYNC_INITIAL_DELAY_MS
        );
      };
  }
  // ============================================================
  // HISTORY PROTECTION UI
  // ============================================================

  const openModalWithoutHistoryProtection =
    openModal;

  openModal =
    async function(options = {}) {
      await openModalWithoutHistoryProtection(options);

      const modal =
        document.getElementById(
          MODAL_ID
        );

      if (
        !modal ||
        modal.querySelector(
          '#ta-history-protection-panel'
        )
      ) {
        return;
      }

      const cached =
        await getLastCacheMeta();

      if (
        !cached?.account_id ||
        !cached?.count
      ) {
        return;
      }

      const settingsBody =
        modal.querySelector(
          '.ta-settings-section .ta-section-body'
        );

      if (
        !settingsBody
      ) {
        return;
      }

      const panel =
        document.createElement(
          'div'
        );

      panel.id =
        'ta-history-protection-panel';

      panel.className =
        'ta-settings-group';

      const heading =
        document.createElement(
          'b'
        );

      heading.textContent =
        'Local history protection';

      const detail =
        document.createElement(
          'div'
        );

      detail.className =
        'small';

      detail.style.marginTop =
        '8px';

      const button =
        document.createElement(
          'button'
        );

      button.id =
        'ta-protect-history';

      button.textContent =
        'Protect Stored History';

      button.style.marginTop =
        '10px';

      const verifyButton =
        document.createElement(
          'button'
        );

      verifyButton.id =
        'ta-verify-history-recovery';

      verifyButton.textContent =
        'Verify Recovery';

      verifyButton.style.marginTop =
        '10px';

      panel.appendChild(
        heading
      );

      panel.appendChild(
        detail
      );

      panel.appendChild(
        button
      );

      panel.appendChild(
        verifyButton
      );

      settingsBody.appendChild(
        panel
      );

      async function refreshProtectionPanel() {
        try {
          const verification =
            await verifyHistoryProtectionPersistence();

          if (
            verification.status ===
            'failed'
          ) {
            detail.textContent =
              `Protection unavailable: ${verification.reason || 'verification failed.'}`;

            button.disabled =
              true;

            verifyButton.disabled =
              true;

            return;
          }

          const status =
            await getAccountHistoryProtectionStatus(
              cached.account_id
            );

          if (
            status.complete
          ) {
            detail.textContent =
              `${status.protected.toLocaleString()} stored Torn logs are encrypted at rest. ` +
              'Only account, record identity, and timestamp indexes remain outside the encrypted payload. ' +
              'Recovery verification is non-destructive.';

            button.textContent =
              'Stored History Protected';

            button.disabled =
              true;

            verifyButton.disabled =
              false;

            return;
          }

          if (
            verification.status ===
            'initialized'
          ) {
            detail.textContent =
              'The local encryption key has been initialized. Reopen Torn before migrating existing history so the key can be verified across a fresh userscript run.';

            button.disabled =
              true;

            verifyButton.disabled =
              true;

            return;
          }

          detail.textContent =
            `${status.plaintext.toLocaleString()} of ${status.total.toLocaleString()} stored logs are still plaintext. ` +
            'Protection is resumable; closing the app mid-migration will not invalidate records already completed.';

          button.textContent =
            status.protected > 0
              ? 'Resume History Protection'
              : 'Protect Stored History';

          button.disabled =
            false;

          verifyButton.disabled =
            true;

        } catch (error) {
          detail.textContent =
            `Protection status check failed: ${error.message}`;

          button.disabled =
            true;

          verifyButton.disabled =
            true;
        }
      }

      button.onclick =
        async () => {
          const confirmed =
            confirm(
              'Protect the locally stored Torn log payloads now?\n\n' +
              'This does not rebuild or delete your history. Each plaintext record is encrypted and verified before it replaces that same IndexedDB record. If TornPDA closes midway, the migration can safely resume later.'
            );

          if (
            !confirmed
          ) {
            return;
          }

          const allButtons =
            Array.from(
              modal.querySelectorAll(
                'button'
              )
            );

          for (
            const control
            of allButtons
          ) {
            control.disabled =
              true;
          }

          detail.textContent =
            'Preparing protected-history migration…';

          try {
            const result =
              await migrateAccountHistoryProtection(
                cached.account_id,
                progress => {
                  detail.textContent =
                    `Protecting stored history: ${progress.protected.toLocaleString()} / ${progress.total.toLocaleString()} logs (${Math.round(progress.percent)}%). ` +
                    `${progress.plaintext.toLocaleString()} plaintext records remain.`;
                }
              );

            detail.textContent =
              `${result.total.toLocaleString()} stored Torn logs are protected. ` +
              `${result.migrated.toLocaleString()} records were encrypted during this run.`;

            button.textContent =
              'Stored History Protected';

            alert(
              'Stored history protection complete.\n\n' +
              `${result.total.toLocaleString()} Torn logs are now encrypted at rest.\n` +
              'No history rebuild was required.'
            );

          } catch (error) {
            console.error(
              '[Torn Analytics] History protection migration failed:',
              error
            );

            detail.textContent =
              `History protection stopped safely: ${error.message}`;

            alert(
              'History protection stopped safely.\n\n' +
              `${error.message}\n\n` +
              'Records completed before the interruption remain valid, and remaining plaintext records can be resumed later.'
            );

          } finally {
            for (
              const control
              of allButtons
            ) {
              control.disabled =
                false;
            }

            await refreshProtectionPanel();
          }
        };

      verifyButton.onclick =
        async () => {
          const allButtons =
            Array.from(
              modal.querySelectorAll(
                'button'
              )
            );

          for (
            const control
            of allButtons
          ) {
            control.disabled =
              true;
          }

          detail.textContent =
            'Verifying protected-history recovery envelope…';

          try {
            const apiKey =
              await loadSecureApiKey();

            if (
              !apiKey
            ) {
              throw new Error(
                'No Torn API key is available in this userscript session.'
              );
            }

            const result =
              await verifyAuthenticatedHistoryRecoveryEnvelope(
                apiKey,
                cached.account_id
              );

            if (
              result.status !==
              'verified' ||
              result.changed !==
              false
            ) {
              throw new Error(
                'Recovery verification returned an unexpected result.'
              );
            }

            const nativeKeyPresent =
              result.native_key_present ===
              true
                ? 'Yes'
                : 'No';

            const nativeKeyMatch =
              result.matches_native_key ===
              true
                ? 'Yes'
                : result.matches_native_key ===
                    false
                  ? 'No'
                  : 'Not available';

            alert(
              'Protected-history recovery verified.\n\n' +
              'Recovery envelope: Authenticated\n' +
              `Account binding: ${result.account_id} verified\n` +
              'Canary authentication: Passed\n' +
              `Native history key present: ${nativeKeyPresent}\n` +
              `Recovered key matches native key: ${nativeKeyMatch}\n` +
              `Data changed: ${result.changed ? 'Yes' : 'No'}\n\n` +
              'No encryption keys or Torn logs were changed.'
            );

          } catch (error) {
            console.error(
              '[Torn Analytics] Recovery verification failed:',
              error
            );

            alert(
              'Recovery verification failed.\n\n' +
              `${error.message}\n\n` +
              'No encryption keys or Torn logs were changed.'
            );

          } finally {
            for (
              const control
              of allButtons
            ) {
              control.disabled =
                false;
            }

            await refreshProtectionPanel();
          }
        };

      modal.addEventListener(
        'ta-history-updated',
        () => {
          void refreshProtectionPanel();
        }
      );

      await refreshProtectionPanel();
    };
  // ============================================================
  // PAGE BUTTON
  // ============================================================

  function removeStaleTornAnalyticsUi() {
    for (
      const id
      of [
        MODAL_ID,
        BUTTON_ID,
        STYLE_ID
      ]
    ) {
      const staleNode =
        document.getElementById(
          id
        );

      staleNode?.remove?.();
    }
  }

  function installButton() {

    if (
      document.getElementById(
        BUTTON_ID
      )
    ) {
      return;
    }

    injectStyles();

    const button =
      document.createElement(
        'button'
      );

    button.id =
      BUTTON_ID;

    button.textContent =
      'Torn Analytics';

    button.addEventListener(
      'click',
      openModal
    );

    document.body.appendChild(
      button
    );

    makeFloatingButtonMovable(
      button,
      BUTTON_POSITION_KEY
    );
  }

  const LAUNCHER_BOOT_RETRY_DELAY_MS =
    250;

  const LAUNCHER_BOOT_MAX_ATTEMPTS =
    40;

  let uiModalWasPresent =
    false;

  let uiModalRestorePromise =
    null;

  async function restoreOpenModalAfterDomReplacement(
    restoreState = null
  ) {
    if (
      document.getElementById(
        MODAL_ID
      )
    ) {
      uiModalWasPresent =
        true;

      return true;
    }

    if (
      uiModalRestorePromise
    ) {
      return uiModalRestorePromise;
    }

    const state =
      restoreState ||
      readUiSessionState();

    if (
      !state?.modal_open
    ) {
      return false;
    }

    const operation =
      (async () => {
        await openModal({
          restoreState:
            state
        });

        const restored =
          Boolean(
            document.getElementById(
              MODAL_ID
            )
          );

        uiModalWasPresent =
          restored;

        return restored;
      })();

    uiModalRestorePromise =
      operation;

    try {
      return await operation;
    } catch (error) {
      console.warn(
        '[Torn Analytics] Could not restore the open modal after a page replacement:',
        error
      );

      return false;
    } finally {
      if (
        uiModalRestorePromise ===
        operation
      ) {
        uiModalRestorePromise =
          null;
      }
    }
  }

  function initialize() {

    // The launcher is the recovery path for every other feature. Install it
    // before optional orientation/session restoration so a non-critical
    // startup failure cannot leave Torn Analytics inaccessible.
    removeStaleTornAnalyticsUi();

    installButton();

    let restoreState =
      null;

    try {
      restoreState =
        consumeUiOrientationRestoreState();
    } catch (error) {
      console.warn(
        '[Torn Analytics] Could not restore the prior UI session:',
        error
      );
    }

    if (
      typeof window !==
      'undefined'
    ) {
      window.addEventListener(
        'orientationchange',
        markUiOrientationRefreshPending,
        { passive: true }
      );

      window.addEventListener(
        'pagehide',
        markUiOrientationRefreshPending,
        { passive: true }
      );

      window.addEventListener(
        'resize',
        markUiOrientationRefreshPending,
        { passive: true }
      );
    }

    if (
      restoreState
    ) {
      void restoreOpenModalAfterDomReplacement(
        restoreState
      );
    }

    try {
      installAutomaticLogSyncScheduler();
    } catch (error) {
      // Automatic synchronization is optional. It must never interfere with
      // the launcher or the user's ability to run a manual verified update.
      console.warn(
        '[Torn Analytics] Automatic log synchronization could not be scheduled:',
        error
      );
    }

    if (
      typeof MutationObserver ===
        'function' &&
      document.documentElement
    ) {
      new MutationObserver(
        () => {

          if (
            !document.getElementById(
              BUTTON_ID
            )
          ) {
            try {
              installButton();
            } catch (error) {
              console.warn(
                '[Torn Analytics] Could not restore the launcher after a page update:',
                error
              );
            }
          }

          const modalPresent =
            Boolean(
              document.getElementById(
                MODAL_ID
              )
            );

          if (
            modalPresent
          ) {
            uiModalWasPresent =
              true;
          } else if (
            uiModalWasPresent
          ) {
            // Closing writes modal_open=false before removal, so this only
            // restores a modal that TornPDA removed while the same tab still
            // expected it to be open.
            uiModalWasPresent =
              false;

            void restoreOpenModalAfterDomReplacement();
          }
        }
      ).observe(
        document.documentElement,
        {
          childList:
            true,

          subtree:
            true
        }
      );
    }
  }

  function initializeWhenDocumentReady(
    attempt = 0
  ) {
    const documentReady =
      typeof document !==
        'undefined' &&
      document.documentElement &&
      document.head &&
      document.body;

    if (
      !documentReady
    ) {
      if (
        attempt <
          LAUNCHER_BOOT_MAX_ATTEMPTS &&
        typeof setTimeout ===
          'function'
      ) {
        setTimeout(
          () => {
            initializeWhenDocumentReady(
              attempt + 1
            );
          },
          LAUNCHER_BOOT_RETRY_DELAY_MS
        );
      }

      return;
    }

    try {
      initialize();
    } catch (error) {
      console.warn(
        '[Torn Analytics] Launcher startup was delayed:',
        error
      );

      if (
        !document.getElementById(
          BUTTON_ID
        ) &&
        attempt <
          LAUNCHER_BOOT_MAX_ATTEMPTS &&
        typeof setTimeout ===
          'function'
      ) {
        setTimeout(
          () => {
            initializeWhenDocumentReady(
              attempt + 1
            );
          },
          LAUNCHER_BOOT_RETRY_DELAY_MS
        );
      }
    }
  }

  initializeWhenDocumentReady();

})();
