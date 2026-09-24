// ==UserScript==
// @name         Torn Analytics
// @namespace    chatgpt.openai.com/torn-tools
// @version      2.18.63
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

  const VERSION = '2.18.63';

  // v2.18.63 rejects Happiness checkpoints superseded by later boosters,
  // groups same-window training and point-refill sessions into one observed
  // Happy Jump, and shows completed-jump guidance and recap evidence.
  // Exporting, synchronization, storage, weekly totals, and predictions are unchanged.

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

  // Non-sensitive launcher diagnostics only. Never place API keys, history
  // keys, account data, or log contents in this localStorage record.
  const STARTUP_HEALTH_STORAGE_KEY =
    'tornAnalyticsStartupHealthV1';

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
  // LAUNCHER STARTUP HEALTH
  // ============================================================

  const STARTUP_HEALTH_ERROR_LIMIT =
    500;

  let startupHealthLastStage =
    'script_loaded';

  let startupHealthLastError =
    null;

  let startupHealthLastErrorStage =
    null;

  function normalizeStartupHealthError(
    error
  ) {
    if (
      error === null ||
      error === undefined
    ) {
      return null;
    }

    const message =
      error &&
      typeof error ===
        'object' &&
      typeof error.message ===
        'string'
        ? error.message
        : String(error);

    return message
      .replace(
        /[\r\n\t]+/g,
        ' '
      )
      .replace(
        /([?&]key=)[^&\s]+/gi,
        '$1[redacted]'
      )
      .replace(
        /\b(authorization|api[_\s-]?key)\s*[:=]\s*[^\s,;]+/gi,
        '$1=[redacted]'
      )
      .trim()
      .slice(
        0,
        STARTUP_HEALTH_ERROR_LIMIT
      ) ||
      'Unknown startup error';
  }

  function recordStartupHealth(
    stage,
    error = null
  ) {
    const normalizedStage =
      typeof stage ===
        'string' &&
      stage.trim()
        ? stage
            .trim()
            .slice(
              0,
              80
            )
        : 'unknown';

    startupHealthLastStage =
      normalizedStage;

    const normalizedError =
      normalizeStartupHealthError(
        error
      );

    if (
      normalizedError
    ) {
      startupHealthLastError =
        normalizedError;

      startupHealthLastErrorStage =
        normalizedStage;
    }

    const record = {
      schema_version: 1,
      version: VERSION,
      stage: normalizedStage,
      recorded_at:
        new Date().toISOString(),
      error: normalizedError,
      last_error:
        startupHealthLastError,
      last_error_stage:
        startupHealthLastErrorStage
    };

    try {
      localStorage.setItem(
        STARTUP_HEALTH_STORAGE_KEY,
        JSON.stringify(record)
      );
    } catch (_) {
      // Startup health is optional and must never block the launcher.
    }

    return record;
  }

  function readStartupHealth() {
    try {
      const parsed =
        JSON.parse(
          localStorage.getItem(
            STARTUP_HEALTH_STORAGE_KEY
          ) ||
          'null'
        );

      if (
        !parsed ||
        typeof parsed !==
          'object' ||
        parsed.schema_version !==
          1
      ) {
        return null;
      }

      return {
        schema_version: 1,
        version:
          typeof parsed.version ===
            'string'
            ? parsed.version
                .trim()
                .slice(
                  0,
                  40
                ) ||
              null
            : null,
        stage:
          typeof parsed.stage ===
            'string'
            ? parsed.stage
                .trim()
                .slice(
                  0,
                  80
                ) ||
              null
            : null,
        recorded_at:
          typeof parsed.recorded_at ===
            'string' &&
          Number.isFinite(
            Date.parse(
              parsed.recorded_at
            )
          )
            ? parsed.recorded_at
            : null,
        error:
          typeof parsed.error ===
            'string' &&
          parsed.error.trim()
            ? normalizeStartupHealthError(
                parsed.error
              )
            : null,
        last_error:
          typeof parsed.last_error ===
            'string' &&
          parsed.last_error.trim()
            ? normalizeStartupHealthError(
                parsed.last_error
              )
            : null,
        last_error_stage:
          typeof parsed.last_error_stage ===
            'string'
            ? parsed.last_error_stage
                .trim()
                .slice(
                  0,
                  80
                ) ||
              null
            : null
      };
    } catch (_) {
      return null;
    }
  }

  function launcherStartupFailure(
    stage,
    error
  ) {
    const record =
      recordStartupHealth(
        stage,
        error
      );

    console.warn(
      `[Torn Analytics] Startup stage ${record.stage} failed:`,
      error
    );

    return record;
  }

  function buildReliabilityHealthReport() {
    const startup =
      readStartupHealth();

    let checkpoint =
      null;

    try {
      if (
        typeof readTrainingCheckpointCanaryState ===
          'function'
      ) {
        const state =
          readTrainingCheckpointCanaryState();

        checkpoint = {
          schema_version:
            Number.isSafeInteger(
              state?.schema_version
            )
              ? state.schema_version
              : null,
          status:
            typeof state?.last_status ===
              'string'
              ? state.last_status
              : 'unavailable',
          checkpoints:
            Array.isArray(
              state?.checkpoints
            )
              ? state.checkpoints.length
              : 0,
          train_intents:
            Array.isArray(
              state?.train_intents
            )
              ? state.train_intents.length
              : 0
        };
      }
    } catch (_) {
      checkpoint =
        null;
    }

    return {
      schema_version: 1,
      version:
        VERSION,
      launcher: {
        stage:
          startup?.stage ||
          'unavailable',
        last_issue:
          startup?.last_error ||
          null,
        last_issue_stage:
          startup?.last_error_stage ||
          null
      },
      checkpoint,
      native_bridge:
        'disabled'
    };
  }

  function reliabilityHealthReportText(
    report =
      buildReliabilityHealthReport()
  ) {
    const lines = [
      `Version: ${report?.version || VERSION}`,
      `Launcher: ${report?.launcher?.stage || 'unavailable'}`
    ];

    if (
      report?.launcher?.last_issue
    ) {
      lines.push(
        `Last startup issue: ${report.launcher.last_issue_stage || 'unknown stage'} â€” ${report.launcher.last_issue}`
      );
    } else {
      lines.push(
        'Last startup issue: None recorded for this version.'
      );
    }

    if (
      report?.checkpoint
    ) {
      lines.push(
        `Checkpoint evidence: Schema v${report.checkpoint.schema_version ?? 'unknown'} Â· ${report.checkpoint.checkpoints.toLocaleString()} checkpoints Â· ${report.checkpoint.train_intents.toLocaleString()} train taps`,
        `Checkpoint engine: ${report.checkpoint.status}`
      );
    } else {
      lines.push(
        'Checkpoint evidence: Unavailable â€” optional module did not report.'
      );
    }

    lines.push(
      'TornPDA native bridge: Disabled'
    );

    return lines.join(
      '\n'
    );
  }

  const previousStartupHealth =
    readStartupHealth();

  if (
    previousStartupHealth?.version ===
      VERSION
  ) {
    startupHealthLastError =
      previousStartupHealth.last_error;

    startupHealthLastErrorStage =
      previousStartupHealth.last_error_stage;
  }

  recordStartupHealth(
    'script_loaded'
  );

  function attemptEarlyLauncherInstall() {
    if (
      typeof document ===
        'undefined' ||
      !document.body
    ) {
      return false;
    }

    installButton();

    recordStartupHealth(
      'launcher_installed_early'
    );

    return true;
  }

  try {
    if (
      !attemptEarlyLauncherInstall() &&
      typeof document !==
        'undefined' &&
      typeof document.addEventListener ===
        'function'
    ) {
      document.addEventListener(
        'DOMContentLoaded',
        () => {
          try {
            attemptEarlyLauncherInstall();
          } catch (error) {
            launcherStartupFailure(
              'early_launcher_failed',
              error
            );
          }
        },
        { once: true }
      );
    }
  } catch (error) {
    launcherStartupFailure(
      'early_launcher_failed',
      error
    );
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
    const POSITION_SCHEMA_VERSION = 2;

    let pointerDown = false;
    let dragging = false;
    let savedAnchor = null;

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

      const viewportWidth =
        Number(window.innerWidth);

      const viewportHeight =
        Number(window.innerHeight);

      if (
        !Number.isFinite(
          viewportWidth
        ) ||
        viewportWidth <= 0 ||
        !Number.isFinite(
          viewportHeight
        ) ||
        viewportHeight <= 0
      ) {
        return false;
      }

      const buttonWidth =
        Number.isFinite(
          Number(rect.width)
        )
          ? Math.max(
              0,
              Number(rect.width)
            )
          : 0;

      const buttonHeight =
        Number.isFinite(
          Number(rect.height)
        )
          ? Math.max(
              0,
              Number(rect.height)
            )
          : 0;

      const maxLeft =
        Math.max(
          0,
          viewportWidth -
          buttonWidth
        );

      const maxTop =
        Math.max(
          0,
          viewportHeight -
          buttonHeight
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

      return true;
    }

    function scheduleVisiblePosition(
      left,
      top,
      afterApply = null
    ) {
      const apply =
        () => {
          if (
            applyPosition(
              left,
              top
            ) &&
            typeof afterApply ===
              'function'
          ) {
            afterApply();
          }
        };

      if (
        typeof requestAnimationFrame ===
          'function'
      ) {
        requestAnimationFrame(
          apply
        );
      } else {
        apply();
      }
    }

    function launcherAnchorFromRect(
      rect
    ) {
      const viewportWidth =
        Number(window.innerWidth);
      const viewportHeight =
        Number(window.innerHeight);
      const width =
        Math.max(
          0,
          Number(rect?.width) ||
            0
        );
      const height =
        Math.max(
          0,
          Number(rect?.height) ||
            0
        );
      const maxLeft =
        Math.max(
          0,
          viewportWidth -
            width
        );
      const maxTop =
        Math.max(
          0,
          viewportHeight -
            height
        );

      if (
        !Number.isFinite(
          viewportWidth
        ) ||
        viewportWidth <= 0 ||
        !Number.isFinite(
          viewportHeight
        ) ||
        viewportHeight <= 0
      ) {
        return null;
      }

      return {
        schema_version:
          POSITION_SCHEMA_VERSION,
        x_ratio:
          maxLeft > 0
            ? clamp(
                Number(rect?.left) /
                  maxLeft,
                0,
                1
              )
            : 0.5,
        y_ratio:
          maxTop > 0
            ? clamp(
                Number(rect?.top) /
                  maxTop,
                0,
                1
              )
            : 0
      };
    }

    function applySavedAnchor() {
      if (
        !savedAnchor
      ) {
        return;
      }

      const rect =
        button.getBoundingClientRect();
      const maxLeft =
        Math.max(
          0,
          Number(window.innerWidth) -
            Math.max(
              0,
              Number(rect.width) ||
                0
            )
        );
      const maxTop =
        Math.max(
          0,
          Number(window.innerHeight) -
            Math.max(
              0,
              Number(rect.height) ||
                0
            )
        );

      scheduleVisiblePosition(
        savedAnchor.x_ratio *
          maxLeft,
        savedAnchor.y_ratio *
          maxTop
      );
    }

    function savePosition() {
      const rect =
        button.getBoundingClientRect();
      const anchor =
        launcherAnchorFromRect(
          rect
        );

      if (
        !anchor
      ) {
        return;
      }

      savedAnchor =
        anchor;

      try {
        localStorage.setItem(
          storageKey,
          JSON.stringify({
            ...anchor
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

        const xRatio =
          Number(saved?.x_ratio);
        const yRatio =
          Number(saved?.y_ratio);

        if (
          saved?.schema_version ===
            POSITION_SCHEMA_VERSION &&
          Number.isFinite(xRatio) &&
          xRatio >= 0 &&
          xRatio <= 1 &&
          Number.isFinite(yRatio) &&
          yRatio >= 0 &&
          yRatio <= 1
        ) {
          savedAnchor = {
            schema_version:
              POSITION_SCHEMA_VERSION,
            x_ratio:
              xRatio,
            y_ratio:
              yRatio
          };

          applySavedAnchor();
          return;
        }

        const left =
          Number(saved?.left);

        const top =
          Number(saved?.top);

        if (
          Number.isFinite(left) &&
          Number.isFinite(top)
        ) {
          scheduleVisiblePosition(
            left,
            top,
            savePosition
          );
        } else {
          localStorage.removeItem(
            storageKey
          );
        }
      } catch (error) {
        try {
          localStorage.removeItem(
            storageKey
          );
        } catch (_) {}

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

    const keepButtonVisible =
      () => {
        // Reapply the last user-chosen proportional anchor after TornPDA
        // settles a new viewport. Never persist transient rotation, resize,
        // page-show, or WebView replacement coordinates.
        applySavedAnchor();
      };

    for (
      const eventName
      of [
        'resize',
        'orientationchange',
        'pageshow'
      ]
    ) {
      window.addEventListener(
        eventName,
        keepButtonVisible,
        { passive: true }
      );
    }

    restorePosition();
  }

  function money(value) {
    if (
      value === null ||
      value === undefined ||
      !Number.isFinite(Number(value))
    ) {
      return 'â€”';
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
      return 'Calculatingâ€¦';
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

  async function apiFetchJsonOnce(
    url,
    apiKey,
    tracker = null
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

    await waitForRequestSlot();

    tracker?.incrementRequest();

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
      'Identifying accountâ€¦',
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
      'Loading item namesâ€¦',
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
          ? 'Rebuilding history safelyâ€¦'
          : (
              i === nextSegment &&
              nextSegment > 0
                ? 'Resuming history buildâ€¦'
                : 'Building historyâ€¦'
            ),

        `${segment.from_date} â†’ ${segment.to_date}`
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
        'Verifying rebuilt historyâ€¦',
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
      'Building analyticsâ€¦',
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
      'Updating logsâ€¦',
      `${timestampToLocalDate(overlapStart)} â†’ now`
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
      'Building analyticsâ€¦',
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
      'Loading stored historyâ€¦',
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
      'Analyzing historyâ€¦',
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
          `(${escapeActivityHtml(activity.largest_inactive_gap.start_date)} â†’ ` +
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
          â†’
          ${escapeActivityHtml(activity.last_date)}
          <br>

          <b>Peak day:</b>
          ${escapeActivityHtml(activity.peak_day?.date || 'â€”')}
          â€”
          ${Number(activity.peak_day?.count || 0).toLocaleString()} logs
          <br>

          <b>Peak hour:</b>
          ${escapeActivityHtml(activity.peak_hour?.label || 'â€”')}
          â€”
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
        `${compactStartLabel}â€“${compactEndLabel}`,
      label:
        `${startLabel}â€“${endLabel}`
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
        : 'âˆ’';

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
              ? ` Â· Today Â· partial Â· latest stored log ${partialContext.latest_stored_time}`
              : ' Â· Today Â· partial'
            : '';

        const detail =
          `${activityDashboardLongDate(row.date)} Â· ` +
          `${count.toLocaleString()} logs Â· ` +
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
        ? `${activityDashboardMonthDay(firstRow.date, firstYear !== lastYear)}â€“${activityDashboardMonthDay(lastRow.date, firstYear !== lastYear)}`
        : '';

    const partialHeading =
      partialContext.is_partial_today
        ? ' Â· includes partial today'
        : '';

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Recent activity</span>
          <span>Last ${layout.recent_days} calendar days Â· ${escapeActivityHtml(dateWindow)}${partialHeading}</span>
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
          `${row.range_label} Â· ` +
          `${count.toLocaleString()} logs Â· ` +
          `${Number(row.percent || 0).toFixed(1)}% of all timestamped activity Â· ` +
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
              <span>â€“${escapeActivityHtml(row.compact_range_end_label)}</span>
            </div>
          </div>
        `;
      }).join('');

    return `
      <div class="ta-chart-card">
        <div class="ta-chart-heading">
          <span>Time-of-day profile</span>
          <span>${layout.hour_bucket_hours}-hour buckets Â· ${escapeActivityHtml(timezone.label)}</span>
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
                    ${count.toLocaleString()} Â· ${Number(row.percent || 0).toFixed(1)}%
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

  function activityDashboardCompactModel(
    activity
  ) {
    const rows =
      activityDashboardRecentDays(
        activity,
        7
      );
    const total =
      rows.reduce(
        (
          sum,
          row
        ) =>
          sum +
          Number(
            row?.count ||
            0
          ),
        0
      );
    const activeDays =
      rows.filter(
        row =>
          Number(
            row?.count ||
            0
          ) >
          0
      ).length;
    const busiest =
      rows.reduce(
        (
          best,
          row
        ) =>
          !best ||
          Number(row?.count || 0) >
          Number(best?.count || 0)
            ? row
            : best,
        null
      );
    const categories =
      (
        activity?.categories ||
        []
      )
        .slice(
          0,
          3
        )
        .map(
          row =>
            String(
              row?.name ||
              ''
            ).trim()
        )
        .filter(Boolean);

    return {
      days: 7,
      total,
      active_days:
        activeDays,
      average_per_active_day:
        activeDays
          ? total /
            activeDays
          : 0,
      busiest,
      categories
    };
  }

  function activityDashboardCompactSentence(
    model
  ) {
    const categoryText =
      model?.categories?.length
        ? ` Most activity: ${model.categories.join(', ')}.`
        : '';

    return `Last 7 days: ${Number(model?.total || 0).toLocaleString()} recorded actions across ${Number(model?.active_days || 0).toLocaleString()} active days.${categoryText}`;
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

    const summary =
      activityDashboardCompactModel(
        activity
      );
    const timezone =
      activityDashboardTimezoneContext(
        new Date(),
        activity?.time_basis
      );
    const partialContext =
      activityDashboardPartialTodayContext(
        activity
      );
    const busiestText =
      summary.busiest
        ? `${activityDashboardShortDate(summary.busiest.date)}: ${Number(summary.busiest.count || 0).toLocaleString()}`
        : 'â€”';
    const partialText =
      partialContext.is_partial_today
        ? ' Â· today partial'
        : '';

    return `
      <details class="ta-section ta-activity-section">
        <summary class="ta-section-summary-row">
          <span class="ta-section-title">
            Overall Activity
          </span>
          <span class="ta-section-meta">
            ${Number(activity.total_logs).toLocaleString()} logs Â· ${Number(activity.active_days).toLocaleString()} active days
          </span>
        </summary>

        <div class="ta-section-body ta-activity-compact-body">
          <section class="ta-activity-compact-summary">
            <strong>${escapeActivityHtml(activityDashboardCompactSentence(summary))}</strong>
            <span>
              ${summary.average_per_active_day.toFixed(0)} per active day Â·
              ${Number(activity.longest_active_streak?.days || 0).toLocaleString()}-day streak Â·
              busiest ${escapeActivityHtml(busiestText)}${partialText}
            </span>
          </section>

          <details class="ta-stat-subsection ta-activity-details-section">
            <summary>
              Activity details
              <span>Recent chart &amp; top categories</span>
            </summary>
            <div class="ta-stat-subsection-body ta-activity-details-body">
              ${renderActivityDailyChart(activity)}
              ${renderActivityCategoryBars(activity)}
              <div class="ta-activity-compact-note">
                Stored ${escapeActivityHtml(activity.first_date)} â†’ ${escapeActivityHtml(activity.last_date)} Â·
                ${escapeActivityHtml(timezone.label)}
              </div>
            </div>
          </details>
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

  // Compact display preferences survive TornPDA's fresh-page reopen path.
  // They contain no account data and never restore the modal itself.
  const UI_RESOURCE_PREFERENCES_STORAGE_KEY =
    'tornAnalyticsResourcePreferencesV1';

  const UI_STAT_GROWTH_PREFERENCES_STORAGE_KEY =
    'tornAnalyticsStatGrowthPreferencesV1';

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

  function readResourceDashboardPreferences() {
    try {
      const raw = uiOrientationHandoffStorage()?.getItem(
        UI_RESOURCE_PREFERENCES_STORAGE_KEY
      );
      const parsed = raw ? JSON.parse(raw) : null;
      return {
        resource_dashboard_open: uiSessionOptionalBoolean(parsed?.resource_dashboard_open),
        resource_energy_open: uiSessionOptionalBoolean(parsed?.resource_energy_open),
        resource_nerve_open: uiSessionOptionalBoolean(parsed?.resource_nerve_open),
        resource_happiness_open: uiSessionOptionalBoolean(parsed?.resource_happiness_open)
      };
    } catch (_) {
      return {
        resource_dashboard_open: null,
        resource_energy_open: null,
        resource_nerve_open: null,
        resource_happiness_open: null
      };
    }
  }

  function writeResourceDashboardPreferences(patch = {}) {
    const keys = ['resource_dashboard_open', 'resource_energy_open', 'resource_nerve_open', 'resource_happiness_open'];
    const current = readResourceDashboardPreferences();
    const next = { ...current };
    for (const key of keys) {
      const value = uiSessionOptionalBoolean(patch[key]);
      if (value !== null) next[key] = value;
    }
    if (JSON.stringify(next) === JSON.stringify(current)) return;
    try {
      uiOrientationHandoffStorage()?.setItem(
        UI_RESOURCE_PREFERENCES_STORAGE_KEY,
        JSON.stringify(next)
      );
    } catch (_) {}
  }

  function uiSessionStatView(
    value
  ) {
    return [
      'all',
      'strength',
      'defense',
      'speed',
      'dexterity'
    ].includes(
      value
    )
      ? value
      : 'all';
  }

  function uiSessionStatsWorkspaceView(
    value
  ) {
    return [
      'overview',
      'charts',
      'data'
    ].includes(
      value
    )
      ? value
      : 'overview';
  }

  function readStatGrowthPreferences() {
    try {
      const raw =
        uiOrientationHandoffStorage()?.getItem(
          UI_STAT_GROWTH_PREFERENCES_STORAGE_KEY
        );
      const parsed =
        raw
          ? JSON.parse(
              raw
            )
          : null;

      const legacyFocus =
        [
          parsed?.stat_growth_recent_stat,
          parsed?.stat_growth_details_stat
        ].find(
          value =>
            [
              'strength',
              'defense',
              'speed',
              'dexterity'
            ].includes(
              value
            )
        );

      return {
        stat_growth_focus:
          uiSessionTrainingFocus(
            parsed?.stat_growth_focus ||
            legacyFocus
          ),
        training_summary_stat:
          uiSessionStatView(
            parsed?.training_summary_stat
          ),
        stats_workspace_view:
          uiSessionStatsWorkspaceView(
            parsed?.stats_workspace_view
          )
      };
    } catch (_) {
      return {
        stat_growth_focus:
          'recent',
        training_summary_stat:
          'all',
        stats_workspace_view:
          'overview'
      };
    }
  }

  function writeStatGrowthPreferences(
    patch
  ) {
    const safePatch =
      patch &&
      typeof patch ===
        'object' &&
      !Array.isArray(
        patch
      )
        ? patch
        : {};
    const current =
      readStatGrowthPreferences();
    const next = {
      ...current
    };

    if (
      Object.prototype.hasOwnProperty.call(
        safePatch,
        'stat_growth_focus'
      )
    ) {
      next.stat_growth_focus =
        uiSessionTrainingFocus(
          safePatch.stat_growth_focus
      );
    }

    if (
      Object.prototype.hasOwnProperty.call(
        safePatch,
        'training_summary_stat'
      )
    ) {
      next.training_summary_stat =
        uiSessionStatView(
          safePatch.training_summary_stat
        );
    }

    if (
      Object.prototype.hasOwnProperty.call(
        safePatch,
        'stats_workspace_view'
      )
    ) {
      next.stats_workspace_view =
        uiSessionStatsWorkspaceView(
          safePatch.stats_workspace_view
        );
    }

    if (
      JSON.stringify(next) ===
      JSON.stringify(current)
    ) {
      return next;
    }

    try {
      uiOrientationHandoffStorage()?.setItem(
        UI_STAT_GROWTH_PREFERENCES_STORAGE_KEY,
        JSON.stringify(
          next
        )
      );
    } catch (_) {}

    return next;
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

  function uiSessionStatGrowthContext(
    value
  ) {
    return [
      'happiness_boost_observed',
      'no_happiness_boost_observed'
    ].includes(
      value
    )
      ? value
      : 'all';
  }

  function uiSessionStatGrowthRange(
    value
  ) {
    const normalized =
      String(
        value ??
        ''
      ).toLowerCase();

    if (
      [
        '10s',
        '20s',
        '30s',
        '7d',
        '14d',
        '30d',
        'all'
      ].includes(
        normalized
      )
    ) {
      return normalized;
    }

    // Migrate the earlier numeric session-window preference into the closest
    // supported compact window. Missing or malformed values use the safest
    // uncluttered default.
    const legacySessionLimit =
      Number(
        value
      );

    if (
      legacySessionLimit ===
      30 ||
      legacySessionLimit ===
      60
    ) {
      return '30s';
    }

    return '10s';
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
      stat_growth_context:
        uiSessionStatGrowthContext(
          state.stat_growth_context
        ),
      stat_growth_range:
        uiSessionStatGrowthRange(
          state.stat_growth_range ??
          state.stat_growth_session_limit
        ),
      resource_energy_open:
        uiSessionOptionalBoolean(
          state.resource_energy_open
        ),
      resource_nerve_open:
        uiSessionOptionalBoolean(
          state.resource_nerve_open
        ),
      resource_happiness_open:
        uiSessionOptionalBoolean(
          state.resource_happiness_open
        ),
      resource_dashboard_open:
        uiSessionOptionalBoolean(
          state.resource_dashboard_open
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
        stat_growth_context:
          uiSessionStatGrowthContext(
            parsed.stat_growth_context
          ),
        stat_growth_range:
          uiSessionStatGrowthRange(
            parsed.stat_growth_range ??
            parsed.stat_growth_session_limit
          ),
        resource_energy_open:
          uiSessionOptionalBoolean(
            parsed.resource_energy_open
          ),
        resource_nerve_open:
          uiSessionOptionalBoolean(
            parsed.resource_nerve_open
          ),
        resource_happiness_open:
          uiSessionOptionalBoolean(
            parsed.resource_happiness_open
          ),
        resource_dashboard_open:
          uiSessionOptionalBoolean(
            parsed.resource_dashboard_open
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
      stat_growth_context:
        'all',
      stat_growth_range:
        '10s',
      resource_energy_open:
        null,
      resource_nerve_open:
        null,
      resource_happiness_open:
        null,
      resource_dashboard_open:
        null,
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
        stat_growth_context:
          uiSessionStatGrowthContext(
            parsed.stat_growth_context
          ),
        stat_growth_range:
          uiSessionStatGrowthRange(
            parsed.stat_growth_range ??
            parsed.stat_growth_session_limit
          ),
        resource_energy_open:
          uiSessionOptionalBoolean(
            parsed.resource_energy_open
          ),
        resource_nerve_open:
          uiSessionOptionalBoolean(
            parsed.resource_nerve_open
          ),
        resource_happiness_open:
          uiSessionOptionalBoolean(
            parsed.resource_happiness_open
          ),
        resource_dashboard_open:
          uiSessionOptionalBoolean(
            parsed.resource_dashboard_open
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

    writeResourceDashboardPreferences(patch);

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

  function consumeUiOrientationRestoreState(
    options = {}
  ) {
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

    const unchangedOrientationHandoff =
      !sessionRestore &&
      handoff?.modal_open &&
      handoffFresh &&
      handoff.orientation ===
        orientation;

    // TornPDA/iOS can start the replacement page before WebKit updates
    // innerWidth and innerHeight. Preserve one fresh, otherwise-valid handoff
    // for a bounded second pass instead of rejecting it against stale viewport
    // dimensions. The final pass still fails closed if orientation never
    // changes, so a normal same-orientation tab cannot inherit the modal.
    if (
      options?.defer_unchanged_orientation ===
        true &&
      unchangedOrientationHandoff
    ) {
      return undefined;
    }

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
        ),
      stat_growth_context:
        uiSessionStatGrowthContext(
          source?.stat_growth_context
        ),
      stat_growth_range:
        uiSessionStatGrowthRange(
          source?.stat_growth_range ??
          source?.stat_growth_session_limit
        ),
      resource_energy_open:
        uiSessionOptionalBoolean(
          source?.resource_energy_open
        ),
      resource_nerve_open:
        uiSessionOptionalBoolean(
          source?.resource_nerve_open
        ),
      resource_happiness_open:
        uiSessionOptionalBoolean(
          source?.resource_happiness_open
        ),
      resource_dashboard_open:
        uiSessionOptionalBoolean(
          source?.resource_dashboard_open
        )
    });

    return restoreState;
  }
  // ============================================================
  // PASSIVE TRAINING SNAPSHOTS
  // ============================================================

  const TRAINING_SNAPSHOT_STORAGE_KEY =
    'tornAnalyticsTrainingSnapshotsV1';

  const TRAINING_LIVE_BARS_STORAGE_KEY =
    'tornAnalyticsRecentLiveBarsV1';

  const TRAINING_SNAPSHOT_LIMIT =
    240;

  const TRAINING_SNAPSHOT_MAX_AGE_SECONDS =
    180 * 24 * 60 * 60;

  const TRAINING_SNAPSHOT_MATCH_WINDOW_SECONDS =
    60;

  const TRAINING_LIVE_BARS_MAX_AGE_SECONDS =
    60;

  const TRAINING_LIVE_BARS_REFRESH_INTERVAL_MS =
    15 * 1000;

  const TRAINING_HAPPINESS_WINDOW_SECONDS =
    15 * 60;

  let passiveTrainingSnapshotCaptureInstalled =
    false;

  let passiveTrainingLiveBarsTimer =
    null;

  function trainingSnapshotFiniteNumber(
    value
  ) {
    if (
      value === null ||
      value === undefined ||
      value === ''
    ) {
      return null;
    }

    const normalized =
      String(value)
        .replace(/,/g, '')
        .trim();

    if (
      !/^[+-]?(?:\d+(?:\.\d*)?|\.\d+)$/.test(
        normalized
      )
    ) {
      return null;
    }

    const number =
      Number(normalized);

    return Number.isFinite(
      number
    ) &&
    number >= 0
      ? number
      : null;
  }

  function trainingSnapshotPositiveInteger(
    value
  ) {
    const number =
      trainingSnapshotFiniteNumber(
        value
      );

    return Number.isSafeInteger(
      number
    ) &&
    number > 0
      ? number
      : null;
  }

  function trainingSnapshotValuePair(
    value
  ) {
    const matches =
      String(value || '')
        .match(
          /\d[\d,]*(?:\.\d+)?/g
        ) || [];

    const numbers =
      matches
        .map(
          trainingSnapshotFiniteNumber
        )
        .filter(
          number =>
            number !== null
        );

    return {
      current:
        numbers[0] ??
        null,
      maximum:
        numbers[1] ??
        null
    };
  }

  function trainingSnapshotReadBar(
    barId,
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null
  ) {
    const root =
      documentValue?.getElementById?.(
        barId
      );

    if (
      !root
    ) {
      return {
        current: null,
        maximum: null
      };
    }

    const probes =
      [
        root.querySelector?.(
          '[aria-valuenow], [data-current], [data-value]'
        ),
        root
      ].filter(Boolean);

    for (
      const probe
      of probes
    ) {
      const current =
        trainingSnapshotFiniteNumber(
          probe.getAttribute?.(
            'aria-valuenow'
          ) ??
          probe.getAttribute?.(
            'data-current'
          ) ??
          probe.getAttribute?.(
            'data-value'
          ) ??
          probe.dataset?.current ??
          probe.dataset?.value
        );

      const maximum =
        trainingSnapshotFiniteNumber(
          probe.getAttribute?.(
            'aria-valuemax'
          ) ??
          probe.getAttribute?.(
            'data-maximum'
          ) ??
          probe.getAttribute?.(
            'data-max'
          ) ??
          probe.dataset?.maximum ??
          probe.dataset?.max
        );

      if (
        current !== null
      ) {
        return {
          current,
          maximum
        };
      }
    }

    for (
      const probe
      of probes
    ) {
      const pair =
        trainingSnapshotValuePair(
          probe.textContent
        );

      if (
        pair.current !==
        null
      ) {
        return pair;
      }
    }

    return {
      current: null,
      maximum: null
    };
  }

  function trainingSnapshotStatFromText(
    value
  ) {
    const normalized =
      String(value || '')
        .toLowerCase();

    const matches =
      [
        'strength',
        'defense',
        'speed',
        'dexterity'
      ].filter(
        stat =>
          new RegExp(
            '(^|[^a-z])' +
            stat +
            '([^a-z]|$)'
          ).test(
            normalized
          )
      );

    return matches.length ===
      1
        ? matches[0]
        : null;
  }

  function trainingSnapshotTrainingIntent(
    target
  ) {
    const button =
      target?.closest?.(
        'button, [role="button"], input[type="button"], input[type="submit"], a[href], [data-action]'
      );

    if (
      !button ||
      button.disabled ||
      button.getAttribute?.(
        'aria-disabled'
      ) ===
        'true'
    ) {
      return null;
    }

    const buttonText =
      [
        button.textContent,
        button.getAttribute?.(
          'aria-label'
        ),
        button.getAttribute?.(
          'title'
        ),
        button.getAttribute?.(
          'name'
        ),
        button.getAttribute?.(
          'value'
        )
      ].filter(Boolean)
        .join(' ');

    if (
      !/(^|\s)train(?:ing)?(\s|$)/i.test(
        buttonText
      )
    ) {
      return null;
    }

    let scope =
      button;

    let stat =
      null;

    for (
      let depth = 0;
      scope &&
      depth < 7;
      depth++
    ) {
      stat =
        trainingSnapshotStatFromText(
          [
            scope.getAttribute?.(
              'data-stat'
            ),
            scope.getAttribute?.(
              'name'
            ),
            scope.getAttribute?.(
              'id'
            ),
            scope.getAttribute?.(
              'class'
            ),
            scope.textContent
          ].filter(Boolean)
            .join(' ')
        );

      if (
        stat
      ) {
        break;
      }

      scope =
        scope.parentElement;
    }

    if (
      !stat
    ) {
      return null;
    }

    const trains =
      trainingSnapshotPositiveInteger(
        button.getAttribute?.(
          'data-trains'
        ) ??
        button.getAttribute?.(
          'data-amount'
        ) ??
        scope?.querySelector?.(
          'input[type="number"], input[data-trains], input[name*="train"]'
        )?.value
      );

    const gym =
      trainingSnapshotPositiveInteger(
        button.getAttribute?.(
          'data-gym'
        ) ??
        scope?.getAttribute?.(
          'data-gym'
        )
      );

    return {
      stat,
      trains,
      gym
    };
  }

  function trainingSnapshotIsGymPage(
    locationValue =
      typeof location !== 'undefined'
        ? location
        : null
  ) {
    const pathname =
      String(
        locationValue?.pathname ||
        ''
      )
        .toLowerCase();

    return pathname ===
      '/gym.php' ||
      pathname.endsWith(
        '/gym.php'
      );
  }

  function trainingSnapshotIsGymNavigation(
    target
  ) {
    const href =
      target?.closest?.(
        'a[href]'
      )?.getAttribute?.(
        'href'
      );

    return /(?:^|\/)gym\.php(?:[?#]|$)/i.test(
      String(
        href ||
        ''
      )
    );
  }

  function trainingSnapshotSanitize(
    snapshot
  ) {
    const capturedAt =
      Number(
        snapshot?.captured_at
      );

    if (
      !Number.isSafeInteger(
        capturedAt
      ) ||
      capturedAt <= 0
    ) {
      return null;
    }

    const rawStatus =
      String(
        snapshot?.status ||
        ''
      );

    const energy =
      trainingSnapshotFiniteNumber(
        snapshot?.energy_before
      );

    const happiness =
      trainingSnapshotFiniteNumber(
        snapshot?.happiness_before
      );

    const happinessMaximum =
      trainingSnapshotFiniteNumber(
        snapshot?.happiness_maximum
      );

    const available =
      [
        'exact_live_snapshot',
        'recent_live_snapshot'
      ].includes(
        rawStatus
      ) &&
      energy !== null &&
      happiness !== null &&
      happinessMaximum !== null &&
      happiness <=
        happinessMaximum * 100;

    return {
      id:
        String(
          snapshot?.id ||
          capturedAt
        )
          .slice(0, 120),
      captured_at:
        capturedAt,
      status:
        available
          ? rawStatus
          : 'unavailable',
      energy_before:
        available
          ? energy
          : null,
      happiness_before:
        available
          ? happiness
          : null,
      happiness_maximum:
        available
          ? happinessMaximum
          : null,
      observed_at:
        available &&
        Number.isSafeInteger(
          Number(
            snapshot?.observed_at
          )
        )
          ? Number(
              snapshot.observed_at
            )
          : capturedAt,
      stat:
        [
          'strength',
          'defense',
          'speed',
          'dexterity'
        ].includes(
          snapshot?.stat
        )
          ? snapshot.stat
          : null,
      trains:
        trainingSnapshotPositiveInteger(
          snapshot?.trains
        ),
      gym:
        trainingSnapshotPositiveInteger(
          snapshot?.gym
        ),
      reason:
        available
          ? null
          : String(
              snapshot?.reason ||
              'live_bars_unavailable'
            )
              .slice(0, 80)
    };
  }

  function trainingSnapshotStorage() {
    try {
      return typeof localStorage !==
        'undefined'
        ? localStorage
        : null;
    } catch {
      return null;
    }
  }

  function trainingSnapshotHappinessWindow(
    timestamp
  ) {
    const normalized =
      Number(
        timestamp
      );

    return Number.isSafeInteger(
      normalized
    ) &&
    normalized > 0
      ? Math.floor(
          normalized /
          TRAINING_HAPPINESS_WINDOW_SECONDS
        )
      : null;
  }

  function trainingSnapshotSanitizeLiveBars(
    snapshot
  ) {
    const capturedAt =
      Number(
        snapshot?.captured_at
      );
    const energy =
      trainingSnapshotFiniteNumber(
        snapshot?.energy
      );
    const happiness =
      trainingSnapshotFiniteNumber(
        snapshot?.happiness
      );
    const happinessMaximum =
      trainingSnapshotFiniteNumber(
        snapshot?.happiness_maximum
      );

    if (
      !Number.isSafeInteger(
        capturedAt
      ) ||
      capturedAt <= 0 ||
      energy === null ||
      happiness === null ||
      happinessMaximum === null ||
      happinessMaximum <= 0 ||
      happiness >
        happinessMaximum * 100
    ) {
      return null;
    }

    return {
      captured_at:
        capturedAt,
      energy,
      energy_maximum:
        trainingSnapshotFiniteNumber(
          snapshot?.energy_maximum
        ),
      happiness,
      happiness_maximum:
        happinessMaximum
    };
  }

  function trainingSnapshotReadVisibleLiveBars(
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null,
    nowMilliseconds =
      Date.now()
  ) {
    const energy =
      trainingSnapshotReadBar(
        'barEnergy',
        documentValue
      );
    const happiness =
      trainingSnapshotReadBar(
        'barHappy',
        documentValue
      );

    return trainingSnapshotSanitizeLiveBars({
      captured_at:
        Math.floor(
          Number(
            nowMilliseconds
          ) /
          1000
        ),
      energy:
        energy.current,
      energy_maximum:
        energy.maximum,
      happiness:
        happiness.current,
      happiness_maximum:
        happiness.maximum
    });
  }

  function trainingSnapshotDetectableControls(
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null
  ) {
    if (
      !documentValue?.querySelectorAll
    ) {
      return [];
    }

    const controls =
      Array.from(
        documentValue.querySelectorAll(
          'button, [role="button"], input[type="button"], input[type="submit"], a[href], [data-action]'
        ) ||
        []
      )
        .slice(
          0,
          750
        );

    return controls
      .map(
        control => ({
          control,
          intent:
            trainingSnapshotTrainingIntent(
              control
            )
        })
      )
      .filter(
        candidate =>
          Boolean(
            candidate.intent
          )
      );
  }

  function trainingSnapshotCapabilityProbe(
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null,
    locationValue =
      typeof location !== 'undefined'
        ? location
        : null,
    nowMilliseconds =
      Date.now(),
    listenerInstalled =
      typeof passiveTrainingSnapshotCaptureInstalled !==
        'undefined' &&
      passiveTrainingSnapshotCaptureInstalled ===
        true
  ) {
    const energyRootFound =
      Boolean(
        documentValue?.getElementById?.(
          'barEnergy'
        )
      );
    const happinessRootFound =
      Boolean(
        documentValue?.getElementById?.(
          'barHappy'
        )
      );
    const visibleBars =
      trainingSnapshotReadVisibleLiveBars(
        documentValue,
        nowMilliseconds
      );
    const gymPage =
      trainingSnapshotIsGymPage(
        locationValue
      );
    const controls =
      gymPage
        ? trainingSnapshotDetectableControls(
            documentValue
          )
        : [];
    const barsReady =
      Boolean(
        visibleBars
      );
    const controlsReady =
      gymPage &&
      controls.length > 0;

    return {
      checked_at:
        Math.floor(
          Number(
            nowMilliseconds
          ) /
          1000
        ),
      listener:
        listenerInstalled
          ? 'ready'
          : 'not_active',
      page:
        gymPage
          ? 'gym'
          : 'other',
      resource_bars:
        barsReady
          ? 'ready'
          : 'not_readable',
      energy_root:
        energyRootFound
          ? 'found'
          : 'not_found',
      happiness_root:
        happinessRootFound
          ? 'found'
          : 'not_found',
      energy:
        barsReady
          ? visibleBars.energy
          : null,
      happiness:
        barsReady
          ? visibleBars.happiness
          : null,
      happiness_maximum:
        barsReady
          ? visibleBars.happiness_maximum
          : null,
      gym_controls:
        gymPage
          ? controlsReady
            ? 'ready'
            : 'not_detected'
          : 'open_gym_to_check',
      gym_control_count:
        controls.length,
      result:
        !listenerInstalled
          ? 'listener_not_active'
          : !barsReady
            ? 'resource_bars_blocked'
            : !gymPage
              ? 'resource_access_confirmed'
              : controlsReady
                ? 'capture_access_confirmed'
                : 'gym_controls_blocked'
    };
  }

  function trainingSnapshotCapabilityText(
    probe
  ) {
    const listenerText =
      probe?.listener ===
        'ready'
        ? 'Ready'
        : 'Not active';
    const barsText =
      probe?.resource_bars ===
        'ready'
        ? `Ready â€” Energy ${Number(probe.energy).toLocaleString()} Â· Happiness ${Number(probe.happiness).toLocaleString()} / ${Number(probe.happiness_maximum).toLocaleString()}`
        : `Not readable â€” #barEnergy ${probe?.energy_root === 'found' ? 'found' : 'missing'} Â· #barHappy ${probe?.happiness_root === 'found' ? 'found' : 'missing'}`;
    const gymText =
      probe?.gym_controls ===
        'ready'
        ? `Ready â€” ${Number(probe.gym_control_count).toLocaleString()} supported training control${Number(probe.gym_control_count) === 1 ? '' : 's'} detected`
        : probe?.gym_controls ===
            'open_gym_to_check'
          ? 'Open the Gym and run this check again; no training is required.'
          : 'Not detected on the Gym page.';
    const resultText =
      probe?.result ===
        'capture_access_confirmed'
        ? 'CONFIRMED â€” the required page access is available.'
        : probe?.result ===
            'resource_access_confirmed'
          ? 'PARTIAL â€” resource access works; check once more on the Gym page.'
          : 'BLOCKED â€” the result identifies which page access is missing.';

    return [
      `Capture listener: ${listenerText}`,
      `Displayed resource bars: ${barsText}`,
      `Gym controls: ${gymText}`,
      `Result: ${resultText}`
    ].join(
      '\n'
    );
  }

  function writeTrainingSnapshotLiveBars(
    snapshot
  ) {
    const safe =
      trainingSnapshotSanitizeLiveBars(
        snapshot
      );

    if (
      !safe
    ) {
      return null;
    }

    try {
      trainingSnapshotStorage()?.setItem(
        TRAINING_LIVE_BARS_STORAGE_KEY,
        JSON.stringify(
          safe
        )
      );
    } catch {
      // Live checkpoints are optional and must never interrupt Torn.
    }

    return safe;
  }

  function readTrainingSnapshotLiveBars(
    nowSeconds =
      Math.floor(
        Date.now() /
        1000
      )
  ) {
    try {
      const safe =
        trainingSnapshotSanitizeLiveBars(
          JSON.parse(
            trainingSnapshotStorage()?.getItem(
              TRAINING_LIVE_BARS_STORAGE_KEY
            ) ||
            'null'
          )
        );

      if (
        !safe
      ) {
        return null;
      }

      const age =
        Number(
          nowSeconds
        ) -
        safe.captured_at;

      if (
        age < 0 ||
        age >
          TRAINING_LIVE_BARS_MAX_AGE_SECONDS ||
        trainingSnapshotHappinessWindow(
          safe.captured_at
        ) !==
          trainingSnapshotHappinessWindow(
            Number(
              nowSeconds
            )
          )
      ) {
        return null;
      }

      return safe;
    } catch {
      return null;
    }
  }

  function refreshPassiveTrainingLiveBars(
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null,
    nowMilliseconds =
      Date.now()
  ) {
    return writeTrainingSnapshotLiveBars(
      trainingSnapshotReadVisibleLiveBars(
        documentValue,
        nowMilliseconds
      )
    );
  }

  function readTrainingSnapshots(
    nowSeconds =
      Math.floor(
        Date.now() /
        1000
      )
  ) {
    try {
      const parsed =
        JSON.parse(
          trainingSnapshotStorage()?.getItem(
            TRAINING_SNAPSHOT_STORAGE_KEY
          ) ||
          '[]'
        );

      if (
        !Array.isArray(
          parsed
        )
      ) {
        return [];
      }

      const minimumTimestamp =
        Number(nowSeconds) -
        TRAINING_SNAPSHOT_MAX_AGE_SECONDS;

      return parsed
        .map(
          trainingSnapshotSanitize
        )
        .filter(
          snapshot =>
            snapshot &&
            snapshot.captured_at >=
              minimumTimestamp
        )
        .slice(
          -TRAINING_SNAPSHOT_LIMIT
        );
    } catch {
      return [];
    }
  }

  function writeTrainingSnapshots(
    snapshots,
    nowSeconds =
      Math.floor(
        Date.now() /
        1000
      )
  ) {
    const minimumTimestamp =
      Number(nowSeconds) -
      TRAINING_SNAPSHOT_MAX_AGE_SECONDS;

    const safe =
      (
        Array.isArray(
          snapshots
        )
          ? snapshots
          : []
      )
        .map(
          trainingSnapshotSanitize
        )
        .filter(
          snapshot =>
            snapshot &&
            snapshot.captured_at >=
              minimumTimestamp
        )
        .sort(
          (
            left,
            right
          ) =>
            left.captured_at -
              right.captured_at ||
            left.id.localeCompare(
              right.id
            )
        )
        .slice(
          -TRAINING_SNAPSHOT_LIMIT
        );

    try {
      trainingSnapshotStorage()?.setItem(
        TRAINING_SNAPSHOT_STORAGE_KEY,
        JSON.stringify(
          safe
        )
      );
    } catch {
      // Snapshot capture is optional and must never interrupt Torn training.
    }

    return safe;
  }

  function trainingSnapshotBuildCapture(
    event,
    documentValue =
      typeof document !== 'undefined'
        ? document
        : null,
    locationValue =
      typeof location !== 'undefined'
        ? location
        : null,
    nowMilliseconds =
      Date.now(),
    recentLiveBars =
      readTrainingSnapshotLiveBars(
        Math.floor(
          Number(
            nowMilliseconds
          ) /
          1000
        )
      )
  ) {
    if (
      !trainingSnapshotIsGymPage(
        locationValue
      )
    ) {
      return null;
    }

    const intent =
      trainingSnapshotTrainingIntent(
        event?.target
      );

    if (
      !intent
    ) {
      return null;
    }

    const visible =
      trainingSnapshotReadVisibleLiveBars(
        documentValue,
        nowMilliseconds
      );

    const capturedAt =
      Math.floor(
        Number(nowMilliseconds) /
        1000
      );

    const exact =
      Number.isSafeInteger(
        capturedAt
      ) &&
      capturedAt > 0 &&
      Boolean(
        visible
      );

    const recentCandidate =
      exact
        ? null
        : trainingSnapshotSanitizeLiveBars(
            recentLiveBars
          );

    const recentAge =
      recentCandidate
        ? capturedAt -
          recentCandidate.captured_at
        : null;

    const recent =
      recentCandidate &&
      recentAge >= 0 &&
      recentAge <=
        TRAINING_LIVE_BARS_MAX_AGE_SECONDS &&
      trainingSnapshotHappinessWindow(
        recentCandidate.captured_at
      ) ===
        trainingSnapshotHappinessWindow(
          capturedAt
        )
        ? recentCandidate
        : null;

    const available =
      visible ||
      recent;

    return trainingSnapshotSanitize({
      id:
        capturedAt +
        '-' +
        intent.stat +
        '-' +
        String(
          Math.random()
        )
          .slice(2, 12),
      captured_at:
        capturedAt,
      status:
        exact
          ? 'exact_live_snapshot'
          : recent
            ? 'recent_live_snapshot'
          : 'unavailable',
      energy_before:
        available?.energy,
      happiness_before:
        available?.happiness,
      happiness_maximum:
        available?.happiness_maximum,
      observed_at:
        available?.captured_at,
      stat:
        intent.stat,
      trains:
        intent.trains,
      gym:
        intent.gym,
      reason:
        exact
          ? null
          : 'live_bars_unavailable'
    });
  }

  function capturePassiveTrainingSnapshot(
    event
  ) {
    const currentLiveBars =
      refreshPassiveTrainingLiveBars();

    const snapshot =
      trainingSnapshotBuildCapture(
        event,
        typeof document !==
          'undefined'
          ? document
          : null,
        typeof location !==
          'undefined'
          ? location
          : null,
        Date.now(),
        currentLiveBars ||
          readTrainingSnapshotLiveBars()
      );

    if (
      !snapshot
    ) {
      if (
        trainingSnapshotIsGymNavigation(
          event?.target
        )
      ) {
        return capturePassiveTrainingFallbackCheckpoint(
          Date.now(),
          currentLiveBars ||
            readTrainingSnapshotLiveBars()
        );
      }

      return null;
    }

    writeTrainingSnapshots(
      [
        ...readTrainingSnapshots(
          snapshot.captured_at
        ),
        snapshot
      ],
      snapshot.captured_at
    );

    return snapshot;
  }

  function trainingSnapshotBuildFallbackCheckpoint(
    nowMilliseconds =
      Date.now(),
    liveBars =
      readTrainingSnapshotLiveBars(
        Math.floor(
          Number(
            nowMilliseconds
          ) /
          1000
        )
      )
  ) {
    const safeBars =
      trainingSnapshotSanitizeLiveBars(
        liveBars
      );
    const capturedAt =
      Math.floor(
        Number(
          nowMilliseconds
        ) /
        1000
      );

    if (
      !safeBars ||
      !Number.isSafeInteger(
        capturedAt
      ) ||
      capturedAt <= 0 ||
      capturedAt -
        safeBars.captured_at < 0 ||
      capturedAt -
        safeBars.captured_at >
          TRAINING_LIVE_BARS_MAX_AGE_SECONDS ||
      trainingSnapshotHappinessWindow(
        safeBars.captured_at
      ) !==
        trainingSnapshotHappinessWindow(
          capturedAt
        )
    ) {
      return null;
    }

    return trainingSnapshotSanitize({
      id:
        'checkpoint-' +
        capturedAt +
        '-' +
        String(
          Math.random()
        )
          .slice(2, 12),
      captured_at:
        capturedAt,
      observed_at:
        safeBars.captured_at,
      status:
        'recent_live_snapshot',
      energy_before:
        safeBars.energy,
      happiness_before:
        safeBars.happiness,
      happiness_maximum:
        safeBars.happiness_maximum
    });
  }

  function capturePassiveTrainingFallbackCheckpoint(
    nowMilliseconds =
      Date.now(),
    liveBars =
      refreshPassiveTrainingLiveBars() ||
      readTrainingSnapshotLiveBars()
  ) {
    const checkpoint =
      trainingSnapshotBuildFallbackCheckpoint(
        nowMilliseconds,
        liveBars
      );

    if (
      !checkpoint
    ) {
      return null;
    }

    const existing =
      readTrainingSnapshots(
        checkpoint.captured_at
      );

    const duplicate =
      existing.find(
        snapshot =>
          snapshot.status ===
            'recent_live_snapshot' &&
          Math.abs(
            snapshot.captured_at -
            checkpoint.captured_at
          ) <= 2 &&
          snapshot.energy_before ===
            checkpoint.energy_before &&
          snapshot.happiness_before ===
            checkpoint.happiness_before
      );

    if (
      duplicate
    ) {
      return duplicate;
    }

    writeTrainingSnapshots(
      [
        ...existing,
        checkpoint
      ],
      checkpoint.captured_at
    );

    return checkpoint;
  }

  function installPassiveTrainingSnapshotCapture() {
    if (
      passiveTrainingSnapshotCaptureInstalled ||
      typeof document ===
        'undefined' ||
      !document.addEventListener
    ) {
      return false;
    }

    document.addEventListener(
      'click',
      capturePassiveTrainingSnapshot,
      true
    );

    const refresh =
      () => {
        if (
          typeof document !==
            'undefined' &&
          document.visibilityState !==
            'hidden'
        ) {
          refreshPassiveTrainingLiveBars();
        }
      };

    document.addEventListener(
      'visibilitychange',
      refresh,
      { passive: true }
    );

    if (
      typeof window !==
        'undefined'
    ) {
      window.addEventListener(
        'pageshow',
        refresh,
        { passive: true }
      );

      window.addEventListener(
        'pagehide',
        () => {
          capturePassiveTrainingFallbackCheckpoint();
        },
        { passive: true }
      );
    }

    refresh();

    if (
      passiveTrainingLiveBarsTimer ===
        null &&
      typeof setInterval ===
        'function'
    ) {
      passiveTrainingLiveBarsTimer =
        setInterval(
          refresh,
          TRAINING_LIVE_BARS_REFRESH_INTERVAL_MS
        );
    }

    passiveTrainingSnapshotCaptureInstalled =
      true;

    return true;
  }

  function trainingSnapshotAttachToActions(
    actions,
    snapshots =
      readTrainingSnapshots()
  ) {
    const safeSnapshots =
      (
        Array.isArray(
          snapshots
        )
          ? snapshots
          : []
      )
        .map(
          trainingSnapshotSanitize
        )
        .filter(
          snapshot =>
            [
              'exact_live_snapshot',
              'recent_live_snapshot'
            ].includes(
              snapshot?.status
            )
        );

    const used =
      new Set();

    for (
      const action
      of Array.isArray(
        actions
      )
        ? actions
        : []
    ) {
      const actionTimestamp =
        Number(
          action?.timestamp
        );

      if (
        !Number.isSafeInteger(
          actionTimestamp
        ) ||
        actionTimestamp <= 0
      ) {
        continue;
      }

      const candidates =
        safeSnapshots
          .filter(
            snapshot => {
              if (
                used.has(
                  snapshot.id
                )
              ) {
                return false;
              }

              const secondsAfterCapture =
                actionTimestamp -
                snapshot.captured_at;

              if (
                secondsAfterCapture <
                  -2 ||
                secondsAfterCapture >
                  TRAINING_SNAPSHOT_MATCH_WINDOW_SECONDS
              ) {
                return false;
              }

              if (
                snapshot.stat &&
                snapshot.stat !==
                  action?.stat
              ) {
                return false;
              }

              if (
                snapshot.trains &&
                snapshot.trains !==
                  Number(
                    action?.trains
                  )
              ) {
                return false;
              }

              if (
                snapshot.gym &&
                snapshot.gym !==
                  Number(
                    action?.gym
                  )
              ) {
                return false;
              }

              return Number(
                snapshot.energy_before
              ) >=
                Number(
                  action?.energy_used ||
                  0
                );
            }
          )
          .sort(
            (
              left,
              right
            ) =>
              Math.abs(
                actionTimestamp -
                left.captured_at
              ) -
              Math.abs(
                actionTimestamp -
                right.captured_at
              ) ||
              (
                left.status ===
                  'exact_live_snapshot'
                  ? 0
                  : 1
              ) -
              (
                right.status ===
                  'exact_live_snapshot'
                  ? 0
                  : 1
              ) ||
              right.captured_at -
                left.captured_at
          );

      const match =
        candidates[0];

      if (
        !match
      ) {
        action.live_snapshot = {
          status:
            'unavailable'
        };

        continue;
      }

      used.add(
        match.id
      );

      action.live_snapshot = {
        status:
          match.status,
        captured_at:
          match.captured_at,
        observed_at:
          match.observed_at,
        seconds_before_log:
          Math.max(
            0,
            actionTimestamp -
              match.captured_at
          ),
        energy_before:
          match.energy_before,
        happiness_before:
          match.happiness_before,
        happiness_maximum:
          match.happiness_maximum
      };
    }

    return actions;
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

  function inspectJobSpecialStrengthLog(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );

    if (
      logId !== 6400
    ) {
      return {
        recognized: false,
        valid: false,
        reason: 'not_job_special_strength',
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

    const jobPointsUsed =
      statGrowthPositiveInteger(
        data.job_points_used
      );

    if (
      jobPointsUsed === null
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_job_points_used',
        record: null
      };
    }

    const jobPointsBalance =
      statGrowthOptionalNonNegativeInteger(
        data.job_points
      );

    if (
      jobPointsBalance === null
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_job_points_balance',
        record: null
      };
    }

    const strengthBefore =
      statGrowthFiniteNumber(
        data.strength_before
      );
    const strengthAfter =
      statGrowthFiniteNumber(
        data.strength_after
      );
    const strengthIncreased =
      statGrowthFiniteNumber(
        data.strength_increased
      );

    if (
      strengthBefore === null ||
      strengthBefore < 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_strength_before',
        record: null
      };
    }

    if (
      strengthAfter === null ||
      strengthAfter < 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_strength_after',
        record: null
      };
    }

    if (
      strengthIncreased === null ||
      strengthIncreased <= 0
    ) {
      return {
        recognized: true,
        valid: false,
        reason: 'invalid_strength_increase',
        record: null
      };
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
          6400,
        title:
          String(
            log?.title ??
            ''
          ),
        category:
          String(
            log?.category ??
            ''
          ),
        timestamp,
        stat:
          'strength',
        stat_label:
          'Strength',
        job_points_used:
          jobPointsUsed,
        job_points_balance:
          jobPointsBalance,
        strength_before:
          strengthBefore,
        strength_after:
          strengthAfter,
        stat_increased:
          strengthIncreased
      }
    };
  }

  function inspectNonGymStatGainCandidate(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );

    if (
      !Number.isSafeInteger(
        logId
      ) ||
      logId === 6400 ||
      gymTrainingSpec(
        logId
      )
    ) {
      return null;
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
      return null;
    }

    const data =
      log?.data;

    if (
      !data ||
      typeof data !== 'object' ||
      Array.isArray(data)
    ) {
      return null;
    }

    const title =
      String(
        log?.title ??
        ''
      ).trim();
    const category =
      String(
        log?.category ??
        ''
      ).trim();
    const metadata =
      `${category} ${title}`;
    const hasJobMetadata =
      /\b(?:army|job|special)\b/i.test(
        metadata
      );
    const hasStatMetadata =
      /\b(?:strength|defen[cs]e|speed|dexterity)\b/i.test(
        metadata
      );
    const fields =
      [];
    const dataEntries =
      Object.entries(
        data
      );
    const hasStatDescriptor =
      dataEntries.some(
        ([
          rawName,
          rawValue
        ]) =>
          (
            /^(?:stat|battle_stat|stat_type|type|name)$/i.test(
              String(
                rawName
              )
            ) ||
            hasJobMetadata
          ) &&
          /^(?:strength|defen[cs]e|speed|dexterity)$/i.test(
            String(
              rawValue
            ).trim()
          )
      );
    let hasStatField =
      hasStatMetadata;
    let hasJobPointField = false;

    for (
      const [
        rawName,
        rawValue
      ]
      of dataEntries
    ) {
      const name =
        String(
          rawName
        );
      const normalizedName =
        name
          .toLowerCase()
          .replace(
            /[^a-z0-9]+/g,
            '_'
          );
      const isStatField =
        /(?:^|_)(?:strength|defen[cs]e|speed|dexterity)(?:_|$)/.test(
          normalizedName
        ) ||
        (
          /^(?:stat|battle_stat|stat_type|type|name)$/.test(
            normalizedName
          ) &&
          /^(?:strength|defen[cs]e|speed|dexterity)$/i.test(
            String(
              rawValue
            ).trim()
          )
        );
      const isRelatedGainField =
        (
          hasStatDescriptor ||
          hasStatMetadata
        ) &&
        /(?:^|_)(?:amount|value|result|change|gain|gained|increase|increased|before|after)(?:_|$)/.test(
          normalizedName
        );
      const isJobPointField =
        /(?:job|army).*points?|points?.*(?:job|army|used|spent|cost)/.test(
          normalizedName
        );

      if (
        !isStatField &&
        !isJobPointField &&
        !isRelatedGainField
      ) {
        continue;
      }

      const valueType =
        typeof rawValue;

      if (
        ![
          'number',
          'string',
          'boolean'
        ].includes(
          valueType
        ) ||
        (
          valueType === 'number' &&
          !Number.isFinite(
            rawValue
          )
        )
      ) {
        continue;
      }

      hasStatField ||= isStatField;
      hasJobPointField ||= isJobPointField;
      fields.push({
        name,
        value:
          String(
            rawValue
          ).slice(
            0,
            120
          )
      });
    }

    if (
      !hasStatField ||
      (
        !hasJobMetadata &&
        !hasJobPointField
      )
    ) {
      return null;
    }

    return {
      id:
        String(
          log?.id ??
          ''
        ),
      log_id:
        logId,
      title,
      category,
      timestamp,
      fields:
        fields.slice(
          0,
          12
        )
    };
  }

  function statGrowthHappinessBoostSource(
    logId
  ) {
    switch (
      Number(
        logId
      )
    ) {
      case 2020:
        return 'Candy';

      case 2180:
        return 'Erotic DVD';

      case 2210:
        return 'Ecstasy';

      case 2280:
        return 'Vicodin';

      default:
        return null;
    }
  }

  function statGrowthHappinessBoostEvent(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );
    const source =
      statGrowthHappinessBoostSource(
        logId
      );

    if (
      !source
    ) {
      return null;
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
      return null;
    }

    return {
      id:
        String(
          log?.id ??
          ''
        ),
      log_id:
        logId,
      timestamp,
      source
    };
  }

  function statGrowthEnergySourceEvent(
    log
  ) {
    const logId =
      Number(
        log?.log ??
        log?.details?.id
      );
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
      return null;
    }

    const data =
      log?.data;

    if (
      !data ||
      typeof data !== 'object' ||
      Array.isArray(
        data
      )
    ) {
      return null;
    }

    if (
      logId === 2290
    ) {
      if (
        statGrowthPositiveInteger(
          data.item
        ) !== 206
      ) {
        return null;
      }

      return {
        id:
          String(
            log?.id ??
            ''
          ),
        log_id: 2290,
        timestamp,
        kind: 'xanax',
        label: 'Xanax',
        energy_granted: 250,
        happiness_granted: 75,
        basis: 'derived_rule'
      };
    }

    if (
      logId === 4900
    ) {
      const energyGranted =
        statGrowthPositiveInteger(
          data.energy_increased
        );

      if (
        energyGranted === null
      ) {
        return null;
      }

      return {
        id:
          String(
            log?.id ??
            ''
          ),
        log_id: 4900,
        timestamp,
        kind: 'point_refill',
        label: 'Point refill',
        energy_granted:
          energyGranted,
        happiness_granted: 0,
        basis: 'observed_exact'
      };
    }

    return null;
  }

  function statGrowthEnergySourceEvidence(
    action,
    energySourceEvents,
    historyFirstTimestamp,
    previousTrainingTimestamp = null,
    windowSeconds = 30 * 60 * 60
  ) {
    const timestamp =
      Number(
        action?.timestamp
      );
    const historyStart =
      Number(
        historyFirstTimestamp
      );
    const previousTimestamp =
      Number(
        previousTrainingTimestamp
      );
    const safeWindow =
      Number.isSafeInteger(
        Number(
          windowSeconds
        )
      ) &&
      Number(windowSeconds) > 0
        ? Number(windowSeconds)
        : 30 * 60 * 60;

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0
    ) {
      return {
        status:
          'energy_context_unavailable',
        window_seconds:
          safeWindow
      };
    }

    const hasPreviousTraining =
      Number.isSafeInteger(
        previousTimestamp
      ) &&
      previousTimestamp > 0 &&
      previousTimestamp <=
        timestamp;
    const boundaryTimestamp =
      hasPreviousTraining
        ? previousTimestamp
        : timestamp -
          safeWindow;

    if (
      !Number.isSafeInteger(
        historyStart
      ) ||
      historyStart <= 0 ||
      historyStart >
        boundaryTimestamp
    ) {
      return {
        status:
          'energy_context_unavailable',
        window_seconds:
          timestamp -
          boundaryTimestamp,
        boundary_reason:
          hasPreviousTraining
            ? 'previous_training'
            : '30_hour_lookback'
      };
    }

    const grouped =
      new Map();

    for (
      const event
      of Array.isArray(
        energySourceEvents
      )
        ? energySourceEvents
        : []
    ) {
      const eventTimestamp =
        Number(
          event?.timestamp
        );

      if (
        !Number.isSafeInteger(
          eventTimestamp
        ) ||
        eventTimestamp <=
          boundaryTimestamp
      ) {
        continue;
      }

      if (
        eventTimestamp >
        timestamp
      ) {
        break;
      }

      const kind =
        String(
          event?.kind ||
          ''
        );

      if (
        !kind
      ) {
        continue;
      }

      const secondsBefore =
        timestamp -
        eventTimestamp;
      const existing =
        grouped.get(
          kind
        ) || {
          kind,
          label:
            String(
              event?.label ||
              'Energy source'
            ),
          count: 0,
          energy_total: 0,
          happiness_total: 0,
          nearest_seconds_before:
            secondsBefore,
          furthest_seconds_before:
            secondsBefore,
          basis:
            String(
              event?.basis ||
              'observed'
            )
        };

      existing.count++;
      existing.energy_total +=
        Number(
          event?.energy_granted ||
          0
        );
      existing.happiness_total +=
        Number(
          event?.happiness_granted ||
          0
        );
      existing.nearest_seconds_before =
        Math.min(
          existing.nearest_seconds_before,
          secondsBefore
        );
      existing.furthest_seconds_before =
        Math.max(
          existing.furthest_seconds_before,
          secondsBefore
        );

      grouped.set(
        kind,
        existing
      );
    }

    const sources =
      Array.from(
        grouped.values()
      );
    const kinds =
      new Set(
        sources.map(
          source =>
            source.kind
        )
      );

    if (
      !sources.length
    ) {
      return {
        status:
          'no_energy_source_observed',
        window_seconds:
          timestamp -
          boundaryTimestamp,
        boundary_reason:
          hasPreviousTraining
            ? 'previous_training'
            : '30_hour_lookback',
        natural_or_stored_energy_possible:
          true,
        sources: []
      };
    }

    const status =
      kinds.size > 1
        ? 'mixed_sources_observed'
        : kinds.has(
            'xanax'
          )
          ? 'xanax_observed'
          : 'point_refill_observed';

    return {
      status,
      window_seconds:
        timestamp -
        boundaryTimestamp,
      boundary_reason:
        hasPreviousTraining
          ? 'previous_training'
          : '30_hour_lookback',
      supported_energy_total:
        sources.reduce(
          (
            total,
            source
          ) =>
            total +
            source.energy_total,
          0
        ),
      supported_happiness_total:
        sources.reduce(
          (
            total,
            source
          ) =>
            total +
            source.happiness_total,
          0
        ),
      natural_or_stored_energy_possible:
        true,
      sources
    };
  }

  function statGrowthTrainingContext(
    action,
    happinessBoostEvents,
    historyFirstTimestamp,
    windowSeconds = 15 * 60
  ) {
    const timestamp =
      Number(
        action?.timestamp
      );
    const historyStart =
      Number(
        historyFirstTimestamp
      );
    const safeWindow =
      Number.isSafeInteger(
        Number(
          windowSeconds
        )
      ) &&
      Number(windowSeconds) > 0
        ? Number(windowSeconds)
        : 15 * 60;

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0 ||
      !Number.isSafeInteger(
        historyStart
      ) ||
      historyStart <= 0 ||
      historyStart >
        timestamp -
        safeWindow
    ) {
      return {
        status:
          'context_unavailable',
        window_seconds:
          safeWindow
      };
    }

    const events =
      Array.isArray(
        happinessBoostEvents
      )
        ? happinessBoostEvents
        : [];

    let low = 0;
    let high =
      events.length -
      1;
    let latest =
      null;
    let latestIndex =
      -1;

    while (
      low <= high
    ) {
      const middle =
        Math.floor(
          (
            low +
            high
          ) /
          2
        );
      const event =
        events[middle];
      const eventTimestamp =
        Number(
          event?.timestamp
        );

      if (
        !Number.isSafeInteger(
          eventTimestamp
        ) ||
        eventTimestamp >
          timestamp
      ) {
        high =
          middle -
          1;
        continue;
      }

      latest =
        event;
      latestIndex =
        middle;
      low =
        middle +
        1;
    }

    if (
      latest &&
      Number(latest.timestamp) >=
        timestamp -
        safeWindow
    ) {
      const boosts =
        [];

      for (
        let index =
          latestIndex;
        index >= 0;
        index--
      ) {
        const event =
          events[index];
        const eventTimestamp =
          Number(
            event?.timestamp
          );

        if (
          eventTimestamp <
          timestamp -
          safeWindow
        ) {
          break;
        }

        boosts.push({
          seconds_before:
            timestamp -
            eventTimestamp,
          source:
            event.source,
          source_log_id:
            Number(event.log_id),
          source_event_id:
            String(event.id || '')
        });
      }

      return {
        status:
          'happiness_boost_observed',
        window_seconds:
          safeWindow,
        seconds_before:
          timestamp -
          Number(
            latest.timestamp
          ),
        source:
          latest.source,
        source_log_id:
          Number(
            latest.log_id
          ),
        source_event_id:
          String(
            latest.id ||
            ''
          ),
        boosts
      };
    }

    return {
      status:
        'no_happiness_boost_observed',
      window_seconds:
        safeWindow
    };
  }

  function statGrowthSnapshotFreshness(
    action
  ) {
    const snapshot =
      action?.live_snapshot;
    const context =
      action?.training_context;
    const status =
      String(
        snapshot?.status ||
        ''
      );
    const observedAt =
      Number(
        snapshot?.observed_at ??
        snapshot?.captured_at
      );

    if (
      ![
        'exact_live_snapshot',
        'recent_live_snapshot',
        'armed_api_snapshot',
        'pretrain_api_checkpoint'
      ].includes(
        status
      ) ||
      !Number.isSafeInteger(
        observedAt
      ) ||
      observedAt <= 0
    ) {
      return {
        status:
          'unavailable',
        boosts_after_snapshot: []
      };
    }

    const actionTimestamp =
      Number(
        action?.timestamp
      );
    const boostsAfterSnapshot =
      (
        Array.isArray(
          context?.boosts
        )
          ? context.boosts
          : []
      )
        .map(
          boost => ({
            ...boost,
            timestamp:
              Number.isSafeInteger(
                actionTimestamp
              ) &&
              Number.isFinite(
                Number(
                  boost?.seconds_before
                )
              )
                ? actionTimestamp -
                  Math.max(
                    0,
                    Number(
                      boost.seconds_before
                    )
                  )
                : null
          })
        )
        .filter(
          boost =>
            Number.isSafeInteger(
              boost.timestamp
            ) &&
            boost.timestamp >=
              observedAt
        )
        .sort(
          (
            left,
            right
          ) =>
            left.timestamp -
              right.timestamp ||
            String(
              left.source_event_id ||
              ''
            ).localeCompare(
              String(
                right.source_event_id ||
                ''
              )
            )
        );

    return {
      status:
        boostsAfterSnapshot.length
          ? 'stale_after_boosters'
          : 'current_for_observed_boosters',
      observed_at:
        observedAt,
      boosts_after_snapshot:
        boostsAfterSnapshot
    };
  }

  function statGrowthHappyJumpEventKey(
    action
  ) {
    const timestamp =
      Number(
        action?.timestamp
      );
    const boosts =
      Array.isArray(
        action?.training_context?.boosts
      )
        ? action.training_context.boosts
        : [];
    const ecstasy =
      boosts
        .filter(
          boost =>
            Number(
              boost?.source_log_id
            ) === 2210 ||
            String(
              boost?.source ||
              ''
            ).toLowerCase() ===
              'ecstasy'
        )
        .sort(
          (
            left,
            right
          ) =>
            Number(
              left?.seconds_before ||
              0
            ) -
            Number(
              right?.seconds_before ||
              0
            )
        )[0];

    if (
      !Number.isSafeInteger(
        timestamp
      ) ||
      timestamp <= 0 ||
      !ecstasy
    ) {
      return null;
    }

    const secondsBefore =
      Math.max(
        0,
        Number(
          ecstasy.seconds_before
        ) ||
        0
      );
    const eventTimestamp =
      timestamp -
      secondsBefore;
    const quarter =
      Math.floor(
        eventTimestamp /
        (15 * 60)
      );
    const eventId =
      String(
        ecstasy.source_event_id ||
        ''
      );

    return {
      key:
        `${eventId || eventTimestamp}|${quarter}`,
      ecstasy_timestamp:
        eventTimestamp,
      ecstasy_event_id:
        eventId,
      quarter
    };
  }

  function statGrowthHappyJumpEvents(
    actions
  ) {
    const grouped =
      new Map();

    for (
      const action
      of Array.isArray(
        actions
      )
        ? actions
        : []
    ) {
      const identity =
        statGrowthHappyJumpEventKey(
          action
        );

      if (
        !identity ||
        Math.floor(
          Number(
            action?.timestamp
          ) /
          (15 * 60)
        ) !==
          identity.quarter
      ) {
        continue;
      }

      const event =
        grouped.get(
          identity.key
        ) || {
          id:
            identity.key,
          status:
            'observed_completed',
          ecstasy_timestamp:
            identity.ecstasy_timestamp,
          ecstasy_event_id:
            identity.ecstasy_event_id,
          first_timestamp:
            Number(
              action.timestamp
            ),
          last_timestamp:
            Number(
              action.timestamp
            ),
          action_ids: [],
          sessions: 0,
          trains: 0,
          energy_used: 0,
          gain: 0,
          stats: {},
          booster_event_ids:
            new Set(),
          booster_count: 0,
          point_refill_observed:
            false
        };

      event.first_timestamp =
        Math.min(
          event.first_timestamp,
          Number(
            action.timestamp
          )
        );
      event.last_timestamp =
        Math.max(
          event.last_timestamp,
          Number(
            action.timestamp
          )
        );
      event.action_ids.push(
        String(
          action?.id ||
          ''
        )
      );
      event.sessions++;
      event.trains +=
        Number(
          action?.trains ||
          0
        );
      event.energy_used +=
        Number(
          action?.energy_used ||
          0
        );
      event.gain +=
        Number(
          action?.stat_increased ||
          0
        );
      event.point_refill_observed =
        event.point_refill_observed ||
        [
          'point_refill_observed',
          'mixed_sources_observed'
        ].includes(
          String(
            action?.energy_source_evidence?.status ||
            ''
          )
        );

      const stat =
        String(
          action?.stat ||
          ''
        );

      if (
        stat
      ) {
        const statRow =
          event.stats[stat] || {
            stat,
            label:
              String(
                action?.stat_label ||
                stat
              ),
            sessions: 0,
            trains: 0,
            energy_used: 0,
            gain: 0
          };

        statRow.sessions++;
        statRow.trains +=
          Number(
            action?.trains ||
            0
          );
        statRow.energy_used +=
          Number(
            action?.energy_used ||
            0
          );
        statRow.gain +=
          Number(
            action?.stat_increased ||
            0
          );
        event.stats[stat] =
          statRow;
      }

      for (
        const boost
        of Array.isArray(
          action?.training_context?.boosts
        )
          ? action.training_context.boosts
          : []
      ) {
        const boostId =
          String(
            boost?.source_event_id ||
            `${boost?.source_log_id || ''}:${Number(action.timestamp) - Number(boost?.seconds_before || 0)}`
          );

        if (
          boostId
        ) {
          event.booster_event_ids.add(
            boostId
          );
        }
      }

      grouped.set(
        identity.key,
        event
      );
    }

    const events =
      Array.from(
        grouped.values()
      )
        .map(
          event => ({
            ...event,
            booster_count:
              event.booster_event_ids.size,
            booster_event_ids:
              Array.from(
                event.booster_event_ids
              ),
            stats:
              Object.values(
                event.stats
              )
          })
        )
        .filter(
          event =>
            event.energy_used >= 750 &&
            event.booster_count >= 2
        )
        .sort(
          (
            left,
            right
          ) =>
            left.first_timestamp -
              right.first_timestamp ||
            String(
              left.id
            ).localeCompare(
              String(
                right.id
              )
            )
        );

    const byActionId =
      new Map();

    for (
      const event
      of events
    ) {
      for (
        const actionId
        of event.action_ids
      ) {
        byActionId.set(
          actionId,
          event
        );
      }
    }

    for (
      const action
      of Array.isArray(
        actions
      )
        ? actions
        : []
    ) {
      action.happy_jump_event =
        byActionId.get(
          String(
            action?.id ||
            ''
          )
        ) ||
        null;
    }

    return events;
  }

  function statGrowthLatestHappyJumpEvent(
    growth
  ) {
    const events =
      Array.isArray(
        growth?.happy_jump_events
      )
        ? growth.happy_jump_events
        : [];

    return events[
      events.length - 1
    ] ||
      null;
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
    range = '10s',
    contextFilter = 'all'
  ) {
    const normalizedStat =
      String(
        stat ||
        ''
      );

    const normalizedContextFilter =
      [
        'happiness_boost_observed',
        'no_happiness_boost_observed'
      ].includes(
        contextFilter
      )
        ? contextFilter
        : 'all';

    const normalizedRange =
      uiSessionStatGrowthRange(
        range
      );

    const rangeDays =
      normalizedRange ===
        '7d'
        ? 7
        : normalizedRange ===
            '14d'
          ? 14
          : normalizedRange ===
              '30d'
            ? 30
            : null;

    const earliestTimestamp =
      rangeDays ===
        null
        ? null
        : Math.floor(
            Date.now() /
            1000
          ) -
          rangeDays *
            86400;

    const sessionLimit =
      normalizedRange ===
        '10s'
        ? 10
        : normalizedRange ===
            '20s'
          ? 20
          : normalizedRange ===
              '30s'
            ? 30
            : null;

    const samples =
      (growth?.training_actions || [])
      .filter(
        action =>
          action?.stat ===
          normalizedStat &&
          (
            earliestTimestamp === null ||
            Number(action?.timestamp || 0) >=
              earliestTimestamp
          ) &&
          (
            normalizedContextFilter === 'all' ||
            action?.training_context?.status ===
              normalizedContextFilter
          )
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
      );

    return sessionLimit ===
      null
        ? samples
        : samples.slice(
            -sessionLimit
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

    const happinessBoostEvents =
      [];

    const energySourceEvents =
      [];

    const nonGymStatGainCandidates =
      [];

    const jobSpecialStrengthGains =
      [];

    let recognizedLogs = 0;
    let jobSpecialRecognizedLogs = 0;
    let historyFirstTimestamp = null;
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
        candidateTimestamp > 0
      ) {
        historyFirstTimestamp =
          historyFirstTimestamp === null
            ? candidateTimestamp
            : Math.min(
                historyFirstTimestamp,
                candidateTimestamp
              );
        historyLastTimestamp =
          historyLastTimestamp === null
            ? candidateTimestamp
            : Math.max(
                historyLastTimestamp,
                candidateTimestamp
              );
      }

      const happinessBoostEvent =
        statGrowthHappinessBoostEvent(
          log
        );

      if (
        happinessBoostEvent
      ) {
        happinessBoostEvents.push(
          happinessBoostEvent
        );
      }

      const energySourceEvent =
        statGrowthEnergySourceEvent(
          log
        );

      if (
        energySourceEvent
      ) {
        energySourceEvents.push(
          energySourceEvent
        );
      }

      const nonGymStatGainCandidate =
        inspectNonGymStatGainCandidate(
          log
        );

      if (
        nonGymStatGainCandidate
      ) {
        nonGymStatGainCandidates.push(
          nonGymStatGainCandidate
        );
      }

      const jobSpecialInspection =
        inspectJobSpecialStrengthLog(
          log
        );

      if (
        jobSpecialInspection.recognized
      ) {
        jobSpecialRecognizedLogs++;

        if (
          jobSpecialInspection.valid
        ) {
          jobSpecialInspection.record.date =
            activityDateKeyForBasis(
              new Date(
                jobSpecialInspection.record.timestamp *
                1000
              ),
              normalizedTimeBasis
            );
          jobSpecialStrengthGains.push(
            jobSpecialInspection.record
          );
        } else {
          const reason =
            jobSpecialInspection.reason;
          rejectionReasons[
            `job_special_${reason}`
          ] =
            (
              rejectionReasons[
                `job_special_${reason}`
              ] ||
              0
            ) +
            1;
        }
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

    happinessBoostEvents.sort(
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

    energySourceEvents.sort(
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

    nonGymStatGainCandidates.sort(
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

    jobSpecialStrengthGains.sort(
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

    const jobSpecialStrengthGain =
      jobSpecialStrengthGains.reduce(
        (
          total,
          record
        ) =>
          total +
          record.stat_increased,
        0
      );
    const jobSpecialJobPointsUsed =
      jobSpecialStrengthGains.reduce(
        (
          total,
          record
        ) =>
          total +
          record.job_points_used,
        0
      );

    if (
      typeof trainingSnapshotAttachToActions ===
        'function' &&
      typeof readTrainingSnapshots ===
        'function'
    ) {
      trainingSnapshotAttachToActions(
        actions,
        readTrainingSnapshots()
      );
    } else {
      for (
        const action
        of actions
      ) {
        action.live_snapshot = {
          status:
            'unavailable'
        };
      }
    }

    if (
      typeof trainingCheckpointCanaryAttachToActions ===
        'function' &&
      typeof readTrainingCheckpointCanaryState ===
        'function'
    ) {
      trainingCheckpointCanaryAttachToActions(
        actions,
        readTrainingCheckpointCanaryState()
      );
    }

    let previousTrainingTimestamp =
      null;

    for (
      const action
      of actions
    ) {
      action.training_context =
        statGrowthTrainingContext(
          action,
          happinessBoostEvents,
          historyFirstTimestamp
        );
      action.energy_source_evidence =
        statGrowthEnergySourceEvidence(
          action,
          energySourceEvents,
          historyFirstTimestamp,
          previousTrainingTimestamp
        );
      action.snapshot_freshness =
        typeof statGrowthSnapshotFreshness ===
          'function'
          ? statGrowthSnapshotFreshness(
              action
            )
          : {
              status:
                'unavailable',
              boosts_after_snapshot: []
            };
      previousTrainingTimestamp =
        action.timestamp;
    }

    const happyJumpEvents =
      typeof statGrowthHappyJumpEvents ===
        'function'
        ? statGrowthHappyJumpEvents(
            actions
          )
        : [];

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
      job_special_recognized_logs:
        jobSpecialRecognizedLogs,
      job_special_valid_logs:
        jobSpecialStrengthGains.length,
      job_special_rejected_logs:
        jobSpecialRecognizedLogs -
        jobSpecialStrengthGains.length,
      job_special_strength_gains:
        jobSpecialStrengthGains,
      job_special_strength_gain:
        jobSpecialStrengthGain,
      job_special_job_points_used:
        jobSpecialJobPointsUsed,
      non_gym_stat_gain_candidates:
        nonGymStatGainCandidates,
      actions:
        actions.length,
      training_actions:
        actions,
      happy_jump_events:
        happyJumpEvents,
      training_context_window_seconds:
        15 * 60,
      energy_source_lookback_seconds:
        30 * 60 * 60,
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
  // GYM TRAINER
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
      drug_ready_at: drug === 0
        ? Math.floor(safeFetchedAt / 1000)
        : Math.ceil(safeFetchedAt / 1000) + drug,
      booster_ready_at: booster === 0
        ? Math.floor(safeFetchedAt / 1000)
        : Math.ceil(safeFetchedAt / 1000) + booster
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
      'Refreshing training cooldownsâ€¦',
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


  const TRAINING_PLAN_STORAGE_KEY = 'tornAnalyticsTrainingPlanV1';

  function trainingReadinessPlan(
    value
  ) {
    const plan = String(value || '').trim().toLowerCase();

    if (plan === 'happy_jump') {
      return plan;
    }

    return 'efficient_training';
  }

  function trainingReadinessPlanStorage() {
    try {
      return typeof localStorage !== 'undefined'
        ? localStorage
        : null;
    } catch {
      return null;
    }
  }

  function readTrainingReadinessPlan() {
    try {
      return trainingReadinessPlan(
        trainingReadinessPlanStorage()?.getItem(TRAINING_PLAN_STORAGE_KEY)
      );
    } catch {
      return 'efficient_training';
    }
  }

  function writeTrainingReadinessPlan(
    value
  ) {
    const plan = trainingReadinessPlan(value);

    try {
      trainingReadinessPlanStorage()?.setItem(
        TRAINING_PLAN_STORAGE_KEY,
        plan
      );
    } catch {
      // A blocked preference store should not break read-only guidance.
    }

    return plan;
  }

  function trainingReadinessHappyJumpSupplies() {
    return [
      {
        item: 'Xanax',
        quantity: 4,
        optional: false,
        inventory_status: 'unknown'
      },
      {
        item: 'Erotic DVD',
        quantity: 5,
        optional: false,
        inventory_status: 'unknown',
        note: 'Standard setup; job and faction perks can change the best amount.'
      },
      {
        item: 'Ecstasy',
        quantity: 1,
        optional: false,
        inventory_status: 'unknown'
      },
      {
        item: 'Points',
        quantity: 30,
        optional: true,
        inventory_status: 'unknown',
        note: 'Optional daily Energy refill; Points are not an inventory item.'
      }
    ];
  }

  function trainingReadinessCooldownLabel(
    readyAtValue,
    nowSeconds = Math.floor(Date.now() / 1000)
  ) {
    const readyAt = Number(readyAtValue);
    const now = Number.isFinite(Number(nowSeconds))
      ? Math.floor(Number(nowSeconds))
      : Math.floor(Date.now() / 1000);

    if (!Number.isSafeInteger(readyAt) || readyAt <= 0) {
      return {
        state: 'unknown',
        label: 'Unavailable'
      };
    }

    if (readyAt <= now) {
      return {
        state: 'complete',
        label: 'Ready'
      };
    }

    return {
      state: 'waiting',
      label: `Ready in ${trainingReadinessFormatDuration(readyAt - now)}`
    };
  }

  function renderTrainingReadinessGuide(
    readiness,
    planValue,
    advice,
    nowSeconds = Math.floor(Date.now() / 1000)
  ) {
    const plan = trainingReadinessPlan(planValue);
    const now = Number.isFinite(Number(nowSeconds))
      ? Math.floor(Number(nowSeconds))
      : Math.floor(Date.now() / 1000);
    const finiteValue = value =>
      value !== null &&
      value !== undefined &&
      value !== '' &&
      Number.isFinite(Number(value))
        ? Number(value)
        : null;
    const energy = finiteValue(readiness?.energy);
    const energyMaximum = finiteValue(readiness?.energy_maximum);
    const drug = trainingReadinessCooldownLabel(
      readiness?.drug_ready_at,
      now
    );
    const booster = trainingReadinessCooldownLabel(
      readiness?.booster_ready_at,
      now
    );
    const statusRow = (label, value, state = 'waiting') => `
      <li class="ta-training-guide-row ta-training-guide-${escapeActivityHtml(state)}">
        <span>${escapeActivityHtml(label)}</span>
        <b>${escapeActivityHtml(value)}</b>
      </li>
    `;

    if (
      plan === 'happy_jump' &&
      advice?.phase ===
        'completed' &&
      advice?.happy_jump_event
    ) {
      const event =
        advice.happy_jump_event;
      const remainingEnergy =
        energy !== null &&
        energy > 0
          ? `${energy.toLocaleString()}E currently available. Continue normal training when convenient.`
          : 'No remaining Energy is waiting to be trained.';

      return `
        <div class="ta-training-guide ta-training-happy-guide ta-training-happy-complete" data-ta-training-guide data-ta-happy-jump-complete>
          <ul class="ta-training-guide-list">
            ${statusRow('Jump result', `+${statGrowthFormatNumber(event.gain, 2)} total stats`, 'complete')}
            ${statusRow('Energy trained', `${Number(event.energy_used || 0).toLocaleString()}E Â· ${Number(event.trains || 0).toLocaleString()} trains`, 'complete')}
            ${statusRow('Drug cooldown', drug.label, drug.state)}
            ${statusRow('Booster cooldown', booster.label, booster.state)}
          </ul>
          <p class="ta-training-guide-note">${escapeActivityHtml(remainingEnergy)}</p>
        </div>
      `;
    }

    if (plan !== 'happy_jump') {
      const energyState = energy === null
        ? 'Live Energy unavailable'
        : energyMaximum !== null && energy >= energyMaximum
          ? 'At maximum â€” train now'
          : energy > 0
            ? `${energy.toLocaleString()}E available`
            : '0E â€” ready for Xanax or refill';

      return `
        <div class="ta-training-guide ta-training-efficient-guide" data-ta-training-guide>
          <p class="ta-training-guide-purpose">
            <strong>Keep your Energy moving.</strong>
            Natural Energy stops regenerating at its normal maximum. Train regularly so it does not sit full.
          </p>
          <ul class="ta-training-guide-list">
            ${statusRow('Natural Energy', energyState, energyMaximum !== null && energy !== null && energy >= energyMaximum ? 'action' : 'complete')}
            ${statusRow('Before Xanax', 'Train to 0E first so an overdose cannot erase saved Energy.', drug.state)}
            ${statusRow('Before daily refill', 'Train to 0E so the refill restores the full bar.', 'waiting')}
          </ul>
          <p class="ta-training-guide-note">If your current gym leaves a small unusable remainder, train as low as that gym allows.</p>
        </div>
      `;
    }

    const stackValue = energy === null
      ? 'Unavailable'
      : `${Math.min(energy, 1000).toLocaleString()} / 1,000E${energy >= 1000 ? ' â€” Complete' : ''}`;
    const stackState = energy !== null && energy >= 1000
      ? 'complete'
      : energy === null
        ? 'unknown'
        : 'waiting';
    const quarter = trainingReadinessQuarterHour(now * 1000);
    const supplyRows = trainingReadinessHappyJumpSupplies()
      .map(supply => `
        <li>
          <span>${escapeActivityHtml(`${supply.item} Ã—${supply.quantity}${supply.optional ? ' Â· optional' : ''}`)}</span>
          <b>Count unknown</b>
          ${supply.note ? `<small>${escapeActivityHtml(supply.note)}</small>` : ''}
        </li>
      `)
      .join('');

    return `
      <div class="ta-training-guide ta-training-happy-guide" data-ta-training-guide>
        <ul class="ta-training-guide-list">
          ${statusRow('Energy stack', stackValue, stackState)}
          ${statusRow('Drug cooldown', drug.label, drug.state)}
          ${statusRow('Booster cooldown', booster.label, booster.state)}
          <li class="ta-training-guide-row ta-training-guide-waiting">
            <span>Begin just after reset</span>
            <b data-ta-training-jump-countdown>Next TCT reset Â· ${escapeActivityHtml(trainingReadinessFormatDuration(quarter.seconds_until))}</b>
          </li>
        </ul>
        <div class="ta-training-jump-sequence">
          <strong>Jump sequence</strong>
          <ol>
            <li>Just after a TCT Happiness reset, use the planned Happiness boosters.</li>
            <li>Take Ecstasy to double current Happiness.</li>
            <li>Train your stacked Energy before your Happiness resets.</li>
            <li>Optional: use the 30-point Energy refill and train again.</li>
          </ol>
        </div>
        <details class="ta-training-supplies">
          <summary><span>Jump supplies</span><b>Inventory counts unknown</b></summary>
          <ul>${supplyRows}</ul>
          <p>Inventory tracking is not connected yet. Torn Analytics will not guess what you own, use items, or make purchases.</p>
        </details>
        <p class="ta-training-guide-note">Xanax and Ecstasy can overdose and erase saved Energy. This assistant is read-only guidance, not a safety guarantee.</p>
      </div>
    `;
  }

  function trainingReadinessPlanAdvice(
    readiness,
    planValue,
    nowSeconds = Math.floor(Date.now() / 1000),
    growth = null
  ) {
    const plan = trainingReadinessPlan(planValue);
    const now = Number.isFinite(Number(nowSeconds))
      ? Math.floor(Number(nowSeconds))
      : Math.floor(Date.now() / 1000);
    const finiteValue = value =>
      value !== null &&
      value !== undefined &&
      value !== '' &&
      Number.isFinite(Number(value))
        ? Number(value)
        : null;
    const energy = finiteValue(readiness?.energy);
    const energyMaximum = finiteValue(readiness?.energy_maximum);
    const happiness = finiteValue(readiness?.happiness);
    const happinessMaximum = finiteValue(readiness?.happiness_maximum);
    const cooldownState = readyAtValue => {
      const readyAt = finiteValue(readyAtValue);

      if (readyAt === null || !Number.isSafeInteger(readyAt) || readyAt <= 0) {
        return 'unavailable';
      }

      return readyAt <= now
        ? 'ready'
        : 'waiting';
    };
    const boosterState = cooldownState(readiness?.booster_ready_at);
    const drugState = cooldownState(readiness?.drug_ready_at);
    if (energy === null) {
      return {
        plan,
        title: 'Live Energy unavailable',
        detail: 'Refresh live bars before using training guidance.',
        tone: 'info'
      };
    }

    if (plan === 'happy_jump') {
      const completedJump =
        typeof statGrowthLatestHappyJumpEvent ===
          'function'
          ? statGrowthLatestHappyJumpEvent(
              growth
            )
          : null;
      const completedAt =
        Number(
          completedJump?.last_timestamp
        );
      const completedRecently =
        Number.isSafeInteger(
          completedAt
        ) &&
        completedAt > 0 &&
        now >= completedAt &&
        now - completedAt <=
          48 * 60 * 60;

      if (
        completedRecently &&
        completedJump?.status ===
          'observed_completed' &&
        boosterState ===
          'waiting' &&
        energy < 750
      ) {
        return {
          plan,
          phase:
            'completed',
          title:
            'Happy Jump complete',
          detail:
            `${Number(completedJump.energy_used || 0).toLocaleString()}E across ${Number(completedJump.sessions || 0).toLocaleString()} gym ${Number(completedJump.sessions || 0) === 1 ? 'session' : 'sessions'} produced +${statGrowthFormatNumber(completedJump.gain, 2)} total stats.`,
          tone:
            'complete',
          happy_jump_event:
            completedJump
        };
      }

      if (readiness?.over_happiness && energy > 0) {
        return {
          plan,
          title: 'Train now',
          detail: 'Use the elevated Happiness before the next TCT Happiness reset.',
          tone: 'ready'
        };
      }

      const stackMilestones = {
        250: 2,
        500: 3,
        750: 4
      };
      const nextXanaxNumber = stackMilestones[energy] || null;

      if (energy === 0) {
        if (drugState === 'unavailable') {
          return {
            plan,
            title: 'Drug cooldown unavailable',
            detail: 'Refresh live cooldowns before starting a four-Xanax stack.',
            tone: 'info'
          };
        }

        if (drugState === 'waiting') {
          return {
            plan,
            title: 'Wait for drug cooldown',
            detail: 'Start the four-Xanax stack from 0E when the cooldown clears.',
            tone: 'wait'
          };
        }

        return {
          plan,
          title: 'Start your four-Xanax stack',
          detail: 'Take Xanax 1 of 4. Wait for each drug cooldown before taking the next.',
          tone: 'ready'
        };
      }

      if (nextXanaxNumber !== null) {
        if (drugState === 'unavailable') {
          return {
            plan,
            title: 'Drug cooldown unavailable',
            detail: `Your stack is at ${energy}E. Refresh live cooldowns before the next Xanax.`,
            tone: 'info'
          };
        }

        if (drugState === 'waiting') {
          return {
            plan,
            title: 'Wait for drug cooldown',
            detail: `Your stack is at ${energy}E. Take Xanax ${nextXanaxNumber} of 4 when it clears.`,
            tone: 'wait'
          };
        }

        return {
          plan,
          title: `Take Xanax ${nextXanaxNumber} of 4`,
          detail: `Your stack is at ${energy}E. Then wait for the next drug cooldown.`,
          tone: 'ready'
        };
      }

      if (energy >= 1000) {
        if (drugState === 'unavailable') {
          return {
            plan,
            title: 'Stack complete â€” cooldown unavailable',
            detail: 'Refresh live cooldowns before planning Ecstasy and Happiness boosters.',
            tone: 'info'
          };
        }

        if (drugState === 'waiting') {
          return {
            plan,
            title: 'Stack complete â€” wait for final drug cooldown',
            detail: 'Keep booster cooldown clear. When both are ready, begin just after a TCT Happiness reset.',
            tone: 'wait'
          };
        }

        if (boosterState === 'unavailable') {
          return {
            plan,
            title: 'Booster cooldown unavailable',
            detail: 'Refresh live cooldowns before using Happiness boosters.',
            tone: 'info'
          };
        }

        if (boosterState === 'waiting') {
          return {
            plan,
            title: 'Wait for booster cooldown',
            detail: 'Your Energy stack is complete. Do not begin the Happiness boost until boosters are ready.',
            tone: 'wait'
          };
        }

        return {
          plan,
          title: 'Stack complete â€” prepare your Happy Jump',
          detail: 'Just after a TCT Happiness reset: use your Happiness boosters, take Ecstasy, then train before the next reset.',
          tone: 'ready'
        };
      }

      return {
        plan,
        title: 'Train to 0E before starting',
        detail: 'A clean 0E start lets four Xanax provide the full 1,000E stack without wasting Energy.',
        tone: 'wait'
      };
    }

    if (readiness?.over_happiness && energy > 0) {
      return {
        plan,
        title: 'Train now',
        detail: 'Use the elevated Happiness before the next TCT Happiness reset.',
        tone: 'ready'
      };
    }

    if (drugState === 'ready') {
      if (energy > 0) {
        return {
          plan,
          title: 'Protect your Energy before Xanax',
          detail: 'Train existing Energy to 0E before taking Xanax. If it overdoses, Torn empties the bar; starting at 0E prevents losing saved Energy and keeps natural regeneration moving.',
          tone: 'wait'
        };
      }

      return {
        plan,
        title: 'Take a Xanax, then train promptly',
        detail: 'Train the Xanax Energy promptly so natural Energy regeneration can resume.',
        tone: 'ready'
      };
    }

    if (drugState === 'waiting') {
      if (energy > 0) {
        return {
          plan,
          title: energyMaximum !== null && energy >= energyMaximum
            ? 'Train now â€” Energy is at maximum'
            : 'Train available Energy',
          detail: energyMaximum !== null && energy >= energyMaximum
            ? 'Natural Energy cannot regenerate while the bar is full. Train now while the Xanax cooldown clears.'
            : 'Use Energy before it reaches maximum so natural regeneration does not stop while the Xanax cooldown clears.',
          tone: 'ready'
        };
      }

      return {
        plan,
        title: 'Wait for Energy or Xanax cooldown',
        detail: 'Train when Energy returns, or use Xanax when the drug cooldown clears.',
        tone: 'wait'
      };
    }

    if (energy > 0) {
      return {
        plan,
        title: 'Train available Energy',
        detail: 'Use Energy before it reaches maximum. Refresh live cooldowns before planning the next Xanax.',
        tone: 'info'
      };
    }

    return {
      plan,
      title: 'Drug cooldown unavailable',
      detail: 'Refresh live cooldowns before planning the next Xanax.',
      tone: 'info'
    };
  }

  function trainingReadinessAdvisorContract(
    readiness,
    advice,
    nowSeconds = Math.floor(Date.now() / 1000)
  ) {
    const now = Number.isFinite(Number(nowSeconds))
      ? Math.floor(Number(nowSeconds))
      : Math.floor(Date.now() / 1000);
    const finiteValue = value =>
      value !== null &&
      value !== undefined &&
      value !== '' &&
      Number.isFinite(Number(value))
        ? Number(value)
        : null;
    const safeAdvice = advice && typeof advice === 'object'
      ? advice
      : {};
    const plan = trainingReadinessPlan(safeAdvice.plan);
    const energy = finiteValue(readiness?.energy);
    const energyMaximum = finiteValue(readiness?.energy_maximum);
    const happiness = finiteValue(readiness?.happiness);
    const happinessMaximum = finiteValue(readiness?.happiness_maximum);
    const drugReadyAt = finiteValue(readiness?.drug_ready_at);
    const boosterReadyAt = finiteValue(readiness?.booster_ready_at);
    const validReadyAt = value =>
      value !== null &&
      Number.isSafeInteger(value) &&
      value > 0;
    const cooldownEvidence = readyAt => {
      if (!validReadyAt(readyAt)) {
        return 'Unavailable';
      }

      if (readyAt <= now) {
        return 'Ready now';
      }

      return `Ready in ${trainingReadinessFormatDuration(readyAt - now)}`;
    };
    const liveValue = (value, maximum) => {
      if (value === null) {
        return 'Unavailable';
      }

      return maximum === null
        ? value.toLocaleString()
        : `${value.toLocaleString()} / ${maximum.toLocaleString()}`;
    };
    const planLabel = plan === 'happy_jump'
      ? 'Happy Jump'
      : 'Efficient training';
    const evidence = [
      `Rule: ${planLabel}`,
      `Live Torn fact â€” Energy: ${liveValue(energy, energyMaximum)}`,
      `Live Torn fact â€” Happiness: ${liveValue(happiness, happinessMaximum)}`,
      `Live Torn fact â€” Drug cooldown: ${cooldownEvidence(drugReadyAt)}`,
      `Live Torn fact â€” Booster cooldown: ${cooldownEvidence(boosterReadyAt)}`
    ];
    const missingInputs = [];

    if (energy === null) {
      missingInputs.push('Energy');
    }

    if (happiness === null || happinessMaximum === null) {
      missingInputs.push('Happiness');
    }

    if (!validReadyAt(drugReadyAt)) {
      missingInputs.push('drug cooldown');
    }

    if (!validReadyAt(boosterReadyAt)) {
      missingInputs.push('booster cooldown');
    }

    const coreInputsAvailable =
      energy !== null &&
      validReadyAt(drugReadyAt);
    const confidence = missingInputs.length === 0
      ? {
          label: 'High',
          detail: 'All live inputs checked by this deterministic plan rule are available.'
        }
      : coreInputsAvailable
        ? {
            label: 'Medium',
            detail: 'Core Energy and drug-cooldown inputs are live, but some supporting context is unavailable.'
          }
        : {
            label: 'Limited',
            detail: 'A required live input is unavailable; refresh before relying on this action.'
          };
    const limitations = [
      'Read-only: no items are used and no training is performed.',
      'Inventory, item prices, and personal risk preferences are not known.',
      'Historical gain estimates are separate; this rule does not predict exact gains or Happiness effects.'
    ];

    if (missingInputs.length) {
      limitations.push(`Missing live context: ${missingInputs.join(', ')}.`);
    }

    return {
      action: String(safeAdvice.title || 'Guidance unavailable'),
      reason: String(safeAdvice.detail || 'No explanation is available for this action.'),
      evidence,
      confidence,
      limitations
    };
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
    gymId,
    trainingContext = null
  ) {
    const knownContexts = [
      'happiness_boost_observed',
      'no_happiness_boost_observed'
    ];
    const requestedContext = knownContexts.includes(trainingContext)
      ? trainingContext
      : null;
    const sameStatAndGym = (actions || [])
      .filter(action =>
        action?.stat === stat &&
        Number.isSafeInteger(Number(gymId)) &&
        Number(gymId) > 0 &&
        Number(action?.gym) === Number(gymId) &&
        Number.isFinite(Number(action?.gain_per_energy)) &&
        Number(action.gain_per_energy) > 0
      );
    const inferredContext = requestedContext ||
      sameStatAndGym
        .slice()
        .sort((left, right) =>
          Number(right.timestamp || 0) - Number(left.timestamp || 0)
        )
        .map(action => action?.training_context?.status)
        .find(status => knownContexts.includes(status)) ||
      null;
    const comparable = (actions || [])
      .filter(action =>
        action?.stat === stat &&
        Number.isSafeInteger(Number(gymId)) &&
        Number(gymId) > 0 &&
        Number(action?.gym) === Number(gymId) &&
        (
          inferredContext === null ||
          action?.training_context?.status === inferredContext
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
    const backtest = trainingReadinessBacktest(
      actions,
      stat,
      gymId,
      inferredContext
    );
    const typicalError = backtest.typical_error_percent;
    const confidence = samples < 2
      ? 'Insufficient'
      : samples >= 8 &&
          backtest.predictions >= 4 &&
          Number.isFinite(typicalError) &&
          typicalError <= 10
        ? 'High'
        : samples >= 4 &&
            backtest.predictions >= 2 &&
            Number.isFinite(typicalError) &&
            typicalError <= 25
          ? 'Medium'
          : 'Low';

    return {
      stat,
      gym_id: gymId,
      gym_source:
        Number.isSafeInteger(Number(gymId)) && Number(gymId) > 0
          ? 'last_observed'
          : 'unknown',
      training_context: inferredContext,
      training_context_source: requestedContext
        ? 'live_snapshot'
        : inferredContext
          ? 'last_observed'
          : 'unknown',
      samples,
      observations,
      confidence,
      backtest_predictions: backtest.predictions,
      typical_error_percent: typicalError,
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

  function trainingReadinessBacktest(
    actions,
    stat,
    gymId,
    trainingContext = null
  ) {
    const knownContexts = [
      'happiness_boost_observed',
      'no_happiness_boost_observed'
    ];
    const context = knownContexts.includes(trainingContext)
      ? trainingContext
      : null;
    const comparable = (actions || [])
      .filter(action =>
        action?.stat === stat &&
        Number.isSafeInteger(Number(gymId)) &&
        Number(gymId) > 0 &&
        Number(action?.gym) === Number(gymId) &&
        (
          context === null ||
          action?.training_context?.status === context
        ) &&
        Number.isFinite(Number(action?.gain_per_energy)) &&
        Number(action.gain_per_energy) > 0
      )
      .sort((left, right) =>
        Number(left.timestamp || 0) - Number(right.timestamp || 0) ||
        String(left.id || '').localeCompare(String(right.id || ''))
      );
    const errors = [];

    for (let index = 2; index < comparable.length; index++) {
      const priorRates = comparable
        .slice(Math.max(0, index - 12), index)
        .map(action => Number(action.gain_per_energy));
      const predictedRate = trainingReadinessQuantile(priorRates, 0.5);
      const actualRate = Number(comparable[index].gain_per_energy);

      if (
        Number.isFinite(predictedRate) &&
        predictedRate > 0 &&
        Number.isFinite(actualRate) &&
        actualRate > 0
      ) {
        errors.push(Math.abs(predictedRate - actualRate) / actualRate * 100);
      }
    }

    return {
      predictions: errors.length,
      errors_percent: errors,
      typical_error_percent: errors.length
        ? trainingReadinessQuantile(errors, 0.5)
        : null
    };
  }

  function trainingReadinessPredictionContext(
    planValue
  ) {
    return trainingReadinessPlan(planValue) === 'happy_jump'
      ? 'happiness_boost_observed'
      : 'no_happiness_boost_observed';
  }

  function trainingReadinessPredictionModel(
    readiness,
    stat,
    planValue
  ) {
    const context = trainingReadinessPredictionContext(planValue);
    const direct = readiness?.models_by_context?.[context]?.[stat];

    if (direct) {
      return direct;
    }

    const legacy = readiness?.models?.[stat];

    return legacy?.training_context === context
      ? legacy
      : null;
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
    const energyMaximum = bars?.status === 'available'
      ? Number(bars?.energy?.maximum)
      : null;
    const energyIncrement = bars?.status === 'available'
      ? Number(bars?.energy?.increment)
      : null;
    const energyInterval = bars?.status === 'available'
      ? Number(bars?.energy?.interval)
      : null;
    const energyFullTime = bars?.status === 'available'
      ? Number(bars?.energy?.full_time)
      : null;
    const barsFetchedAt = bars?.status === 'available'
      ? Number(bars?.fetched_at)
      : null;
    const energyFullAt =
      Number.isFinite(barsFetchedAt) &&
      Number.isFinite(energyFullTime) &&
      energyFullTime >= 0
        ? barsFetchedAt + energyFullTime * 1000
        : null;
    const happiness = bars?.status === 'available'
      ? Number(bars?.happiness?.current)
      : null;
    const happinessMaximum = bars?.status === 'available'
      ? Number(bars?.happiness?.maximum)
      : null;
    const targetTrainingContext =
      Number.isFinite(happiness) &&
      Number.isFinite(happinessMaximum)
        ? happiness > happinessMaximum
          ? 'happiness_boost_observed'
          : 'no_happiness_boost_observed'
        : null;
    const models = {};
    const modelsByContext = {
      happiness_boost_observed: {},
      no_happiness_boost_observed: {}
    };

    for (const stat of ['strength', 'defense', 'speed', 'dexterity']) {
      models[stat] = trainingReadinessModel(
        actions,
        stat,
        gymId,
        targetTrainingContext
      );

      for (const context of [
        'happiness_boost_observed',
        'no_happiness_boost_observed'
      ]) {
        modelsByContext[context][stat] = trainingReadinessModel(
          actions,
          stat,
          gymId,
          context
        );
      }
    }

    return {
      page_is_gym: /(?:^|\/)gym\.php(?:[?#]|$)/i.test(effectiveUrl),
      default_stat: defaultStat,
      gym_id: gymId,
      last_training_timestamp: latest?.timestamp || null,
      energy: Number.isFinite(energy) ? energy : null,
      energy_maximum: Number.isFinite(energyMaximum)
        ? energyMaximum
        : null,
      energy_increment: Number.isFinite(energyIncrement)
        ? energyIncrement
        : null,
      energy_interval: Number.isFinite(energyInterval)
        ? energyInterval
        : null,
      energy_full_at: Number.isFinite(energyFullAt)
        ? energyFullAt
        : null,
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
      models,
      models_by_context: modelsByContext
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

    const typicalError =
      model?.typical_error_percent !== null &&
      model?.typical_error_percent !== undefined &&
      model?.typical_error_percent !== '' &&
      Number.i×Nºï¦òµë(š+myÖ–v‡BÐ¢†V–v‡BÐ¢F÷Ð¢&÷GFöÓ° ¢6öç7BF÷FÇ2Ð¢6×ÆW2æÖ€¢7F–öâÓà¢çVÖ&W"€¢7F–öâç7FEögFW"ÇÀ¢ ¢¢“° ¢6öç7Bv–ç2Ð¢6×ÆW2æÖ€¢7F–öâÓà¢çVÖ&W"€¢7F–öâç7FEö–æ7&V6VBÇÀ¢ ¢¢“° ¢6öç7BÖ–æ–×VÕF÷FÂÐ¢ÖF‚æÖ–â€¢ââçF÷FÇ0¢“° ¢6öç7BÖ†–×VÕF÷FÂÐ¢ÖF‚æÖ‚€¢ââçF÷FÇ0¢“° ¢6öç7BF÷FÅ&ævRÐ¢ÖF‚æÖ‚€¢À¢Ö†–×VÕF÷FÂÐ¢Ö–æ–×VÕF÷FÀ¢“° ¢6öç7BÖ†–×VÔv–âÐ¢ÖF‚æÖ‚€¢À¢ââæv–ç0¢“° ¢6öç7B6W76–öåf—7VÇ2Ð¢6×ÆW2æÖ€¢7FDw&÷wF…6W76–öåf—7VÄ6Æ76–f–6F–öà¢“° ¢6öç7Bö–çE‚Ð¢–æFW‚Óà¢7FDw&÷wF…6W76–öä÷&FW%ö–çE‚€¢–æFW‚À¢6×ÆW2æÆVæwF‚À¢ÆVgBÀ¢Æ÷Ev–GF€¢“° ¢6öç7Bö–çE’Ð¢F÷FÂÓà¢F÷°¢€¢Ð¢‡F÷FÂÐ¢Ö–æ–×VÕF÷FÂ’ð¢F÷FÅ&ævP¢’ ¢Æ÷D†V–v‡C° ¢6öç7Bf—6–&ÆTÖ&¶W$–æFW†W2Ð¢æWr6WB€¢7FDw&÷wF…f—6–&ÆTÖ&¶W$–æFW†W2€¢6×ÆW2À¢6VÆV7FVE&ævRÀ¢ö–çE‚À¢6×ÆW2æÆVæwF‚Ò¢¢“° ¢6öç7BÆ–æRÐ¢6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óà¢G¶–æFW‚òtÂr¢tÒwÒG·ö–çE‚†–æFW‚’çFôf—†VBƒ"—ÒG·ö–çE’„çVÖ&W"†7F–öâç7FEögFW"ÇÂ’’çFôf—†VBƒ"—Ö ¢’æ¦ö–â‚rr“° ¢6öç7B&%v–GF‚Ð¢ÖF‚æÖ‚€¢RÀ¢ÖF‚æÖ–â€¢#À¢Æ÷Ev–GF‚ð¢6×ÆW2æÆVæwF‚ ¢ãS`¢¢“° ¢6öç7B&$†V–v‡Df÷"Ð¢7F–öâÓà¢ÖF‚æÖ‚€¢"À¢çVÖ&W"€¢7F–öãòç7FEö–æ7&V6VBÇÀ¢ ¢’ð¢Ö†–×VÔv–â ¢Æ÷D†V–v‡B ¢ã3`¢“° ¢6öç7B&'2Ð¢6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óâ°¢6öç7B&$†V–v‡BÐ¢&$†V–v‡Df÷"€¢7F–öà¢“°¢6öç7Bf—7VÂÐ¢6W76–öåf—7VÇ5°¢–æFW€¢Ó°¢6öç7B7F—fRÐ¢–æFW‚ÓÓÐ¢6×ÆW2æÆVæwF‚Ò° ¢&WGW&âÇ&V7BƒÒ"G²‡ö–çE‚†–æFW‚’Ò&%v–GF‚ò"’çFôf—†VBƒ"—Ò"“Ò"G²‡F÷²Æ÷D†V–v‡BÒ&$†V–v‡B’çFôf—†VBƒ"—Ò"v–GFƒÒ"G¶&%v–GF‚çFôf—†VBƒ"—Ò"†V–v‡CÒ"G¶&$†V–v‡BçFôf—†VBƒ"—Ò"'ƒÒ#""6Æ73Ò'F×7FB×F÷FÂÖ&"G·f—7VÂæ6Æ75öæÖWÒG¶7F—fRòrF×7FB×6W76–öâÖ7F—fRr¢rwÒ"FF×F×7FBÖVæW&w’×6÷W&6SÒ"G·f—7VÂæ¶W—Ò"FF×F×7FB×6W76–öâ×f—7VÃÒ"G¶–æFW‡Ò#ãÂ÷&V7Cæ°¢Ð¢’æ¦ö–â‚rr“° ¢6öç7B†”§V×Ö&¶W'2Ð¢6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óâ°¢6öç7Bf—7VÂÐ¢6W76–öåf—7VÇ5°¢–æFW€¢Ó° ¢–b€¢f—7VÂæ†•ö§V×ÇÀ¢f—6–&ÆTÖ&¶W$–æFW†W2æ†2€¢–æFW€¢¢’°¢&WGW&ârs°¢Ð ¢6öç7BÖ&¶W%’Ð¢ÖF‚æÖ‚€¢F÷²BÀ¢F÷°¢Æ÷D†V–v‡BÐ¢&$†V–v‡Df÷"€¢7F–öà¢’Ð¢p¢“° ¢&WGW&âÆ6—&6ÆR7ƒÒ"G·ö–çE‚†–æFW‚’çFôf—†VBƒ"—Ò"7“Ò"G¶Ö&¶W%’çFôf—†VBƒ"—Ò"#Ò#B"6Æ73Ò'F×7FBÖ†’Ö§V×ÖÖ&¶W""&–Ö†–FFVãÒ'G'VR#ãÂö6—&6ÆSæ°¢Ð¢’æ¦ö–â‚rr“° ¢6öç7B6÷W&6TÆVvVæBÐ¢'&’æg&öÒ€¢æWrÖ€¢6W76–öåf—7VÇ2æÖ€¢f—7VÂÓâ°¢f—7VÂæ¶W’À¢f—7VÀ¢Ð¢¢’çfÇVW2‚¢’æÖ€¢f—7VÂÓà¢Ç7ããÆ’6Æ73Ò'F×7FB×6÷W&6RÖ¶W’F×7FB×6÷W&6RÖ¶W’ÒG·f—7VÂæ¶W—Ò#ãÂö“âG¶W66T7F—f—G”‡FÖÂ‡f—7VÂæÆ&VÂ—ÓÂ÷7ãæ ¢’æ¦ö–â‚rr“° ¢6öç7B†”§V×ÆVvVæBÐ¢6W76–öåf—7VÇ2ç6öÖR€¢f—7VÂÓà¢f—7VÂæ†•ö§V× ¢¢òsÇ7ããÆ’6Æ73Ò'F×7FBÖ†’Ö§V×Ö¶W’#ãÂö“å÷FVçF–Â†’§V×Â÷7ãâp¢¢rs° ¢6öç7B&$†—G2Ð¢6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óâ°¢6öç7BFWF–ÂÐ¢7FDw&÷wF„7V×VÆF—fU6×ÆTFWF–Â€¢7F–öà¢“°¢6öç7B7F–öä¶W’Ð¢7FDw&÷wF…6W76–öä7F–öä¶W’€¢7F–öà¢“°¢6öç7B†—Ev–GF‚Ð¢ÖF‚æÖ–â€¢3bÀ¢ÖF‚æÖ‚€¢#BÀ¢&%v–GF‚°¢`¢¢“° ¢&WGW&â ¢Ç&V7@¢ƒÒ"G²‡ö–çE‚†–æFW‚’Ò†—Ev–GF‚ò"’çFôf—†VBƒ"—Ò ¢“Ò"G·F÷Ò ¢v–GFƒÒ"G¶†—Ev–GF‚çFôf—†VBƒ"—Ò ¢†V–v‡CÒ"G·Æ÷D†V–v‡BçFôf—†VBƒ"—Ò ¢6Æ73Ò'F×7FB×F÷FÂÖ&"Ö†—B ¢FF×F×7FB×F÷FÂÖFWF–ÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢FF×F×7FB×6W76–öâÖ–æFWƒÒ"G¶–æFW‡Ò ¢FF×F×7FBÖæÖSÒ"G¶W66T7F—f—G”‡FÖÂ‡7FB—Ò ¢FF×F×7FBÖ7F–öâÖ¶W“Ò"G¶W66T7F—f—G”‡FÖÂ†7F–öä¶W’—Ò ¢&–Ö†–FFVãÒ'G'VR ¢F&–æFWƒÒ"Ó ¢ãÂ÷&V7Cà¢°¢Ð¢’æ¦ö–â‚rr“° ¢6öç7Bö–çG2Ð¢6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óâ°¢6öç7BFWF–ÂÐ¢7FDw&÷wF„7V×VÆF—fU6×ÆTFWF–Â€¢7F–öà¢“°¢6öç7B7F–öä¶W’Ð¢7FDw&÷wF…6W76–öä7F–öä¶W’€¢7F–öà¢“°¢6öç7B7F—fRÐ¢–æFW‚ÓÓÐ¢6×ÆW2æÆVæwF‚Ò°¢6öç7BÖ&¶W%f—6–&ÆRÐ¢f—6–&ÆTÖ&¶W$–æFW†W2æ†2€¢–æFW€¢“° ¢&WGW&â ¢Æ6—&6ÆP¢7ƒÒ"G·ö–çE‚†–æFW‚’çFôf—†VBƒ"—Ò ¢7“Ò"G·ö–çE’„çVÖ&W"†7F–öâç7FEögFW"ÇÂ’’çFôf—†VBƒ"—Ò ¢#Ò#‚ ¢6Æ73Ò'F×7FB×F÷FÂÖ†—B ¢FF×F×7FB×F÷FÂÖFWF–ÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢FF×F×7FB×6W76–öâÖ–æFWƒÒ"G¶–æFW‡Ò ¢FF×F×7FBÖæÖSÒ"G¶W66T7F—f—G”‡FÖÂ‡7FB—Ò ¢FF×F×7FBÖ7F–öâÖ¶W“Ò"G¶W66T7F—f—G”‡FÖÂ†7F–öä¶W’—Ò ¢&öÆSÒ&'WGFöâ ¢F&–æFWƒÒ# ¢&–×&W76VCÒ"G¶7F—fRòwG'VRr¢vfÇ6RwÒ ¢&–ÖÆ&VÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢ãÂö6—&6ÆSà¢Æ6—&6ÆP¢7ƒÒ"G·ö–çE‚†–æFW‚’çFôf—†VBƒ"—Ò ¢7“Ò"G·ö–çE’„çVÖ&W"†7F–öâç7FEögFW"ÇÂ’’çFôf—†VBƒ"—Ò ¢#Ò#2ãr ¢6Æ73Ò'F×7FB×F÷FÂ×ö–çBG¶Ö&¶W%f—6–&ÆRòrr¢rF×7FBÖÖ&¶W"Ö†–FFVâwÒG¶7F—fRòrF×7FB×6W76–öâÖ7F—fRr¢rwÒ ¢FF×F×7FB×6W76–öâ×f—7VÃÒ"G¶–æFW‡Ò ¢FF×F×7FBÖÖ&¶W"×f—6–&ÆSÒ"G¶Ö&¶W%f—6–&ÆRòwG'VRr¢vfÇ6RwÒ ¢ãÂö6—&6ÆSà¢°¢Ð¢’æ¦ö–â‚rr“° ¢6öç7B6W76–öä÷&FW"Ð¢7FDw&÷wF…&ævUW6W56W76–öç2€¢6VÆV7FVE&ævP¢“°¢6öç7Bf—'7DFFRÐ¢6W76–öä÷&FW ¢òtöÆFW7Bp¢¢æWrFFR€¢çVÖ&W"‡6×ÆW5³ÒçF–ÖW7F×ÇÂ’ ¢ ¢’çFôÆö6ÆTFFU7G&–ær€¢VæFVf–æVBÀ¢°¢ÖöçFƒ¢w6†÷'BrÀ¢F“¢vçVÖW&–2p¢Ð¢“° ¢6öç7BÆ7DFFRÐ¢6W76–öä÷&FW ¢òtÆFW7Bp¢¢æWrFFR€¢çVÖ&W"‡6×ÆW5·6×ÆW2æÆVæwF‚ÒÒçF–ÖW7F×ÇÂ’ ¢ ¢’çFôÆö6ÆTFFU7G&–ær€¢VæFVf–æVBÀ¢°¢ÖöçFƒ¢w6†÷'BrÀ¢F“¢vçVÖW&–2p¢Ð¢“° ¢6öç7Bf—'7E6W76–öâÐ¢6×ÆW5°¢6×ÆW2æÆVæwF‚Ò¢Ó° ¢&WGW&â ¢ÆF—b6Æ73Ò'FÖ6†'BÖ6&BF×7FB×F÷FÂÖ6†'B"FF×F×7FB×F÷FÂÖ6&Cà¢ÆF—b6Æ73Ò'FÖ6†'BÖ†VF–ær#à¢Ç7ãäö'6W'fVBF÷FÂf×²6W76–öâv–ãÂ÷7ãà¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ†Æ&VÂ—Ò+rG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…&ævTÆ&VÂ‡6VÆV7FVE&ævR’—Ò+rG·6×ÆW2æÆVæwF‡Òö'6W'fF–öç3Â÷7ãà¢ÂöF—cà ¢Ç7frf–Wt&÷ƒÒ#G·v–GF‡ÒG¶†V–v‡GÒ"&öÆSÒ&–Ör"&–ÖÆ&VÃÒ"G¶W66T7F—f—G”‡FÖÂ†Æ&VÂ—Òö'6W'fVBF÷FÂÆ–æRG·6W76–öä÷&FW"òv–âöÆFW7B×FòÖÆFW7B6W76–öâ÷&FW"r¢v÷fW"6ÆVæF"F–ÖRwÒv—F‚6W76–öâv–â&'26Æ76–f–VB'’ö'6W'fVBVæW&w’×6÷W&6RWf–FVæ6R"6Æ73Ò'F×7FB×F÷FÂ×7fr"FF×F×7FB×F÷FÂ×7fsà¢ÆÆ–æRƒÒ"G¶ÆVgGÒ"“Ò"G·F÷Ò"ƒ#Ò"G¶ÆVgGÒ"“#Ò"G·F÷²Æ÷D†V–v‡GÒ"6Æ73Ò'F×7FB×F÷FÂÖ†—2#ãÂöÆ–æSà¢ÆÆ–æRƒÒ"G¶ÆVgGÒ"“Ò"G·F÷²Æ÷D†V–v‡GÒ"ƒ#Ò"G¶ÆVgB²Æ÷Ev–GF‡Ò"“#Ò"G·F÷²Æ÷D†V–v‡GÒ"6Æ73Ò'F×7FB×F÷FÂÖ†—2#ãÂöÆ–æSà¢ÆÆ–æRƒÒ"G¶ÆVgGÒ"“Ò"G·F÷²Æ÷D†V–v‡Bò'Ò"ƒ#Ò"G¶ÆVgB²Æ÷Ev–GF‡Ò"“#Ò"G·F÷²Æ÷D†V–v‡Bò'Ò"6Æ73Ò'F×7FB×F÷FÂÖwV–FR#ãÂöÆ–æSà¢ÆFVg3à¢ÆÆ–æV$w&F–VçB–CÒ'F×7FBÖÖ—†VBÖVæW&w’"ƒÒ#"ƒ#Ò##à¢Ç7F÷öfg6WCÒ#R"7F÷Ö6öÆ÷#Ò"3Fc–F6R#ãÂ÷7F÷à¢Ç7F÷öfg6WCÒ#C‚R"7F÷Ö6öÆ÷#Ò"3Fc–F6R#ãÂ÷7F÷à¢Ç7F÷öfg6WCÒ#S"R"7F÷Ö6öÆ÷#Ò"3–svCB#ãÂ÷7F÷à¢Ç7F÷öfg6WCÒ#R"7F÷Ö6öÆ÷#Ò"3–svCB#ãÂ÷7F÷à¢ÂöÆ–æV$w&F–VçCà¢ÂöFVg3à¢G¶&'7Ð¢G¶†”§V×Ö&¶W'7Ð¢ÇF‚CÒ"G¶Æ–æWÒ"6Æ73Ò'F×7FB×F÷FÂÖÆ–æR#ãÂ÷Fƒà¢G·ö–çG7Ð¢G¶&$†—G7Ð¢ÇFW‡BƒÒ"G¶ÆVgBÒ‡Ò"“Ò"G·F÷²GÒ"FW‡BÖæ6†÷#Ò&VæB"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ"&–ÖÆ&VÃÒ$W†7BÖ†–×VÒF÷FÂG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDçVÖ&W"†Ö†–×VÕF÷FÂÂ"’—Ò#ãÇF—FÆSäW†7BÖ†–×VÒF÷FÂG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDçVÖ&W"†Ö†–×VÕF÷FÂÂ"’—ÓÂ÷F—FÆSâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7DçVÖ&W"†Ö†–×VÕF÷FÂÂ"’—ÓÂ÷FW‡Cà¢ÇFW‡BƒÒ"G¶ÆVgBÒ‡Ò"“Ò"G·F÷²Æ÷D†V–v‡GÒ"FW‡BÖæ6†÷#Ò&VæB"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ"&–ÖÆ&VÃÒ$W†7BÖ–æ–×VÒF÷FÂG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDçVÖ&W"†Ö–æ–×VÕF÷FÂÂ"’—Ò#ãÇF—FÆSäW†7BÖ–æ–×VÒF÷FÂG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDçVÖ&W"†Ö–æ–×VÕF÷FÂÂ"’—ÓÂ÷F—FÆSâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7DçVÖ&W"†Ö–æ–×VÕF÷FÂÂ"’—ÓÂ÷FW‡Cà¢ÇFW‡BƒÒ"G¶ÆVgGÒ"“Ò"G¶†V–v‡BÒ‡Ò"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ#âG¶W66T7F—f—G”‡FÖÂ†f—'7DFFR—ÓÂ÷FW‡Cà¢ÇFW‡BƒÒ"G¶ÆVgB²Æ÷Ev–GF‡Ò"“Ò"G¶†V–v‡BÒ‡Ò"FW‡BÖæ6†÷#Ò&VæB"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ#âG¶W66T7F—f—G”‡FÖÂ†Æ7DFFR—ÓÂ÷FW‡Cà¢Â÷7fsà ¢ÆF—b6Æ73Ò'F×7FB×F÷FÂÖÆVvVæB"&–ÖÆ&VÃÒ%6W76–öâ&"6Æ76–f–6F–öâÆVvVæB#à¢Ç7ããÆ’6Æ73Ò'F×7FB×F÷FÂÖÆ–æRÖ¶W’#ãÂö“åF÷FÂ7FCÂ÷7ãà¢G·6÷W&6TÆVvVæGÐ¢G¶†”§V×ÆVvVæGÐ¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FB×F÷FÂ×66ÆR#à¢G·6W76–öä÷&FW"òtWfVâ6W76–öâ76–ær+rr¢rwÕ6W76–öâv–â66ÆS¢(	2G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7Dv–â†Ö†–×VÔv–â’—Ò+rF&"ÂÆ–æRÂ÷"ö–çBf÷"W†7BfÇVW0¢ÂöF—cà ¢G·&VæFW%7FDw&÷wF…6W76–öä–ç7V7F÷"†f—'7E6W76–öâ—Ð ¢ÆF—b6Æ73Ò'F×7FB×÷7BÖ6†'BÖ6öçG&öÇ2#à¢G·&VæFW%7FDw&÷wF…66÷T6öçG&öÂ‡66÷R—Ð¢G·&VæFW%7FDw&÷wF„fö7W46öçG&öÂ†fö7W2Â6VÆV7FVD6öçFW‡BÂ6VÆV7FVE&ævRÂ66÷R—Ð¢G·&VæFW%7FDw&÷wF…66÷VDv–å7VÖÖ'’†w&÷wF‚Âfö7W2Â66÷RÂ6VÆV7FVE&ævRÂ6VÆV7FVD6öçFW‡B—Ð¢ÂöF—cà  ¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„ÆÄ6†'B€¢w&÷wF‚À¢fö7W2Òw&V6VçBrÀ¢6öçFW‡BÒvÆÂrÀ¢&ævRÒs2p¢’°¢6öç7B6VÆV7FVD6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢6öçFW‡@¢“°¢6öç7B6VÆV7FVE&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢&ævP¢“°¢6öç7BFVf–æ—F–öç2Ò°¢°¢7FC¢w7G&VæwF‚rÀ¢Æ&VÃ¢u7G&VæwF‚rÀ¢6†÷'C¢u5E"p¢ÒÀ¢°¢7FC¢vFVfVç6RrÀ¢Æ&VÃ¢tFVfVç6RrÀ¢6†÷'C¢tDTbp¢ÒÀ¢°¢7FC¢w7VVBrÀ¢Æ&VÃ¢u7VVBrÀ¢6†÷'C¢u5Bp¢ÒÀ¢°¢7FC¢vFW‡FW&—G’rÀ¢Æ&VÃ¢tFW‡FW&—G’rÀ¢6†÷'C¢tDU‚p¢Ð¢Ó°¢6öç7BÆæW2Ð¢FVf–æ—F–öç2æÖ€¢FVf–æ—F–öâÓâ‡°¢ââæFVf–æ—F–öâÀ¢6×ÆW3 ¢7FDw&÷wF„7V×VÆF—fU6×ÆW2€¢w&÷wF‚À¢FVf–æ—F–öâç7FBÀ¢6VÆV7FVE&ævRÀ¢6VÆV7FVD6öçFW‡@¢¢Ò¢“°¢6öç7BÆÅ6×ÆW2Ð¢ÆæW0¢æfÆDÖ€¢ÆæRÓà¢ÆæRç6×ÆW0¢¢ç6Æ–6R‚¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢çVÖ&W"†ÆVgCòçF–ÖW7F×ÇÂ’Ð¢çVÖ&W"‡&–v‡CòçF–ÖW7F×ÇÂ’ÇÀ¢7G&–ær†ÆVgCòæ–BÇÂrr’æÆö6ÆT6ö×&R€¢7G&–ær‡&–v‡Còæ–BÇÂrr¢¢“° ¢–b€¢ÆÅ6×ÆW2æÆVæwF€¢’°¢&WGW&â ¢ÆF—b6Æ73Ò'FÖ6†'BÖ6&BF×7FB×F÷FÂÖ6†'BF×7FBÖÆÂÖ6†'B"FF×F×7FB×F÷FÂÖ6&Cà¢ÆF—b6Æ73Ò'FÖ6†'BÖ†VF–ær#à¢Ç7ãäÆÂ×7FB†—7F÷'“Â÷7ãà¢Ç7ãäæòö'6W'fF–öç2+rG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…&ævTÆ&VÂ‡6VÆV7FVE&ævR’—ÓÂ÷7ãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×7FB×÷7BÖ6†'BÖ6öçG&öÇ2#à¢G·&VæFW%7FDw&÷wF…66÷T6öçG&öÂ‚vÆÂr—Ð¢G·&VæFW%7FDw&÷wF„fö7W46öçG&öÂ†fö7W2Â6VÆV7FVD6öçFW‡BÂ6VÆV7FVE&ævRÂvÆÂr—Ð¢G·&VæFW%7FDw&÷wF…66÷VDv–å7VÖÖ'’†w&÷wF‚Âfö7W2ÂvÆÂrÂ6VÆV7FVE&ævRÂ6VÆV7FVD6öçFW‡B—Ð¢ÂöF—cà¢ÂöF—cà¢°¢Ð ¢6öç7Bv–GF‚Ð¢c#°¢6öç7BÆVgBÐ¢#°¢6öç7B&–v‡BÐ¢#°¢6öç7BF÷Ð¢#°¢6öç7B&÷GFöÒÐ¢3°¢6öç7BÆæT†V–v‡BÐ¢Sƒ°¢6öç7BÆæTvÐ¢ƒ°¢6öç7B†V–v‡BÐ¢F÷°¢&÷GFöÒ°¢ÆæT†V–v‡B ¢ÆæW2æÆVæwF‚°¢ÆæTv ¢€¢ÆæW2æÆVæwF‚Ð¢¢“°¢6öç7BÆ÷Ev–GF‚Ð¢v–GF‚Ð¢ÆVgBÐ¢&–v‡C°¢6öç7BÖ–æ–×VÕF–ÖW7F×Ð¢ÖF‚æÖ–â€¢ââæÆÅ6×ÆW2æÖ€¢7F–öâÓà¢çVÖ&W"†7F–öãòçF–ÖW7F×ÇÂ¢¢“°¢6öç7BÖ†–×VÕF–ÖW7F×Ð¢ÖF‚æÖ‚€¢ââæÆÅ6×ÆW2æÖ€¢7F–öâÓà¢çVÖ&W"†7F–öãòçF–ÖW7F×ÇÂ¢¢“°¢6öç7BF–ÖW7F×&ævRÐ¢ÖF‚æÖ‚€¢À¢Ö†–×VÕF–ÖW7F×Ð¢Ö–æ–×VÕF–ÖW7F× ¢“°¢6öç7Bö–çE‚Ð¢7F–öâÓà¢Ö–æ–×VÕF–ÖW7F×ÓÓÐ¢Ö†–×VÕF–ÖW7F× ¢òÆVgB°¢Æ÷Ev–GF‚ð¢ ¢¢ÆVgB°¢€¢çVÖ&W"†7F–öãòçF–ÖW7F×ÇÂ’Ð¢Ö–æ–×VÕF–ÖW7F× ¢’ð¢F–ÖW7F×&ævR ¢Æ÷Ev–GFƒ°¢6öç7B6W76–öä÷&FW"Ð¢7FDw&÷wF…&ævUW6W56W76–öç2€¢6VÆV7FVE&ævP¢“°¢6öç7BÆFW7E6W76–öâÐ¢ÆÅ6×ÆW5°¢ÆÅ6×ÆW2æÆVæwF‚Ð¢¢Ó°¢6öç7BÆFW7E6W76–öä¶W’Ð¢G¶ÆFW7E6W76–öãòç7FBÇÂw7FBwÒÒGµ7G&–ær†ÆFW7E6W76–öãòæ–BÇÂÆFW7E6W76–öãòçF–ÖW7F×ÇÂrr—Ö°¢6öç7BÆFW7E6W76–öå7FBÐ¢7G&–ær€¢ÆFW7E6W76–öãòç7FBÇÀ¢rp¢“° ¢6öç7BÆæTÖ&·WÐ¢ÆæW2æÖ€¢€¢ÆæRÀ¢ÆæT–æFW€¢’Óâ°¢6öç7BÆæUF÷Ð¢F÷°¢ÆæT–æFW‚ ¢€¢ÆæT†V–v‡B°¢ÆæTv ¢“°¢6öç7BF÷FÇ2Ð¢ÆæRç6×ÆW2æÖ€¢7F–öâÓà¢çVÖ&W"†7F–öãòç7FEögFW"ÇÂ¢“°¢6öç7BÖ–æ–×VÕF÷FÂÐ¢F÷FÇ2æÆVæwF€¢òÖF‚æÖ–â€¢ââçF÷FÇ0¢¢¢°¢6öç7BÖ†–×VÕF÷FÂÐ¢F÷FÇ2æÆVæwF€¢òÖF‚æÖ‚€¢ââçF÷FÇ0¢¢¢°¢6öç7BF÷FÅ&ævRÐ¢ÖF‚æÖ‚€¢À¢Ö†–×VÕF÷FÂÐ¢Ö–æ–×VÕF÷FÀ¢“°¢6öç7BÆ–æUF÷Ð¢ÆæUF÷°¢ƒ°¢6öç7BÆ–æT†V–v‡BÐ¢ÆæT†V–v‡BÐ¢#C°¢6öç7Bö–çE’Ð¢7F–öâÓà¢ÆæRç6×ÆW2æÆVæwF‚ÓÓÐ¢¢òÆ–æUF÷°¢Æ–æT†V–v‡Bð¢ ¢¢Æ–æUF÷°¢€¢Ð¢€¢çVÖ&W"†7F–öãòç7FEögFW"ÇÂ’Ð¢Ö–æ–×VÕF÷FÀ¢’ð¢F÷FÅ&ævP¢’ ¢Æ–æT†V–v‡C°¢6öç7BÆæUö–çE‚Ð¢€¢7F–öâÀ¢–æFW€¢’Óà¢6W76–öä÷&FW ¢ò7FDw&÷wF…6W76–öä÷&FW%ö–çE‚€¢–æFW‚À¢ÆæRç6×ÆW2æÆVæwF‚À¢ÆVgBÀ¢Æ÷Ev–GF€¢¢¢ö–çE‚€¢7F–öà¢“°¢6öç7BF‚Ð¢ÆæRç6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óà¢G¶–æFW‚òtÂr¢tÒwÒG¶ÆæUö–çE‚†7F–öâÂ–æFW‚’çFôf—†VBƒ"—ÒG·ö–çE’†7F–öâ’çFôf—†VBƒ"—Ö ¢’æ¦ö–â‚rr“°¢6öç7Bf—6–&ÆTÖ&¶W$–æFW†W2Ð¢æWr6WB€¢7FDw&÷wF…f—6–&ÆTÖ&¶W$–æFW†W2€¢ÆæRç6×ÆW2À¢6VÆV7FVE&ævRÀ¢–æFW‚Óà¢ÆæUö–çE‚€¢ÆæRç6×ÆW5°¢–æFW€¢ÒÀ¢–æFW€¢’À¢ÆæRç6×ÆW2æÆVæwF‚Ò¢¢“°¢6öç7Bö–çG2Ð¢ÆæRç6×ÆW2æÖ€¢€¢7F–öâÀ¢–æFW€¢’Óâ°¢6öç7BFWF–ÂÐ¢7FDw&÷wF„7V×VÆF—fU6×ÆTFWF–Â€¢7F–öà¢“°¢6öç7B7F–öä¶W’Ð¢7FDw&÷wF…6W76–öä7F–öä¶W’€¢7F–öà¢“°¢6öç7B6W76–öä¶W’Ð¢G¶ÆæRç7FGÒÒGµ7G&–ær†7F–öãòæ–BÇÂ7F–öãòçF–ÖW7F×ÇÂrr—Ö°¢6öç7B7F—fRÐ¢6W76–öä¶W’ÓÓÐ¢ÆFW7E6W76–öä¶W“°¢6öç7BÖ&¶W%f—6–&ÆRÐ¢f—6–&ÆTÖ&¶W$–æFW†W2æ†2€¢–æFW€¢“° ¢&WGW&â ¢Æ6—&6ÆP¢7ƒÒ"G¶ÆæUö–çE‚†7F–öâÂ–æFW‚’çFôf—†VBƒ"—Ò ¢7“Ò"G·ö–çE’†7F–öâ’çFôf—†VBƒ"—Ò ¢#Ò#" ¢6Æ73Ò'F×7FB×F÷FÂÖ†—B ¢FF×F×7FB×F÷FÂÖFWF–ÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢FF×F×7FB×6W76–öâÖ–æFWƒÒ"G¶W66T7F—f—G”‡FÖÂ‡6W76–öä¶W’—Ò ¢FF×F×7FBÖæÖSÒ"G¶W66T7F—f—G”‡FÖÂ†ÆæRç7FB—Ò ¢FF×F×7FBÖ7F–öâÖ¶W“Ò"G¶W66T7F—f—G”‡FÖÂ†7F–öä¶W’—Ò ¢&öÆSÒ&'WGFöâ ¢F&–æFWƒÒ# ¢&–×&W76VCÒ"G¶7F—fRòwG'VRr¢vfÇ6RwÒ ¢&–ÖÆ&VÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢ãÂö6—&6ÆSà¢Æ6—&6ÆP¢7ƒÒ"G¶ÆæUö–çE‚†7F–öâÂ–æFW‚’çFôf—†VBƒ"—Ò ¢7“Ò"G·ö–çE’†7F–öâ’çFôf—†VBƒ"—Ò ¢#Ò#2ãB ¢6Æ73Ò'F×7FBÖÆæR×ö–çBF×7FBÖÆæRÒG¶ÆæRç7FGÒG¶Ö&¶W%f—6–&ÆRòrr¢rF×7FBÖÖ&¶W"Ö†–FFVâwÒG¶7F—fRòrF×7FB×6W76–öâÖ7F—fRr¢rwÒ ¢FF×F×7FB×6W76–öâ×f—7VÃÒ"G¶W66T7F—f—G”‡FÖÂ‡6W76–öä¶W’—Ò ¢FF×F×7FBÖÖ&¶W"×f—6–&ÆSÒ"G¶Ö&¶W%f—6–&ÆRòwG'VRr¢vfÇ6RwÒ ¢&–Ö†–FFVãÒ'G'VR ¢ãÂö6—&6ÆSà¢°¢Ð¢’æ¦ö–â‚rr“°¢6öç7BÆFW7EF÷FÂÐ¢ÆæRç6×ÆW2æÆVæwF€¢ò7FDw&÷wF„f÷&ÖD6ö×7DçVÖ&W"€¢ÆæRç6×ÆW5°¢ÆæRç6×ÆW2æÆVæwF‚Ð¢¢Óòç7FEögFW"À¢ ¢¢¢tæòFFs° ¢&WGW&â ¢Ær6Æ73Ò'F×7FBÖÆæRF×7FBÖÆæRÒG¶ÆæRç7FGÒG·6W76–öä÷&FW"òrr¢ÆæRç7FBÓÓÒÆFW7E6W76–öå7FBòrF×7FBÖÆæRÖ7F—fRr¢rF×7FBÖÆæRÖ×WFVBwÒ"FF×F×7FBÖÆæRÖw&÷WÒ"G¶W66T7F—f—G”‡FÖÂ†ÆæRç7FB—Ò#à¢Ç&V7BƒÒ"G¶ÆVgGÒ"“Ò"G¶ÆæUF÷Ò"v–GFƒÒ"G·Æ÷Ev–GF‡Ò"†V–v‡CÒ"G¶ÆæT†V–v‡GÒ"'ƒÒ#r"6Æ73Ò'F×7FBÖÆæRÖ&6¶w&÷VæB#ãÂ÷&V7Cà¢G·F‚òÇF‚CÒ"G·F‡Ò"6Æ73Ò'F×7FBÖÆæRÖÆ–æRF×7FBÖÆæRÒG¶ÆæRç7FGÒ#ãÂ÷Fƒæ¢rwÐ¢G·ö–çG7Ð¢ÇFW‡BƒÒ"G¶ÆVgB²wÒ"“Ò"G¶ÆæUF÷²7Ò"6Æ73Ò'F×7FBÖÆæRÖÆ&VÂF×7FBÖÆæRÒG¶ÆæRç7FGÒ#âG¶ÆæRç6†÷'GÓÂ÷FW‡Cà¢ÇFW‡BƒÒ"G¶ÆVgB²Æ÷Ev–GF‚ÒwÒ"“Ò"G¶ÆæUF÷²7Ò"FW‡BÖæ6†÷#Ò&VæB"6Æ73Ò'F×7FBÖÆæR×F÷FÂ#âG¶W66T7F—f—G”‡FÖÂ†ÆFW7EF÷FÂ—ÓÂ÷FW‡Cà¢Âösà¢°¢Ð¢’æ¦ö–â‚rr“°¢6öç7Bf—'7DFFRÐ¢6W76–öä÷&FW ¢òtöÆFW7Bp¢¢æWrFFR€¢Ö–æ–×VÕF–ÖW7F× ¢ ¢’çFôÆö6ÆTFFU7G&–ær€¢VæFVf–æVBÀ¢°¢ÖöçFƒ¢w6†÷'BrÀ¢F“¢vçVÖW&–2p¢Ð¢“°¢6öç7BÆ7DFFRÐ¢6W76–öä÷&FW ¢òtÆFW7Bp¢¢æWrFFR€¢Ö†–×VÕF–ÖW7F× ¢ ¢’çFôÆö6ÆTFFU7G&–ær€¢VæFVf–æVBÀ¢°¢ÖöçFƒ¢w6†÷'BrÀ¢F“¢vçVÖW&–2p¢Ð¢“°¢6öç7BÆFW7DÆæRÐ¢ÆæW2æf–æB€¢ÆæRÓà¢ÆæRç7FBÓÓÐ¢ÆFW7E6W76–öå7F@¢“°¢6öç7BÆFW7DÆæT–æFW‚Ð¢ÖF‚æÖ‚€¢À¢ÆFW7DÆæSòç6×ÆW3òæf–æD–æFW‚€¢7F–öâÓà¢7FDw&÷wF…6W76–öä7F–öä¶W’€¢7F–öà¢’ÓÓÐ¢7FDw&÷wF…6W76–öä7F–öä¶W’€¢ÆFW7E6W76–öà¢¢’ÇÀ¢ ¢“°¢6öç7BÆFW7DÆæT6÷VçBÐ¢çVÖ&W"€¢ÆFW7DÆæSòç6×ÆW3òæÆVæwF‚ÇÀ¢ ¢“°¢6öç7BÆFW7E6W76–öäÖöFVÂÐ¢7FDw&÷wF…6W76–öä–ç7V7F÷$ÖöFVÂ€¢ÆFW7E6W76–öà¢“°¢6öç7B6ÆVæF$æf–vF÷"Ð¢6W76–öä÷&FW ¢òrp¢¢ ¢ÆF—b6Æ73Ò'F×7FBÖ6ÆVæF"Öæf–vF÷""FF×F×7FBÖ6ÆVæF"Öæf–vF÷#à¢ÆF—b6Æ73Ò'F×7FBÖ6ÆVæF"Öæf–vF÷"Ö†VF–ær#à¢Ç7G&öærFF×F×7FBÖ6ÆVæF"Öæf–vF÷"ÖÆ&VÃâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…f–WtÆ&VÂ†ÆFW7E6W76–öå7FB’—Ò+rG¶ÆFW7DÆæT–æFW‚²ÒöbG¶ÆFW7DÆæT6÷VçGÓÂ÷7G&öæsà¢Ç7âFF×F×7FBÖ6ÆVæF"Öæf–vF÷"ÖFFSâG¶W66T7F—f—G”‡FÖÂ†ÆFW7E6W76–öäÖöFVÂæFFR—ÓÂ÷7ãà¢ÂöF—cà¢Æ–çW@¢G—SÒ'&ævR ¢Ö–ãÒ# ¢ÖƒÒ"G´ÖF‚æÖ‚ƒÂÆFW7DÆæT6÷VçBÒ—Ò ¢7FWÒ# ¢fÇVSÒ"G¶ÆFW7DÆæT–æFW‡Ò ¢FF×F×7FBÖ6ÆVæF"×67'V&&W ¢FF×F×7FBÖæÖSÒ"G¶W66T7F—f—G”‡FÖÂ†ÆFW7E6W76–öå7FB—Ò ¢&–ÖÆ&VÃÒ$'&÷w6RG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…f–WtÆ&VÂ†ÆFW7E6W76–öå7FB’—Ò6W76–öç2 ¢&–×fÇVWFW‡CÒ"G¶W66T7F—f—G”‡FÖÂ†ÆFW7E6W76–öäÖöFVÂæFFR—Ò ¢à¢Ç6ÖÆÃäG&rFòæV&'’W†7B6W76–öâ+rW6R(’(¢f÷"öæR6W76–öâBF–ÖSÂ÷6ÖÆÃà¢ÂöF—cà¢° ¢&WGW&â ¢ÆF—b6Æ73Ò'FÖ6†'BÖ6&BF×7FB×F÷FÂÖ6†'BF×7FBÖÆÂÖ6†'BG·6W76–öä÷&FW"òwF×7FB×6W76–öâÖ÷&FW"ÖÖöFRr¢wF×7FBÖ6ÆVæF"ÖÖöFRwÒ"FF×F×7FB×F÷FÂÖ6&Cà¢ÆF—b6Æ73Ò'FÖ6†'BÖ†VF–ær#à¢Ç7ãäÆÂ×7FB†—7F÷'“Â÷7ãà¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…&ævTÆ&VÂ‡6VÆV7FVE&ævR’—ÒG·7FDw&÷wF…&ævUW6W56W76–öç2‡6VÆV7FVE&ævR’òrW"7FBr¢rwÒ+rG¶ÆÅ6×ÆW2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—Òö'6W'fF–öç3Â÷7ãà¢ÂöF—cà ¢Ç7frf–Wt&÷ƒÒ#G·v–GF‡ÒG¶†V–v‡GÒ"&öÆSÒ&–Ör"&–ÖÆ&VÃÒ%7G&VæwF‚ÂFVfVç6RÂ7VVBÂæBFW‡FW&—G’ö'6W'fVBF÷FÇ2G·6W76–öä÷&FW"òv–â–æFWVæFVçBöÆFW7B×FòÖÆFW7B6W76–öâ÷&FW"W"7FBr¢÷fW"G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…&ævTÆ&VÂ‡6VÆV7FVE&ævR’—ÖÒ"6Æ73Ò'F×7FB×F÷FÂ×7frF×7FBÖÆÂ×7fr"FF×F×7FB×F÷FÂ×7fsà¢G¶ÆæTÖ&·WÐ¢ÇFW‡BƒÒ"G¶ÆVgGÒ"“Ò"G¶†V–v‡BÒ‡Ò"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ#âG¶W66T7F—f—G”‡FÖÂ†f—'7DFFR—ÓÂ÷FW‡Cà¢ÇFW‡BƒÒ"G¶ÆVgB²Æ÷Ev–GF‡Ò"“Ò"G¶†V–v‡BÒ‡Ò"FW‡BÖæ6†÷#Ò&VæB"6Æ73Ò'F×7FB×F÷FÂÖÆ&VÂ#âG¶W66T7F—f—G”‡FÖÂ†Æ7DFFR—ÓÂ÷FW‡Cà¢Â÷7fsà ¢ÆF—b6Æ73Ò'F×7FBÖÆæRÖÆVvVæBG·6W76–öä÷&FW"òrr¢rF×7FBÖÆæR×6VÆV7F÷"wÒ"&–ÖÆ&VÃÒ"G·6W76–öä÷&FW"òtÆÂ×7FB6†'BÆVvVæBr¢t6†ö÷6RF†R7F—fR7FBÆæRwÒ#à¢G¶FVf–æ—F–öç2æÖ€¢FVf–æ—F–öâÓâ°¢6öç7BÆæRÐ¢ÆæW2æf–æB€¢6æF–FFRÓà¢6æF–FFRç7FBÓÓÐ¢FVf–æ—F–öâç7F@¢“° ¢&WGW&â6W76–öä÷&FW ¢òÇ7ããÆ’6Æ73Ò'F×7FBÖÆæRÖ¶W’F×7FBÖÆæRÒG¶FVf–æ—F–öâç7FGÒ#ãÂö“âG¶FVf–æ—F–öâæÆ&VÇÓÂ÷7ãæ ¢¢Æ'WGFöâG—SÒ&'WGFöâ"FF×F×7FBÖÆæR×6VÆV7CÒ"G¶FVf–æ—F–öâç7FGÒ"&–×&W76VCÒ"G¶FVf–æ—F–öâç7FBÓÓÒÆFW7E6W76–öå7FBòwG'VRr¢vfÇ6RwÒ"G¶ÆæSòç6×ÆW3òæÆVæwF‚òrr¢vF—6&ÆVBwÓãÆ’6Æ73Ò'F×7FBÖÆæRÖ¶W’F×7FBÖÆæRÒG¶FVf–æ—F–öâç7FGÒ#ãÂö“âG¶FVf–æ—F–öâæÆ&VÇÓÂö'WGFöãæ°¢Ð¢’æ¦ö–â‚rr—Ð¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FB×F÷FÂ×66ÆR#à¢G·6W76–öä÷&FW"òtV6‚ÆæR'Vç2öÆFW7B(i"ÆFW7Bv—F‚WfVâ6W76–öâ76–ær+rFÆ–æR÷"ö–çBf÷"W†7BfÇVW2r¢tV6‚7FBW6W2—G2÷vâÆæRæB66ÆR+r6†ö÷6R7FBÂF†VâG&rf÷"W†7B6W76–öç2wÐ¢ÂöF—cà ¢G¶6ÆVæF$æf–vF÷'Ð ¢G·&VæFW%7FDw&÷wF…6W76–öä–ç7V7F÷"†ÆFW7E6W76–öâ—Ð ¢ÆF—b6Æ73Ò'F×7FB×÷7BÖ6†'BÖ6öçG&öÇ2#à¢G·&VæFW%7FDw&÷wF…66÷T6öçG&öÂ‚vÆÂr—Ð¢G·&VæFW%7FDw&÷wF„fö7W46öçG&öÂ†fö7W2Â6VÆV7FVD6öçFW‡BÂ6VÆV7FVE&ævRÂvÆÂr—Ð¢G·&VæFW%7FDw&÷wF…66÷VDv–å7VÖÖ'’†w&÷wF‚Âfö7W2ÂvÆÂrÂ6VÆV7FVE&ævRÂ6VÆV7FVD6öçFW‡B—Ð¢ÂöF—cà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢w&÷wF‚À¢fö7W2Òw&V6VçBrÀ¢6öçFW‡BÒvÆÂrÀ¢&ævRÒs2rÀ¢66÷RÒw6VÆV7FVBp¢’°¢&WGW&â66÷RÓÓÐ¢vÆÂp¢ò&VæFW%7FDw&÷wF„ÆÄ6†'B€¢w&÷wF‚À¢fö7W2À¢6öçFW‡BÀ¢&ævP¢¢¢&VæFW%7FDw&÷wF…6VÆV7FVD6†'B€¢w&÷wF‚À¢fö7W2À¢6öçFW‡BÀ¢&ævRÀ¢w6VÆV7FVBp¢“°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF…&V6VçD6†'B€¢w&÷wF‚À¢f–WrÒvÆÂp¢’°¢6öç7BÆ–÷WBÐ¢7F—f—G”F6†&ö&DÆ–÷WB‚“° ¢6öç7Bæ÷&ÖÆ—¦VEf–WrÐ¢V•6W76–öå7FEf–Wr€¢f–Wp¢“° ¢6öç7B&÷w2Ð¢7FDw&÷wF…&V6VçDF—2€¢w&÷wF‚À¢Æ–÷WBç&V6VçEöF—0¢“° ¢6öç7BÖ†–×VÒÐ¢ÖF‚æÖ‚€¢À¢ââç&÷w2æÖ€¢&÷rÓâ°¢6öç7B66÷VBÐ¢7FDw&÷wF…66÷VE&÷r€¢&÷rÀ¢æ÷&ÖÆ—¦VEf–Wp¢“° ¢&WGW&âçVÖ&W"€¢66÷VCòæv–âÇÀ¢ ¢“°¢Ð¢¢“° ¢6öç7B'F–ÂÐ¢7F—f—G”F6†&ö&E'F–ÅFöF”6öçFW‡B‡°¢F–ÖUö&6—3 ¢w&÷wFƒòçF–ÖUö&6—2À¢Æ7EöFFS ¢w&÷wFƒòæ†—7F÷'•öÆ7EöFFRÇÀ¢w&÷wFƒòæÆ7EöFFRÇÀ¢çVÆÂÀ¢Æ7E÷F–ÖW7F× ¢w&÷wFƒòæ†—7F÷'•öÆ7E÷F–ÖW7F×ÇÀ¢w&÷wFƒòæÆ7E÷F–ÖW7F×ÇÀ¢çVÆÀ¢Ò“° ¢6öç7B&'2Ð¢&÷w0¢æÖ€¢&÷rÓâ°¢6öç7B66÷VBÐ¢7FDw&÷wF…66÷VE&÷r€¢&÷rÀ¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7Bv–âÐ¢çVÖ&W"€¢66÷VCòæv–âÇÀ¢ ¢“° ¢6öç7B†V–v‡BÐ¢7F—f—G”F6†&ö&EW&6VçB€¢v–âÀ¢Ö†–×VÐ¢“° ¢6öç7B—5'F–ÂÐ¢'F–Âæ—5÷'F–Å÷FöF’b`¢&÷ræFFRÓÓÐ¢'F–ÂçFöF“° ¢6öç7BFWF–ÂÐ¢7FDw&÷wF„F”FWF–Â€¢&÷rÀ¢w&÷wF‚À¢Æ–÷WBç&V6VçEöF—2À¢æ÷&ÖÆ—¦VEf–Wp¢“° ¢&WGW&â ¢ÆF—`¢6Æ73Ò'FÖ6†'BÖ6öÇVÖâG¶—5'F–ÂòrFÖ6†'BÖ6öÇVÖâ×'F–Âr¢rwÒ ¢&öÆSÒ&'WGFöâ ¢F&–æFWƒÒ# ¢FF×F×7FBÖFWF–ÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢&–ÖÆ&VÃÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢F—FÆSÒ"G¶W66T7F—f—G”‡FÖÂ†FWF–Â—Ò ¢à¢ÆF—b6Æ73Ò'FÖ6†'B×fÇVR#à¢G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7Dv–â†v–â’—Ð¢ÂöF—cà¢ÆF—b6Æ73Ò'FÖ6†'B×&–Â#à¢ÆF—`¢6Æ73Ò'FÖ6†'BÖ&" ¢7G–ÆSÒ&†V–v‡C¢G¶†V–v‡GÒR ¢ãÂöF—cà¢ÂöF—cà¢ÆF—b6Æ73Ò'FÖ6†'BÖÆ&VÂ#à¢G¶W66T7F—f—G”‡FÖÂ†7F—f—G”F6†&ö&E6†÷'DFFR‡&÷ræFFR’—Ð¢G¶—5'F–ÂòsÇ7â6Æ73Ò'FÖ6†'B×'F–ÂÖ&FvR#ç'F–ÃÂ÷7ãâr¢rwÐ¢ÂöF—cà¢ÂöF—cà¢°¢Ð¢¢æ¦ö–â‚rr“° ¢6öç7Bf—'7BÐ¢&÷w5³ÒÇÀ¢çVÆÃ° ¢6öç7BÆ7BÐ¢&÷w5°¢&÷w2æÆVæwF‚Ò¢ÒÇÀ¢çVÆÃ° ¢6öç7BFFUv–æF÷rÐ¢f—'7Bb`¢Æ7@¢òG¶7F—f—G”F6†&ö&DÖöçF„F’†f—'7BæFFR—Þ(	2G¶7F—f—G”F6†&ö&DÖöçF„F’†Æ7BæFFR—Ö ¢¢rs° ¢&WGW&â ¢ÆF—b6Æ73Ò'FÖ6†'BÖ6&BF×7FBÖw&÷wF‚Ö6†'B#à¢ÆF—b6Æ73Ò'FÖ6†'BÖ†VF–ær#à¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…f–WtÆ&VÂ†æ÷&ÖÆ—¦VEf–Wr’—Òw&÷wFƒÂ÷7ãà¢Ç7ãäÆ7BG¶Æ–÷WBç&V6VçEöF—7Ò6ÆVæF"F—2+rG¶W66T7F—f—G”‡FÖÂ†FFUv–æF÷r—ÓÂ÷7ãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'FÖ6†'B×67&öÆÂ#à¢ÆF—`¢6Æ73Ò'FÖ6†'BÖ6öÇVÖç2FÖ6†'BÖ6öÇVÖç2ÖF–Ç’ ¢7G–ÆSÒ&w&–B×FV×ÆFRÖ6öÇVÖç3§&WVB‚G·&÷w2æÆVæwF‡ÒÆÖ–æÖ‚ƒÃg"’’ ¢à¢G¶&'7Ð¢ÂöF—cà¢ÂöF—cà ¢ÆF—`¢6Æ73Ò'FÖ6†'BÖFWF–Â ¢FF×F×7FBÖFWF–ÂÖ÷WGW@¢à¢FF’f÷"ö'6W'fVBv–âÂVæW&w’ÂG&–ç2ÂæB7FB'&V¶F÷vâà¢ÂöF—cà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF…v–æF÷w2€¢w&÷wF‚À¢f–WrÒvÆÂp¢’°¢6öç7Bæ÷&ÖÆ—¦VEf–WrÐ¢V•6W76–öå7FEf–Wr€¢f–Wp¢“°¢6öç7B6÷fW&vRÐ¢7FDw&÷wF…66÷VD6÷fW&vR€¢w&÷wF‚À¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7Bv–æF÷w2Ò°¢²svBrÂsrF—2rÂw&÷wFƒòç&V6VçEóuöF—2ÂçVÆÅÒÀ¢²sFBrÂsBF—2rÂw&÷wFƒòç&V6VçEóEöF—2ÂçVÆÅÒÀ¢²s3BrÂs3F—2rÂw&÷wFƒòç&V6VçEó3öF—2ÂçVÆÅÒÀ¢²tÆÂF–ÖRrÂtÆÂÆö6ÆÇ’&WF–æVB†—7F÷'’rÂw&÷wF‚Â6÷fW&vSòæÆ&VÂÇÂtæò&V6÷&FVBG&–æ–æruÐ¢Ó° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FB×v–æF÷r×F&ÆR×w&#à¢ÇF&ÆR6Æ73Ò'F×7FB×v–æF÷r×F&ÆR#à¢Æ6F–öãâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…f–WtÆ&VÂ†æ÷&ÖÆ—¦VEf–Wr’—Òö'6W'fVBw&÷wF‚6ö×&—6öãÂö6F–öãà¢ÇF†VCà¢ÇG#à¢ÇF‚66÷SÒ&6öÂ#åW&–öCÂ÷Fƒà¢ÇF‚66÷SÒ&6öÂ#äv–ãÂ÷Fƒà¢ÇF‚66÷SÒ&6öÂ#äVæW&w“Â÷Fƒà¢ÇF‚66÷SÒ&6öÂ#äv–âôSÂ÷Fƒà¢Â÷G#à¢Â÷F†VCà¢ÇF&öG“à¢G°¢v–æF÷w0¢æÖ€¢…°¢Æ&VÂÀ¢66W76–&ÆTÆ&VÂÀ¢&÷rÀ¢6÷fW&vTÆ&VÀ¢Ò’Óâ°¢6öç7B66÷VBÐ¢7FDw&÷wF…66÷VE&÷r€¢&÷rÀ¢æ÷&ÖÆ—¦VEf–Wp¢“° ¢&WGW&â ¢ÇG"&–ÖÆ&VÃÒ"G¶W66T7F—f—G”‡FÖÂ†66W76–&ÆTÆ&VÂ—Ò#à¢ÇF‚66÷SÒ'&÷r#à¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ†Æ&VÂ—ÓÂ÷7ãà¢G¶6÷fW&vTÆ&VÂòÇ6ÖÆÃâG¶W66T7F—f—G”‡FÖÂ†6÷fW&vTÆ&VÂ—ÓÂ÷6ÖÆÃæ¢rwÐ¢Â÷Fƒà¢ÇFBF—FÆSÒ"G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDv–â‡66÷VCòæv–âÇÂ’—Ò#âG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7Dv–â‡66÷VCòæv–âÇÂ’—ÓÂ÷FCà¢ÇFBF—FÆSÒ"G´çVÖ&W"‡66÷VCòæVæW&w•÷W6VBÇÂ’çFôÆö6ÆU7G&–ær‚—Ò#âG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖD6ö×7DçVÖ&W"‡66÷VCòæVæW&w•÷W6VBÇÂÂ’—ÓÂ÷FCà¢ÇFCâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖE&FR‡66÷VCòæv–å÷W%öVæW&w’ÇÂ’—ÓÂ÷FCà¢Â÷G#à¢°¢Ð¢¢æ¦ö–â‚rr¢Ð¢Â÷F&öG“à¢Â÷F&ÆSà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„FWF–Ç566÷R€¢w&÷wF‚À¢f–WrÒvÆÂp¢’°¢6öç7Bæ÷&ÖÆ—¦VEf–WrÐ¢V•6W76–öå7FEf–Wr€¢f–Wp¢“°¢6öç7B&÷rÐ¢7FDw&÷wF…66÷VE&÷r€¢w&÷wF‚À¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7BÆ&VÂÐ¢7FDw&÷wF…f–WtÆ&VÂ€¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7BG&–æ–ætF—2Ð¢7FDw&÷wF…66÷VEG&–æ–ætF—2€¢w&÷wF‚À¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7B&W7DF’Ð¢7FDw&÷wF…66÷VD&W7DF’€¢w&÷wF‚À¢æ÷&ÖÆ—¦VEf–Wp¢“°¢6öç7B7F–öä6÷VçBÐ¢çVÖ&W"€¢&÷sòæ7F–öç2óð¢w&÷wFƒòçfÆ–EöÆöw2óð¢ ¢“°¢6öç7BÖWG&–72Ò°¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢tVæW&w’G&–æVBrÀ¢çVÖ&W"‡&÷sòæVæW&w•÷W6VBÇÂ’çFôÆö6ÆU7G&–ær‚’À¢G´çVÖ&W"‡&÷sòçG&–ç2ÇÂ’çFôÆö6ÆU7G&–ær‚—Ò–æF—f–GVÂG&–ç2–âF†R6VÆV7FVBG¶Æ&VÇÒ†—7F÷'’æ ¢’À¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢tv–âòVæW&w’rÀ¢7FDw&÷wF„f÷&ÖE&FR€¢&÷sòæv–å÷W%öVæW&w’ÇÀ¢ ¢’À¢ö'6W'fVBG¶Æ&VÂçFôÆ÷vW$66R‚—Òv–âF—f–FVB'’W†7BVæW&w’W6VBæ ¢’À¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢uG&–æ–ærF—2rÀ¢G&–æ–ætF—2çFôÆö6ÆU7G&–ær‚’À¢6ÆVæF"F—26öçF–æ–ærö'6W'fVBG¶Æ&VÂçFôÆ÷vW$66R‚—ÒG&–æ–æræ ¢’À¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢t&W7Bw&÷wF‚F’rÀ¢&W7DF¢ò7FDw&÷wF„f÷&ÖDv–â€¢&W7DF’æv–à¢¢¢~(	BrÀ¢&W7DF“òæFFP¢òG¶7F—f—G”F6†&ö&DÆöætFFR†&W7DF’æFFR—Ò–âF†R6VÆV7FVBF–ÖR&6—2æ ¢¢æòö'6W'fVBG¶Æ&VÂçFôÆ÷vW$66R‚—ÒG&–æ–ærF’æ ¢’À¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢t†–æW726öç7VÖVBrÀ¢çVÖ&W"‡&÷sòæ†•÷W6VBÇÂ’çFôÆö6ÆU7G&–ær‚’À¢G´çVÖ&W"‡&÷sòæ†•ö¶æ÷våö7F–öç2ÇÂ’çFôÆö6ÆU7G&–ær‚—ÒòG¶7F–öä6÷VçBçFôÆö6ÆU7G&–ær‚—Ò7F–öç2–æ6ÇVFRfÆ–B†–æW72×W6VBFFæ ¢’À¢&VæFW%7FDw&÷wF„FVç6TÖWG&–2€¢uG&–æ–ær7F–öç2rÀ¢7F–öä6÷VçBçFôÆö6ÆU7G&–ær‚’À¢'6VBF÷&âw–Ò7F–öç2–æ6ÇVFVB–âF†R6VÆV7FVBG¶Æ&VÇÒ†—7F÷'’æ ¢¢Òæ¦ö–â‚rr“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖFWF–Ç2×66÷R"FF×F×7FBÖFWF–Ç2×66÷Sà¢ÆF—b6Æ73Ò'F×7FBÖw&÷wF‚Ö6ö×7BÖÖWG&–72#à¢G¶ÖWG&–77Ð¢ÂöF—cà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF…&V6VçEæVÂ€¢w&÷wF‚À¢f–WrÒvÆÂp¢’°¢6öç7Bæ÷&ÖÆ—¦VEf–WrÐ¢V•6W76–öå7FEf–Wr€¢f–Wp¢“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FB×&V6VçB×æVÂ"FF×F×7FB×&V6VçB×æVÃà¢G·&VæFW%7FDw&÷wF…v–æF÷w2†w&÷wF‚Âæ÷&ÖÆ—¦VEf–Wr—Ð ¢G·&VæFW%7FDw&÷wF…&V6VçD6†'B†w&÷wF‚Âæ÷&ÖÆ—¦VEf–Wr—Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„VæW&w”ÆÆö6F–öâ€¢w&÷wF€¢’°¢6öç7BF÷FÄVæW&w’Ð¢çVÖ&W"€¢w&÷wFƒòæVæW&w•÷W6VBÇÀ¢ ¢“° ¢–b€¢F÷FÄVæW&w’ÃÒ ¢’°¢&WGW&ârs°¢Ð ¢6öç7B&÷w2Ð¢°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Ð¢æÖ€¢7FBÓà¢w&÷wF‚ç7FG5·7FEÐ¢“° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×7FBÖFFÖ&Æö6²F×7FBÖVæW&w’ÖÆÆö6F–öâ#à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢Ç7ãäVæW&w’ÆÆö6F–öãÂ÷7ãà¢Ç7ãå6†&Röbö'6W'fVBw–ÒVæW&w“Â÷7ãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'FÖ6FVv÷'’ÖÆ—7B#à¢G°¢&÷w0¢æÖ€¢&÷rÓâ°¢6öç7BVæW&w’Ð¢çVÖ&W"€¢&÷ræVæW&w•÷W6VBÇÀ¢ ¢“° ¢6öç7BW&6VçBÐ¢VæW&w’ð¢F÷FÄVæW&w’ ¢° ¢&WGW&â ¢ÆF—b6Æ73Ò'FÖ6FVv÷'’×&÷r#à¢ÆF—b6Æ73Ò'FÖ6FVv÷'’×F÷Æ–æR#à¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡&÷ræÆ&VÂ—ÓÂ÷7ãà¢Ç7ãâG¶VæW&w’çFôÆö6ÆU7G&–ær‚—ÒR+rG·W&6VçBçFôf—†VBƒ—ÒSÂ÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'FÖ6FVv÷'’×G&6²#à¢ÆF—`¢6Æ73Ò'FÖ6FVv÷'’Öf–ÆÂ ¢7G–ÆSÒ'v–GFƒ¢G¶7F—f—G”F6†&ö&EW&6VçB†VæW&w’ÂF÷FÄVæW&w’Â"—ÒR ¢ãÂöF—cà¢ÂöF—cà¢ÂöF—cà¢°¢Ð¢¢æ¦ö–â‚rr¢Ð¢ÂöF—cà¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„w–Ô'&V¶F÷vâ€¢w&÷wF€¢’°¢6öç7Bw–×2Ð¢'&’æ—4'&’€¢w&÷wFƒòæw–×0¢¢òw&÷wF‚æw–×0¢¢µÓ° ¢–b€¢w–×2æÆVæwF€¢’°¢&WGW&ârs°¢Ð ¢6öç7B&÷w2Ð¢w–×0¢æÖ€¢w–ÒÓâ°¢6öç7BæÖRÐ¢7FDw&÷wF„w–ÔæÖR€¢w–Òæw–Õö–@¢“° ¢6öç7BVæW&w•W%G&–âÐ¢çVÖ&W"†w–ÒçG&–ç2ÇÂ’â ¢òçVÖ&W"†w–ÒæVæW&w•÷W6VBÇÂ’ð¢çVÖ&W"†w–ÒçG&–ç2¢¢° ¢6öç7B7FE'G2Ð¢°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Ð¢æÖ€¢7FBÓâ°¢6öç7B&÷rÐ¢w–Òç7FG3òå·7FEÓ° ¢&WGW&â&÷sòæv–à¢òG·&÷ræÆ&VÂç6Æ–6RƒÂ2’çFõWW$66R‚—ÒG·7FDw&÷wF„f÷&ÖDv–â‡&÷ræv–â—Ö ¢¢çVÆÃ°¢Ð¢¢æf–ÇFW"„&ööÆVâ¢æ¦ö–â‚r+rr“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×&÷r#à¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×F÷Æ–æR#à¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ†æÖR—ÓÂ÷7ãà¢Ç7ãà¢G´çVÖ&W"†w–ÒæVæW&w•÷W6VBÇÂ’çFôÆö6ÆU7G&–ær‚—ÒR+p¢G´çVÖ&W"†w–ÒçG&–ç2ÇÂ’çFôÆö6ÆU7G&–ær‚—ÒG&–ç0¢Â÷7ãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×fÇVW2#à¢Ç7ãà¢ö'6W'fVBv–âG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDv–â†w–Òæv–â’—Ð¢Â÷7ãà¢Ç7ãà¢G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖE&FR†w–Òæv–å÷W%öVæW&w’’—Òv–âôR+p¢G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDçVÖ&W"†VæW&w•W%G&–âÂ"’—ÒfrR÷G&–à¢Â÷7ãà¢ÂöF—cà ¢G°¢7FE'G0¢òÆF—b6Æ73Ò'F×7FBÖw–ÒÖæ÷FR#âG¶W66T7F—f—G”‡FÖÂ‡7FE'G2—ÓÂöF—cæ ¢¢rp¢Ð¢ÂöF—cà¢°¢Ð¢¢æ¦ö–â‚rr“° ¢&WGW&â ¢ÆFWF–Ç26Æ73Ò'F×7FBÖFFÖ&Æö6²F×7FBÖw–ÒÖ'&V¶F÷vâ#à¢Ç7VÖÖ'’6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢w&÷wF‚'’w–Ð¢Ç7ãâG¶w–×2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—Òw–×2ö'6W'fVCÂ÷7ãà¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ&öG’#à¢G·&÷w7Ð¢ÂöF—cà¢ÂöFWF–Ç3à¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„FFVÆ—G’€¢w&÷wF€¢’°¢6öç7B&V¦V7FVBÐ¢çVÖ&W"€¢w&÷wFƒòç&V¦V7FVEöÆöw2ÇÀ¢ ¢“° ¢6öç7Bv&æ–æw2Ð¢ö&¦V7BçfÇVW2€¢w&÷wFƒòçv&æ–æu÷&V6öç2ÇÀ¢·Ð¢’ç&VGV6R€¢€¢F÷FÂÀ¢fÇVP¢’Óà¢F÷FÂ°¢çVÖ&W"€¢fÇVRÇÀ¢ ¢’À¢ ¢“° ¢6öç7B7FGW2Ð¢&V¦V7FVBâ ¢òG·&V¦V7FVBçFôÆö6ÆU7G&–ær‚—Ò&V6övæ—¦VBw–ÒÆöw2&V¦V7FVB'’FVfVç6—fRfÆ–FF–öæ ¢¢tÆÂ&V6övæ—¦VBw–ÒG&–æ–ærÆöw276VBFVfVç6—fRfÆ–FF–öâs° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×7FBÖFFÖ&Æö6²F×7FB×VÆ—G’G·&V¦V7FVBòrF×7FB×VÆ—G’×v&æ–ærr¢rwÒ#à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢FFVÆ—G¢Ç7ãâG´çVÖ&W"†w&÷wFƒòçfÆ–EöÆöw2ÇÂ’çFôÆö6ÆU7G&–ær‚—ÒòG´çVÖ&W"†w&÷wFƒòç&V6övæ—¦VEöÆöw2ÇÂ’çFôÆö6ÆU7G&–ær‚—Ò'6VCÂ÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FBÖFFÖ&öG’#à¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#à¢G¶W66T7F—f—G”‡FÖÂ‡7FGW2—Òà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#à¢†–æW72Ö6öç7VÖVBFFv2fÆ–Bf÷ ¢G´çVÖ&W"†w&÷wFƒòæ†•ö¶æ÷våö7F–öç2ÇÂ’çFôÆö6ÆU7G&–ær‚—Òð¢G´çVÖ&W"†w&÷wFƒòçfÆ–EöÆöw2ÇÂ’çFôÆö6ÆU7G&–ær‚—Ò'6VB7F–öç2à¢ÂöF—cà¢G°¢v&æ–æw0¢òÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#âG·v&æ–æw2çFôÆö6ÆU7G&–ær‚—Ò÷F–öæÂÖWFFFv&æ–æw2vW&R&WF–æVBv—F†÷WBF—66&F–ær÷F†W'v—6RfÆ–Bö'6W'fVBv–ç2ãÂöF—cæ ¢¢rp¢Ð¢ÂöF—cà¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ&VæFW$æöäw–Õ7FDv–ä6æF–FFW2€¢w&÷wF€¢’°¢6öç7B6æF–FFW2Ð¢'&’æ—4'&’€¢w&÷wFƒòææöåöw–Õ÷7FEöv–åö6æF–FFW0¢¢òw&÷wF‚ææöåöw–Õ÷7FEöv–åö6æF–FFW0¢¢µÓ° ¢–b€¢6æF–FFW2æÆVæwF‚ÓÓÒ ¢’°¢&WGW&ârs°¢Ð ¢6öç7Bf—6–&ÆT6æF–FFW2Ð¢6æF–FFW0¢ç6Æ–6R€¢Ó€¢¢ç&WfW'6R‚“°¢6öç7B&÷w2Ð¢f—6–&ÆT6æF–FFW0¢æÖ€¢6æF–FFRÓâ°¢6öç7BÆöt–BÐ¢çVÖ&W"æ—56fT–çFVvW"€¢çVÖ&W"€¢6æF–FFSòæÆöuö–@¢¢¢ò7G&–ær€¢6æF–FFRæÆöuö–@¢¢¢uVæ¶æ÷vâs°¢6öç7BF—FÆRÐ¢7G&–ær€¢6æF–FFSòçF—FÆRÇÀ¢uVçF—FÆVB&V6÷&Bp¢“°¢6öç7B6FVv÷'’Ð¢7G&–ær€¢6æF–FFSòæ6FVv÷'’ÇÀ¢uVæ6FVv÷&—¦VBp¢“°¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢6æF–FFSòçF–ÖW7F× ¢“°¢6öç7Bö'6W'fVDBÐ¢çVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F× ¢’b`¢F–ÖW7F×â ¢òæWrFFR€¢F–ÖW7F× ¢ ¢’çFôÆö6ÆU7G&–ær‚¢¢uVæ¶æ÷vâF–ÖRs°¢6öç7Bf–VÆG2Ð¢€¢'&’æ—4'&’€¢6æF–FFSòæf–VÆG0¢¢ò6æF–FFRæf–VÆG0¢¢µÐ¢¢æÖ€¢f–VÆBÓà¢Gµ7G&–ær†f–VÆCòææÖRÇÂvf–VÆBr—ÓÒGµ7G&–ær†f–VÆCòçfÇVRóòrr—Ö ¢¢æ¦ö–â€¢r+rp¢“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×&÷r#à¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×F÷Æ–æR#à¢Ç7G&öæsäÆörG¶W66T7F—f—G”‡FÖÂ†Æöt–B—ÓÂ÷7G&öæsà¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡F—FÆR—ÓÂ÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FBÖw–Ò×fÇVW2#à¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ†6FVv÷'’—ÓÂ÷7ãà¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ†ö'6W'fVDB—ÓÂ÷7ãà¢ÂöF—cà¢G°¢f–VÆG0¢òÆF—b6Æ73Ò'F×7FBÖw–ÒÖæ÷FR#âG¶W66T7F—f—G”‡FÖÂ†f–VÆG2—ÓÂöF—cæ ¢¢rp¢Ð¢ÂöF—cà¢°¢Ð¢¢æ¦ö–â‚rr“° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×7FBÖFFÖ&Æö6²F×7FB×VÆ—G’G¶6æF–FFW2æÆVæwF‚òrF×7FB×VÆ—G’×v&æ–ærr¢rwÒ#à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢æöâÖw–Òv–âF—66÷fW'¢Ç7ãâG¶6æF–FFW2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—Ò÷76–&ÆRG¶6æF–FFW2æÆVæwF‚ÓÓÒòw&V6÷&Br¢w&V6÷&G2wÓÂ÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FBÖFFÖ&öG’#à¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#à¢F—66÷fW'’öæÇ’âF†W6R&V6÷&G2&RW†6ÇVFVBg&öÒF÷FÇ2æB&VF–7F–öç2VçF–ÂF†V—"ÆörG—RæBf–VÆG2&R6öæf—&ÖVBà¢ÂöF—cà¢G°¢&÷w2ÇÀ¢sÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#äæò÷76–&ÆR&×’÷"¦ö"×7V6–Â7FBv–ç2vW&Rf÷VæB–âF†R7F÷&VBÆöw2ãÂöF—câp¢Ð¢G°¢6æF–FFW2æÆVæwF‚âf—6–&ÆT6æF–FFW2æÆVæwF€¢òÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#å6†÷v–ærF†RG·f—6–&ÆT6æF–FFW2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—ÒÖ÷7B&V6VçB÷76–&ÆR&V6÷&G2ãÂöF—cæ ¢¢rp¢Ð¢ÂöF—cà¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ&VæFW$¦ö%7V6–Å7G&VæwF…7VÖÖ'’€¢w&÷wF€¢’°¢6öç7BfÆ–BÐ¢çVÖ&W"€¢w&÷wFƒòæ¦ö%÷7V6–Å÷fÆ–EöÆöw2ÇÀ¢ ¢“°¢6öç7B&V¦V7FVBÐ¢çVÖ&W"€¢w&÷wFƒòæ¦ö%÷7V6–Å÷&V¦V7FVEöÆöw2ÇÀ¢ ¢“° ¢–b€¢fÆ–BÓÓÒb`¢&V¦V7FVBÓÓÒ ¢’°¢&WGW&ârs°¢Ð ¢6öç7Bv–âÐ¢çVÖ&W"€¢w&÷wFƒòæ¦ö%÷7V6–Å÷7G&VæwF…öv–âÇÀ¢ ¢“°¢6öç7Bö–çG2Ð¢çVÖ&W"€¢w&÷wFƒòæ¦ö%÷7V6–Åö¦ö%÷ö–çG5÷W6VBÇÀ¢ ¢“° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×7FBÖFFÖ&Æö6²G·&V¦V7FVBòrF×7FB×VÆ—G’×v&æ–ærr¢rwÒ#à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢&×’¦ö"7V6–Ç0¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDv–â†v–â’—Ò7G&VæwF‚+rG·ö–çG2çFôÆö6ÆU7G&–ær‚—Ò¥Â÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FBÖFFÖ&öG’#à¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#à¢G·fÆ–BçFôÆö6ÆU7G&–ær‚—ÒfW&–f–VBG·fÆ–BÓÓÒòwW6Rr¢wW6W2wÒöbF÷&âÆörcCâ–æ6ÇVFVB–âÖF6†–ærW&–öBF÷FÇ2æB6†&V&ÆR&V63²W†6ÇVFVBg&öÒw–ÒVæW&w’Vff–6–Væ7’æB&VF–7F–öç2à¢ÂöF—cà¢G°¢&V¦V7FV@¢òÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#âG·&V¦V7FVBçFôÆö6ÆU7G&–ær‚—ÒÖÆf÷&ÖVBG·&V¦V7FVBÓÓÒòw&V6÷&Bv2r¢w&V6÷&G2vW&RwÒW†6ÇVFVBãÂöF—cæ ¢¢rp¢Ð¢ÂöF—cà¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ7FDw&÷wF„¦ö%7V6–Å7VÖÖ'’€¢w&÷wF‚À¢7FBÒvÆÂrÀ¢&ævRÒvÆÂrÀ¢6öçFW‡BÒvÆÂrÀ¢w–Õ6×ÆW2ÒµÐ¢’°¢–b€¢°¢vÆÂrÀ¢w7G&VæwF‚p¢Òæ–æ6ÇVFW2€¢7F@¢’ÇÀ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢6öçFW‡@¢’ÓÒvÆÂp¢’°¢&WGW&â°¢WfVçG3¢À¢v–ã¢À¢¦ö%÷ö–çG5÷W6VC¢ ¢Ó°¢Ð ¢6öç7Bæ÷&ÖÆ—¦VE&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢&ævP¢“°¢6öç7B&V6÷&G2Ð¢'&’æ—4'&’€¢w&÷wFƒòæ¦ö%÷7V6–Å÷7G&VæwF…öv–ç0¢¢òw&÷wF‚æ¦ö%÷7V6–Å÷7G&VæwF…öv–ç0¢¢µÓ°¢ÆWB6VÆV7FVBÐ¢&V6÷&G3° ¢–b€¢õâƒó£Ã#Ã3—2BòçFW7B€¢æ÷&ÖÆ—¦VE&ævP¢¢’°¢6öç7BF–ÖW7F×2Ð¢€¢'&’æ—4'&’€¢w–Õ6×ÆW0¢¢òw–Õ6×ÆW0¢¢µÐ¢¢æÖ€¢6×ÆRÓà¢çVÖ&W"€¢6×ÆSòçF–ÖW7F× ¢¢¢æf–ÇFW"€¢F–ÖW7F×Óà¢çVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F× ¢’b`¢F–ÖW7F×â ¢“° ¢–b€¢F–ÖW7F×2æÆVæwF‚ÓÓÒ ¢’°¢6VÆV7FVBÐ¢µÓ°¢ÒVÇ6R°¢6öç7Bf—'7EF–ÖW7F×Ð¢ÖF‚æÖ–â€¢ââçF–ÖW7F×0¢“°¢6öç7BÆ7EF–ÖW7F×Ð¢ÖF‚æÖ‚€¢ââçF–ÖW7F×0¢“° ¢6VÆV7FVBÐ¢&V6÷&G2æf–ÇFW"€¢&V6÷&BÓà¢çVÖ&W"‡&V6÷&CòçF–ÖW7F×’ãÒf—'7EF–ÖW7F×b`¢çVÖ&W"‡&V6÷&CòçF–ÖW7F×’ÃÒÆ7EF–ÖW7F× ¢“°¢Ð¢ÒVÇ6R–b€¢æ÷&ÖÆ—¦VE&ævRÓÒvÆÂp¢’°¢6öç7Bv–æF÷tF—2Ò°¢svBs¢rÀ¢sFBs¢BÀ¢s3Bs¢3 ¢Õ°¢æ÷&ÖÆ—¦VE&ævP¢Ó°¢6öç7BfÆÆ&6´VæDFFRÐ¢&V6÷&G2æB‚Ó“òæFFRÇÀ¢çVÆÃ°¢6öç7BVæDFFRÐ¢w&÷wFƒòæ†—7F÷'•öÆ7EöFFRÇÀ¢fÆÆ&6´VæDFFS°¢6öç7BVæDF’Ð¢7FDw&÷wF„F”çVÖ&W"€¢VæDFFP¢“° ¢–b€¢çVÖ&W"æ—4–çFVvW"€¢v–æF÷tF—0¢’ÇÀ¢çVÖ&W"æ—4f–æ—FR€¢VæDF¢¢’°¢6VÆV7FVBÐ¢µÓ°¢ÒVÇ6R°¢6öç7B7F'DF’Ð¢VæDF’Ð¢v–æF÷tF—2°¢° ¢6VÆV7FVBÐ¢&V6÷&G2æf–ÇFW"€¢&V6÷&BÓâ°¢6öç7BFFRÐ¢&V6÷&CòæFFRÇÀ¢7F—f—G”FFT¶W”f÷$&6—2€¢æWrFFR€¢çVÖ&W"‡&V6÷&CòçF–ÖW7F×ÇÂ’ ¢ ¢’À¢w&÷wFƒòçF–ÖUö&6—0¢“°¢6öç7BF’Ð¢7FDw&÷wF„F”çVÖ&W"€¢FFP¢“° ¢&WGW&âçVÖ&W"æ—4f–æ—FR€¢F¢’b`¢F’ãÒ7F'DF’b`¢F’ÃÒVæDF“°¢Ð¢“°¢Ð¢Ð ¢&WGW&â6VÆV7FVBç&VGV6R€¢€¢7VÖÖ'’À¢&V6÷&@¢’Óâ°¢7VÖÖ'’æWfVçG2²³°¢7VÖÖ'’æv–â³Ð¢çVÖ&W"€¢&V6÷&Còç7FEö–æ7&V6VBÇÀ¢ ¢“°¢7VÖÖ'’æ¦ö%÷ö–çG5÷W6VB³Ð¢çVÖ&W"€¢&V6÷&Còæ¦ö%÷ö–çG5÷W6VBÇÀ¢ ¢“° ¢&WGW&â7VÖÖ'“°¢ÒÀ¢°¢WfVçG3¢À¢v–ã¢À¢¦ö%÷ö–çG5÷W6VC¢ ¢Ð¢“°¢Ð ¢gVæ7F–öâ7FDw&÷wF…66÷VDv–å7VÖÖ'’€¢w&÷wF‚À¢fö7W2Òw&V6VçBrÀ¢66÷RÒw6VÆV7FVBrÀ¢&ævRÒvÆÂrÀ¢6öçFW‡BÒvÆÂp¢’°¢6öç7Bæ÷&ÖÆ—¦VDfö7W2Ð¢°¢w&V6VçBrÀ¢vÖ÷7E÷G&–æVBrÀ¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Òæ–æ6ÇVFW2€¢fö7W0¢¢òfö7W0¢¢w&V6VçBs° ¢6öç7Bæ÷&ÖÆ—¦VE66÷RÐ¢66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs° ¢6öç7B7FBÐ¢7FDw&÷wF„fö7W57FB€¢w&÷wF‚À¢æ÷&ÖÆ—¦VDfö7W0¢“° ¢6öç7B6VÆV7FVBÐ¢7F@¢òw&÷wFƒòç7FG3òå·7FEÐ¢¢çVÆÃ° ¢6öç7Bæ÷&ÖÆ—¦VE&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢&ævP¢“°¢6öç7Bæ÷&ÖÆ—¦VD6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢6öçFW‡@¢“°¢6öç7B7FG2Ð¢æ÷&ÖÆ—¦VE66÷RÓÓÐ¢vÆÂp¢ò°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Ð¢¢7F@¢ò·7FEÐ¢¢µÓ°¢6öç7B6×ÆW2Ð¢7FG2æfÆDÖ€¢7FDæÖRÓà¢7FDw&÷wF„7V×VÆF—fU6×ÆW2€¢w&÷wF‚À¢7FDæÖRÀ¢æ÷&ÖÆ—¦VE&ævRÀ¢æ÷&ÖÆ—¦VD6öçFW‡@¢¢“°¢6öç7Bw–Ôv–âÐ¢6×ÆW2ç&VGV6R€¢€¢F÷FÂÀ¢7F–öà¢’Óà¢F÷FÂ°¢çVÖ&W"€¢7F–öãòç7FEö–æ7&V6VBÇÀ¢ ¢’À¢ ¢“°¢6öç7B¦ö%7V6–ÂÐ¢7FDw&÷wF„¦ö%7V6–Å7VÖÖ'’€¢w&÷wF‚À¢æ÷&ÖÆ—¦VE66÷RÓÓÒvÆÂp¢òvÆÂp¢¢7FBÀ¢æ÷&ÖÆ—¦VE&ævRÀ¢æ÷&ÖÆ—¦VD6öçFW‡BÀ¢6×ÆW0¢“°¢6öç7Bv–âÐ¢w–Ôv–â°¢¦ö%7V6–Âæv–ã°¢6öç7BVæW&w•W6VBÐ¢6×ÆW2ç&VGV6R€¢€¢F÷FÂÀ¢7F–öà¢’Óà¢F÷FÂ°¢çVÖ&W"€¢7F–öãòæVæW&w•÷W6VBÇÀ¢ ¢’À¢ ¢“°¢6öç7BG&–æ–ætF—2Ð¢æWr6WB€¢6×ÆW0¢æÖ€¢7F–öâÓâ°¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢7F–öãòçF–ÖW7F× ¢“° ¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F× ¢’b`¢F–ÖW7F×â ¢ò7F—f—G”FFT¶W”f÷$&6—2€¢æWrFFR€¢F–ÖW7F× ¢ ¢’À¢w&÷wFƒòçF–ÖUö&6—0¢¢¢çVÆÃ°¢Ð¢¢æf–ÇFW"„&ööÆVâ¢’ç6—¦S° ¢&WGW&â°¢fö7W3 ¢æ÷&ÖÆ—¦VDfö7W2À¢66÷S ¢æ÷&ÖÆ—¦VE66÷RÀ¢7FBÀ¢Æ&VÃ ¢æ÷&ÖÆ—¦VE66÷RÓÓÐ¢vÆÂp¢òtÆÂ7FG2p¢¢6VÆV7FVCòæÆ&VÂÇÀ¢u6VÆV7FVB7FBrÀ¢&ævS ¢æ÷&ÖÆ—¦VE&ævRÀ¢&ævUöÆ&VÃ ¢7FDw&÷wF…&ævTÆ&VÂ€¢æ÷&ÖÆ—¦VE&ævP¢’À¢v–âÀ¢w–Õöv–ã ¢w–Ôv–âÀ¢¦ö%÷7V6–Åöv–ã ¢¦ö%7V6–Âæv–âÀ¢¦ö%÷7V6–ÅöWfVçG3 ¢¦ö%7V6–ÂæWfVçG2À¢¦ö%÷ö–çG5÷W6VC ¢¦ö%7V6–Âæ¦ö%÷ö–çG5÷W6VBÀ¢7F–öç3 ¢6×ÆW2æÆVæwF‚À¢VæW&w•÷W6VC ¢VæW&w•W6VBÀ¢v–å÷W%öVæW&w“ ¢VæW&w•W6VBâ ¢òw–Ôv–âð¢VæW&w•W6V@¢¢À¢G&–æ–æuöF—3 ¢G&–æ–ætF—0¢Ó°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF…66÷VDv–å7VÖÖ'’€¢w&÷wF‚À¢fö7W2Òw&V6VçBrÀ¢66÷RÒw6VÆV7FVBrÀ¢&ævRÒvÆÂrÀ¢6öçFW‡BÒvÆÂp¢’°¢6öç7B7VÖÖ'’Ð¢7FDw&÷wF…66÷VDv–å7VÖÖ'’€¢w&÷wF‚À¢fö7W2À¢66÷RÀ¢&ævRÀ¢6öçFW‡@¢“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖv–â×66÷RF×7FBÖ6ö×7BÖVff–6–Væ7’"FF×F×7FBÖv–â×7VÖÖ'“à¢Ç7G&öæsâG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDv–â‡7VÖÖ'’æv–â’—ÓÂ÷7G&öæsà¢Ç7ãà¢G¶W66T7F—f—G”‡FÖÂ‡7VÖÖ'’ç&ævUöÆ&VÂ—Ò+p¢G·7VÖÖ'’æ7F–öç2çFôÆö6ÆU7G&–ær‚—Ò7F–öç2+p¢G·7VÖÖ'’æVæW&w•÷W6VBçFôÆö6ÆU7G&–ær‚—ÒR+p¢G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖE&FR‡7VÖÖ'’æv–å÷W%öVæW&w’’—Òw–Òv–âôR+p¢G·7VÖÖ'’çG&–æ–æuöF—2çFôÆö6ÆU7G&–ær‚—ÒF—2G°¢7VÖÖ'’æ¦ö%÷7V6–Åöv–ââ ¢ò+rG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF„f÷&ÖDv–â‡7VÖÖ'’æ¦ö%÷7V6–Åöv–â’—Ò&×’7G&VæwF‚òG·7VÖÖ'’æ¦ö%÷ö–çG5÷W6VBçFôÆö6ÆU7G&–ær‚—Ò¥ ¢¢rp¢Ð¢Â÷7ãà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF…66÷T6öçG&öÂ€¢66÷RÒw6VÆV7FVBp¢’°¢6öç7B6VÆV7FVBÐ¢66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖv–â×66÷RÖ6öçG&öÇ2"FF×F×7FBÖv–â×66÷RÖ6öçG&öÇ2&öÆSÒ&w&÷W"&–ÖÆ&VÃÒ%7FB6†'B66÷R#à¢Gµ°¢²w6VÆV7FVBrÂu6VÆV7FVB7FBuÒÀ¢²vÆÂrÂtÆÂ7FG2uÐ¢ÒæÖ€¢…·fÇVRÂÆ&VÅÒ’Óâ ¢Æ'WGFöà¢G—SÒ&'WGFöâ ¢6Æ73Ò"G·fÇVRÓÓÒ6VÆV7FVBòwF×7FBÖv–â×66÷RÖ7F—fRr¢rwÒ ¢FF×F×7FBÖv–â×66÷RÖ÷F–öãÒ"G·fÇVWÒ ¢&–×&W76VCÒ"G·fÇVRÓÓÒ6VÆV7FVBòwG'VRr¢vfÇ6RwÒ ¢âG¶Æ&VÇÓÂö'WGFöãà¢ ¢’æ¦ö–â‚rr—Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„F6†&ö&B€¢w&÷wF‚À¢÷F–öç0¢’°¢6öç7B6fT÷F–öç2Ð¢÷F–öç2b`¢G—Vöb÷F–öç2ÓÓÐ¢vö&¦V7Bp¢ò÷F–öç0¢¢·Ó°¢6öç7Bfö7W2Ð¢V•6W76–öåG&–æ–ætfö7W2€¢6fT÷F–öç2æfö7W0¢“°¢6öç7B66÷RÐ¢6fT÷F–öç2ç66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs°¢6öç7B&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢6fT÷F–öç2ç&ævP¢“°¢6öç7B6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢6fT÷F–öç2æ6öçFW‡@¢“° ¢–b€¢w&÷wFƒòçfÆ–EöÆöw0¢’°¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FG2ÖV×G’×7FFR#à¢æòfÆ–BF÷&âw–Ò×G&–æ–ærÆöw2vW&Rf÷VæB–âF†R7F÷&VB†—7F÷'’à¢ÂöF—cà¢°¢Ð ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FBÖw&÷wF‚Ö6ö×7BÖ&öG’#à¢G·&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B†w&÷wF‚Âfö7W2Â6öçFW‡BÂ&ævRÂ66÷R—Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FDw&÷wF„FFf–Wr€¢w&÷wF‚À¢&VF–æW72ÒçVÆÂÀ¢ÆåfÇVRÒçVÆÂÀ¢7FEfÇVRÒçVÆÀ¢’°¢–b€¢w&÷wF€¢’°¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FG2ÖV×G’×7FFR#à¢æò7F÷&VBG&–æ–ærFF—2f–Æ&ÆR–WBà¢ÂöF—cà¢°¢Ð ¢6öç7B6V7F–öç2Ò°¢&VæFW%&VF–7F–öå&VÆ–&–Æ—G”FF‡&VF–æW72ÂÆåfÇVRÂ7FEfÇVR’À¢&VæFW%7FDw&÷wF„VæW&w”ÆÆö6F–öâ†w&÷wF‚’À¢&VæFW%7FDw&÷wF„w–Ô'&V¶F÷vâ†w&÷wF‚’À¢&VæFW$¦ö%7V6–Å7G&VæwF…7VÖÖ'’†w&÷wF‚’À¢&VæFW$æöäw–Õ7FDv–ä6æF–FFW2†w&÷wF‚’À¢&VæFW%7FDw&÷wF„FFVÆ—G’†w&÷wF‚¢Òæf–ÇFW"„&ööÆVâ“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FG2ÖFFÖÆ—7B#à¢G·6V7F–öç2æ¦ö–â‚rr—Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%&VF–7F–öå&VÆ–&–Æ—G”FF€¢&VF–æW72À¢ÆåfÇVRÒçVÆÂÀ¢7FEfÇVRÒçVÆÀ¢’°¢6öç7BÆâÒG&–æ–æu&VF–æW75Æâ€¢ÆåfÇVRÇÂ&VEG&–æ–æu&VF–æW75Æâ‚¢“°¢6öç7B&WVW7FVE7FBÒ7FDw&÷wF„6ö×7E7VÖÖ'•7FB‡7FEfÇVR“°¢6öç7B7FBÒ²w7G&VæwF‚rÂvFVfVç6RrÂw7VVBrÂvFW‡FW&—G’uÒæ–æ6ÇVFW2‡&WVW7FVE7FB¢ò&WVW7FVE7F@¢¢&VF–æW73òæFVfVÇE÷7FBÇÂw7G&VæwF‚s°¢6öç7BÖöFVÂÒG&–æ–æu&VF–æW75&VF–7F–öäÖöFVÂ‡&VF–æW72Â7FBÂÆâ“°¢6öç7B&VF–7F–öç2ÒçVÖ&W"†ÖöFVÃòæ&6·FW7E÷&VF–7F–öç2ÇÂ“°¢6öç7BW'&÷"Ð¢ÖöFVÃòçG—–6ÅöW'&÷%÷W&6VçBÓÒçVÆÂb`¢ÖöFVÃòçG—–6ÅöW'&÷%÷W&6VçBÓÒVæFVf–æVBb`¢ÖöFVÃòçG—–6ÅöW'&÷%÷W&6VçBÓÒrrb`¢çVÖ&W"æ—4f–æ—FR„çVÖ&W"†ÖöFVÂçG—–6ÅöW'&÷%÷W&6VçB’¢òçVÖ&W"†ÖöFVÂçG—–6ÅöW'&÷%÷W&6VçB¢¢çVÆÃ°¢6öç7BW'&÷%FW‡BÒW'&÷"ÓÒçVÆÀ¢ò+G·7FDw&÷wF„f÷&ÖDçVÖ&W"†W'&÷"Â—ÒRG—–6ÂW'&÷& ¢¢t†—7F÷&–6ÂW'&÷"VæF–ærs°¢6öç7BÖWF†öBÒ&VF–7F–öç2â ¢òG·&VF–7F–öç2çFôÆö6ÆU7G&–ær‚—Ò6‡&öæöÆöv–6ÂG·&VF–7F–öç2ÓÓÒòw&VF–7F–öâr¢w&VF–7F–öç2wÒ6†V6¶VBv—F†÷WBgWGW&R×6W76–öâÆöö¶†VBæ ¢¢tBÆV7BF‡&VRÖF6†–ær6W76–öç2&RæVVFVB&Vf÷&R†—7F÷&–6ÂW'&÷"6â&RÖV7W&VBâs° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×7FBÖFFÖ&Æö6²"FF×F×&VF–7F–öâ×&VÆ–&–Æ—G“à¢ÆF—b6Æ73Ò'F×7FBÖFFÖ†VF–ær#à¢&VF–7F–öâWf–FVæ6P¢Ç7ãâG¶W66T7F—f—G”‡FÖÂ‡G&–æ–æu&VF–æW757FDÆ&VÂ‡7FB’—Ò+rG·ÆâÓÓÒv†•ö§V×ròt†’§V×r¢tVff–6–VçBwÒ+rG¶W66T7F—f—G”‡FÖÂ†W'&÷%FW‡B—ÓÂ÷7ãà¢ÂöF—cà¢ÆF—b6Æ73Ò'F×7FBÖFFÖ&öG’#à¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#âG¶W66T7F—f—G”‡FÖÂ‡G&–æ–æu&VF–æW74Wf–FVæ6UFW‡B†ÖöFVÂ’—ÓÂöF—cà¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#âG¶W66T7F—f—G”‡FÖÂ†ÖWF†öB—ÓÂöF—cà¢ÆF—b6Æ73Ò'F×7FB×VÆ—G’ÖÆ–æR#äöæÇ’ÖF6†–ær7FBÂ¶æ÷vâw–ÒÂæBö'6W'fVB†–æW726öçFW‡B6W76–öç2&R6ö×&VBãÂöF—cà¢ÂöF—cà¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ7FDw&÷wF„æV&W7D7V×VÆF—fUö–çB€¢ö–çG2À¢F&vWE‚À¢F&vWE’ÒçVÆÀ¢’°¢6öç7B‚Ð¢çVÖ&W"€¢F&vWE€¢“° ¢–b€¢çVÖ&W"æ—4f–æ—FR€¢€¢¢’°¢&WGW&âçVÆÃ°¢Ð ¢ÆWBæV&W7BÐ¢çVÆÃ°¢6öç7B’Ð¢çVÖ&W"€¢F&vWE¢“°¢6öç7BW6U’Ð¢F&vWE’ÓÐ¢çVÆÂb`¢F&vWE’ÓÐ¢VæFVf–æVBb`¢çVÖ&W"æ—4f–æ—FR€¢¢“° ¢f÷"€¢6öç7B6æF–FFP¢öb'&’æ—4'&’€¢ö–çG0¢¢òö–çG0¢¢µÐ¢’°¢6öç7B6æF–FFU‚Ð¢çVÖ&W"€¢6æF–FFSòç€¢“° ¢–b€¢çVÖ&W"æ—4f–æ—FR€¢6æF–FFU€¢¢’°¢6öçF–çVS°¢Ð ¢6öç7B6æF–FFU’Ð¢çVÖ&W"€¢6æF–FFSòç¢“°¢6öç7B„F—7Fæ6RÐ¢6æF–FFU‚Ð¢ƒ°¢6öç7B”F—7Fæ6RÐ¢W6U’b`¢çVÖ&W"æ—4f–æ—FR€¢6æF–FFU¢¢ò6æF–FFU’Ð¢¢¢°¢6öç7BF—7Fæ6RÐ¢W6U’b`¢çVÖ&W"æ—4f–æ—FR€¢6æF–FFU¢¢òÖF‚æ‡—÷B€¢„F—7Fæ6RÀ¢”F—7Fæ6R ¢ã3P¢¢¢ÖF‚æ'2€¢„F—7Fæ6P¢“° ¢–b€¢æV&W7BÇÀ¢F—7Fæ6RÀ¢æV&W7BæF—7Fæ6P¢’°¢æV&W7BÒ°¢ö–çC¢6æF–FFRçö–çBÇÀ¢çVÆÂÀ¢F—7Fæ6P¢Ó°¢Ð¢Ð ¢&WGW&âæV&W7Còçö–çBÇÀ¢çVÆÃ°¢Ð  ¢gVæ7F–öâ&–æE7FDw&÷wF„F6†&ö&D–çFW&7F–öç2€¢&ö÷BÀ¢w&÷wF‚ÒçVÆÀ¢’°¢–b€¢&ö÷CòçVW'•6VÆV7F÷$ÆÀ¢’°¢&WGW&ã°¢Ð ¢6öç7BV•7FFRÐ¢&VEV•6W76–öå7FFR‚“°¢6öç7B7FDw&÷wF…&VfW&Væ6W2Ð¢&VE7FDw&÷wF…&VfW&Væ6W2‚“° ¢&ö÷Båõ÷F7FDw&÷wF‚Ð¢w&÷wF‚ÇÀ¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢çVÆÃ° ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2Ð¢V•6W76–öåG&–æ–ætfö7W2€¢7FDw&÷wF…&VfW&Væ6W2ç7FEöw&÷wF…öfö7W2ÇÀ¢V•7FFRç7FEöw&÷wF…öfö7W0¢“° ¢&ö÷Båõ÷F7FDw&÷wF…66÷RÐ¢V•7FFRç7FEöw&÷wF…÷66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs° ¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢V•7FFRç7FEöw&÷wF…ö6öçFW‡@¢“° ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢V•7FFRç7FEöw&÷wF…÷&ævP¢“° ¢6öç7B&–æE&V6VçD6†'D–çFW&7F–öç2Ð¢66÷RÓâ°¢6öç7B6öÇVÖç2Ð¢'&’æg&öÒ€¢66÷RçVW'•6VÆV7F÷$ÆÂ€¢rçFÖ6†'BÖ6öÇVÖå¶FF×F×7FBÖFWF–ÅÒp¢¢“° ¢6öç7B7F—fFRÐ¢6öÇVÖâÓâ°¢6öç7B6&BÐ¢6öÇVÖãòæ6Æ÷6W7Còâ€¢rçFÖ6†'BÖ6&Bp¢“° ¢–b€¢6&@¢’°¢&WGW&ã°¢Ð ¢6öç7B÷WGWBÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖFWF–ÂÖ÷WGWEÒp¢“° ¢–b€¢÷WGW@¢’°¢÷WGWBçFW‡D6öçFVçBÐ¢6öÇVÖâævWDGG&–'WFR€¢vFF×F×7FBÖFWF–Âp¢’ÇÀ¢rs°¢Ð ¢f÷"€¢6öç7B6æF–FFP¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢rçFÖ6†'BÖ6öÇVÖå¶FF×F×7FBÖFWF–ÅÒp¢¢’°¢6æF–FFRæ6Æ74Æ—7BçFövvÆR€¢wFÖ6†'BÖ6öÇVÖâÖ7F—fRrÀ¢6æF–FFRÓÓÒ6öÇVÖà¢“°¢Ð¢Ó° ¢f÷"€¢6öç7B6öÇVÖà¢öb6öÇVÖç0¢’°¢6öÇVÖâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óà¢7F—fFR€¢6öÇVÖà¢¢“° ¢6öÇVÖâæFDWfVçDÆ—7FVæW"€¢v¶W–F÷vârÀ¢WfVçBÓâ°¢–b€¢WfVçBæ¶W’ÓÒtVçFW"rb`¢WfVçBæ¶W’ÓÒrp¢’°¢&WGW&ã°¢Ð ¢WfVçBç&WfVçDFVfVÇB‚“°¢7F—fFR€¢6öÇVÖà¢“°¢Ð¢“°¢Ð¢Ó° ¢6öç7B7W'&VçDfö7W5f–WrÐ¢‚’Óà¢7FDw&÷wF„fö7W5f–Wr€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W0¢“° ¢6öç7B7W'&VçDw&÷wF…f–WrÐ¢‚’Óà¢&ö÷Båõ÷F7FDw&÷wF…66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢7W'&VçDfö7W5f–Wr‚“° ¢6öç7B7–æ5G&–æ–æu&VF–æW74fö7W2Ð¢‚’Óâ°¢–b€¢çVÖ&W"€¢&ö÷Båõ÷F7FDw&÷wFƒòçfÆ–EöÆöw2ÇÀ¢ ¢’ÃÒ ¢’°¢&WGW&ã°¢Ð ¢6öç7B6V7F–öâÐ¢&ö÷BçVW'•6VÆV7F÷"€¢rçF×G&–æ–ær×&VF–æW72×6V7F–öâp¢“° ¢–b€¢6V7F–öâÇÀ¢G—Vöb7W7FöÔWfVçBÓÐ¢vgVæ7F–öâp¢’°¢&WGW&ã°¢Ð ¢6V7F–öâæF—7F6„WfVçB€¢æWr7W7FöÔWfVçB€¢wFÖw&÷wF‚Öfö7W2×7FBrÀ¢°¢FWF–Ã¢°¢7FC ¢7W'&VçDfö7W5f–Wr‚¢Ð¢Ð¢¢“°¢Ó° ¢6öç7B&Vg&W6„w&÷wF„fö7W5æVÇ2Ð¢€¢7–æ5&VF–æW72ÒG'VP¢’Óâ°¢6öç7Bf–WrÐ¢7W'&VçDw&÷wF…f–Wr‚“°¢6öç7BFWF–Ç5æVÂÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖFWF–Ç2×66÷UÒp¢“°¢6öç7B&V6VçEæVÂÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×&V6VçB×æVÅÒp¢“° ¢–b€¢FWF–Ç5æVÀ¢’°¢FWF–Ç5æVÂæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„FWF–Ç566÷R€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢f–Wp¢“°¢Ð ¢–b€¢&V6VçEæVÀ¢’°¢&V6VçEæVÂæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF…&V6VçEæVÂ€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢f–Wp¢“° ¢6öç7B&WÆ6VÖVçBÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×&V6VçB×æVÅÒp¢“° ¢–b€¢&WÆ6VÖVç@¢’°¢&–æE&V6VçD6†'D–çFW&7F–öç2€¢&WÆ6VÖVç@¢“°¢Ð¢Ð ¢&Vg&W6…66÷VDv–å7VÖÖ'’‚“° ¢–b€¢7–æ5&VF–æW70¢’°¢7–æ5G&–æ–æu&VF–æW74fö7W2‚“°¢Ð¢Ó° ¢6öç7B&–æD7V×VÆF—fT–çFW&7F–öç2Ð¢66÷RÓâ°¢6öç7B6&BÐ¢66÷SòæÖF6†W3òâ€¢u¶FF×F×7FB×F÷FÂÖ6&EÒp¢¢ò66÷P¢¢66÷SòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×7FB×F÷FÂÖ6&EÒp¢“° ¢–b€¢6&@¢’°¢&WGW&ã°¢Ð ¢6öç7B7V×VÆF—fUö–çG2Ð¢‚’Óà¢6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Òp¢“° ¢6öç7B7–æ46ÆVæF$æf–vF÷"Ð¢€¢ö–çBÀ¢ÖöFVÀ¢’Óâ°¢6öç7Bæf–vF÷"Ð¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖ6ÆVæF"Öæf–vF÷%Òp¢“° ¢–b€¢æf–vF÷"ÇÀ¢ö–ç@¢’°¢&WGW&ã°¢Ð ¢6öç7B7FBÐ¢ö–çBævWDGG&–'WFR€¢vFF×F×7FBÖæÖRp¢’ÇÀ¢rs°¢6öç7Bö–çG2Ð¢7FDw&÷wF„7V×VÆF—fUö–çG4f÷%7FB€¢7V×VÆF—fUö–çG2‚’À¢7F@¢“°¢6öç7B–æFW‚Ð¢ö–çG2æ–æFW„öb€¢ö–ç@¢“° ¢–b€¢–æFW‚ÂÇÀ¢ö–çG2æÆVæwF€¢’°¢&WGW&ã°¢Ð ¢6öç7BÆ&VÂÐ¢7FDw&÷wF…f–WtÆ&VÂ€¢7F@¢“°¢6öç7BFFRÐ¢7G&–ær€¢ÖöFVÃòæFFRÇÀ¢rp¢“°¢6öç7B6Æ–FW"Ð¢æf–vF÷"çVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖ6ÆVæF"×67'V&&W%Òp¢“°¢6öç7B†VF–ærÐ¢æf–vF÷"çVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖ6ÆVæF"Öæf–vF÷"ÖÆ&VÅÒp¢“°¢6öç7BFFT÷WGWBÐ¢æf–vF÷"çVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖ6ÆVæF"Öæf–vF÷"ÖFFUÒp¢“° ¢–b€¢6Æ–FW ¢’°¢6Æ–FW"æÖ–âÐ¢ss°¢6Æ–FW"æÖ‚Ð¢7G&–ær€¢ö–çG2æÆVæwF‚Ð¢¢“°¢6Æ–FW"çfÇVRÐ¢7G&–ær€¢–æFW€¢“°¢6Æ–FW"ç6WDGG&–'WFR€¢vFF×F×7FBÖæÖRrÀ¢7F@¢“°¢6Æ–FW"ç6WDGG&–'WFR€¢v&–ÖÆ&VÂrÀ¢'&÷w6RG¶Æ&VÇÒ6W76–öç6 ¢“°¢6Æ–FW"ç6WDGG&–'WFR€¢v&–×fÇVWFW‡BrÀ¢G¶FFWÒ+rG¶–æFW‚²ÒöbG·ö–çG2æÆVæwF‡Ö ¢“°¢Ð ¢–b€¢†VF–æp¢’°¢†VF–ærçFW‡D6öçFVçBÐ¢G¶Æ&VÇÒ+rG¶–æFW‚²ÒöbG·ö–çG2æÆVæwF‡Ö°¢Ð ¢–b€¢FFT÷WGW@¢’°¢FFT÷WGWBçFW‡D6öçFVçBÐ¢FFS°¢Ð ¢f÷"€¢6öç7B'WGFöà¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FBÖÆæR×6VÆV7EÒp¢¢’°¢'WGFöâç6WDGG&–'WFR€¢v&–×&W76VBrÀ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FBÖÆæR×6VÆV7Bp¢’ÓÓÐ¢7F@¢òwG'VRp¢¢vfÇ6Rp¢“°¢Ð ¢f÷"€¢6öç7BÆæP¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FBÖÆæRÖw&÷WÒp¢¢’°¢6öç7B7F—fRÐ¢ÆæRævWDGG&–'WFR€¢vFF×F×7FBÖÆæRÖw&÷Wp¢’ÓÓÐ¢7FC° ¢ÆæRæ6Æ74Æ—7BçFövvÆR€¢wF×7FBÖÆæRÖ7F—fRrÀ¢7F—fP¢“°¢ÆæRæ6Æ74Æ—7BçFövvÆR€¢wF×7FBÖÆæRÖ×WFVBrÀ¢7F—fP¢“°¢Ð¢Ó° ¢6öç7B7F—fFUö–çBÐ¢ö–çBÓâ°¢6öç7B÷WGWBÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂÖFWF–ÂÖ÷WGWEÒp¢“° ¢–b€¢÷WGW@¢’°¢÷WGWBçFW‡D6öçFVçBÐ¢ö–çBævWDGG&–'WFR€¢vFF×F×7FB×F÷FÂÖFWF–Âp¢’ÇÀ¢rs°¢Ð ¢6öç7B7F–öâÐ¢7FDw&÷wF…6W76–öä7F–öäg&öÔVÆVÖVçB€¢ö–çBÀ¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·Ð¢“°¢6öç7BÖöFVÂÐ¢7FDw&÷wF…6W76–öäÖöFVÄg&öÔVÆVÖVçB€¢ö–ç@¢’ÇÀ¢€¢7F–öà¢ò7FDw&÷wF…6W76–öä–ç7V7F÷$ÖöFVÂ€¢7F–öà¢¢¢çVÆÀ¢“° ¢7FDw&÷wF„Ç•6W76–öä–ç7V7F÷"€¢6&BÀ¢ÖöFVÀ¢“° ¢6öç7B–æFW‚Ð¢ö–çBævWDGG&–'WFR€¢vFF×F×7FB×6W76–öâÖ–æFW‚p¢“° ¢f÷"€¢6öç7Bf—7VÀ¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâ×f—7VÅÒp¢¢’°¢f—7VÂæ6Æ74Æ—7BçFövvÆR€¢wF×7FB×6W76–öâÖ7F—fRrÀ¢f—7VÂævWDGG&–'WFR€¢vFF×F×7FB×6W76–öâ×f—7VÂp¢’ÓÓÐ¢–æFW€¢“°¢Ð ¢f÷"€¢6öç7B6VÆV7F&ÆP¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Òp¢¢’°¢6VÆV7F&ÆRç6WDGG&–'WFR€¢v&–×&W76VBrÀ¢6VÆV7F&ÆRævWDGG&–'WFR€¢vFF×F×7FB×6W76–öâÖ–æFW‚p¢’ÓÓÐ¢–æFW€¢òwG'VRp¢¢vfÇ6Rp¢“°¢Ð ¢6&Båõ÷F7FDw&÷wF„7F—fUö–çBÐ¢ö–çC° ¢7–æ46ÆVæF$æf–vF÷"€¢ö–çBÀ¢ÖöFVÀ¢“° ¢f÷"€¢6öç7B'WGFöà¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâ×7FWÒp¢¢’°¢6öç7BF¦6VçBÐ¢7FDw&÷wF„F¦6VçD7V×VÆF—fUö–çB€¢6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Òp¢’À¢ö–çBÀ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FB×6W76–öâ×7FWp¢¢“° ¢'WGFöâæF—6&ÆVBÐ¢F¦6VçC°¢'WGFöâç6WDGG&–'WFR€¢v&–ÖF—6&ÆVBrÀ¢F¦6Vç@¢òvfÇ6Rp¢¢wG'VRp¢“°¢Ð¢Ó° ¢6öç7B–æ—F–ÆÇ”7F—fUö–çBÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Õ¶&–×&W76VCÒ'G'VR%Òp¢“° ¢–b€¢–æ—F–ÆÇ”7F—fUö–ç@¢’°¢6&Båõ÷F7FDw&÷wF„7F—fUö–çBÐ¢–æ—F–ÆÇ”7F—fUö–çC° ¢6öç7B–æ—F–Ä7F–öâÐ¢7FDw&÷wF…6W76–öä7F–öäg&öÔVÆVÖVçB€¢–æ—F–ÆÇ”7F—fUö–çBÀ¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·Ð¢“° ¢7–æ46ÆVæF$æf–vF÷"€¢–æ—F–ÆÇ”7F—fUö–çBÀ¢–æ—F–Ä7F–öà¢ò7FDw&÷wF…6W76–öä–ç7V7F÷$ÖöFVÂ€¢–æ—F–Ä7F–öà¢¢¢çVÆÀ¢“°¢Ð ¢f÷"€¢6öç7B'WGFöà¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâ×7FWÒp¢¢’°¢6öç7BF—&V7F–öâÐ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FB×6W76–öâ×7FWp¢“°¢6öç7BF¦6VçBÐ¢–æ—F–ÆÇ”7F—fUö–ç@¢ò7FDw&÷wF„F¦6VçD7V×VÆF—fUö–çB€¢6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Òp¢’À¢–æ—F–ÆÇ”7F—fUö–çBÀ¢F—&V7F–öà¢¢¢çVÆÃ° ¢'WGFöâæF—6&ÆVBÐ¢F¦6VçC°¢'WGFöâç6WDGG&–'WFR€¢v&–ÖF—6&ÆVBrÀ¢F¦6Vç@¢òvfÇ6Rp¢¢wG'VRp¢“°¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óâ°¢6öç7B7W'&VçEö–çBÐ¢6&Båõ÷F7FDw&÷wF„7F—fUö–çBÇÀ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Õ¶&–×&W76VCÒ'G'VR%Òp¢“°¢6öç7BæW‡Eö–çBÐ¢7FDw&÷wF„F¦6VçD7V×VÆF—fUö–çB€¢6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×6W76–öâÖ–æFW…Õ·&öÆSÒ&'WGFöâ%Òp¢’À¢7W'&VçEö–çBÀ¢F—&V7F–öà¢“° ¢–b€¢æW‡Eö–ç@¢’°¢7F—fFUö–çB€¢æW‡Eö–ç@¢“°¢æW‡Eö–çBæfö7W3òâ‡°¢&WfVçE67&öÆÃ¢G'VP¢Ò“°¢Ð¢Ð¢“°¢Ð ¢f÷"€¢6öç7B'WGFöà¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FBÖÆæR×6VÆV7EÒp¢¢’°¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óâ°¢6öç7B7FBÐ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FBÖÆæR×6VÆV7Bp¢“°¢6öç7Bö–çG2Ð¢7FDw&÷wF„7V×VÆF—fUö–çG4f÷%7FB€¢7V×VÆF—fUö–çG2‚’À¢7F@¢“°¢6öç7Bö–çBÐ¢ö–çG5°¢ö–çG2æÆVæwF‚Ð¢¢Ó° ¢–b€¢ö–ç@¢’°¢7F—fFUö–çB€¢ö–ç@¢“°¢Ð¢Ð¢“°¢Ð ¢6öç7B6ÆVæF%67'V&&W"Ð¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖ6ÆVæF"×67'V&&W%Òp¢“° ¢6ÆVæF%67'V&&W#òæFDWfVçDÆ—7FVæW"€¢v–çWBrÀ¢‚’Óâ°¢6öç7Bö–çG2Ð¢7FDw&÷wF„7V×VÆF—fUö–çG4f÷%7FB€¢7V×VÆF—fUö–çG2‚’À¢6ÆVæF%67'V&&W"ævWDGG&–'WFR€¢vFF×F×7FBÖæÖRp¢¢“°¢6öç7B–æFW‚Ð¢7FDw&÷wF„6Æ×VE6W76–öä–æFW‚€¢6ÆVæF%67'V&&W"çfÇVRÀ¢ö–çG2æÆVæwF€¢“°¢6öç7Bö–çBÐ¢ö–çG5°¢–æFW€¢Ó° ¢–b€¢ö–ç@¢’°¢7F—fFUö–çB€¢ö–ç@¢“°¢Ð¢Ð¢“° ¢f÷"€¢6öç7Bö–ç@¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×F÷FÂÖFWF–ÅÒp¢¢’°¢ö–çBæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óà¢7F—fFUö–çB€¢ö–ç@¢¢“° ¢ö–çBæFDWfVçDÆ—7FVæW"€¢v¶W–F÷vârÀ¢WfVçBÓâ°¢–b€¢WfVçBæ¶W’ÓÒtVçFW"rb`¢WfVçBæ¶W’ÓÒrp¢’°¢&WGW&ã°¢Ð ¢WfVçBç&WfVçDFVfVÇB‚“°¢7F—fFUö–çB€¢ö–ç@¢“°¢Ð¢“°¢Ð ¢6öç7B6†'BÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂ×7fuÒp¢“° ¢6†'CòæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢WfVçBÓâ°¢6öç7B&V7BÐ¢6†'BævWD&÷VæF–æt6Æ–VçE&V7Còâ‚“°¢6öç7Bf–Wuv–GF‚Ð¢çVÖ&W"€¢6†'Bçf–Wt&÷ƒòæ&6UfÃòçv–GF€¢“°¢6öç7Bf–Wt†V–v‡BÐ¢çVÖ&W"€¢6†'Bçf–Wt&÷ƒòæ&6UfÃòæ†V–v‡@¢“° ¢–b€¢&V7BÇÀ¢&V7Bçv–GF‚ÃÒÇÀ¢&V7Bæ†V–v‡BÃÒÇÀ¢çVÖ&W"æ—4f–æ—FR€¢f–Wuv–GF€¢’ÇÀ¢f–Wuv–GF‚ÃÒ ¢’°¢&WGW&ã°¢Ð ¢6öç7BF‚Ð¢€¢çVÖ&W"€¢WfVçBæ6Æ–VçE€¢’Ð¢&V7BæÆVg@¢’ð¢&V7Bçv–GF‚ ¢f–Wuv–GFƒ°¢6öç7BW6TÆæU’Ð¢6&Bæ6Æ74Æ—7Bæ6öçF–ç2€¢wF×7FBÖÆÂÖ6†'Bp¢“°¢6öç7BF’Ð¢W6TÆæU’b`¢çVÖ&W"æ—4f–æ—FR€¢f–Wt†V–v‡@¢’b`¢f–Wt†V–v‡Bâ ¢ò€¢çVÖ&W"€¢WfVçBæ6Æ–VçE¢’Ð¢&V7BçF÷ ¢’ð¢&V7Bæ†V–v‡B ¢f–Wt†V–v‡@¢¢çVÆÃ°¢6öç7BæV&W7BÐ¢7FDw&÷wF„æV&W7D7V×VÆF—fUö–çB€¢'&’æg&öÒ€¢6&BçVW'•6VÆV7F÷$ÆÂ€¢v6—&6ÆU¶FF×F×7FB×F÷FÂÖFWF–ÅÒp¢¢’æÖ€¢ö–çBÓâ‡°¢ö–çBÀ¢ƒ¢çVÖ&W"€¢ö–çBævWDGG&–'WFR€¢v7‚p¢¢’À¢“¢çVÖ&W"€¢ö–çBævWDGG&–'WFR€¢v7’p¢¢¢Ò¢’À¢F‚À¢F¢“° ¢–b€¢æV&W7@¢’°¢7F—fFUö–çB€¢æV&W7@¢“°¢Ð¢Ð¢“° ¢6öç7B6VÆV7BÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂÖfö7W5Òp¢“° ¢6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢&ö÷Båõ÷F7FDw&÷wF„fö7W2Ð¢V•6W76–öåG&–æ–ætfö7W2€¢6VÆV7BçfÇVP¢“° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…öfö7W3 ¢&ö÷Båõ÷F7FDw&÷wF„fö7W0¢Ò“°¢w&—FU7FDw&÷wF…&VfW&Væ6W2‡°¢7FEöw&÷wF…öfö7W3 ¢&ö÷Båõ÷F7FDw&÷wF„fö7W0¢Ò“° ¢6&Bæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2À¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢“° ¢&Vg&W6„w&÷wF„fö7W5æVÇ2‚“° ¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“°¢Ð¢“° ¢6öç7B6öçFW‡E6VÆV7BÐ¢6&BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂÖ6öçFW‡EÒp¢“° ¢6öçFW‡E6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢6öçFW‡E6VÆV7BçfÇVP¢“° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…ö6öçFW‡C ¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡@¢Ò“° ¢6&Bæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2À¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢“° ¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“°¢&–æE66÷VDv–ä–çFW&7F–öç2‚“°¢Ð¢“° ¢f÷"€¢6öç7B&ævT'WGFöà¢öb6&BçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FB×F÷FÂ×&ævUÒp¢¢’°¢&ævT'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óâ°¢&ö÷Båõ÷F7FDw&÷wF…&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢&ævT'WGFöâævWDGG&–'WFR€¢vFF×F×7FB×F÷FÂ×&ævRp¢¢“° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…÷&ævS ¢&ö÷Båõ÷F7FDw&÷wF…&ævP¢Ò“° ¢6&Bæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2À¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢“° ¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“°¢&–æE66÷VDv–ä–çFW&7F–öç2‚“°¢Ð¢“°¢Ð¢Ó° ¢6öç7B&Vg&W6…66÷VDv–å7VÖÖ'’Ð¢‚’Óâ°¢6öç7B7W'&VçBÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖv–â×7VÖÖ'•Òp¢“° ¢–b€¢7W'&Vç@¢’°¢&WGW&ã°¢Ð ¢7W'&VçBæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF…66÷VDv–å7VÖÖ'’€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2À¢&ö÷Båõ÷F7FDw&÷wF…66÷RÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡@¢“° ¢&–æE66÷VDv–ä–çFW&7F–öç2‚“°¢Ó° ¢6öç7B&–æE66÷VDv–ä–çFW&7F–öç2Ð¢‚’Óâ°¢6öç7BæVÂÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FBÖv–â×66÷RÖ6öçG&öÇ5Òp¢“° ¢–b€¢æVÀ¢’°¢&WGW&ã°¢Ð ¢f÷"€¢6öç7B'WGFöà¢öbæVÂçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×7FBÖv–â×66÷RÖ÷F–öåÒp¢¢’°¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óâ°¢&ö÷Båõ÷F7FDw&÷wF…66÷RÐ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FBÖv–â×66÷RÖ÷F–öâp¢’ÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…÷66÷S ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢Ò“° ¢6öç7B6&BÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂÖ6&EÒp¢“° ¢–b€¢6&@¢’°¢6&Bæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2À¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢“°¢Ð ¢&Vg&W6„w&÷wF„fö7W5æVÇ2€¢fÇ6P¢“°¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“°¢Ð¢“°¢Ð¢Ó° ¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“° ¢&–æE66÷VDv–ä–çFW&7F–öç2‚“° ¢&–æE&V6VçD6†'D–çFW&7F–öç2€¢&ö÷@¢“° ¢–b€¢&ö÷Båõ÷FG&–æ–æu7FD'&–FvT&÷VæBÓÐ¢G'VP¢’°¢&ö÷Båõ÷FG&–æ–æu7FD'&–FvT&÷VæBÐ¢G'VS° ¢&ö÷BæFDWfVçDÆ—7FVæW"€¢wF×G&–æ–ær×7FBÖ6†ævRrÀ¢WfVçBÓâ°¢6öç7BæW‡BÐ¢WfVçCòæFWF–Ãòç7FC° ¢–b€¢°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Òæ–æ6ÇVFW2€¢æW‡@¢¢’°¢&WGW&ã°¢Ð ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2Ð¢æW‡C° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…öfö7W3 ¢æW‡@¢Ò“°¢w&—FU7FDw&÷wF…&VfW&Væ6W2‡°¢7FEöw&÷wF…öfö7W3 ¢æW‡@¢Ò“° ¢6öç7B6&BÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FB×F÷FÂÖ6&EÒp¢“° ¢–b€¢6&@¢’°¢6&Bæ÷WFW$…DÔÂÐ¢&VæFW%7FDw&÷wF„7V×VÆF—fT6†'B€¢&ö÷Båõ÷F7FDw&÷wF‚ÇÀ¢·ÒÀ¢æW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢&ö÷Båõ÷F7FDw&÷wF…66÷P¢“°¢Ð ¢&Vg&W6„w&÷wF„fö7W5æVÇ2€¢fÇ6P¢“°¢&–æD7V×VÆF—fT–çFW&7F–öç2€¢&ö÷@¢“°¢Ð¢“°¢Ð ¢7–æ5G&–æ–æu&VF–æW74fö7W2‚“°¢Ð ¢gVæ7F–öâ7FDw&÷wF„6ö×7EW&–öB‡fÇVR’°¢6öç7Bæ÷&ÖÆ—¦VBÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢fÇVP¢“°¢ ¢&WGW&â°¢svBrÀ¢sFBrÀ¢s3BrÀ¢vÆÂp¢Òæ–æ6ÇVFW2€¢æ÷&ÖÆ—¦V@¢¢òæ÷&ÖÆ—¦V@¢¢svBs°¢Ð ¢gVæ7F–öâ7FDw&÷wF„6ö×7EW&–öDÆ&VÂ‡fÇVR’°¢&WGW&â°¢svBs¢u7BvVV²rÀ¢sFBs¢u7B"vVV·2rÀ¢s3Bs¢u7BÖöçF‚rÀ¢ÆÃ¢tÆÂF–ÖRp¢Õ°¢7FDw&÷wF„6ö×7EW&–öB€¢fÇVP¢¢Ó°¢Ð ¢gVæ7F–öâ7FDw&÷wF„6ö×7E7VÖÖ'•7FB‡fÇVR’°¢&WGW&âV•6W76–öå7FEf–Wr€¢fÇVP¢“°¢Ð ¢gVæ7F–öâ7FDw&÷wF„6ö×7E7VÖÖ'”ÖöFVÂ€¢w&÷wF‚À¢&ævRÒsvBrÀ¢7FEfÇVRÒvÆÂp¢’°¢6öç7BW&–öBÐ¢7FDw&÷wF„6ö×7EW&–öB€¢&ævP¢“°¢6öç7B&÷rÐ¢W&–öBÓÓÒsvBp¢òw&÷wFƒòç&V6VçEóuöF—0¢¢W&–öBÓÓÒsFBp¢òw&÷wFƒòç&V6VçEóEöF—0¢¢W&–öBÓÓÒs3Bp¢òw&÷wFƒòç&V6VçEó3öF—0¢¢w&÷wFƒ°¢6öç7B7FD÷&FW"Ò°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Ó°¢6öç7B6VÆV7FVE7FBÐ¢7FDw&÷wF„6ö×7E7VÖÖ'•7FB€¢7FEfÇVP¢“°¢6öç7B¦ö%7V6–ÂÐ¢7FDw&÷wF„¦ö%7V6–Å7VÖÖ'’€¢w&÷wF‚À¢6VÆV7FVE7FBÀ¢W&–ö@¢“°¢6öç7Bw–Õ7FE&÷w2Ð¢7FD÷&FW ¢æÖ€¢7FBÓâ°¢6öç7B—FVÒÐ¢&÷sòç7FG3òå·7FEÒÇÀ¢·Ó°¢ ¢&WGW&â°¢7FBÀ¢Æ&VÃ ¢—FVÒæÆ&VÂÇÀ¢G&–æ–æu&VF–æW757FDÆ&VÂ€¢7F@¢’À¢v–ã ¢çVÖ&W"€¢—FVÒæv–âÇÀ¢ ¢’À¢w–Õöv–ã ¢çVÖ&W"€¢—FVÒæv–âÇÀ¢ ¢’À¢7F–öç3 ¢çVÖ&W"€¢—FVÒæ7F–öç2ÇÀ¢ ¢’À¢G&–ç3 ¢çVÖ&W"€¢—FVÒçG&–ç2ÇÀ¢ ¢’À¢VæW&w•÷W6VC ¢çVÖ&W"€¢—FVÒæVæW&w•÷W6VBÇÀ¢ ¢¢Ó°¢Ð¢“°¢6öç7B7FE&÷w2Ð¢w–Õ7FE&÷w2æÖ€¢—FVÒÓà¢—FVÒç7FBÓÓÒw7G&VæwF‚p¢ò°¢ââæ—FVÒÀ¢v–ã ¢—FVÒæw–Õöv–â°¢¦ö%7V6–Âæv–âÀ¢¦ö%÷7V6–Åöv–ã ¢¦ö%7V6–Âæv–à¢Ð¢¢°¢ââæ—FVÒÀ¢¦ö%÷7V6–Åöv–ã¢ ¢Ð¢“°¢6öç7B7FG2Ð¢7FE&÷w0¢æf–ÇFW"€¢—FVÒÓà¢—FVÒæv–ââ ¢“°¢6öç7B6VÆV7FVBÐ¢6VÆV7FVE7FBÓÓÒvÆÂp¢òçVÆÀ¢¢7FE&÷w2æf–æB€¢—FVÒÓà¢—FVÒç7FBÓÓÐ¢6VÆV7FVE7F@¢’ÇÀ¢çVÆÃ°¢6öç7B66÷VBÐ¢6VÆV7FVE7FBÓÓÒvÆÂp¢ò&÷rÇÂ·Ð¢¢6VÆV7FVBÇÂ·Ó°¢6öç7Bw–Ôv–âÐ¢6VÆV7FVE7FBÓÓÒvÆÂp¢òçVÖ&W"€¢&÷sòæv–âÇÀ¢ ¢¢¢çVÖ&W"€¢6VÆV7FVCòæw–Õöv–âÇÀ¢ ¢“°¢6öç7BÖ÷7EG&–æVBÐ¢7FG0¢ç6Æ–6R‚¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢&–v‡BçG&–ç2Ð¢ÆVgBçG&–ç2ÇÀ¢&–v‡Bæv–âÐ¢ÆVgBæv–à¢•³ÒÇÀ¢çVÆÃ°¢ ¢&WGW&â°¢W&–öBÀ¢W&–öEöÆ&VÃ ¢7FDw&÷wF„6ö×7EW&–öDÆ&VÂ€¢W&–ö@¢’À¢7FC ¢6VÆV7FVE7FBÀ¢7FEöÆ&VÃ ¢6VÆV7FVCòæÆ&VÂÇÀ¢tÆÂ7FG2rÀ¢v–ã ¢w–Ôv–â°¢¦ö%7V6–Âæv–âÀ¢w–Õöv–ã ¢w–Ôv–âÀ¢¦ö%÷7V6–Åöv–ã ¢¦ö%7V6–Âæv–âÀ¢¦ö%÷7V6–ÅöWfVçG3 ¢¦ö%7V6–ÂæWfVçG2À¢¦ö%÷ö–çG5÷W6VC ¢¦ö%7V6–Âæ¦ö%÷ö–çG5÷W6VBÀ¢7F–öç3 ¢çVÖ&W"€¢66÷VCòæ7F–öç2óð¢€¢W&–öBÓÓÒvÆÂp¢òw&÷wFƒòçfÆ–EöÆöw0¢¢ ¢’óð¢ ¢’À¢G&–ç3 ¢çVÖ&W"€¢66÷VCòçG&–ç2ÇÀ¢ ¢’À¢VæW&w•÷W6VC ¢çVÖ&W"€¢66÷VCòæVæW&w•÷W6VBÇÀ¢ ¢’À¢7FG3 ¢6VÆV7FVE7FBÓÓÒvÆÂp¢ò7FG0¢¢6VÆV7FVCòæv–ââ ¢ò·6VÆV7FVEÐ¢¢µÒÀ¢w–Õ÷7FG3 ¢w–Õ7FE&÷w2æf–ÇFW"€¢—FVÒÓà¢—FVÒæw–Õöv–ââ ¢’À¢Ö÷7E÷G&–æVC ¢6VÆV7FVE7FBÓÓÒvÆÂp¢òÖ÷7EG&–æV@¢¢6VÆV7FV@¢Ó°¢Ð ¢gVæ7F–öâ7FDw&÷wF„6ö×7E7VÖÖ'•6VçFVæ6R€¢ÖöFVÀ¢’°¢–b€¢ÖöFVÂÇÀ¢ÖöFVÂæv–âÃÒ ¢’°¢6öç7B7V&¦V7BÐ¢ÖöFVÃòç7FBb`¢ÖöFVÂç7FBÓÒvÆÂp¢òG¶ÖöFVÂç7FEöÆ&VÇÒG&–æ–æv ¢¢vw–ÒG&–æ–ærs° ¢&WGW&âG¶ÖöFVÃòçW&–öEöÆ&VÂÇÂu6VÆV7FVBW&–öBwÓ¢æòö'6W'fVBG·7V&¦V7GÒæ°¢Ð ¢–b€¢ÖöFVÂç7FBÓÒvÆÂp¢’°¢–b€¢ÖöFVÂæ¦ö%÷7V6–Åöv–ââ ¢’°¢6öç7Bw–Õ'BÐ¢ÖöFVÂæw–Õöv–ââ ¢òG·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæw–Õöv–â—Òg&öÒG¶ÖöFVÂæ7F–öç2çFôÆö6ÆU7G&–ær‚—Òw–ÒG¶ÖöFVÂæ7F–öç2ÓÓÒòw6W76–öâr¢w6W76–öç2wÒ+r ¢¢rs° ¢&WGW&âG¶ÖöFVÂçW&–öEöÆ&VÇÓ¢G·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæv–â—ÒG¶ÖöFVÂç7FEöÆ&VÇÒ(	BG¶w–Õ'GÒG·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæ¦ö%÷7V6–Åöv–â—Òg&öÒ&×’W6–ærG¶ÖöFVÂæ¦ö%÷ö–çG5÷W6VBçFôÆö6ÆU7G&–ær‚—Ò¥æ°¢Ð ¢&WGW&âG¶ÖöFVÂçW&–öEöÆ&VÇÓ¢G·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæv–â—ÒG¶ÖöFVÂç7FEöÆ&VÇÒg&öÒG¶ÖöFVÂæ7F–öç2çFôÆö6ÆU7G&–ær‚—Òw–ÒG¶ÖöFVÂæ7F–öç2ÓÓÒòw6W76–öâr¢w6W76–öç2wÒæ°¢Ð¢ ¢6öç7B7FEFW‡BÐ¢€¢ÖöFVÂæw–Õ÷7FG2ÇÀ¢ÖöFVÂç7FG0¢¢æÖ€¢—FVÒÓà¢G·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†—FVÒæv–â—ÒG¶—FVÒæÆ&VÇÖ ¢¢æ¦ö–â‚r+rr“°¢ ¢6öç7B6÷W&6UFW‡BÐ¢ÖöFVÂæ7F–öç2â ¢òg&öÒG¶ÖöFVÂæ7F–öç2çFôÆö6ÆU7G&–ær‚—Òw–ÒG¶ÖöFVÂæ7F–öç2ÓÓÒòw6W76–öâr¢w6W76–öç2wÖ ¢¢rs°¢6öç7B&×•FW‡BÐ¢ÖöFVÂæ¦ö%÷7V6–Åöv–ââ ¢ò+r&×’G·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæ¦ö%÷7V6–Åöv–â—Ò7G&VæwF‚òG¶ÖöFVÂæ¦ö%÷ö–çG5÷W6VBçFôÆö6ÆU7G&–ær‚—Ò¥ ¢¢rs° ¢&WGW&âG¶ÖöFVÂçW&–öEöÆ&VÇÓ¢G·7FDw&÷wF„f÷&ÖD6ö×7Dv–â†ÖöFVÂæv–â—ÒF÷FÂ7FG2G·6÷W&6UFW‡GÒG·7FEFW‡Bò(	BG·7FEFW‡GÖ¢rwÒG¶&×•FW‡GÒæ°¢Ð ¢gVæ7F–öâ7FDw&÷wF…G&–æ–æu&V66VçFVæ6R€¢ÖöFVÀ¢’°¢6öç7BÆVBÒ°¢svBs¢t÷fW"F†R7BvVV²rÀ¢sFBs¢t÷fW"F†R7B"vVV·2rÀ¢s3Bs¢t÷fW"F†R7BÖöçF‚rÀ¢ÆÃ¢t7&÷72ÆÂ&V6÷&FVBG&–æ–ærp¢Õ°¢7FDw&÷wF„6ö×7EW&–öB€¢ÖöFVÃòçW&–ö@¢¢Ó° ¢–b€¢ÖöFVÂÇÀ¢ÖöFVÂæv–âÃÒ ¢’°¢6öç7B7V&¦V7BÐ¢ÖöFVÃòç7FBb`¢ÖöFVÂç7FBÓÒvÆÂp¢òf÷"G¶ÖöFVÂç7FEöÆ&VÇÖ ¢¢rs° ¢&WGW&âG¶ÆVGÒÂæòw–Òv–ç2vW&R&V6÷&FVBG·7V&¦V7GÒæ°¢Ð ¢6öç7B6W76–öç2Ð¢G¶ÖöFVÂæ7F–öç2çFôÆö6ÆU7G&–ær‚—Òw–ÒG¶ÖöFVÂæ7F–öç2ÓÓÒòw6W76–öâr¢w6W76–öç2wÖ°¢6öç7BVæW&w’Ð¢çVÖ&W"†ÖöFVÂæVæW&w•÷W6VB’â ¢òW6–ærG´çVÖ&W"†ÖöFVÂæVæW&w•÷W6VB’çFôÆö6ÆU7G&–ær‚—ÒVæW&w– ¢¢rs° ¢6öç7B&×•6VçFVæ6RÐ¢ÖöFVÂæ¦ö%÷7V6–Åöv–ââ ¢òG¶ÖöFVÂæw–Õöv–ââòr–÷RÇ6òv–æVBr¢G¶ÆVGÒÂ–÷Rv–æVFÒG·7FDw&÷wF„f÷&ÖDçVÖ&W"†ÖöFVÂæ¦ö%÷7V6–Åöv–âÂ"—Ò7G&VæwF‚g&öÒG¶ÖöFVÂæ¦ö%÷7V6–ÅöWfVçG2çFôÆö6ÆU7G&–ær‚—Ò&×’¦ö"G¶ÖöFVÂæ¦ö%÷7V6–ÅöWfVçG2ÓÓÒòw7V6–Âr¢w7V6–Ç2wÒW6–ærG¶ÖöFVÂæ¦ö%÷ö–çG5÷W6VBçFôÆö6ÆU7G&–ær‚—Ò¦ö"ö–çG2æ ¢¢rs° ¢–b€¢ÖöFVÂç7FBÓÒvÆÂp¢’°¢6öç7Bw–Õ6VçFVæ6RÐ¢ÖöFVÂæw–Õöv–ââ ¢òG¶ÆVGÒÂ–÷Rv–æVBG·7FDw&÷wF„f÷&ÖDçVÖ&W"†ÖöFVÂæw–Õöv–âÂ"—ÒG¶ÖöFVÂç7FEöÆ&VÇÒg&öÒG·6W76–öç7ÒG¶VæW&w—Òæ ¢¢rs°¢6öç7BF÷FÅ6VçFVæ6RÐ¢ÖöFVÂæw–Õöv–ââb`¢ÖöFVÂæ¦ö%÷7V6–Åöv–ââ ¢ò–÷Rv–æVBG·7FDw&÷wF„f÷&ÖDçVÖ&W"†ÖöFVÂæv–âÂ"—ÒG¶ÖöFVÂç7FEöÆ&VÇÒ–âF÷FÂæ ¢¢rs° ¢&WGW&âG¶w–Õ6VçFVæ6WÒG¶&×•6VçFVæ6WÒG·F÷FÅ6VçFVæ6WÖçG&–Ò‚“°¢Ð ¢6öç7B7FE'G2Ð¢€¢ÖöFVÂæw–Õ÷7FG2ÇÀ¢µÐ¢’æÖ€¢—FVÒÓà¢G·7FDw&÷wF„f÷&ÖDçVÖ&W"†—FVÒæv–âÂ"—ÒG¶—FVÒæÆ&VÇÖ ¢“°¢6öç7B'&V¶F÷vâÐ¢7FE'G2æÆVæwF‚ÓÓÒ¢ò7FE'G5³Ð¢¢7FE'G2æÆVæwF‚ÓÓÒ ¢òG·7FE'G5³×ÒæBG·7FE'G5³×Ö ¢¢7FE'G2æÆVæwF‚â ¢òG·7FE'G2ç6Æ–6RƒÂÓ’æ¦ö–â‚rÂr—ÒÂæBG·7FE'G2æB‚Ó—Ö ¢¢G·7FDw&÷wF„f÷&ÖDçVÖ&W"†ÖöFVÂæw–Õöv–âÂ"—ÒF÷FÂ7FG6°¢6öç7BF÷FÂÐ¢ÖöFVÂæv–ââ ¢ò–÷Rv–æVBG·7FDw&÷wF„f÷&ÖDçVÖ&W"†ÖöFVÂæv–âÂ"—ÒF÷FÂ7FG2æ ¢¢rs°¢6öç7Bw–Õ6VçFVæ6RÐ¢ÖöFVÂæw–Õöv–ââ ¢òG¶ÆVGÒÂ–÷Rv–æVBG¶'&V¶F÷vçÒg&öÒG·6W76–öç7ÒG¶VæW&w—Òæ ¢¢rs° ¢&WGW&âG¶w–Õ6VçFVæ6WÒG¶&×•6VçFVæ6WÒG·F÷FÇÖçG&–Ò‚“°¢Ð ¢7–æ2gVæ7F–öâ6÷•G&–æ–æu&V6FW‡B€¢fÇVP¢’°¢6öç7BFW‡BÐ¢7G&–ær€¢fÇVRÇÀ¢rp¢’çG&–Ò‚“° ¢–b€¢FW‡@¢’°¢&WGW&âfÇ6S°¢Ð ¢G'’°¢6öç7Bw&—FUFW‡BÐ¢vÆö&ÅF†—2ææf–vF÷ ¢òæ6Æ—&ö&@¢òçw&—FUFW‡C° ¢–b€¢G—Vöbw&—FUFW‡BÓÓÐ¢vgVæ7F–öâp¢’°¢v—Bw&—FUFW‡Bæ6ÆÂ€¢vÆö&ÅF†—2ææf–vF÷"æ6Æ—&ö&BÀ¢FW‡@¢“° ¢&WGW&âG'VS°¢Ð¢Ò6F6‚°¢òòF÷&åDvV%f–Ww2Ö’W‡÷6R6Æ—&ö&Bv—F†÷WBÆÆ÷v–ærF†R6ÆÂà¢Ð ¢ÆWBFW‡F&VÐ¢çVÆÃ° ¢G'’°¢FW‡F&VÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢wFW‡F&Vp¢“°¢FW‡F&VçfÇVRÐ¢FW‡C°¢FW‡F&Vç6WDGG&–'WFR€¢w&VFöæÇ’rÀ¢rp¢“°¢FW‡F&Vç7G–ÆRç÷6—F–öâÐ¢vf—†VBs°¢FW‡F&Vç7G–ÆRçF÷Ð¢rÓ‚s°¢FW‡F&Vç7G–ÆRæföçE6—¦RÐ¢sg‚s°¢Fö7VÖVçBæ&öG’æVæD6†–ÆB€¢FW‡F&V¢“°¢FW‡F&Væfö7W2‚“°¢FW‡F&Vç6VÆV7B‚“°¢FW‡F&Vç6WE6VÆV7F–öå&ævR€¢À¢FW‡BæÆVæwF€¢“° ¢&WGW&âFö7VÖVçBæW†V46öÖÖæB€¢v6÷’p¢’ÓÓÒG'VS°¢Ò6F6‚°¢&WGW&âfÇ6S°¢Òf–æÆÇ’°¢FW‡F&Vòç&VÖ÷fSòâ‚“°¢Ð¢Ð ¢gVæ7F–öâ&VæFW%G&–æ–æt6ö×7E7VÖÖ'’€¢&VF–æW72À¢w&÷wF‚À¢&ævRÒsvBrÀ¢ÆåfÇVRÒçVÆÂÀ¢7FEfÇVRÒvÆÂp¢’°¢6öç7BW&–öBÐ¢7FDw&÷wF„6ö×7EW&–öB€¢&ævP¢“°¢6öç7B7VÖÖ'’Ð¢7FDw&÷wF„6ö×7E7VÖÖ'”ÖöFVÂ€¢w&÷wF‚ÇÀ¢·ÒÀ¢W&–öBÀ¢7FEfÇVP¢“°¢6öç7BÆâÐ¢G&–æ–æu&VF–æW75Æâ€¢ÆåfÇVRÇÀ¢&VEG&–æ–æu&VF–æW75Æâ‚¢“°¢6öç7BÆFW7D†”§V×Ð¢G—Vöb7FDw&÷wF„ÆFW7D†”§V×WfVçBÓÓÐ¢vgVæ7F–öâp¢ò7FDw&÷wF„ÆFW7D†”§V×WfVçB€¢w&÷wF€¢¢¢çVÆÃ°¢6öç7BW&–öDF—2Ð¢W&–öBÓÓÒsvBp¢òp¢¢W&–öBÓÓÒsFBp¢ò@¢¢W&–öBÓÓÒs3Bp¢ò3 ¢¢çVÆÃ°¢6öç7BW&–öD7WFöfbÐ¢W&–öDF—2ÓÓÒçVÆÀ¢òçVÆÀ¢¢ÖF‚æfÆö÷"€¢FFRææ÷r‚’ð¢ ¢’Ð¢W&–öDF—2 ¢ƒcC°¢6öç7B§V×ÖF6†W57FBÐ¢7VÖÖ'’ç7FBÓÓÒvÆÂrÇÀ¢€¢'&’æ—4'&’€¢ÆFW7D†”§V×òç7FG0¢’b`¢ÆFW7D†”§V×ç7FG2ç6öÖR€¢&÷rÓà¢&÷sòç7FBÓÓÐ¢7VÖÖ'’ç7F@¢¢“°¢6öç7B§V×–åW&–öBÐ¢ÆFW7D†”§V×b`¢§V×ÖF6†W57FBb`¢€¢W&–öD7WFöfbÓÓÒçVÆÂÇÀ¢çVÖ&W"€¢ÆFW7D†”§V×æÆ7E÷F–ÖW7F×ÇÀ¢ ¢’ãÐ¢W&–öD7WFöf`¢“°¢6öç7B§V×&V6Ð¢§V×–åW&–ö@¢ò7FDw&÷wF„†”§V×WfVçE6VçFVæ6R€¢ÆFW7D†”§V× ¢¢¢rs°¢6öç7BGf–6RÐ¢&VF–æW70¢òG&–æ–æu&VF–æW75ÆäGf–6R€¢&VF–æW72À¢ÆâÀ¢VæFVf–æVBÀ¢w&÷wF€¢¢¢çVÆÃ°¢6öç7B6VÆV7FVE&VF–7F–öå7FBÐ¢²w7G&VæwF‚rÂvFVfVç6RrÂw7VVBrÂvFW‡FW&—G’uÒæ–æ6ÇVFW2‡7VÖÖ'’ç7FB¢ò7VÖÖ'’ç7F@¢¢&VF–æW73òæFVfVÇE÷7FBÇÂçVÆÃ°¢6öç7BÖöFVÂÐ¢6VÆV7FVE&VF–7F–öå7F@¢òG&–æ–æu&VF–æW75&VF–7F–öäÖöFVÂ€¢&VF–æW72À¢6VÆV7FVE&VF–7F–öå7FBÀ¢Æà¢¢¢çVÆÃ°¢6öç7BÆææVDVæW&w’Ð¢çVÖ&W"æ—4f–æ—FR€¢çVÖ&W"€¢&VF–æW73òæVæW&w¢¢’b`¢çVÖ&W"€¢&VF–æW72æVæW&w¢’à¢ ¢òÖF‚æfÆö÷"€¢çVÖ&W"€¢&VF–æW72æVæW&w¢¢¢¢çVÆÃ°¢6öç7B&ö¦V7F–öâÐ¢ÆææVDVæW&w’ÓÓÐ¢çVÆÀ¢òçVÆÀ¢¢G&–æ–æu&VF–æW75&ö¦V7F–öâ€¢ÖöFVÂÀ¢ÆææVDVæW&w¢“°¢6öç7B&VF–7F–öåFW‡BÐ¢&ö¦V7F–öãòæf–Æ&ÆP¢òG·ÆææVDVæW&w’çFôÆö6ÆU7G&–ær‚—ÔRG·G&–æ–æu&VF–æW757FDÆ&VÂ‡6VÆV7FVE&VF–7F–öå7FB—ÒW7F–ÖFS¢G·7FDw&÷wF„f÷&ÖDçVÖ&W"‡&ö¦V7F–öâæÆ÷rÂ"—Þ(	2G·7FDw&÷wF„f÷&ÖDçVÖ&W"‡&ö¦V7F–öâæ†–v‚Â"—Ö ¢¢ÖöFVÃòæw–Õ÷6÷W&6RÓÓÒwVæ¶æ÷vâp¢òu&VF–7F–öâVæf–Æ&ÆR(	Bw–ÒVæ¶æ÷vâp¢¢u&VF–7F–öâVæf–Æ&ÆR(	Bæ÷BVæ÷Vv‚ÖF6†–ær6W76–öç2s°¢6öç7B&VF–7F–öäWf–FVæ6RÐ¢ÖöFVÀ¢òG&–æ–æu&VF–æW74Wf–FVæ6UFW‡B†ÖöFVÂ¢¢sÖF6†–ær6W76–öç2+r†—7F÷&–6ÂW'&÷"VæF–ær+r†–æW726öçFW‡BVæ¶æ÷vâ+rw–ÒVæ¶æ÷vâs°¢6öç7B7W'&VçD†–æW757FFRÐ¢&VF–æW73òæ†–æW72ÓÓÒçVÆÂÇÀ¢&VF–æW73òæ†–æW72ÓÓÒVæFVf–æV@¢òv7W'&VçB†–æW72Væf–Æ&ÆRp¢¢&VF–æW73òæ÷fW%ö†–æW70¢òv&ö÷7BFWFV7FVBæ÷rp¢¢v&ö÷7Bæ÷BFWFV7FVB–WBs°¢6öç7B&VF–7F–öä6öçFW‡EFW‡BÐ¢ÆâÓÓÒv†•ö§V×p¢òÆææVB6öçFW‡C¢&ö÷7FVB†–æW72+ræ÷s¢G¶7W'&VçD†–æW757FFWÖ ¢¢uÆææVB6öçFW‡C¢æò†–æW72&ö÷7Bö'6W'fVBs°¢6öç7BW&–öD÷F–öç2Ò°¢²svBrÂsvVV²uÒÀ¢²sFBrÂs"vVV·2uÒÀ¢²s3BrÂsÖöçF‚uÒÀ¢²vÆÂrÂtÆÂF–ÖRuÐ¢Ð¢æÖ€¢…°¢fÇVRÀ¢Æ&VÀ¢Ò’Óà¢Æ÷F–öâfÇVSÒ"G·fÇVWÒ"G·fÇVRÓÓÒW&–öBòw6VÆV7FVBr¢rwÓâG¶Æ&VÇÓÂö÷F–öãæ ¢¢æ¦ö–â‚rr“°¢6öç7B7FD÷F–öç2Ò°¢²vÆÂrÂtÆÂ7FG2uÒÀ¢²w7G&VæwF‚rÂu7G&VæwF‚uÒÀ¢²vFVfVç6RrÂtFVfVç6RuÒÀ¢²w7VVBrÂu7VVBuÒÀ¢²vFW‡FW&—G’rÂtFW‡FW&—G’uÐ¢Ð¢æÖ€¢…°¢fÇVRÀ¢Æ&VÀ¢Ò’Óà¢Æ÷F–öâfÇVSÒ"G·fÇVWÒ"G·fÇVRÓÓÒ7VÖÖ'’ç7FBòw6VÆV7FVBr¢rwÓâG¶Æ&VÇÓÂö÷F–öãæ ¢¢æ¦ö–â‚rr“°¢6öç7B&VF–7F–öå7FD÷F–öç2Ò°¢²w7G&VæwF‚rÂu7G&VæwF‚uÒÀ¢²vFVfVç6RrÂtFVfVç6RuÒÀ¢²w7VVBrÂu7VVBuÒÀ¢²vFW‡FW&—G’rÂtFW‡FW&—G’uÐ¢Ð¢æÖ€¢…°¢fÇVRÀ¢Æ&VÀ¢Ò’Óà¢Æ÷F–öâfÇVSÒ"G·fÇVWÒ"G·fÇVRÓÓÒ6VÆV7FVE&VF–7F–öå7FBòw6VÆV7FVBr¢rwÓâG¶Æ&VÇÓÂö÷F–öãæ ¢¢æ¦ö–â‚rr“°¢6öç7BÆä÷F–öç2Ò°¢°¢vVff–6–VçE÷G&–æ–ærrÀ¢tVff–6–VçBp¢ÒÀ¢°¢v†•ö§V×rÀ¢t†’§V×p¢Ð¢Ð¢æÖ€¢…°¢fÇVRÀ¢Æ&VÀ¢Ò’Óà¢Æ÷F–öâfÇVSÒ"G·fÇVWÒ"G·fÇVRÓÓÒÆâòw6VÆV7FVBr¢rwÓâG¶Æ&VÇÓÂö÷F–öãæ ¢¢æ¦ö–â‚rr“° ¢&WGW&â ¢Ç6V7F–öâ6Æ73Ò'F×G&–æ–ærÖ6ö×7B×7VÖÖ'’"FF×F×G&–æ–ær×7VÖÖ'“à¢ÆF—b6Æ73Ò'F×G&–æ–ær×7VÖÖ'’Ö†VFW"#à¢ÆF—cà¢Ç7â6Æ73Ò'F×G&–æ–ær×7VÖÖ'’Ö¶–6¶W"#åG&–âæ÷sÂ÷7ãà¢Ç7G&öæsâG¶W66T7F—f—G”‡FÖÂ†Gf–6SòçF—FÆRÇÂuG&–æ–ær†—7F÷'’r—ÓÂ÷7G&öæsà¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×6VÆV7F÷'2#à¢ÆÆ&VÂ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×W&–öB#à¢Ç7ãåÆãÂ÷7ãà¢Ç6VÆV7BFF×F×G&–æ–ær×Æâ&–ÖÆ&VÃÒ%G&–æ–ærÆâ#à¢G·Æä÷F–öç7Ð¢Â÷6VÆV7Cà¢ÂöÆ&VÃà¢ÂöF—cà¢ÂöF—cà ¢G°¢Gf–6SòæFWF–À¢òÇ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’ÖGf–6R#âG¶W66T7F—f—G”‡FÖÂ†Gf–6RæFWF–Â—ÓÂ÷æ ¢¢rp¢Ð ¢G·&VæFW%G&–æ–æu&VF–æW74wV–FR€¢&VF–æW72À¢ÆâÀ¢Gf–6RÀ¢ÖF‚æfÆö÷"„FFRææ÷r‚’ò¢—Ð ¢ÆFWF–Ç0¢6Æ73Ò'F×G&–æ–ær×7W÷'B×6V7F–öâ ¢FF×F×G&–æ–ær×7W÷'B×6V7F–öãÒ'&V6 ¢à¢Ç7VÖÖ'“à¢Ç7ãåG&–æ–ær&V6Â÷7ãà¢Æ#âG¶W66T7F—f—G”‡FÖÂ‡7VÖÖ'’çW&–öEöÆ&VÂ—ÓÂö#à¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×G&–æ–ær×7W÷'BÖ6öçG&öÇ2#à¢ÆÆ&VÂ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×W&–öB#à¢Ç7ãåW&–öCÂ÷7ãà¢Ç6VÆV7BFF×F×G&–æ–ær×7VÖÖ'’×&ævR&–ÖÆ&VÃÒ%G&–æ–ær7VÖÖ'’W&–öB#à¢G·W&–öD÷F–öç7Ð¢Â÷6VÆV7Cà¢ÂöÆ&VÃà¢ÆÆ&VÂ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×W&–öB#à¢Ç7ãå7FG3Â÷7ãà¢Ç6VÆV7BFF×F×G&–æ–ær×7VÖÖ'’×7FB&–ÖÆ&VÃÒ%G&–æ–ær7VÖÖ'’7FB#à¢G·7FD÷F–öç7Ð¢Â÷6VÆV7Cà¢ÂöÆ&VÃà¢ÂöF—cà¢G°¢§V×&V6 ¢òÇ6Æ73Ò'F×G&–æ–ærÖ§V××&V6"FF×F×G&–æ–ærÖ§V××&V6ãÇ7ãäÆFW7B†’§V×Â÷7ããÆ#âG¶W66T7F—f—G”‡FÖÂ†§V×&V6—ÓÂö#ãÂ÷æ ¢¢rp¢Ð¢Æ'WGFöà¢G—SÒ&'WGFöâ ¢6Æ73Ò'F×G&–æ–ær×&V6 ¢FF×F×G&–æ–ær×&V6 ¢FF×F×G&–æ–ær×&V6×FW‡CÒ"G¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…G&–æ–æu&V66VçFVæ6R‡7VÖÖ'’’—Ò ¢FF×FÖ6÷’×7FFSÒ&–FÆR ¢&–ÖÆ&VÃÒ%&W&RG&–æ–ær&V66÷’ ¢à¢Ç7ãå6†&V&ÆR&V6Â÷7ãà¢Æ#âG¶W66T7F—f—G”‡FÖÂ‡7FDw&÷wF…G&–æ–æu&V66VçFVæ6R‡7VÖÖ'’’—ÓÂö#à¢Ç6ÖÆÂFF×F×G&–æ–ær×&V6Ö6÷’ÖÆ&VÂ&–ÖÆ—fSÒ'öÆ—FR#ãÂ÷6ÖÆÃà¢Âö'WGFöãà¢ÂöFWF–Ç3à ¢ÆFWF–Ç0¢6Æ73Ò'F×G&–æ–ær×7W÷'B×6V7F–öâ ¢FF×F×G&–æ–ær×7W÷'B×6V7F–öãÒ'&VF–7F–öâ ¢à¢Ç7VÖÖ'“à¢Ç7ãäW7F–ÖFVBv–ãÂ÷7ãà¢Æ#âG·&ö¦V7F–öãòæf–Æ&ÆRòG·7FDw&÷wF„f÷&ÖDçVÖ&W"‡&ö¦V7F–öâæÆ÷rÂ"—Þ(	2G·7FDw&÷wF„f÷&ÖDçVÖ&W"‡&ö¦V7F–öâæ†–v‚Â"—Ö¢tæ÷BVæ÷Vv‚Wf–FVæ6RwÓÂö#à¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×G&–æ–ær×7W÷'BÖ6öçG&öÇ2F×G&–æ–ær×&VF–7F–öâÖ6öçG&öÇ2#à¢ÆÆ&VÂ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×W&–öB#à¢Ç7ãå7FCÂ÷7ãà¢Ç6VÆV7BFF×F×G&–æ–ær×&VF–7F–öâ×7FB&–ÖÆ&VÃÒ%&VF–7F–öâ7FB#à¢G·&VF–7F–öå7FD÷F–öç7Ð¢Â÷6VÆV7Cà¢ÂöÆ&VÃà¢ÂöF—cà¢Ç6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×&VF–7F–öâ#ãÇ7ãå&VF–7F–öãÂ÷7ãâG¶W66T7F—f—G”‡FÖÂ‡&VF–7F–öåFW‡B—Ò+rG¶W66T7F—f—G”‡FÖÂ‡&VF–7F–öäWf–FVæ6R—ÓÇ6ÖÆÂ6Æ73Ò'F×G&–æ–ær×7VÖÖ'’×&VF–7F–öâÖ6öçFW‡B#âG¶W66T7F—f—G”‡FÖÂ‡&VF–7F–öä6öçFW‡EFW‡B—ÓÂ÷6ÖÆÃãÂ÷à¢ÂöFWF–Ç3à ¢Â÷6V7F–öãà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FG5v÷&·76Tæf–vF–öâ€¢f–WrÒv÷fW'f–Wrp¢’°¢6öç7B7F—fUf–WrÐ¢V•6W76–öå7FG5v÷&·76Uf–Wr€¢f–Wp¢“°¢6öç7Bf–Ww2Ò°¢²v÷fW'f–WrrÂt÷fW'f–WruÒÀ¢²v6†'G2rÂt6†'G2uÒÀ¢²vFFrÂtFFuÐ¢Ó° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×7FG2×f–WrÖæb"&öÆSÒ'F&Æ—7B"&–ÖÆ&VÃÒ%7FG2f–Ww2#à¢G·f–Ww2æÖ€¢…·fÇVRÂÆ&VÅÒ’Óâ ¢Æ'WGFöà¢G—SÒ&'WGFöâ ¢–CÒ'F×7FG2×f–WrÒG·fÇVWÒ×F" ¢&öÆSÒ'F" ¢FF×F×7FG2×f–WrÖ÷F–öãÒ"G·fÇVWÒ ¢&–Ö6öçG&öÇ3Ò'F×7FG2×f–WrÒG·fÇVWÒ ¢&–×6VÆV7FVCÒ"G·fÇVRÓÓÒ7F—fUf–WròwG'VRr¢vfÇ6RwÒ ¢F&–æFWƒÒ"G·fÇVRÓÓÒ7F—fUf–Wròsr¢rÓwÒ ¢6Æ73Ò"G·fÇVRÓÓÒ7F—fUf–WròwF×7FG2×f–WrÖ7F—fRr¢rwÒ ¢âG¶Æ&VÇÓÂö'WGFöãà¢ ¢’æ¦ö–â‚rr—Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%7FG5v÷&·76Uf–Wr€¢f–WrÀ¢&VF–æW72À¢w&÷wF‚À¢÷F–öç2Ò·Ð¢’°¢6öç7B7F—fUf–WrÐ¢V•6W76–öå7FG5v÷&·76Uf–Wr€¢f–Wp¢“°¢ÆWB6öçFVçBÒrs° ¢–b€¢7F—fUf–WrÓÓÐ¢v6†'G2p¢’°¢6öçFVçBÐ¢&VæFW%7FDw&÷wF„F6†&ö&B€¢w&÷wF‚À¢÷F–öç0¢“°¢ÒVÇ6R–b€¢7F—fUf–WrÓÓÐ¢vFFp¢’°¢6öçFVçBÐ¢&VæFW%7FDw&÷wF„FFf–Wr€¢w&÷wF‚À¢&VF–æW72À¢÷F–öç2çÆâÀ¢÷F–öç2ç7VÖÖ'•÷7F@¢“°¢ÒVÇ6R°¢6öçFVçBÐ¢&VæFW%G&–æ–æt6ö×7E7VÖÖ'’€¢&VF–æW72À¢w&÷wF‚À¢÷F–öç2ç&ævRÀ¢÷F–öç2çÆâÀ¢÷F–öç2ç7VÖÖ'•÷7F@¢“°¢Ð ¢&WGW&â ¢ÆF—`¢–CÒ'F×7FG2×f–WrÒG¶7F—fUf–WwÒ ¢6Æ73Ò'F×7FG2×f–Wr×æVÂF×7FG2ÒG¶7F—fUf–WwÒ×f–Wr ¢FF×F×7FG2×f–WrÖ†÷7@¢FF×F×7FG2×f–WsÒ"G¶7F—fUf–WwÒ ¢&öÆSÒ'F'æVÂ ¢&–ÖÆ&VÆÆVF'“Ò'F×7FG2×f–WrÒG¶7F—fUf–WwÒ×F" ¢à¢G¶6öçFVçGÐ¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%G&–æ–æuv÷&·76R€¢&VF–æW72À¢w&÷wF€¢’°¢–b€¢&VF–æW72b`¢w&÷wF€¢’°¢&WGW&ârs°¢Ð ¢6öç7B7FFRÐ¢°¢ââç&VEV•6W76–öå7FFR‚’À¢ââç&VE&W6÷W&6TF6†&ö&E&VfW&Væ6W2‚’À¢ââç&VE7FDw&÷wF…&VfW&Væ6W2‚¢Ó° ¢6öç7BFVfVÇD÷VâÐ¢&VF–æW73òçvUö—5öw–ÒÓÓÐ¢G'VS° ¢6öç7Bv÷&·76T÷VâÐ¢7FFRçG&–æ–æu÷v÷&·76Uö÷VâÓÓÐ¢çVÆÀ¢òFVfVÇD÷Và¢¢7FFRçG&–æ–æu÷v÷&·76Uö÷Vã° ¢6öç7B&VF–æW74÷VâÐ¢7FFRçG&–æ–æu÷&VF–æW75ö÷VâÓÓÐ¢çVÆÀ¢òFVfVÇD÷Và¢¢7FFRçG&–æ–æu÷&VF–æW75ö÷Vã° ¢6öç7Bfö7W2Ð¢V•6W76–öåG&–æ–ætfö7W2€¢7FFRç7FEöw&÷wF…öfö7W0¢“° ¢6öç7B66÷RÐ¢7FFRç7FEöw&÷wF…÷66÷RÓÓÐ¢vÆÂp¢òvÆÂp¢¢w6VÆV7FVBs°¢6öç7B6öçFW‡BÐ¢V•6W76–öå7FDw&÷wF„6öçFW‡B€¢7FFRç7FEöw&÷wF…ö6öçFW‡@¢“°¢6öç7B&ævRÐ¢V•6W76–öå7FDw&÷wF…&ævR€¢7FFRç7FEöw&÷wF…÷&ævP¢“°¢6öç7B7VÖÖ'•7FBÐ¢7FDw&÷wF„6ö×7E7VÖÖ'•7FB€¢7FFRçG&–æ–æu÷7VÖÖ'•÷7F@¢“°¢6öç7B7F—fUf–WrÐ¢V•6W76–öå7FG5v÷&·76Uf–Wr€¢7FFRç7FG5÷v÷&·76U÷f–Wp¢“° ¢6öç7BÖWFÒ°¢&VF–æW73òæVæW&w’ÓÓÒçVÆÂÇÀ¢&VF–æW73òæVæW&w’ÓÓÒVæFVf–æV@¢òt†—7F÷&–6Â&VF–æW72p¢¢G´çVÖ&W"‡&VF–æW72æVæW&w’’çFôÆö6ÆU7G&–ær‚—ÒVÀ¢w&÷wFƒòçfÆ–EöÆöw0¢òG´çVÖ&W"†w&÷wF‚çfÆ–EöÆöw2’çFôÆö6ÆU7G&–ær‚—Ò7F–öç6 ¢¢çVÆÀ¢Òæf–ÇFW"„&ööÆVâ’æ¦ö–â‚r+rr“° ¢&WGW&â ¢ÆFWF–Ç26Æ73Ò'F×6V7F–öâF×G&–æ–ær×v÷&·76R×6V7F–öâ"G·v÷&·76T÷Vâòv÷Vâr¢rwÓà¢Ç7VÖÖ'’6Æ73Ò'F×6V7F–öâ×7VÖÖ'’×&÷r#à¢Ç7â6Æ73Ò'F×6V7F–öâ×F—FÆR#å7FG3Â÷7ãà¢Ç7â6Æ73Ò'F×6V7F–öâÖÖWF#âG¶W66T7F—f—G”‡FÖÂ†ÖWF—ÓÂ÷7ãà¢Â÷7VÖÖ'“à ¢ÆF—b6Æ73Ò'F×6V7F–öâÖ&öG’F×G&–æ–ær×v÷&·76RÖ&öG’#à¢G·&VæFW%7FG5v÷&·76Tæf–vF–öâ†7F—fUf–Wr—Ð¢G·&VæFW%7FG5v÷&·76Uf–Wr€¢7F—fUf–WrÀ¢&VF–æW72À¢w&÷wF‚À¢°¢fö7W2À¢66÷RÀ¢6öçFW‡BÀ¢&ævRÀ¢Æã¢&VEG&–æ–æu&VF–æW75Æâ‚’À¢7VÖÖ'•÷7FC¢7VÖÖ'•7F@¢Ð¢—Ð¢ÂöF—cà¢ÂöFWF–Ç3à¢°¢Ð ¢gVæ7F–öâG&–æ–æu7W÷'D÷Vå6V7F–öç2€¢7VÖÖ'¢’°¢&WGW&â'&’æg&öÒ€¢7VÖÖ'“òçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×G&–æ–ær×7W÷'B×6V7F–öåÕ¶÷VåÒp¢’ÇÀ¢µÐ¢¢æÖ‡6V7F–öâÓà¢6V7F–öâævWDGG&–'WFSòâ€¢vFF×F×G&–æ–ær×7W÷'B×6V7F–öâp¢’ÇÀ¢rp¢¢æf–ÇFW"„&ööÆVâ“°¢Ð ¢gVæ7F–öâ&W7F÷&UG&–æ–æu7W÷'D÷Vå6V7F–öç2€¢7VÖÖ'’À¢÷Vå6V7F–öç2ÒµÐ¢’°¢6öç7B÷Vå6WBÐ¢æWr6WB€¢'&’æ—4'&’†÷Vå6V7F–öç2¢ò÷Vå6V7F–öç0¢¢µÐ¢“° ¢f÷"€¢6öç7B6V7F–öà¢öb7VÖÖ'“òçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×G&–æ–ær×7W÷'B×6V7F–öåÒp¢’ÇÀ¢µÐ¢’°¢6V7F–öâæ÷VâÐ¢÷Vå6WBæ†2€¢6V7F–öâævWDGG&–'WFSòâ€¢vFF×F×G&–æ–ær×7W÷'B×6V7F–öâp¢’ÇÀ¢rp¢“°¢Ð¢Ð ¢gVæ7F–öâ&–æEG&–æ–æuv÷&·76T–çFW&7F–öç2€¢&ö÷BÀ¢&VF–æW72ÒçVÆÂÀ¢w&÷wF‚ÒçVÆÀ¢’°¢&ö÷Båõ÷FG&–æ–æu&VF–æW72Ð¢&VF–æW72ÇÀ¢&ö÷Båõ÷FG&–æ–æu&VF–æW72ÇÀ¢çVÆÃ°¢&ö÷Båõ÷FG&–æ–ætw&÷wF‚Ð¢w&÷wF‚ÇÀ¢&ö÷Båõ÷FG&–æ–ætw&÷wF‚ÇÀ¢çVÆÃ° ¢&ö÷Båõ÷F7FG5v÷&·76Uf–WrÐ¢V•6W76–öå7FG5v÷&·76Uf–Wr€¢&VE7FDw&÷wF…&VfW&Væ6W2‚¢ç7FG5÷v÷&·76U÷f–Wp¢“° ¢6öç7B&Vg&W6„§V×6÷VçFF÷vâÐ¢‚’Óâ°¢6ÆV%F–ÖV÷WB€¢&ö÷Båõ÷FG&–æ–æt§V×6÷VçFF÷våF–ÖW ¢“° ¢6öç7B6÷VçFF÷vâÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ærÖ§V×Ö6÷VçFF÷våÒp¢“° ¢–b‚6÷VçFF÷vâ’°¢&WGW&ã°¢Ð ¢6öç7BWFFRÐ¢‚’Óâ°¢–b‚6÷VçFF÷vâæ—46öææV7FVB’°¢&WGW&ã°¢Ð ¢6öç7BV'FW"Ð¢G&–æ–æu&VF–æW75V'FW$†÷W"€¢FFRææ÷r‚¢“° ¢6÷VçFF÷vâçFW‡D6öçFVçBÐ¢æW‡BD5B&W6WB+rG·G&–æ–æu&VF–æW74f÷&ÖDGW&F–öâ‡V'FW"ç6V6öæG5÷VçF–Â—Ö° ¢&ö÷Båõ÷FG&–æ–æt§V×6÷VçFF÷våF–ÖW"Ð¢6WEF–ÖV÷WB€¢WFFRÀ¢Ò„FFRææ÷r‚’R’²# ¢“°¢Ó° ¢WFFR‚“°¢Ó° ¢6öç7B&Vg&W6„6ö×7E7VÖÖ'’Ð¢€¢&ævUfÇVRÀ¢7FEfÇVRÒçVÆÀ¢’Óâ°¢6öç7B7W'&VçBÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×7VÖÖ'•Òp¢“° ¢–b€¢7W'&Vç@¢’°¢&WGW&ã°¢Ð ¢6öç7B&ævRÐ¢7FDw&÷wF„6ö×7EW&–öB€¢&ævUfÇVP¢“°¢6öç7B7VÖÖ'•7FBÐ¢7FDw&÷wF„6ö×7E7VÖÖ'•7FB€¢7FEfÇVRÇÀ¢&ö÷Båõ÷FG&–æ–æu7VÖÖ'•7FBÇÀ¢&VE7FDw&÷wF…&VfW&Væ6W2‚¢çG&–æ–æu÷7VÖÖ'•÷7F@¢“° ¢&ö÷Båõ÷FG&–æ–æu7VÖÖ'•7FBÐ¢7VÖÖ'•7FC° ¢6öç7B÷Vå7W÷'E6V7F–öç2Ð¢G&–æ–æu7W÷'D÷Vå6V7F–öç2€¢7W'&Vç@¢“°¢6öç7B67&öÆÄ6öçF–æW"Ð¢7W'&VçBæ6Æ÷6W7Còâ€¢rçFÖÖöFÂ×67&öÆÂp¢’ÇÀ¢çVÆÃ°¢6öç7B67&öÆÅF÷Ð¢çVÖ&W"æ—4f–æ—FR€¢çVÖ&W"€¢67&öÆÄ6öçF–æW#òç67&öÆÅF÷ ¢¢¢òçVÖ&W"€¢67&öÆÄ6öçF–æW"ç67&öÆÅF÷ ¢¢¢çVÆÃ° ¢7W'&VçBæ÷WFW$…DÔÂÐ¢&VæFW%G&–æ–æt6ö×7E7VÖÖ'’€¢&ö÷Båõ÷FG&–æ–æu&VF–æW72À¢&ö÷Båõ÷FG&–æ–ætw&÷wF‚À¢&ævRÀ¢&VEG&–æ–æu&VF–æW75Æâ‚’À¢7VÖÖ'•7F@¢“° ¢6öç7BæW‡E7VÖÖ'’Ð¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×7VÖÖ'•Òp¢“° ¢&W7F÷&UG&–æ–æu7W÷'D÷Vå6V7F–öç2€¢æW‡E7VÖÖ'’À¢÷Vå7W÷'E6V7F–öç0¢“° ¢–b€¢67&öÆÄ6öçF–æW"b`¢67&öÆÅF÷ÓÒçVÆÀ¢’°¢67&öÆÄ6öçF–æW"ç67&öÆÅF÷Ð¢67&öÆÅF÷°¢Ð ¢&–æD6ö×7E7VÖÖ'’‚“°¢&Vg&W6„§V×6÷VçFF÷vâ‚“°¢Ó° ¢6öç7B&–æD6ö×7E7VÖÖ'’Ð¢‚’Óâ°¢6öç7B&ævU6VÆV7BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×7VÖÖ'’×&ævUÒp¢“°¢6öç7BÆå6VÆV7BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×ÆåÒp¢“°¢6öç7B7FE6VÆV7BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×7VÖÖ'’×7FEÒp¢“°¢6öç7B&VF–7F–öå7FE6VÆV7BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×&VF–7F–öâ×7FEÒp¢“°¢6öç7B&V6Ð¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢u¶FF×F×G&–æ–ær×&V6Òp¢“° ¢&V6òæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢7–æ2‚’Óâ°¢6öç7B7FFRÐ¢&V6ævWDGG&–'WFR€¢vFF×FÖ6÷’×7FFRp¢’ÇÀ¢v–FÆRs°¢6öç7BÆ&VÂÐ¢&V6çVW'•6VÆV7F÷"€¢u¶FF×F×G&–æ–ær×&V6Ö6÷’ÖÆ&VÅÒp¢“° ¢6ÆV%F–ÖV÷WB€¢&ö÷Båõ÷FG&–æ–æu&V66÷•F–ÖW ¢“° ¢–b€¢7FFRÓÒv&ÖVBp¢’°¢&V6ç6WDGG&–'WFR€¢vFF×FÖ6÷’×7FFRrÀ¢v&ÖVBp¢“°¢&V6ç6WDGG&–'WFR€¢v&–ÖÆ&VÂrÀ¢t6÷’G&–æ–ær&V6p¢“° ¢–b€¢Æ&VÀ¢’°¢Æ&VÂçFW‡D6öçFVçBÐ¢t6÷’s°¢Ð ¢&ö÷Båõ÷FG&–æ–æu&V66÷•F–ÖW"Ð¢6WEF–ÖV÷WB€¢‚’Óâ°¢–b€¢&V6æ—46öææV7FV@¢’°¢&V6ç6WDGG&–'WFR€¢vFF×FÖ6÷’×7FFRrÀ¢v–FÆRp¢“°¢&V6ç6WDGG&–'WFR€¢v&–ÖÆ&VÂrÀ¢u&W&RG&–æ–ær&V66÷’p¢“° ¢–b€¢Æ&VÀ¢’°¢Æ&VÂçFW‡D6öçFVçBÐ¢rs°¢Ð¢Ð¢ÒÀ¢C ¢“° ¢&WGW&ã°¢Ð ¢6öç7B6÷–VBÐ¢v—B6÷•G&–æ–æu&V6FW‡B€¢&V6ævWDGG&–'WFR€¢vFF×F×G&–æ–ær×&V6×FW‡Bp¢¢“°¢6öç7BæW‡E7FFRÐ¢6÷–V@¢òv6÷–VBp¢¢vW'&÷"s° ¢&V6ç6WDGG&–'WFR€¢vFF×FÖ6÷’×7FFRrÀ¢æW‡E7FFP¢“°¢&V6ç6WDGG&–'WFR€¢v&–ÖÆ&VÂrÀ¢6÷–V@¢òuG&–æ–ær&V66÷–VBp¢¢uG&–æ–ær&V66÷’f–ÆVBp¢“° ¢–b€¢Æ&VÀ¢’°¢Æ&VÂçFW‡D6öçFVçBÐ¢6÷–V@¢òt6÷–VBp¢¢t6÷’f–ÆVBs°¢Ð ¢&ö÷Båõ÷FG&–æ–æu&V66÷•F–ÖW"Ð¢6WEF–ÖV÷WB€¢‚’Óâ°¢–b€¢&V6æ—46öææV7FV@¢’°¢&V6ç6WDGG&–'WFR€¢vFF×FÖ6÷’×7FFRrÀ¢v–FÆRp¢“°¢&V6ç6WDGG&–'WFR€¢v&–ÖÆ&VÂrÀ¢u&W&RG&–æ–ær&V66÷’p¢“° ¢–b€¢Æ&VÀ¢’°¢Æ&VÂçFW‡D6öçFVçBÐ¢rs°¢Ð¢Ð¢ÒÀ¢#S ¢“°¢Ð¢“° ¢&ævU6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢6öç7B&ævRÐ¢7FDw&÷wF„6ö×7EW&–öB€¢&ævU6VÆV7BçfÇVP¢“° ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÐ¢&ævS° ¢w&—FUV•6W76–öå7FFR‡°¢7FEöw&÷wF…÷&ævS ¢&ævP¢Ò“° ¢&Vg&W6„6ö×7E7VÖÖ'’€¢&ævRÀ¢7FE6VÆV7CòçfÇVP¢“°¢Ð¢“° ¢7FE6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢6öç7B7VÖÖ'•7FBÐ¢7FDw&÷wF„6ö×7E7VÖÖ'•7FB€¢7FE6VÆV7BçfÇVP¢“° ¢&ö÷Båõ÷FG&–æ–æu7VÖÖ'•7FBÐ¢7VÖÖ'•7FC° ¢w&—FU7FDw&÷wF…&VfW&Væ6W2‡°¢G&–æ–æu÷7VÖÖ'•÷7FC ¢7VÖÖ'•7F@¢Ò“° ¢&Vg&W6„6ö×7E7VÖÖ'’€¢&ævU6VÆV7CòçfÇVRÇÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢7VÖÖ'•7F@¢“°¢Ð¢“° ¢&VF–7F–öå7FE6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢6öç7B7VÖÖ'•7FBÐ¢7FDw&÷wF„6ö×7E7VÖÖ'•7FB€¢&VF–7F–öå7FE6VÆV7BçfÇVP¢“° ¢&ö÷Båõ÷FG&–æ–æu7VÖÖ'•7FBÐ¢7VÖÖ'•7FC° ¢w&—FU7FDw&÷wF…&VfW&Væ6W2‡°¢G&–æ–æu÷7VÖÖ'•÷7FC ¢7VÖÖ'•7F@¢Ò“° ¢&Vg&W6„6ö×7E7VÖÖ'’€¢&ævU6VÆV7CòçfÇVRÇÀ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÀ¢7VÖÖ'•7F@¢“°¢Ð¢“° ¢Æå6VÆV7CòæFDWfVçDÆ—7FVæW"€¢v6†ævRrÀ¢‚’Óâ°¢w&—FUG&–æ–æu&VF–æW75Æâ€¢Æå6VÆV7BçfÇVP¢“° ¢&Vg&W6„6ö×7E7VÖÖ'’€¢&ö÷Båõ÷F7FDw&÷wF…&ævRÇÀ¢&VEV•6W76–öå7FFR‚¢ç7FEöw&÷wF…÷&ævRÀ¢7FE6VÆV7CòçfÇVP¢“°¢Ð¢“°¢Ó° ¢&–æD6ö×7E7VÖÖ'’‚“°¢&Vg&W6„§V×6÷VçFF÷vâ‚“° ¢6öç7Bf–Wt'WGFöç2Ð¢'&’æg&öÒ€¢&ö÷CòçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×7FG2×f–WrÖ÷F–öåÒp¢’ÇÀ¢µÐ¢“° ¢6öç7B7F—fFU7FG5f–WrÐ¢f–WufÇVRÓâ°¢6öç7BæW‡Ef–WrÐ¢V•6W76–öå7FG5v÷&·76Uf–Wr€¢f–WufÇVP¢“° ¢&ö÷Båõ÷F7FG5v÷&·76Uf–WrÐ¢æW‡Ef–Ws° ¢w&—FU7FDw&÷wF…&VfW&Væ6W2‡°¢7FG5÷v÷&·76U÷f–Ws ¢æW‡Ef–Wp¢Ò“° ¢f÷"€¢6öç7B'WGFöà¢öbf–Wt'WGFöç0¢’°¢6öç7B7F—fRÐ¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FG2×f–WrÖ÷F–öâp¢’ÓÓÐ¢æW‡Ef–Ws° ¢'WGFöâæ6Æ74Æ—7BçFövvÆR€¢wF×7FG2×f–WrÖ7F—fRrÀ¢7F—fP¢“°¢'WGFöâç6WDGG&–'WFR€¢v&–×6VÆV7FVBrÀ¢7F—fP¢òwG'VRp¢¢vfÇ6Rp¢“°¢'WGFöâçF$–æFW‚Ð¢7F—fP¢ò ¢¢Ó°¢Ð ¢6öç7B†÷7BÐ¢&ö÷BçVW'•6VÆV7F÷"€¢u¶FF×F×7FG2×f–WrÖ†÷7EÒp¢“° ¢–b€¢†÷7@¢’°¢6öç7B7W'&VçE7FFRÐ¢&VEV•6W76–öå7FFR‚“°¢6öç7B&VfW&Væ6W2Ð¢&VE7FDw&÷wF…&VfW&Væ6W2‚“° ¢†÷7Bæ÷WFW$…DÔÂÐ¢&VæFW%7FG5v÷&·76Uf–Wr€¢æW‡Ef–WrÀ¢&ö÷Båõ÷FG&–æ–æu&VF–æW72À¢&ö÷Båõ÷FG&–æ–ætw&÷wF‚À¢°¢fö7W3 ¢&ö÷Båõ÷F7FDw&÷wF„fö7W2ÇÀ¢&VfW&Væ6W2ç7FEöw&÷wF…öfö7W2ÇÀ¢7W'&VçE7FFRç7FEöw&÷wF…öfö7W2À¢66÷S ¢&ö÷Båõ÷F7FDw&÷wF…66÷RÇÀ¢7W'&VçE7FFRç7FEöw&÷wF…÷66÷RÀ¢6öçFW‡C ¢&ö÷Båõ÷F7FDw&÷wF„6öçFW‡BÇÀ¢7W'&VçE7FFRç7FEöw&÷wF…ö6öçFW‡BÀ¢&ævS ¢&ö÷Båõ÷F7FDw&÷wF…&ævRÇÀ¢7W'&VçE7FFRç7FEöw&÷wF…÷&ævRÀ¢Æã ¢&VEG&–æ–æu&VF–æW75Æâ‚’À¢7VÖÖ'•÷7FC ¢&ö÷Båõ÷FG&–æ–æu7VÖÖ'•7FBÇÀ¢&VfW&Væ6W2çG&–æ–æu÷7VÖÖ'•÷7F@¢Ð¢“°¢Ð ¢&–æD6ö×7E7VÖÖ'’‚“°¢&Vg&W6„§V×6÷VçFF÷vâ‚“°¢&–æE7FDw&÷wF„F6†&ö&D–çFW&7F–öç2€¢&ö÷BÀ¢&ö÷Båõ÷FG&–æ–ætw&÷wF€¢“°¢Ó° ¢f÷"€¢6öç7B¶–æFW‚Â'WGFöåÐ¢öbf–Wt'WGFöç2æVçG&–W2‚¢’°¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óà¢7F—fFU7FG5f–Wr€¢'WGFöâævWDGG&–'WFR€¢vFF×F×7FG2×f–WrÖ÷F–öâp¢¢¢“° ¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v¶W–F÷vârÀ¢WfVçBÓâ°¢–b€¢WfVçBæ¶W’ÓÐ¢t'&÷tÆVgBrb`¢WfVçBæ¶W’ÓÐ¢t'&÷u&–v‡Bp¢’°¢&WGW&ã°¢Ð ¢WfVçBç&WfVçDFVfVÇB‚“°¢6öç7BF—&V7F–öâÐ¢WfVçBæ¶W’ÓÓÐ¢t'&÷u&–v‡Bp¢ò¢¢Ó°¢6öç7BæW‡D'WGFöâÐ¢f–Wt'WGFöç5°¢€¢–æFW‚°¢F—&V7F–öâ°¢f–Wt'WGFöç2æÆVæwF€¢’P¢f–Wt'WGFöç2æÆVæwF€¢Ó° ¢æW‡D'WGFöãòæfö7W3òâ‚“°¢æW‡D'WGFöãòæ6Æ–6³òâ‚“°¢Ð¢“°¢Ð ¢6öç7B&–æF–æw2Ò°¢°¢rçF×G&–æ–ær×v÷&·76R×6V7F–öârÀ¢wG&–æ–æu÷v÷&·76Uö÷Vâp¢ÒÀ¢°¢rçF×G&–æ–ær×&VF–æW72×6V7F–öârÀ¢wG&–æ–æu÷&VF–æW75ö÷Vâp¢Ð¢Ó° ¢f÷"€¢6öç7B·6VÆV7F÷"Â¶W•Ð¢öb&–æF–æw0¢’°¢6öç7B6V7F–öâÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢6VÆV7F÷ ¢“° ¢6V7F–öãòæFDWfVçDÆ—7FVæW"€¢wFövvÆRrÀ¢‚’Óâ°¢w&—FUV•6W76–öå7FFR‡°¢¶¶W•Ó ¢6V7F–öâæ÷VâÓÓÐ¢G'VP¢Ò“°¢Ð¢“°¢Ð¢Ð ¢gVæ7F–öâ&VæFW%7F÷&VDæÇ—6—4F6†&ö&G2€¢æÇ—6—0¢’°¢&WGW&â€¢&VæFW%G&–æ–æuv÷&·76R€¢æÇ—6—3òçG&–æ–æu÷&VF–æW72À¢æÇ—6—3òç7FEöw&÷wF€¢’°¢&VæFW%vVV¶Ç”†–v†Æ–v‡G2€¢æÇ—6—3òç&W6÷W&6UöfÆ÷rÀ¢æÇ—6—3òæ7F—f—G¢¢“°¢Ð ¢gVæ7F–öâ&–æE7F÷&VDæÇ—6—4F6†&ö&D–çFW&7F–öç2€¢&ö÷BÀ¢æÇ—6—2ÒçVÆÀ¢’°¢&–æE&W6÷W&6TF6†&ö&D–çFW&7F–öç2€¢&ö÷@¢“° ¢&–æEG&–æ–æuv÷&·76T–çFW&7F–öç2€¢&ö÷BÀ¢æÇ—6—3òçG&–æ–æu÷&VF–æW72À¢æÇ—6—3òç7FEöw&÷wF€¢“° ¢&–æEG&–æ–æu&VF–æW74–çFW&7F–öç2€¢&ö÷@¢“° ¢&–æD7F—f—G”F6†&ö&D–çFW&7F–öç2€¢&ö÷@¢“° ¢&–æE7FDw&÷wF„F6†&ö&D–çFW&7F–öç2€¢&ö÷BÀ¢æÇ—6—3òç7FEöw&÷wF€¢“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòTäU$u’òäU%dRò„”äU52$U4õU$4RÔdÄõrdõTäDD”ôà¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâ&W6÷W&6TfÆ÷tf–æ—FTçVÖ&W"€¢fÇVP¢’°¢–b€¢G—VöbfÇVRÓÓÒvçVÖ&W"p¢’°¢&WGW&âçVÖ&W"æ—4f–æ—FR€¢fÇVP¢¢òfÇVP¢¢çVÆÃ°¢Ð ¢–b€¢G—VöbfÇVRÓÒw7G&–ærp¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7Bæ÷&ÖÆ—¦VBÐ¢fÇVRçG&–Ò‚“° ¢–b€¢æ÷&ÖÆ—¦VBÇÀ¢õå²²ÕÓõÆB²BòçFW7B€¢æ÷&ÖÆ—¦V@¢¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7BçVÖ&W"Ð¢çVÖ&W"€¢æ÷&ÖÆ—¦V@¢“° ¢&WGW&âçVÖ&W"æ—4f–æ—FR€¢çVÖ&W ¢¢òçVÖ&W ¢¢çVÆÃ°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢fÇVP¢’°¢6öç7BçVÖ&W"Ð¢&W6÷W&6TfÆ÷tf–æ—FTçVÖ&W"€¢fÇVP¢“° ¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢çVÖ&W ¢’b`¢çVÖ&W"â ¢òçVÖ&W ¢¢çVÆÃ°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷tæöäæVvF—fTÖ÷VçB€¢fÇVP¢’°¢6öç7BçVÖ&W"Ð¢&W6÷W&6TfÆ÷tf–æ—FTçVÖ&W"€¢fÇVP¢“° ¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢çVÖ&W ¢’b`¢çVÖ&W"ãÒ ¢òçVÖ&W ¢¢çVÆÃ°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷tö'6W'fVE7V72€¢Æöt–@¢’°¢6öç7B–BÐ¢çVÖ&W"€¢Æöt–@¢“° ¢7v—F6‚€¢–@¢’°¢66RC“ ¢&WGW&â·°¢f–VÆC¢vVæW&w•ö–æ7&V6VBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢wö–çE÷&Vf–ÆÂrÀ¢FWF–Ã¢wö–çG2p¢ÕÓ° ¢66RC“S ¢&WGW&â·°¢f–VÆC¢væW'fUö–æ7&V6VBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢wö–çE÷&Vf–ÆÂrÀ¢FWF–Ã¢wö–çG2p¢ÕÓ° ¢66RsƒS ¢&WGW&â·°¢f–VÆC¢vVæW&w•÷&V6V—fVBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vÖ—76–öå÷&Wv&BrÀ¢FWF–Ã¢vÖ—76–öâp¢ÕÓ° ¢òòF÷&â7W'&VçFÇ’æÖW2F†—2–ÆöBf–VÆBVæW&w•÷&V6V—fVBWfVâF†÷Vv€¢òòÆörG—RsƒSW‡Æ–6—FÇ’FW67&–&W2æW'fR&Wv&Bà¢66RsƒS ¢&WGW&â·°¢f–VÆC¢vVæW&w•÷&V6V—fVBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vÖ—76–öå÷&Wv&BrÀ¢FWF–Ã¢vÖ—76–öâp¢ÕÓ° ¢66R#3 ¢&WGW&â·°¢f–VÆC¢væW'fUö–æ7&V6VBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢v6öç7VÖ&ÆRrÀ¢FWF–Ã¢vÆ6ö†öÂp¢ÕÓ° ¢66R## ¢&WGW&â·°¢f–VÆC¢væW'fUö–æ7&V6VBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vG'VrrÀ¢FWF–Ã¢v6ææ&—2p¢ÕÓ° ¢66R## ¢&WGW&â·°¢f–VÆC¢v†•ö–æ7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢v6öç7VÖ&ÆRrÀ¢FWF–Ã¢v6æG’p¢ÕÓ° ¢66R#ƒ ¢&WGW&â·°¢f–VÆC¢v†•ö–æ7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢v6öç7VÖ&ÆRrÀ¢FWF–Ã¢vW&÷F–5öGfBp¢ÕÓ° ¢66R## ¢&WGW&â·°¢f–VÆC¢v†•ö–æ7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vG'VrrÀ¢FWF–Ã¢vV77F7’p¢ÕÓ° ¢66R##ƒ ¢&WGW&â·°¢f–VÆC¢v†•ö–æ7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vG'VrrÀ¢FWF–Ã¢wf–6öF–âp¢ÕÓ° ¢66RcS ¢&WGW&â·°¢f–VÆC¢v†•ö–æ7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢w&V†"rÀ¢FWF–Ã¢çVÆÂÀ¢ÆÆ÷u÷¦W&ó¢G'VP¢ÕÓ° ¢66R##“ ¢&WGW&â°¢°¢f–VÆC¢vVæW&w•öFV7&V6VBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢vÆ÷72rÀ¢6FVv÷'“¢v÷fW&F÷6RrÀ¢FWF–Ã¢w†æ‚rÀ¢ÆÆ÷u÷¦W&ó¢G'VP¢ÒÀ¢°¢f–VÆC¢væW'fUöFV7&V6VBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢vÆ÷72rÀ¢6FVv÷'“¢v÷fW&F÷6RrÀ¢FWF–Ã¢w†æ‚rÀ¢ÆÆ÷u÷¦W&ó¢G'VP¢ÒÀ¢°¢f–VÆC¢v†•öFV7&V6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢vÆ÷72rÀ¢6FVv÷'“¢v÷fW&F÷6RrÀ¢FWF–Ã¢w†æ‚rÀ¢ÆÆ÷u÷¦W&ó¢G'VP¢Ð¢Ó° ¢66RCC ¢&WGW&â·°¢f–VÆC¢vVæW&w•÷W6VBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢vGV×÷6V&6‚rÀ¢FWF–Ã¢çVÆÀ¢ÕÓ° ¢66RS3 ¢66RS3 ¢66RS3# ¢66RS33 ¢&WGW&â°¢°¢f–VÆC¢vVæW&w•÷W6VBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢vw–Õ÷G&–æ–ærrÀ¢FWF–Ã¢çVÆÀ¢ÒÀ¢°¢f–VÆC¢v†•÷W6VBrÀ¢&W6÷W&6S¢v†–æW72rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢vw–Õ÷G&–æ–ærrÀ¢FWF–Ã¢çVÆÂÀ¢ÆÆ÷u÷¦W&ó¢G'VP¢Ð¢Ó° ¢66RS3c# ¢&WGW&â·°¢f–VÆC¢væW'fU÷W6VBrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢v'W7BrÀ¢FWF–Ã¢çVÆÀ¢ÕÓ° ¢66Rƒ ¢66RƒS ¢66Rƒ ¢66RƒS ¢66RƒC ¢66RƒCS ¢66RƒS ¢66RƒSS ¢&WGW&â·°¢f–VÆC¢vVæW&w•÷W6VBrÀ¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢vGF6²rÀ¢FWF–Ã¢çVÆÀ¢ÕÓ° ¢66R“ ¢66R“S ¢66R“# ¢66R“#s ¢66R“S ¢66R“S# ¢66R“SS ¢66R“Sc ¢66R“c ¢66R“S ¢66R“SC ¢66R“SS ¢66R“Sƒ ¢66R“c ¢66R“c3 ¢&WGW&â·°¢f–VÆC¢væW'fRrÀ¢&W6÷W&6S¢væW'fRrÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢v7&–ÖRrÀ¢FWF–Ã¢çVÆÀ¢ÕÓ° ¢FVfVÇC ¢&WGW&âµÓ°¢Ð¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷tFW&—fVE7V2€¢Æöt–@¢’°¢7v—F6‚€¢çVÖ&W"€¢Æöt–@¢¢’°¢66R##“ ¢&WGW&â°¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v–ârÀ¢¶–æC¢vv–ârÀ¢6FVv÷'“¢vG'VrrÀ¢FWF–Ã¢w†æ‚rÀ¢Ö÷VçC¢#SÀ¢W‡V7FVEö—FVÕö–C¢#bÀ¢'VÆS¢w7V66W76gVÅ÷†æ…÷7FæF&EöVæW&w’p¢Ó° ¢66Rc# ¢&WGW&â°¢&W6÷W&6S¢vVæW&w’rÀ¢fÆ÷s¢v÷WBrÀ¢¶–æC¢wW6RrÀ¢6FVv÷'“¢v‡VçF–ærrÀ¢FWF–Ã¢çVÆÂÀ¢Ö÷VçC¢À¢W‡V7FVEö—FVÕö–C¢çVÆÂÀ¢'VÆS¢w7FæF&Eö‡VçF–æuöVæW&w•ö6÷7Bp¢Ó° ¢FVfVÇC ¢&WGW&âçVÆÃ°¢Ð¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷t6æF–FFTf–VÆG2€¢FFÀ¢Æöt–BÒçVÆÀ¢’°¢–b€¢FFÇÀ¢G—VöbFFÓÒvö&¦V7BrÇÀ¢'&’æ—4'&’€¢FF¢¢’°¢&WGW&âµÓ°¢Ð ¢6öç7B¶æ÷väæöäfÆ÷tf–VÆG2Ð¢æWr6WB…°¢vÖ†–×VÕöVæW&w•ö&Vf÷&RrÀ¢vÖ†–×VÕöVæW&w•ögFW"rÀ¢vÖ†–×VÕöæW'fUö&Vf÷&RrÀ¢vÖ†–×VÕöæW'fUögFW"rÀ¢vÖ†–×VÕö†•ö&Vf÷&RrÀ¢vÖ†–×VÕö†•ögFW"p¢Ò“° ¢7v—F6‚€¢çVÖ&W"€¢Æöt–@¢¢’°¢66RS“ ¢66RS“S ¢66RS“ ¢66RS“#s ¢66RS“#ƒ ¢66RS“33 ¢66RS“3c ¢66RS“3ƒ ¢¶æ÷väæöäfÆ÷tf–VÆG2æFB€¢v†’p¢“°¢'&V³° ¢FVfVÇC ¢'&V³°¢Ð ¢&WGW&âö&¦V7Bæ¶W—2€¢FF¢’æf–ÇFW"€¢f–VÆBÓà¢ò…çÅò’†VæW&w—ÆæW'fWÆ†—Æ†–æW72’…÷ÂB’ö’çFW7B€¢f–VÆ@¢’b`¢¶æ÷väæöäfÆ÷tf–VÆG2æ†2€¢f–VÆ@¢¢’ç6÷'B‚“°¢Ð ¢gVæ7F–öâ–ç7V7D†–æW74Ö†–×VÔÆör€¢Æöp¢’°¢6öç7BÆöt–BÐ¢çVÖ&W"€¢ÆösòæÆöróð¢ÆösòæFWF–Ç3òæ–@¢“° ¢–b€¢Æöt–BÓÒƒƒC@¢’°¢&WGW&â°¢&V6övæ—¦VC¢fÇ6RÀ¢fÆ–C¢G'VRÀ¢&V6öã¢çVÆÂÀ¢WfVçC¢çVÆÀ¢Ó°¢Ð ¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢ÆösòçF–ÖW7F× ¢“° ¢–b€¢çVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F× ¢’ÇÀ¢F–ÖW7F×ÃÒ ¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–E÷F–ÖW7F×rÀ¢WfVçC¢çVÆÀ¢Ó°¢Ð ¢6öç7B&Vf÷&RÐ¢&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢ÆösòæFFòæÖ†–×VÕö†•ö&Vf÷&P¢“° ¢6öç7BgFW"Ð¢&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢ÆösòæFFòæÖ†–×VÕö†•ögFW ¢“° ¢–b€¢&Vf÷&RÓÓÒçVÆÂÇÀ¢gFW"ÓÓÒçVÆÂÇÀ¢gFW"Â&Vf÷&P¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–Eö†–æW75öÖ†–×VÕö6†ævRrÀ¢WfVçC¢çVÆÀ¢Ó°¢Ð ¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢fÆ–C¢G'VRÀ¢&V6öã¢çVÆÂÀ¢WfVçC¢°¢–C ¢7G&–ær€¢Æösòæ–Bóð¢rp¢’À¢Æöuö–C¢Æöt–BÀ¢F–ÖW7F×À¢&Vf÷&RÀ¢gFW"À¢&6—3¢vö'6W'fVEöW†7Bp¢Ð¢Ó°¢Ð ¢gVæ7F–öâ'V–ÆD†–æW74Ö†–×VÔ†—7F÷'’€¢Æöw0¢’°¢6öç7BWfVçG2Ð¢µÓ° ¢6öç7B&V¦V7F–öå&V6öç2Ð¢·Ó° ¢ÆWB&V6övæ—¦VDÆöw2Ò°¢ÆWBfÆ–DÆöw2Ò°¢ÆWB&V¦V7FVDÆöw2Ò° ¢f÷"€¢6öç7BÆöp¢öbÆöw2ÇÂµÐ¢’°¢6öç7B–ç7V7FVBÐ¢–ç7V7D†–æW74Ö†–×VÔÆör€¢Æöp¢“° ¢–b€¢–ç7V7FVBç&V6övæ—¦V@¢’°¢6öçF–çVS°¢Ð ¢&V6övæ—¦VDÆöw2²³° ¢–b€¢–ç7V7FVBçfÆ–@¢’°¢&V¦V7FVDÆöw2²³° ¢&V¦V7F–öå&V6öç5°¢–ç7V7FVBç&V6öà¢ÒÐ¢€¢&V¦V7F–öå&V6öç5°¢–ç7V7FVBç&V6öà¢ÒÇÀ¢ ¢’°¢° ¢6öçF–çVS°¢Ð ¢fÆ–DÆöw2²³°¢WfVçG2çW6‚€¢–ç7V7FVBæWfVç@¢“°¢Ð ¢WfVçG2ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBçF–ÖW7F×Ð¢&–v‡BçF–ÖW7F×ÇÀ¢ÆVgBæ–BæÆö6ÆT6ö×&R€¢&–v‡Bæ–@¢¢“° ¢ÆWB6öçF–çV—G”'&V·2Ò° ¢f÷"€¢ÆWB–æFW‚Ò°¢–æFW‚ÂWfVçG2æÆVæwFƒ°¢–æFW‚²°¢’°¢–b€¢WfVçG5¶–æFW‚ÒÒægFW"ÓÐ¢WfVçG5¶–æFW…Òæ&Vf÷&P¢’°¢6öçF–çV—G”'&V·2²³°¢Ð¢Ð ¢&WGW&â°¢WfVçG2À¢f—'7Eö¶æ÷våöÖ†–×VÓ ¢WfVçG2æÆVæwF€¢òWfVçG5³Òæ&Vf÷&P¢¢çVÆÂÀ¢ÆFW7Eö¶æ÷våöÖ†–×VÓ ¢WfVçG2æÆVæwF€¢òWfVçG5¶WfVçG2æÆVæwF‚ÒÒægFW ¢¢çVÆÂÀ¢VÆ—G“¢°¢&V6övæ—¦VEöÆöw3 ¢&V6övæ—¦VDÆöw2À¢fÆ–EöÆöw3 ¢fÆ–DÆöw2À¢&V¦V7FVEöÆöw3 ¢&V¦V7FVDÆöw2À¢6öçF–çV—G•ö'&V·3 ¢6öçF–çV—G”'&V·2À¢&V¦V7F–öå÷&V6öç3 ¢&V¦V7F–öå&V6öç0¢Ð¢Ó°¢Ð ¢gVæ7F–öâ†–æW74Ö†–×VÔB€¢†—7F÷'’À¢F–ÖW7F× ¢’°¢6öç7BF&vWBÐ¢çVÖ&W"€¢F–ÖW7F× ¢“° ¢6öç7BWfVçG2Ð¢†—7F÷'“òæWfVçG3° ¢–b€¢çVÖ&W"æ—56fT–çFVvW"€¢F&vW@¢’ÇÀ¢F&vWBÃÒÇÀ¢'&’æ—4'&’€¢WfVçG0¢’ÇÀ¢WfVçG2æÆVæwF‚ÇÀ¢çVÖ&W"€¢†—7F÷'“òçVÆ—G“òæ6öçF–çV—G•ö'&V·2ÇÀ¢ ¢’â ¢’°¢&WGW&âçVÆÃ°¢Ð ¢ÆWBÖ†–×VÒÐ¢WfVçG5³Òæ&Vf÷&S° ¢f÷"€¢6öç7BWfVç@¢öbWfVçG0¢’°¢–b€¢WfVçBçF–ÖW7F×âF&vW@¢’°¢'&V³°¢Ð ¢Ö†–×VÒÐ¢WfVçBægFW#°¢Ð ¢&WGW&âÖ†–×VÓ°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷tWfVçB€¢ÆörÀ¢7V2À¢Ö÷VçBÀ¢&6—0¢’°¢6öç7B—FVÔ–BÐ¢&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢ÆösòæFFòæ—FVÐ¢“° ¢&WGW&â°¢–C ¢7G&–ær€¢Æösòæ–Bóð¢rp¢’À¢Æöuö–C ¢çVÖ&W"€¢ÆösòæÆöp¢’À¢F—FÆS ¢7G&–ær€¢ÆösòçF—FÆRóð¢rp¢’À¢F–ÖW7F× ¢çVÖ&W"€¢ÆösòçF–ÖW7F× ¢’À¢&W6÷W&6S ¢7V2ç&W6÷W&6RÀ¢fÆ÷s ¢7V2æfÆ÷rÀ¢¶–æC ¢7V2æ¶–æBÀ¢6FVv÷'“ ¢7V2æ6FVv÷'’À¢FWF–Ã ¢7V2æFWF–Âóð¢çVÆÂÀ¢Ö÷VçBÀ¢&6—2À¢'VÆS ¢7V2ç'VÆRóð¢çVÆÂÀ¢—FVÕö–C ¢—FVÔ–@¢Ó°¢Ð ¢gVæ7F–öâ–ç7V7E&W6÷W&6TfÆ÷tÆör€¢Æöp¢’°¢6öç7BÆöt–BÐ¢çVÖ&W"€¢ÆösòæÆöróð¢ÆösòæFWF–Ç3òæ–@¢“° ¢6öç7Bö'6W'fVE7V72Ð¢&W6÷W&6TfÆ÷tö'6W'fVE7V72€¢Æöt–@¢“° ¢6öç7BFW&—fVE7V2Ð¢&W6÷W&6TfÆ÷tFW&—fVE7V2€¢Æöt–@¢“° ¢6öç7BFFÐ¢ÆösòæFF° ¢–b€¢ö'6W'fVE7V72æÆVæwF‚b`¢FW&—fVE7V0¢’°¢6öç7B6æF–FFTf–VÆG2Ð¢&W6÷W&6TfÆ÷t6æF–FFTf–VÆG2€¢FFÀ¢Æöt–@¢“° ¢&WGW&â°¢&V6övæ—¦VC¢fÇ6RÀ¢&W6÷W&6Uö6æF–FFS ¢6æF–FFTf–VÆG2æÆVæwF‚âÀ¢fÆ–C ¢6æF–FFTf–VÆG2æÆVæwF‚ÓÓÒÀ¢&V6öã ¢6æF–FFTf–VÆG2æÆVæwF€¢òwVç7W÷'FVE÷&W6÷W&6U÷66†VÖp¢¢çVÆÂÀ¢6æF–FFUöf–VÆG3 ¢6æF–FFTf–VÆG2À¢WfVçG3¢µÐ¢Ó°¢Ð ¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢ÆösòçF–ÖW7F× ¢“° ¢–b€¢çVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F× ¢’ÇÀ¢F–ÖW7F×ÃÒ ¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–E÷F–ÖW7F×rÀ¢6æF–FFUöf–VÆG3¢µÒÀ¢WfVçG3¢µÐ¢Ó°¢Ð ¢–b€¢FFÇÀ¢G—VöbFFÓÒvö&¦V7BrÇÀ¢'&’æ—4'&’€¢FF¢¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–EöFFrÀ¢6æF–FFUöf–VÆG3¢µÒÀ¢WfVçG3¢µÐ¢Ó°¢Ð ¢6öç7B6æF–FFTf–VÆG2Ð¢&W6÷W&6TfÆ÷t6æF–FFTf–VÆG2€¢FFÀ¢Æöt–@¢“° ¢6öç7BW‡V7FVDf–VÆG2Ð¢æWr6WB€¢ö'6W'fVE7V72æÖ€¢7V2Óà¢7V2æf–VÆ@¢¢“° ¢6öç7BVæW‡V7FVDf–VÆG2Ð¢6æF–FFTf–VÆG2æf–ÇFW"€¢f–VÆBÓà¢W‡V7FVDf–VÆG2æ†2€¢f–VÆ@¢¢“° ¢–b€¢VæW‡V7FVDf–VÆG2æÆVæwF€¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢wVæW‡V7FVE÷&W6÷W&6Uöf–VÆG2rÀ¢6æF–FFUöf–VÆG3 ¢VæW‡V7FVDf–VÆG2À¢WfVçG3¢µÐ¢Ó°¢Ð ¢6öç7BWfVçG2Ð¢µÓ° ¢f÷"€¢6öç7B7V0¢öbö'6W'fVE7V70¢’°¢6öç7BÖ÷VçBÐ¢7V2æÆÆ÷u÷¦W&ð¢ò&W6÷W&6TfÆ÷tæöäæVvF—fTÖ÷VçB€¢FF·7V2æf–VÆEÐ¢¢¢&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢FF·7V2æf–VÆEÐ¢“° ¢–b€¢Ö÷VçBÓÓÒçVÆÀ¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–E÷&W6÷W&6UöÖ÷VçBrÀ¢6æF–FFUöf–VÆG3¢°¢7V2æf–VÆ@¢ÒÀ¢WfVçG3¢µÐ¢Ó°¢Ð ¢–b€¢Ö÷VçBâ ¢’°¢WfVçG2çW6‚€¢&W6÷W&6TfÆ÷tWfVçB€¢ÆörÀ¢7V2À¢Ö÷VçBÀ¢vö'6W'fVEöW†7Bp¢¢“°¢Ð¢Ð ¢–b€¢FW&—fVE7V0¢’°¢–b€¢FW&—fVE7V2æW‡V7FVEö—FVÕö–BÓÒçVÆÂb`¢&W6÷W&6TfÆ÷u÷6—F—fTÖ÷VçB€¢FFæ—FVÐ¢’ÓÐ¢FW&—fVE7V2æW‡V7FVEö—FVÕö–@¢’°¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢fÇ6RÀ¢&V6öã¢v–çfÆ–EöFW&—fVE÷'VÆUö&–æF–ærrÀ¢6æF–FFUöf–VÆG3¢µÒÀ¢WfVçG3¢µÐ¢Ó°¢Ð ¢WfVçG2çW6‚€¢&W6÷W&6TfÆ÷tWfVçB€¢ÆörÀ¢FW&—fVE7V2À¢FW&—fVE7V2æÖ÷VçBÀ¢vFW&—fVE÷'VÆRp¢¢“°¢Ð ¢&WGW&â°¢&V6övæ—¦VC¢G'VRÀ¢&W6÷W&6Uö6æF–FFS¢G'VRÀ¢fÆ–C¢G'VRÀ¢&V6öã¢çVÆÂÀ¢6æF–FFUöf–VÆG3 ¢6æF–FFTf–VÆG2À¢WfVçG0¢Ó°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢&W6÷W&6P¢’°¢&WGW&â°¢&W6÷W&6RÀ¢–å÷F÷FÃ¢À¢÷WE÷F÷FÃ¢À¢v–å÷F÷FÃ¢À¢W6U÷F÷FÃ¢À¢Æ÷75÷F÷FÃ¢À¢ö'6W'fVEö–ã¢À¢ö'6W'fVEö÷WC¢À¢FW&—fVEö–ã¢À¢FW&—fVEö÷WC¢À¢WfVçEö6÷VçC¢À¢6FVv÷&–W3¢·Ð¢Ó°¢Ð ¢gVæ7F–öâ&W6÷W&6TfÆ÷tFDWfVçB€¢F&vWBÀ¢WfVç@¢’°¢F&vWBæWfVçEö6÷VçB²³° ¢–b€¢WfVçBæfÆ÷rÓÓÒv–âp¢’°¢F&vWBæ–å÷F÷FÂ³Ð¢WfVçBæÖ÷VçC° ¢–b€¢WfVçBæ&6—2ÓÓÒvö'6W'fVEöW†7Bp¢’°¢F&vWBæö'6W'fVEö–â³Ð¢WfVçBæÖ÷VçC°¢ÒVÇ6R°¢F&vWBæFW&—fVEö–â³Ð¢WfVçBæÖ÷VçC°¢Ð¢ÒVÇ6R°¢F&vWBæ÷WE÷F÷FÂ³Ð¢WfVçBæÖ÷VçC° ¢–b€¢WfVçBæ&6—2ÓÓÒvö'6W'fVEöW†7Bp¢’°¢F&vWBæö'6W'fVEö÷WB³Ð¢WfVçBæÖ÷VçC°¢ÒVÇ6R°¢F&vWBæFW&—fVEö÷WB³Ð¢WfVçBæÖ÷VçC°¢Ð¢Ð ¢–b€¢WfVçBæ¶–æBÓÓÒvv–âp¢’°¢F&vWBæv–å÷F÷FÂ³Ð¢WfVçBæÖ÷VçC°¢ÒVÇ6R–b€¢WfVçBæ¶–æBÓÓÒwW6Rp¢’°¢F&vWBçW6U÷F÷FÂ³Ð¢WfVçBæÖ÷VçC°¢ÒVÇ6R–b€¢WfVçBæ¶–æBÓÓÒvÆ÷72p¢’°¢F&vWBæÆ÷75÷F÷FÂ³Ð¢WfVçBæÖ÷VçC°¢Ð ¢6öç7B6FVv÷'’Ð¢F&vWBæ6FVv÷&–W5°¢WfVçBæ6FVv÷'¢ÒÇÂ°¢Ö÷VçC¢À¢WfVçG3¢ ¢Ó° ¢6FVv÷'’æÖ÷VçB³Ð¢WfVçBæÖ÷VçC°¢6FVv÷'’æWfVçG2²³° ¢F&vWBæ6FVv÷&–W5°¢WfVçBæ6FVv÷'¢ÒÐ¢6FVv÷'“°¢Ð ¢gVæ7F–öâ'V–ÆE&W6÷W&6TfÆ÷r€¢Æöw0¢’°¢6öç7BWfVçG2Ð¢µÓ° ¢6öç7BVæW&w’Ð¢&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢vVæW&w’p¢“° ¢6öç7BæW'fRÐ¢&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢væW'fRp¢“° ¢6öç7B†–æW72Ð¢&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢v†–æW72p¢“° ¢6öç7B†–æW74Ö†–×VÒÐ¢'V–ÆD†–æW74Ö†–×VÔ†—7F÷'’€¢Æöw0¢“° ¢6öç7BVç7W÷'FVDÆöt–G2Ð¢æWr6WB‚“° ¢6öç7B&V¦V7F–öå&V6öç2Ð¢·Ó° ¢ÆWB&V6övæ—¦VDÆöw2Ò°¢ÆWBfÆ–DÆöw2Ò°¢ÆWB&V¦V7FVDÆöw2Ò°¢ÆWBVç7W÷'FVD6æF–FFTÆöw2Ò°¢ÆWB–væ÷&VDÆöw2Ò°¢ÆWBö'6W'fVDW†7DWfVçG2Ò°¢ÆWBFW&—fVE'VÆTWfVçG2Ò° ¢f÷"€¢6öç7BÆöp¢öbÆöw2ÇÂµÐ¢’°¢6öç7B–ç7V7FVBÐ¢–ç7V7E&W6÷W&6TfÆ÷tÆör€¢Æöp¢“° ¢–b€¢–ç7V7FVBç&V6övæ—¦V@¢’°¢–b€¢–ç7V7FVBç&W6÷W&6Uö6æF–FFP¢’°¢Vç7W÷'FVD6æF–FFTÆöw2²³° ¢6öç7BÆöt–BÐ¢çVÖ&W"€¢ÆösòæÆöróð¢ÆösòæFWF–Ç3òæ–@¢“° ¢–b€¢çVÖ&W"æ—56fT–çFVvW"€¢Æöt–@¢¢’°¢Vç7W÷'FVDÆöt–G2æFB€¢Æöt–@¢“°¢Ð¢ÒVÇ6R°¢–væ÷&VDÆöw2²³°¢Ð ¢6öçF–çVS°¢Ð ¢&V6övæ—¦VDÆöw2²³° ¢–b€¢–ç7V7FVBçfÆ–@¢’°¢&V¦V7FVDÆöw2²³° ¢&V¦V7F–öå&V6öç5°¢–ç7V7FVBç&V6öà¢ÒÐ¢€¢&V¦V7F–öå&V6öç5°¢–ç7V7FVBç&V6öà¢ÒÇÀ¢ ¢’°¢° ¢6öçF–çVS°¢Ð ¢fÆ–DÆöw2²³° ¢f÷"€¢6öç7BWfVç@¢öb–ç7V7FVBæWfVçG0¢’°¢WfVçG2çW6‚€¢WfVç@¢“° ¢–b€¢WfVçBæ&6—2ÓÓÒvö'6W'fVEöW†7Bp¢’°¢ö'6W'fVDW†7DWfVçG2²³°¢ÒVÇ6R°¢FW&—fVE'VÆTWfVçG2²³°¢Ð ¢&W6÷W&6TfÆ÷tFDWfVçB€¢WfVçBç&W6÷W&6RÓÓÒvVæW&w’p¢òVæW&w¢¢WfVçBç&W6÷W&6RÓÓÒvæW'fRp¢òæW'fP¢¢†–æW72À¢WfVç@¢“°¢Ð¢Ð ¢WfVçG2ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBçF–ÖW7F×Ð¢&–v‡BçF–ÖW7F×ÇÀ¢ÆVgBæ–BæÆö6ÆT6ö×&R€¢&–v‡Bæ–@¢’ÇÀ¢ÆVgBç&W6÷W&6RæÆö6ÆT6ö×&R€¢&–v‡Bç&W6÷W&6P¢¢“° ¢&WGW&â°¢WfVçG2À¢VæW&w’À¢æW'fRÀ¢†–æW72À¢†–æW75öÖ†–×VÓ ¢†–æW74Ö†–×VÒÀ¢VÆ—G“¢°¢–çWEöÆöw3 ¢'&’æ—4'&’†Æöw2¢òÆöw2æÆVæwF€¢¢À¢&V6övæ—¦VEöÆöw3 ¢&V6övæ—¦VDÆöw2À¢fÆ–EöÆöw3 ¢fÆ–DÆöw2À¢&V¦V7FVEöÆöw3 ¢&V¦V7FVDÆöw2À¢–væ÷&VEöÆöw3 ¢–væ÷&VDÆöw2À¢ö'6W'fVEöW†7EöWfVçG3 ¢ö'6W'fVDW†7DWfVçG2À¢FW&—fVE÷'VÆUöWfVçG3 ¢FW&—fVE'VÆTWfVçG2À¢Vç7W÷'FVEö6æF–FFUöÆöw3 ¢Vç7W÷'FVD6æF–FFTÆöw2À¢Vç7W÷'FVEöÆöuö–G3 ¢²ââçVç7W÷'FVDÆöt–G5Òç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBÐ¢&–v‡@¢’À¢&V¦V7F–öå÷&V6öç3 ¢&V¦V7F–öå&V6öç0¢ÒÀ¢Æ–Ö—FF–öç3¢°¢æGW&Å÷&VvVæW&F–öã ¢væ÷Eöö'6W'f&ÆUög&öÕöÆöuö†—7F÷'’rÀ¢7W'&VçEö&%÷7FFS ¢væ÷E÷&V6öç7G'V7F&ÆUög&öÕöfÆ÷w5öÆöæRp¢Ð¢Ó°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òò$Tt”ääU"Ôd•%5BTäU$u’òäU%dRò„”äU52D4„$ô$@¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢ÆWB†–æW746GW&T6æ'•&öÖ—6RÐ¢çVÆÃ° ¢gVæ7F–öâW66U&W6÷W&6TF6†&ö&D‡FÖÂ€¢fÇVP¢’°¢&WGW&â7G&–ær€¢fÇVRóð¢rp¢¢ç&WÆ6R‚òbörÂrf×²r¢ç&WÆ6R‚óÂörÂrfÇC²r¢ç&WÆ6R‚óâörÂrfwC²r¢ç&WÆ6R‚ò"örÂrgV÷C²r¢ç&WÆ6R‚òrörÂrb33“²r“°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DæöäæVvF—fT–çFVvW"€¢fÇVP¢’°¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢fÇVP¢’b`¢fÇVRãÒ ¢òfÇVP¢¢çVÆÃ°¢Ð ¢gVæ7F–öâæ÷&ÖÆ—¦U&W6÷W&6TF6†&ö&D&"€¢&"À¢&W6÷W&6P¢’°¢–b€¢&"ÇÀ¢G—Vöb&"ÓÒvö&¦V7BrÇÀ¢'&’æ—4'&’†&"¢’°¢F‡&÷ræWrW'&÷"€¢F÷&â’&WGW&æVBâ–çfÆ–BG·&W6÷W&6WÒ&"æ ¢“°¢Ð ¢6öç7Bæ÷&ÖÆ—¦VBÐ¢·Ó° ¢f÷"€¢6öç7Bf–VÆ@¢öb°¢v7W'&VçBrÀ¢vÖ†–×VÒrÀ¢v–æ7&VÖVçBrÀ¢v–çFW'fÂrÀ¢wF–6µ÷F–ÖRrÀ¢vgVÆÅ÷F–ÖRp¢Ð¢’°¢6öç7BfÇVRÐ¢&W6÷W&6TF6†&ö&DæöäæVvF—fT–çFVvW"€¢&%¶f–VÆEÐ¢“° ¢–b€¢fÇVRÓÓÒçVÆÀ¢’°¢F‡&÷ræWrW'&÷"€¢F÷&â’&WGW&æVBâ–çfÆ–BG·&W6÷W&6WÒG¶f–VÆGÒfÇVRæ ¢“°¢Ð ¢æ÷&ÖÆ—¦VE¶f–VÆEÒÐ¢fÇVS°¢Ð ¢–b€¢æ÷&ÖÆ—¦VBæÖ†–×VÒÂ¢’°¢F‡&÷ræWrW'&÷"€¢F÷&â’&WGW&æVBâ–æ6öç6—7FVçBG·&W6÷W&6WÒ&"æ ¢“°¢Ð ¢&WGW&âæ÷&ÖÆ—¦VC°¢Ð ¢gVæ7F–öâæ÷&ÖÆ—¦U&W6÷W&6T&'5&W7öç6R€¢§6öâÀ¢fWF6†VDBÒFFRææ÷r‚¢’°¢6öç7B&'2Ð¢§6öãòæ&'3° ¢–b€¢&'2ÇÀ¢G—Vöb&'2ÓÒvö&¦V7BrÇÀ¢'&’æ—4'&’†&'2¢’°¢F‡&÷ræWrW'&÷"€¢uF÷&â’&WGW&æVBâ–çfÆ–B&'2&W7öç6Râp¢“°¢Ð ¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢fWF6†VD@¢“° ¢–b€¢çVÖ&W"æ—4f–æ—FR‡F–ÖW7F×’ÇÀ¢F–ÖW7F×ÃÒ ¢’°¢F‡&÷ræWrW'&÷"€¢tÆ—fR&W6÷W&6R&Vg&W6‚F–ÖR—2–çfÆ–Bâp¢“°¢Ð ¢&WGW&â°¢7FGW3¢vf–Æ&ÆRrÀ¢6÷W&6S¢wF÷&åö•÷c%÷W6W%ö&'2rÀ¢fWF6†VEöC¢F–ÖW7F×À¢VæW&w“ ¢æ÷&ÖÆ—¦U&W6÷W&6TF6†&ö&D&"€¢&'2æVæW&w’À¢tVæW&w’p¢’À¢æW'fS ¢æ÷&ÖÆ—¦U&W6÷W&6TF6†&ö&D&"€¢&'2ææW'fRÀ¢tæW'fRp¢’À¢†–æW73 ¢æ÷&ÖÆ—¦U&W6÷W&6TF6†&ö&D&"€¢&'2æ†’À¢t†–æW72p¢¢Ó°¢Ð ¢7–æ2gVæ7F–öâfWF6…&W6÷W&6T&'56æ6†÷B€¢”¶W’À¢G&6¶W ¢’°¢6öç7B§6öâÐ¢v—B”fWF6„§6öâ€¢G´•ô$4WÒ÷W6W"ö&'6À¢”¶W’À¢G&6¶W ¢“° ¢&WGW&âæ÷&ÖÆ—¦U&W6÷W&6T&'5&W7öç6R€¢§6öâÀ¢FFRææ÷r‚¢“°¢Ð ¢gVæ7F–öâ†–æW746GW&T6æ'”W'&÷%FW‡B€¢W'&÷"À¢”¶W’Òrp¢’°¢6öç7Bæ÷&ÖÆ—¦VD¶W’Ð¢7G&–ær€¢”¶W’ÇÀ¢rp¢’çG&–Ò‚“° ¢ÆWBÖW76vRÐ¢W'&÷"b`¢G—VöbW'&÷"ÓÓÒvö&¦V7Brb`¢G—VöbW'&÷"æÖW76vRÓÓÒw7G&–ærp¢òW'&÷"æÖW76vP¢¢7G&–ær€¢W'&÷"ÇÀ¢uF†R†–æW72’6†V6²f–ÆVBâp¢“° ¢–b€¢æ÷&ÖÆ—¦VD¶W¢’°¢ÖW76vRÐ¢ÖW76vP¢ç7Æ—B€¢æ÷&ÖÆ—¦VD¶W¢¢æ¦ö–â€¢u·&VF7FVEÒp¢“°¢Ð ¢&WGW&âÖW76vP¢ç&WÆ6R€¢õµÇ%ÆåÇEÒ²örÀ¢rp¢¢ç&WÆ6R€¢ô”¶W•Ç2µµåÇ3ÃâeÒ²öv’À¢t”¶W’·&VF7FVEÒp¢¢ç&WÆ6R€¢õÆ"†WF†÷&—¦F–öçÆ•µõÇ2ÕÓö¶W’•Ç2¥³£ÕÕÇ2¥µåÇ2ÃµÒ²öv’À¢rCÕ·&VF7FVEÒp¢¢çG&–Ò‚¢ç6Æ–6R€¢À¢# ¢’ÇÀ¢uF†R†–æW72’6†V6²f–ÆVB6fVÇ’âs°¢Ð ¢7–æ2gVæ7F–öâ'Vä†–æW746GW&T6æ'’€¢”¶W¢’°¢6öç7Bæ÷&ÖÆ—¦VD¶W’Ð¢7G&–ær€¢”¶W’ÇÀ¢rp¢’çG&–Ò‚“° ¢–b€¢æ÷&ÖÆ—¦VD¶W¢’°¢F‡&÷ræWrW'&÷"€¢u6fRF÷&â’¶W’–â6WGF–æw2f—'7Bâp¢“°¢Ð ¢–b€¢†–æW746GW&T6æ'•&öÖ—6P¢’°¢&WGW&âv—B†–æW746GW&T6æ'•&öÖ—6S°¢Ð ¢6öç7B÷W&F–öâÐ¢†7–æ2‚’Óâ°¢6öç7B&WVW7FVDBÐ¢FFRææ÷r‚“° ¢6öç7B§6öâÐ¢v—B”fWF6„§6öäöæ6R€¢G´•ô$4WÒ÷W6W"ö&'6À¢æ÷&ÖÆ—¦VD¶W’À¢çVÆÀ¢“° ¢6öç7B&V6V—fVDBÐ¢FFRææ÷r‚“° ¢6öç7B6æ6†÷BÐ¢æ÷&ÖÆ—¦U&W6÷W&6T&'5&W7öç6R€¢§6öâÀ¢&V6V—fVD@¢“° ¢&WGW&â°¢7FGW3¢vf–Æ&ÆRrÀ¢6÷W&6S¢töff–6–ÂF÷&â’c"÷W6W"ö&'2rÀ¢&WVW7FVEöC¢&WVW7FVDBÀ¢&V6V—fVEöC¢&V6V—fVDBÀ¢ÆFVæ7•ö×3 ¢ÖF‚æÖ‚€¢À¢&V6V—fVDBÐ¢&WVW7FVD@¢’À¢VæW&w“¢°¢7W'&VçC ¢6æ6†÷BæVæW&w’æ7W'&VçBÀ¢Ö†–×VÓ ¢6æ6†÷BæVæW&w’æÖ†–×VÐ¢ÒÀ¢†–æW73¢°¢7W'&VçC ¢6æ6†÷Bæ†–æW72æ7W'&VçBÀ¢Ö†–×VÓ ¢6æ6†÷Bæ†–æW72æÖ†–×VÐ¢Ð¢Ó°¢Ò’‚“° ¢†–æW746GW&T6æ'•&öÖ—6RÐ¢÷W&F–öã° ¢G'’°¢&WGW&âv—B÷W&F–öã°¢Òf–æÆÇ’°¢–b€¢†–æW746GW&T6æ'•&öÖ—6RÓÓÐ¢÷W&F–öà¢’°¢†–æW746GW&T6æ'•&öÖ—6RÐ¢çVÆÃ°¢Ð¢Ð¢Ð ¢7–æ2gVæ7F–öâÆöE&W6÷W&6T&'56æ6†÷B€¢”¶W’À¢G&6¶W ¢’°¢6öç7Bæ÷&ÖÆ—¦VD¶W’Ð¢7G&–ær€¢”¶W’ÇÀ¢rp¢’çG&–Ò‚“° ¢–b€¢æ÷&ÖÆ—¦VD¶W¢’°¢&WGW&â°¢7FGW3¢wVæf–Æ&ÆRrÀ¢&V6öã¢v•ö¶W•÷Væf–Æ&ÆRrÀ¢fWF6†VEöC¢çVÆÀ¢Ó°¢Ð ¢G&6¶W#òç6WE7FvR€¢u&Vg&W6†–ærVæW&w’ÂæW'fRÂæB†–æW7>(
brÀ¢töæRÆ—fRF÷&â’&WVW7Bp¢“° ¢G'’°¢&WGW&âv—BfWF6…&W6÷W&6T&'56æ6†÷B€¢æ÷&ÖÆ—¦VD¶W’À¢G&6¶W ¢“°¢Ò6F6‚€¢W'&÷ ¢’°¢6öç6öÆRçv&â€¢tÆ—fR&W6÷W&6R&Vg&W6‚f–ÆVBârÀ¢W'&÷ ¢“° ¢&WGW&â°¢7FGW3¢wVæf–Æ&ÆRrÀ¢&V6öã¢v•÷&WVW7Eöf–ÆVBrÀ¢ÖW76vS ¢7G&–ær€¢W'&÷#òæÖW76vRÇÀ¢tÆ—fRF÷&â’FF—2Væf–Æ&ÆRâp¢’À¢fWF6†VEöC¢çVÆÀ¢Ó°¢Ð¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"€¢fÇVP¢’°¢6öç7BçVÖ&W"Ð¢çVÖ&W"€¢fÇVP¢“° ¢&WGW&âçVÖ&W"æ—4f–æ—FR€¢çVÖ&W ¢¢òçVÖ&W"çFôÆö6ÆU7G&–ær‚¢¢~(	Bs°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&Df÷&ÖEW&6VçFvR€¢Ö÷VçBÀ¢F÷FÀ¢’°¢6öç7Bæ÷&ÖÆ—¦VDÖ÷VçBÐ¢çVÖ&W"€¢Ö÷Vç@¢“° ¢6öç7Bæ÷&ÖÆ—¦VEF÷FÂÐ¢çVÖ&W"€¢F÷FÀ¢“° ¢–b€¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VDÖ÷VçB’ÇÀ¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VEF÷FÂ’ÇÀ¢æ÷&ÖÆ—¦VDÖ÷VçBÂÇÀ¢æ÷&ÖÆ—¦VEF÷FÂÃÒ ¢’°¢&WGW&âsRs°¢Ð ¢6öç7BW&6VçFvRÐ¢ÖF‚æÖ‚€¢À¢ÖF‚æÖ–â€¢À¢€¢æ÷&ÖÆ—¦VDÖ÷VçBð¢æ÷&ÖÆ—¦VEF÷FÀ¢’ ¢ ¢¢“° ¢&WGW&â€¢çVÖ&W"€¢W&6VçFvRçFôf—†VB€¢¢¢’çFôÆö6ÆU7G&–ær‚’°¢rRp¢“°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&Df÷&ÖDGW&F–öâ€¢6V6öæG0¢’°¢6öç7B&VÖ–æ–ærÐ¢ÖF‚æÖ‚€¢À¢ÖF‚æ6V–Â€¢çVÖ&W"‡6V6öæG2’ÇÀ¢ ¢¢“° ¢–b€¢&VÖ–æ–ærÓÓÒ ¢’°¢&WGW&âtgVÆÂæ÷rs°¢Ð ¢6öç7B†÷W'2Ð¢ÖF‚æfÆö÷"€¢&VÖ–æ–ærð¢3c ¢“° ¢6öç7BÖ–çWFW2Ð¢ÖF‚æfÆö÷"€¢€¢&VÖ–æ–ærP¢3c ¢’ð¢c ¢“° ¢6öç7B6V6öæG5'BÐ¢&VÖ–æ–ærP¢c° ¢–b€¢†÷W'2â ¢’°¢&WGW&âG¶†÷W'7Ö‚G¶Ö–çWFW7ÖÖ°¢Ð ¢–b€¢Ö–çWFW2â ¢’°¢&WGW&âG¶Ö–çWFW7ÖÒG·6V6öæG5'G×6°¢Ð ¢&WGW&âG·6V6öæG5'G×6°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DgVÆÄ6Æö6µF–ÖR€¢gVÆÄ@¢’°¢6öç7BFFRÐ¢æWrFFR€¢çVÖ&W"†gVÆÄB¢“° ¢–b€¢çVÖ&W"æ—4f–æ—FR€¢FFRævWEF–ÖR‚¢¢’°¢&WGW&ârs°¢Ð ¢&WGW&âFFRçFôÆö6ÆUF–ÖU7G&–ær€¢VæFVf–æVBÀ¢°¢†÷W#¢vçVÖW&–2rÀ¢Ö–çWFS¢s"ÖF–v—Bp¢Ð¢“°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DWFFW‡B€¢gVÆÄBÀ¢æ÷rÒFFRææ÷r‚¢’°¢6öç7B&VÖ–æ–æu6V6öæG2Ð¢ÖF‚æÖ‚€¢À¢ÖF‚æ6V–Â€¢€¢çVÖ&W"†gVÆÄB’Ð¢çVÖ&W"†æ÷r¢’ð¢ ¢¢“° ¢–b€¢&VÖ–æ–æu6V6öæG2ÓÓÒ ¢’°¢&WGW&âtgVÆÂæ÷rs°¢Ð ¢&WGW&â€¢gVÆÂ–âG·&W6÷W&6TF6†&ö&Df÷&ÖDGW&F–öâ‡&VÖ–æ–æu6V6öæG2—Ö°¢+rG·&W6÷W&6TF6†&ö&DgVÆÄ6Æö6µF–ÖR†gVÆÄB—Ö ¢“°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DÆ—fU7FGW5FW‡B€¢7W'&VçBÀ¢Ö†–×VÒÀ¢gVÆÄBÀ¢æ÷rÒFFRææ÷r‚¢’°¢6öç7Bæ÷&ÖÆ—¦VD7W'&VçBÐ¢çVÖ&W"€¢7W'&Vç@¢“° ¢6öç7Bæ÷&ÖÆ—¦VDÖ†–×VÒÐ¢çVÖ&W"€¢Ö†–×VÐ¢“° ¢6öç7B÷fW$Ö†–×VÒÐ¢æ÷&ÖÆ—¦VD7W'&VçBÐ¢æ÷&ÖÆ—¦VDÖ†–×VÓ° ¢–b€¢çVÖ&W"æ—4f–æ—FR†÷fW$Ö†–×VÒ’b`¢÷fW$Ö†–×VÒâ ¢’°¢&WGW&â€¢t÷fW"Ö†–×VÒ'’r°¢&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"€¢÷fW$Ö†–×VÐ¢¢“°¢Ð ¢–b€¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VD7W'&VçB’b`¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VDÖ†–×VÒ’b`¢æ÷&ÖÆ—¦VD7W'&VçBãÒæ÷&ÖÆ—¦VDÖ†–×VÐ¢’°¢&WGW&âtgVÆÂæ÷rs°¢Ð ¢6öç7BWFFW‡BÐ¢&W6÷W&6TF6†&ö&DWFFW‡B€¢gVÆÄBÀ¢æ÷p¢“° ¢–b€¢WFFW‡BÓÓÒtgVÆÂæ÷rrb`¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VD7W'&VçB’b`¢çVÖ&W"æ—4f–æ—FR†æ÷&ÖÆ—¦VDÖ†–×VÒ’b`¢æ÷&ÖÆ—¦VD7W'&VçBÂæ÷&ÖÆ—¦VDÖ†–×VÐ¢’°¢&WGW&âtW‡V7FVBgVÆÂæ÷r+r&Vg&W6‚Fò6öæf—&Òs°¢Ð ¢&WGW&âWFFW‡C°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DVæW&w•7F6µ7FGW2€¢7W'&VçBÀ¢Ö†–×VÐ¢’°¢6öç7Bæ÷&ÖÆ—¦VD7W'&VçBÐ¢G—Vöb7W'&VçBÓÓÒvçVÖ&W"p¢ò7W'&Vç@¢¢çVÖ&W"äæã°¢6öç7Bæ÷&ÖÆ—¦VDÖ†–×VÒÐ¢G—VöbÖ†–×VÒÓÓÒvçVÖ&W"p¢òÖ†–×VÐ¢¢çVÖ&W"äæã° ¢–b€¢çVÖ&W"æ—4f–æ—FR€¢æ÷&ÖÆ—¦VD7W'&Vç@¢’ÇÀ¢çVÖ&W"æ—4f–æ—FR€¢æ÷&ÖÆ—¦VDÖ†–×VÐ¢’ÇÀ¢æ÷&ÖÆ—¦VD7W'&VçBÂÇÀ¢æ÷&ÖÆ—¦VDÖ†–×VÒÂ¢’°¢&WGW&â°¢7F—fS¢fÇ6RÀ¢Ö÷VçC¢çVÆÂÀ¢Æ&VÃ ¢tÆ—fRFFVæf–Æ&ÆRp¢Ó°¢Ð ¢6öç7BÖ÷VçBÐ¢æ÷&ÖÆ—¦VD7W'&VçBÐ¢æ÷&ÖÆ—¦VDÖ†–×VÓ° ¢–b€¢Ö÷VçBâ ¢’°¢&WGW&â°¢7F—fS¢G'VRÀ¢Ö÷VçBÀ¢Æ&VÃ ¢u7F6²7F—fR+r²r°¢&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"€¢Ö÷Vç@¢’°¢r&÷fRæGW&ÂÖ‚p¢Ó°¢Ð ¢&WGW&â°¢7F—fS¢fÇ6RÀ¢Ö÷VçC¢À¢Æ&VÃ¢tæ÷B7F6¶VBp¢Ó°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&E6÷W&6TÆ&VÂ€¢WfVç@¢’°¢6öç7BÆ&VÇ2Ò°¢ö–çE÷&Vf–ÆÃ¢uö–çB&Vf–ÆÂrÀ¢Ö—76–öå÷&Wv&C¢tÖ—76–öâ&Wv&BrÀ¢6öç7VÖ&ÆS¢t6öç7VÖ&ÆRrÀ¢G'Vs¢tG'VrrÀ¢&V†#¢u&V†"rÀ¢÷fW&F÷6S¢t÷fW&F÷6RrÀ¢GV×÷6V&6ƒ¢tGV×6V&6†–ærrÀ¢w–Õ÷G&–æ–æs¢tw–ÒG&–æ–ærrÀ¢'W7C¢t'W7G2rÀ¢GF6³¢tGF6·2rÀ¢7&–ÖS¢t7&–ÖW2rÀ¢‡VçF–æs¢t‡VçF–ærp¢Ó° ¢6öç7BFWF–ÄÆ&VÇ2Ò°¢†æƒ¢u†æ‚rÀ¢6ææ&—3¢t6ææ&—2rÀ¢Æ6ö†öÃ¢tÆ6ö†öÂrÀ¢6æG“¢t6æG’rÀ¢W&÷F–5öGfC¢tW&÷F–2EdBrÀ¢V77F7“¢tV77F7’rÀ¢f–6öF–ã¢uf–6öF–ârÀ¢ö–çG3¢uö–çB&Vf–ÆÂrÀ¢Ö—76–öã¢tÖ—76–öâ&Wv&Bp¢Ó° ¢–b€¢WfVçCòæ6FVv÷'’ÓÓÐ¢v÷fW&F÷6Rp¢’°¢6öç7B—FVÒÐ¢FWF–ÄÆ&VÇ5°¢WfVçCòæFWF–À¢Ó° ¢&WGW&â—FVÐ¢òG¶—FV×Ò÷fW&F÷6V ¢¢t÷fW&F÷6Rs°¢Ð ¢&WGW&âFWF–ÄÆ&VÇ5°¢WfVçCòæFWF–À¢ÒÇÀ¢Æ&VÇ5¶WfVçCòæ6FVv÷'•ÒÇÀ¢7G&–ær€¢WfVçCòæ6FVv÷'’ÇÀ¢t÷F†W"7F—f—G’p¢’ç&WÆ6R€¢õòörÀ¢rp¢“°¢Ð ¢gVæ7F–öâ&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢WfVçG2À¢&W6÷W&6RÀ¢fÆ÷rÀ¢¶–æBÒrp¢’°¢6öç7Bw&÷WVBÐ¢æWrÖ‚“° ¢f÷"€¢6öç7BWfVç@¢öbWfVçG2ÇÂµÐ¢’°¢–b€¢WfVçCòç&W6÷W&6RÓÒ&W6÷W&6RÇÀ¢WfVçCòæfÆ÷rÓÒfÆ÷rÇÀ¢€¢¶–æBb`¢WfVçCòæ¶–æBÓÒ¶–æ@¢¢’°¢6öçF–çVS°¢Ð ¢6öç7BÆ&VÂÐ¢&W6÷W&6TF6†&ö&E6÷W&6TÆ&VÂ€¢WfVç@¢“° ¢6öç7B7W'&VçBÐ¢w&÷WVBævWB€¢Æ&VÀ¢’ÇÂ°¢Æ&VÂÀ¢Ö÷VçC¢À¢WfVçG3¢ ¢Ó° ¢7W'&VçBæÖ÷VçB³Ð¢çVÖ&W"€¢WfVçBæÖ÷Vç@¢’ÇÀ¢° ¢7W'&VçBæWfVçG2²³° ¢w&÷WVBç6WB€¢Æ&VÂÀ¢7W'&Vç@¢“°¢Ð ¢&WGW&â²ââæw&÷WVBçfÇVW2‚•Ð¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢&–v‡BæÖ÷VçBÐ¢ÆVgBæÖ÷VçBÇÀ¢ÆVgBæÆ&VÂæÆö6ÆT6ö×&R€¢&–v‡BæÆ&VÀ¢¢“°¢Ð ¢  ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&DÆ—fT6&B€¢&W6÷W&6RÀ¢&"À¢fWF6†VD@¢’°¢6öç7BF—FÆRÐ¢&W6÷W&6RÓÓÒvVæW&w’p¢òtVæW&w’p¢¢&W6÷W&6RÓÓÒvæW'fRp¢òtæW'fRp¢¢t†–æW72s° ¢6öç7BW&6VçFvRÐ¢ÖF‚æÖ‚€¢À¢ÖF‚æÖ–â€¢À¢€¢&"æ7W'&VçBð¢&"æÖ†–×VÐ¢’ ¢ ¢¢“° ¢6öç7BgVÆÄBÐ¢çVÖ&W"†fWF6†VDB’°¢&"ægVÆÅ÷F–ÖR ¢° ¢6öç7B&FUFW‡BÐ¢&"æ–æ7&VÖVçBâb`¢&"æ–çFW'fÂâ ¢òr²r°¢&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"€¢&"æ–æ7&VÖVç@¢’°¢rWfW'’r°¢&W6÷W&6TF6†&ö&Df÷&ÖDGW&F–öâ€¢&"æ–çFW'fÀ¢¢¢tæòæGW&Â&Vf–ÆÂ&FR&W÷'FVBs° ¢6öç7B7FGW5FW‡BÐ¢&W6÷W&6TF6†&ö&DÆ—fU7FGW5FW‡B€¢&"æ7W'&VçBÀ¢&"æÖ†–×VÒÀ¢gVÆÄ@¢“° ¢6öç7B7F6µ7FGW2Ð¢&W6÷W&6RÓÓÒvVæW&w’p¢ò&W6÷W&6TF6†&ö&DVæW&w•7F6µ7FGW2€¢&"æ7W'&VçBÀ¢&"æÖ†–×VÐ¢¢¢çVÆÃ° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖÆ—fRÖ6&B#à¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖÆ—fR×F÷Æ–æR#à¢Ç7ãâG·F—FÆWÓÂ÷7ãà¢Æ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"†&"æ7W'&VçB—ÒòG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"†&"æÖ†–×VÒ—ÓÂö#à¢ÂöF—cà¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖÆ—fR×G&6²#à¢ÆF—b7G–ÆSÒ'v–GFƒ¢G·W&6VçFvRçFôf—†VBƒ"—ÒR#ãÂöF—cà¢ÂöF—cà¢G°¢7F6µ7FGW0¢ò ¢ÆF—b6Æ73Ò'F×&W6÷W&6R×7F6²×7FGW2G·7F6µ7FGW2æ7F—fRòv—2Ö7F—fRr¢rwÒ#à¢Ç7ãäVæW&w’7F6³Â÷7ãà¢Æ#âG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡7F6µ7FGW2æÆ&VÂ—ÓÂö#à¢ÂöF—cà¢ ¢¢rp¢Ð¢ÆF—`¢6Æ73Ò'F×&W6÷W&6RÖWF ¢FF×F×&W6÷W&6RÖgVÆÂÖCÒ"G¶gVÆÄGÒ ¢FF×F×&W6÷W&6RÖ7W'&VçCÒ"G¶&"æ7W'&VçGÒ ¢FF×F×&W6÷W&6RÖÖ†–×VÓÒ"G¶&"æÖ†–×V×Ò ¢à¢G¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡7FGW5FW‡B—Ð¢ÂöF—cà¢ÆF—b6Æ73Ò'F×&W6÷W&6R×&FR#à¢G·&FUFW‡GÒ+rÆ—fRg&öÒF÷&à¢ÂöF—cà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&D6ö×7D'&V¶F÷vâ€¢&÷w2À¢Æ&VÀ¢’°¢6öç7B÷6—F—fU&÷w2Ð¢€¢&÷w2ÇÀ¢µÐ¢’æf–ÇFW"€¢&÷rÓà¢çVÖ&W"€¢&÷sòæÖ÷VçBÇÀ¢ ¢’à¢ ¢“° ¢–b€¢÷6—F—fU&÷w2æÆVæwF€¢’°¢&WGW&â ¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖ6ö×7BÖfÆ÷r#à¢Æ#âG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ†Æ&VÂ—ÓÂö#à¢Ç7ãäæöæR&V6÷&FVCÂ÷7ãà¢ÂöF—cà¢°¢Ð ¢6öç7Bf—6–&ÆU&÷w2Ð¢÷6—F—fU&÷w2ç6Æ–6R€¢À¢0¢“°¢6öç7B†–FFVä6÷VçBÐ¢ÖF‚æÖ‚€¢À¢÷6—F—fU&÷w2æÆVæwF‚Ð¢f—6–&ÆU&÷w2æÆVæwF€¢“°¢6öç7BFW‡BÐ¢f—6–&ÆU&÷w0¢æÖ€¢&÷rÓà¢G¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡&÷ræÆ&VÂ—ÒG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡&÷ræÖ÷VçB—Ö ¢¢æ¦ö–â‚r+rr“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖ6ö×7BÖfÆ÷r#à¢Æ#âG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ†Æ&VÂ—ÓÂö#à¢Ç7ãâG·FW‡GÒG¶†–FFVä6÷VçBò+r²G¶†–FFVä6÷VçGÒÖ÷&V¢rwÓÂ÷7ãà¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&EæVÅ7VÖÖ'’€¢&W6÷W&6RÀ¢F—FÆRÀ¢7VÖÖ'’À¢&"À¢fWF6†VD@¢’°¢–b€¢& ¢’°¢&WGW&â ¢Ç7ãâG·F—FÆWÓÂ÷7ãà¢Ç7â6Æ73Ò'F×&W6÷W&6RÖ6ö×7B×7FGW2#à¢Æ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡7VÖÖ'’æv–å÷F÷FÂ—Òv–æVCÂö#à¢Ç6ÖÆÃäÆ—fRfÇVRVæf–Æ&ÆSÂ÷6ÖÆÃà¢Â÷7ãà¢°¢Ð ¢6öç7BgVÆÄBÐ¢çVÖ&W"€¢fWF6†VD@¢’°¢çVÖ&W"€¢&"ægVÆÅ÷F–ÖRÇÀ¢ ¢’ ¢°¢6öç7B7FGW5FW‡BÐ¢&W6÷W&6TF6†&ö&DÆ—fU7FGW5FW‡B€¢&"æ7W'&VçBÀ¢&"æÖ†–×VÒÀ¢gVÆÄ@¢“°¢6öç7B7F6²Ð¢&W6÷W&6RÓÓÐ¢vVæW&w’p¢ò&W6÷W&6TF6†&ö&DVæW&w•7F6µ7FGW2€¢&"æ7W'&VçBÀ¢&"æÖ†–×VÐ¢¢¢çVÆÃ° ¢&WGW&â ¢Ç7ãâG·F—FÆWÓÂ÷7ãà¢Ç7â6Æ73Ò'F×&W6÷W&6RÖ6ö×7B×7FGW2#à¢Æ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"†&"æ7W'&VçB—ÒòG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"†&"æÖ†–×VÒ—ÓÂö#à¢Ç6ÖÆÀ¢FF×F×&W6÷W&6RÖgVÆÂÖCÒ"G¶gVÆÄGÒ ¢FF×F×&W6÷W&6RÖ7W'&VçCÒ"G¶&"æ7W'&VçGÒ ¢FF×F×&W6÷W&6RÖÖ†–×VÓÒ"G¶&"æÖ†–×V×Ò ¢âG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡7FGW5FW‡B—ÓÂ÷6ÖÆÃà¢G·7F6³òæ7F—fRòÇ6ÖÆÂ6Æ73Ò&—2Ö7F—fR#å7F6¶VB²G·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡7F6²æÖ÷VçB—ÓÂ÷6ÖÆÃæ¢rwÐ¢Â÷7ãà¢°¢Ð ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&D†—7F÷'”6&B€¢fÆ÷rÀ¢&W6÷W&6P¢’°¢6öç7B7VÖÖ'’Ð¢fÆ÷sòå·&W6÷W&6UÒÇÀ¢&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢&W6÷W&6P¢“°¢6öç7B–æ6öÖ–ærÐ¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢fÆ÷sòæWfVçG2À¢&W6÷W&6RÀ¢v–ârÀ¢vv–âp¢“°¢6öç7B÷WFvö–ærÐ¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢fÆ÷sòæWfVçG2À¢&W6÷W&6RÀ¢v÷WBrÀ¢wW6Rp¢“°¢6öç7B6WF&6·2Ð¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢fÆ÷sòæWfVçG2À¢&W6÷W&6RÀ¢v÷WBrÀ¢vÆ÷72p¢“° ¢&WGW&â ¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖ†—7F÷'’Ö6&BF×&W6÷W&6RÖ6ö×7BÖ†—7F÷'’#à¢ÆF—b6Æ73Ò'F×&W6÷W&6RÖ6ö×7B×F÷FÇ2#à¢Ç7ããÇ6ÖÆÃäv–æVCÂ÷6ÖÆÃãÆ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡7VÖÖ'’æv–å÷F÷FÂ—ÓÂö#ãÂ÷7ãà¢Ç7ããÇ6ÖÆÃåW6VCÂ÷6ÖÆÃãÆ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡7VÖÖ'’çW6U÷F÷FÂ—ÓÂö#ãÂ÷7ãà¢Ç7ããÇ6ÖÆÃå6WF&6·3Â÷6ÖÆÃãÆ#âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡7VÖÖ'’æÆ÷75÷F÷FÂ—ÓÂö#ãÂ÷7ãà¢ÂöF—cà¢G·&VæFW%&W6÷W&6TF6†&ö&D6ö×7D'&V¶F÷vâ†–æ6öÖ–ærÂtg&öÒr—Ð¢G·&VæFW%&W6÷W&6TF6†&ö&D6ö×7D'&V¶F÷vâ†÷WFvö–ærÂuFòr—Ð¢G°¢çVÖ&W"‡7VÖÖ'’æÆ÷75÷F÷FÂ’â ¢ò&VæFW%&W6÷W&6TF6†&ö&D6ö×7D'&V¶F÷vâ‡6WF&6·2ÂtÆ÷7Br¢¢rp¢Ð¢ÂöF—cà¢°¢Ð ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&B€¢fÆ÷rÀ¢&'56æ6†÷BÀ¢÷F–öç2Ò·Ð¢’°¢–b€¢fÆ÷p¢’°¢&WGW&ârs°¢Ð ¢6öç7BF÷FÄWfVçG2Ð¢çVÖ&W"€¢fÆ÷sòæWfVçG3òæÆVæwF‚ÇÀ¢ ¢“°¢6öç7BÆ—fTf–Æ&ÆRÐ¢&'56æ6†÷Còç7FGW2ÓÓÐ¢vf–Æ&ÆRs°¢6öç7B7FFW2Ð¢÷F–öç2b`¢G—Vöb÷F–öç2ÓÓÐ¢vö&¦V7Bp¢ò÷F–öç0¢¢·Ó°¢6öç7BF6†&ö&D÷VâÐ¢7FFW2ç&W6÷W&6UöF6†&ö&Eö÷VâÓÓÐ¢G'VS°¢6öç7B&W6÷W&6UæVÂÐ¢&W6÷W&6RÓâ°¢6öç7B7VÖÖ'’Ð¢fÆ÷sòå·&W6÷W&6UÒÇÀ¢&W6÷W&6TfÆ÷t&Ææµ&W6÷W&6R€¢&W6÷W&6P¢“°¢6öç7B&"Ð¢Æ—fTf–Æ&ÆP¢ò&'56æ6†÷Còå·&W6÷W&6UÐ¢¢çVÆÃ°¢6öç7BF—FÆRÐ¢&W6÷W&6RÓÓÐ¢vVæW&w’p¢òtVæW&w’p¢¢&W6÷W&6RÓÓÐ¢væW'fRp¢òtæW'fRp¢¢t†–æW72s°¢6öç7B7FFT¶W’Ð¢&W6÷W&6UòG·&W6÷W&6WÕö÷Væ°¢6öç7B÷VâÐ¢7FFW5·7FFT¶W•ÒÓÓÐ¢G'VS° ¢&WGW&â ¢ÆFWF–Ç26Æ73Ò'F×&W6÷W&6R×æVÂ"FF×F×&W6÷W&6R×æVÃÒ"G·&W6÷W&6WÒ"G¶÷Vâòv÷Vâr¢rwÓà¢Ç7VÖÖ'“à¢G·&VæFW%&W6÷W&6TF6†&ö&EæVÅ7VÖÖ'’€¢&W6÷W&6RÀ¢F—FÆRÀ¢7VÖÖ'’À¢&"À¢&'56æ6†÷CòæfWF6†VEö@¢—Ð¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×&W6÷W&6R×æVÂÖ&öG’#à¢G·&VæFW%&W6÷W&6TF6†&ö&D†—7F÷'”6&B†fÆ÷rÂ&W6÷W&6R—Ð¢ÂöF—cà¢ÂöFWF–Ç3à¢°¢Ó° ¢&WGW&â ¢ÆFWF–Ç26Æ73Ò'F×6V7F–öâF×&W6÷W&6R×6V7F–öâ"G¶F6†&ö&D÷Vâòv÷Vâr¢rwÓà¢Ç7VÖÖ'’6Æ73Ò'F×6V7F–öâ×7VÖÖ'’×&÷r#à¢Ç7â6Æ73Ò'F×6V7F–öâ×F—FÆR#å&W6÷W&6W3Â÷7ãà¢Ç7â6Æ73Ò'F×6V7F–öâÖÖWF#à¢G·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡F÷FÄWfVçG2—ÒWfVçG0¢Â÷7ãà¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×6V7F–öâÖ&öG’F×&W6÷W&6RÖ6ö×7BÖ&öG’#à¢ÆF—b6Æ73Ò'F×&W6÷W&6R×æVÂÖÆ—7B#à¢G·&W6÷W&6UæVÂ‚vVæW&w’r—Ð¢G·&W6÷W&6UæVÂ‚væW'fRr—Ð¢G·&W6÷W&6UæVÂ‚v†–æW72r—Ð¢ÂöF—cà¢Ç6Æ73Ò'F×&W6÷W&6RÖ6ö×7BÖF—66Æ–ÖW"#à¢æGW&Â&VvVæW&F–öâ—2æ÷B–æ6ÇVFVB–â†—7F÷&–6Âv–ç2&V6W6RF÷&âFöW2æ÷BÆör—Bà¢Â÷à¢ÂöF—cà¢ÂöFWF–Ç3à¢°¢Ð ¢gVæ7F–öâvVV¶Ç”†–v†Æ–v‡G5&W6÷W&6TÖöFVÂ€¢fÆ÷rÀ¢7F—f—G’À¢F—2Òp¢’°¢6öç7BF•&÷w2Ð¢7F—f—G”F6†&ö&E&V6VçDF—2€¢7F—f—G’À¢F—0¢“°¢6öç7BF”¶W—2Ð¢æWr6WB€¢F•&÷w2æÖ€¢&÷rÓà¢&÷ræFFP¢¢“°¢6öç7BF–ÖT&6—2Ð¢æ÷&ÖÆ—¦T7F—f—G•F–ÖT&6—2€¢7F—f—G“òçF–ÖUö&6—0¢“°¢6öç7BWfVçG2Ð¢€¢fÆ÷sòæWfVçG2ÇÀ¢µÐ¢’æf–ÇFW"€¢WfVçBÓâ°¢6öç7BF–ÖW7F×Ð¢çVÖ&W"€¢WfVçCòçF–ÖW7F× ¢“° ¢&WGW&âçVÖ&W"æ—4f–æ—FR€¢F–ÖW7F× ¢’b`¢F–ÖW7F×âb`¢F”¶W—2æ†2€¢7F—f—G”FFT¶W”f÷$&6—2€¢æWrFFR€¢F–ÖW7F× ¢ ¢’À¢F–ÖT&6—0¢¢“°¢Ð¢“°¢6öç7B7F—f—G•7VÖÖ'’Ð¢7F—f—G”F6†&ö&D6ö×7DÖöFVÂ€¢7F—f—G’ÇÀ¢·Ð¢“°¢6öç7B7VÖÖ&—¦U&W6÷W&6RÐ¢&W6÷W&6RÓâ°¢6öç7B&W6÷W&6TWfVçG2Ð¢WfVçG2æf–ÇFW"€¢WfVçBÓà¢WfVçCòç&W6÷W&6RÓÓÐ¢&W6÷W&6P¢“°¢6öç7BF÷FÄf÷$¶–æBÐ¢¶–æBÓà¢&W6÷W&6TWfVçG2ç&VGV6R€¢€¢F÷FÂÀ¢WfVç@¢’Óà¢F÷FÂ°¢€¢WfVçCòæ¶–æBÓÓÐ¢¶–æ@¢òçVÖ&W"€¢WfVçCòæÖ÷VçBÇÀ¢ ¢¢¢ ¢’À¢ ¢“° ¢&WGW&â°¢v–æVC ¢F÷FÄf÷$¶–æB€¢vv–âp¢’À¢W6VC ¢F÷FÄf÷$¶–æB€¢wW6Rp¢’À¢6WF&6·3 ¢F÷FÄf÷$¶–æB€¢vÆ÷72p¢’À¢–æ6öÖ–æs ¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢&W6÷W&6TWfVçG2À¢&W6÷W&6RÀ¢v–ârÀ¢vv–âp¢’À¢÷WFvö–æs ¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢&W6÷W&6TWfVçG2À¢&W6÷W&6RÀ¢v÷WBrÀ¢wW6Rp¢’À¢Æ÷76W3 ¢&W6÷W&6TF6†&ö&D'&V¶F÷vâ€¢&W6÷W&6TWfVçG2À¢&W6÷W&6RÀ¢v÷WBrÀ¢vÆ÷72p¢¢Ó°¢Ó° ¢&WGW&â°¢F—3 ¢F•&÷w2æÆVæwF‚ÇÀ¢ÖF‚æÖ‚€¢À¢çVÖ&W"†F—2’ÇÀ¢p¢’À¢7F—f—G“ ¢7F—f—G•7VÖÖ'’À¢VæW&w“ ¢7VÖÖ&—¦U&W6÷W&6R€¢vVæW&w’p¢’À¢æW'fS ¢7VÖÖ&—¦U&W6÷W&6R€¢væW'fRp¢’À¢†–æW73 ¢7VÖÖ&—¦U&W6÷W&6R€¢v†–æW72p¢¢Ó°¢Ð ¢gVæ7F–öâvVV¶Ç”†–v†Æ–v‡G5&W6÷W&6U6VçFVæ6R€¢ÖöFVÀ¢’°¢6öç7B'G2Ò°¢¶ÖöFVÃòæVæW&w’ÂtVæW&w’uÒÀ¢¶ÖöFVÃòææW'fRÂtæW'fRuÒÀ¢¶ÖöFVÃòæ†–æW72Ât†–æW72uÐ¢Ð¢æÖ€¢…·&W6÷W&6RÂÆ&VÅÒ’Óâ°¢6öç7BW6VBÐ¢çVÖ&W"€¢&W6÷W&6SòçW6VBÇÀ¢ ¢“° ¢–b€¢W6VBÃÒ ¢’°¢&WGW&ârs°¢Ð ¢6öç7BFW7F–æF–öâÐ¢&W6÷W&6Sòæ÷WFvö–æsòå³Ð¢òæÆ&VÃ° ¢&WGW&âG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"‡W6VB—ÒG¶Æ&VÇÒG¶FW7F–æF–öâòÂÖ÷7FÇ’öâG¶FW7F–æF–öçÖ¢rwÖ°¢Ð¢¢æf–ÇFW"„&ööÆVâ“° ¢–b€¢'G2æÆVæwF€¢’°¢&WGW&âtæò&V6÷&FVB&W6÷W&6RW6Rv2f÷VæBf÷"F†—2vVV²âs°¢Ð ¢6öç7B¦ö–æVBÐ¢'G2æÆVæwF‚ÓÓÒ¢ò'G5³Ð¢¢'G2æÆVæwF‚ÓÓÒ ¢òG·'G5³×ÒæBG·'G5³×Ö ¢¢G·'G2ç6Æ–6RƒÂÓ’æ¦ö–â‚rÂr—ÒÂæBG·'G2æB‚Ó—Ö° ¢&WGW&â–÷RW6VBG¶¦ö–æVGÒæ°¢Ð ¢gVæ7F–öâvVV¶Ç”†–v†Æ–v‡G56WF&6µ6VçFVæ6R€¢ÖöFVÀ¢’°¢6öç7B&W6÷W&6W2Ò°¢°¢ÖöFVÃòæVæW&w’À¢tVæW&w’p¢ÒÀ¢°¢ÖöFVÃòææW'fRÀ¢tæW'fRp¢ÒÀ¢°¢ÖöFVÃòæ†–æW72À¢t†–æW72p¢Ð¢Ó°¢6öç7BÆ÷76W2Ð¢&W6÷W&6W0¢æf–ÇFW"€¢…·&W6÷W&6UÒ’Óà¢çVÖ&W"€¢&W6÷W&6Sòç6WF&6·2ÇÀ¢ ¢’â ¢¢æÖ€¢…°¢&W6÷W&6RÀ¢Æ&VÀ¢Ò’Óâ°¢6öç7BF÷Æ÷72Ð¢&W6÷W&6SòæÆ÷76W3òå³Ð¢ÇÂçVÆÃ°¢6öç7B6÷W&6RÐ¢F÷Æ÷73òæÆ&VÂÇÀ¢u6WF&6²s°¢6öç7BÖ÷VçBÐ¢çVÖ&W"€¢F÷Æ÷73òæÖ÷VçBÇÀ¢&W6÷W&6Rç6WF&6·0¢“°¢6öç7BWfVçD6÷VçBÐ¢çVÖ&W"€¢F÷Æ÷73òæWfVçG2ÇÀ¢ ¢“°¢6öç7B7V&¦V7BÐ¢WfVçD6÷VçBÓÓÒ¢òöæRG·6÷W&6RçFôÆö6ÆTÆ÷vW$66R‚—Ö ¢¢G·6÷W&6WÒ6WF&6·6° ¢&WGW&âG·7V&¦V7GÒ6÷7BG·&W6÷W&6TF6†&ö&Df÷&ÖDçVÖ&W"†Ö÷VçB—ÒG¶Æ&VÇÖ°¢Ð¢“° ¢&WGW&âÆ÷76W2æÆVæwF€¢òG¶Æ÷76W2æ¦ö–â‚ræBr—Òæ ¢¢rs°¢Ð ¢gVæ7F–öâ&VæFW%vVV¶Ç”†–v†Æ–v‡G2€¢fÆ÷rÀ¢7F—f—G¢’°¢–b€¢fÆ÷rb`¢7F—f—G¢’°¢&WGW&ârs°¢Ð ¢6öç7BÖöFVÂÐ¢vVV¶Ç”†–v†Æ–v‡G5&W6÷W&6TÖöFVÂ€¢fÆ÷rÀ¢7F—f—G’À¢p¢“°¢6öç7B7F—fTF—2Ð¢çVÖ&W"€¢ÖöFVÂæ7F—f—G“òæ7F—fUöF—2ÇÀ¢ ¢“°¢6öç7B7F—f—G•FW‡BÐ¢7F—fTF—2ÓÓÒÖöFVÂæF—0¢òu6öÆ–BvVV¾(	G–÷RvW&R7F—fRWfW'’F’âp¢¢7F—fTF—2â ¢ò–÷RvW&R7F—fRG¶7F—fTF—7ÒöbG¶ÖöFVÂæF—7ÒF—2F†—2vVV²æ ¢¢æò&V6÷&FVB7F—f—G’v2f÷VæBf÷"F†RÆ7BG¶ÖöFVÂæF—7ÒF—2æ°¢6öç7B6WF&6µFW‡BÐ¢vVV¶Ç”†–v†Æ–v‡G56WF&6µ6VçFVæ6R€¢ÖöFVÀ¢“° ¢&WGW&â ¢ÆFWF–Ç26Æ73Ò'F×6V7F–öâF×vVV¶Ç’Ö†–v†Æ–v‡G2×6V7F–öâ#à¢Ç7VÖÖ'’6Æ73Ò'F×6V7F–öâ×7VÖÖ'’×&÷r#à¢Ç7â6Æ73Ò'F×6V7F–öâ×F—FÆR#åvVV¶Ç’†–v†Æ–v‡G3Â÷7ãà¢Ç7â6Æ73Ò'F×6V7F–öâÖÖWF#à¢7BG¶ÖöFVÂæF—2çFôÆö6ÆU7G&–ær‚—ÒF—0¢Â÷7ãà¢Â÷7VÖÖ'“à ¢ÆF—b6Æ73Ò'F×6V7F–öâÖ&öG’F×vVV¶Ç’Ö†–v†Æ–v‡G2Ö&öG’#à¢Ç6V7F–öâ6Æ73Ò'F×vVV¶Ç’Ö†–v†Æ–v‡B×7VÖÖ'’#à¢ÇâG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ†7F—f—G•FW‡B—ÓÂ÷à¢ÇâG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡vVV¶Ç”†–v†Æ–v‡G5&W6÷W&6U6VçFVæ6R†ÖöFVÂ’—ÓÂ÷à¢G·6WF&6µFW‡BòÇ6Æ73Ò&—2Öæ÷F&ÆR#âG¶W66U&W6÷W&6TF6†&ö&D‡FÖÂ‡6WF&6µFW‡B—ÓÂ÷æ¢rwÐ¢Â÷6V7F–öãà ¢ÆFWF–Ç26Æ73Ò'F×7FB×7V'6V7F–öâF×vVV¶Ç’Ö†—7F÷'’ÖFWF–Ç2#à¢Ç7VÖÖ'“à¢ÆÂ×F–ÖR†—7F÷'¢Ç7ãå&V6÷&FVB&W6÷W&6RF÷FÇ3Â÷7ãà¢Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×7FB×7V'6V7F–öâÖ&öG’F×vVV¶Ç’Ö†—7F÷'’Ö&öG’#à¢Ç6V7F–öãà¢ÆƒCäVæW&w’†—7F÷'“ÂöƒCà¢G·&VæFW%&W6÷W&6TF6†&ö&D†—7F÷'”6&B†fÆ÷rÂvVæW&w’r—Ð¢Â÷6V7F–öãà¢Ç6V7F–öãà¢ÆƒCäæW'fR†—7F÷'“ÂöƒCà¢G·&VæFW%&W6÷W&6TF6†&ö&D†—7F÷'”6&B†fÆ÷rÂvæW'fRr—Ð¢Â÷6V7F–öãà¢Ç6V7F–öãà¢ÆƒCä†–æW72†—7F÷'“ÂöƒCà¢G·&VæFW%&W6÷W&6TF6†&ö&D†—7F÷'”6&B†fÆ÷rÂv†–æW72r—Ð¢Â÷6V7F–öãà¢Ç6Æ73Ò'F×&W6÷W&6RÖ6ö×7BÖF—66Æ–ÖW"#à¢&W6÷W&6R†—7F÷'’W6W2&V6÷&FVBWfVçG2âæGW&Â&VvVæW&F–öâ—2æ÷B–æ6ÇVFVB&V6W6RF÷&âFöW2æ÷BÆör—Bà¢Â÷à¢ÂöF—cà¢ÂöFWF–Ç3à¢ÂöF—cà¢ÂöFWF–Ç3à¢°¢Ð ¢gVæ7F–öâ&–æE&W6÷W&6TF6†&ö&D–çFW&7F–öç2€¢&ö÷@¢’°¢6öç7BW'6—7BÐ¢‚’Óâ°¢W'6—7E&W6÷W&6TF6†&ö&E7FFR€¢&ö÷@¢“°¢Ó°¢6öç7BF6†&ö&BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢rçF×&W6÷W&6R×6V7F–öâp¢“° ¢F6†&ö&CòæFDWfVçDÆ—7FVæW"€¢wFövvÆRrÀ¢W'6—7@¢“° ¢f÷"€¢6öç7BæVÀ¢öb&ö÷CòçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×&W6÷W&6R×æVÅÒp¢’ÇÂµÐ¢’°¢æVÂæFDWfVçDÆ—7FVæW"€¢wFövvÆRrÀ¢W'6—7@¢“°¢Ð ¢òòF÷&åDw2VÖ&VFFVBvV$¶—B6âÖ—72FWF–Ç2'FövvÆR"WfVçBgFW"¢òòF÷V6‚âFVfW'&VB7VÖÖ'’Ö6Æ–6²6GW&R&VG2F†Rf–æÂæF—fR7FFRà¢&ö÷CòæFDWfVçDÆ—7FVæW#òâ€¢v6Æ–6²rÀ¢WfVçBÓâ°¢6öç7B7VÖÖ'’Ð¢WfVçBçF&vWCòæ6Æ÷6W7Còâ€¢w7VÖÖ'’p¢“° ¢–b€¢7VÖÖ'“òç&VçDVÆVÖVçCòæÖF6†W3òâ€¢rçF×&W6÷W&6R×6V7F–öâÂ¶FF×F×&W6÷W&6R×æVÅÒp¢¢’°¢&WGW&ã°¢Ð ¢6WEF–ÖV÷WB€¢W'6—7BÀ¢ ¢“°¢Ð¢“° ¢6öç7B6÷VçFF÷vç2Ð¢&ö÷CòçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×&W6÷W&6RÖgVÆÂÖEÒp¢’ÇÀ¢µÓ° ¢–b€¢6÷VçFF÷vç2æÆVæwF€¢’°¢&WGW&ã°¢Ð ¢6öç7BWFFRÐ¢‚’Óâ°¢–b€¢&ö÷Bæ—46öææV7FV@¢’°¢&WGW&ã°¢Ð ¢ÆWB7F–ÆÄ6÷VçF–ærÐ¢fÇ6S° ¢f÷"€¢6öç7B÷WGW@¢öb6÷VçFF÷vç0¢’°¢6öç7BgVÆÄBÐ¢çVÖ&W"€¢÷WGWBævWDGG&–'WFR€¢vFF×F×&W6÷W&6RÖgVÆÂÖBp¢¢“° ¢6öç7B7W'&VçBÐ¢çVÖ&W"€¢÷WGWBævWDGG&–'WFR€¢vFF×F×&W6÷W&6RÖ7W'&VçBp¢¢“° ¢6öç7BÖ†–×VÒÐ¢çVÖ&W"€¢÷WGWBævWDGG&–'WFR€¢vFF×F×&W6÷W&6RÖÖ†–×VÒp¢¢“° ¢÷WGWBçFW‡D6öçFVçBÐ¢&W6÷W&6TF6†&ö&DÆ—fU7FGW5FW‡B€¢7W'&VçBÀ¢Ö†–×VÒÀ¢gVÆÄ@¢“° ¢–b€¢gVÆÄBà¢FFRææ÷r‚¢’°¢7F–ÆÄ6÷VçF–ærÐ¢G'VS°¢Ð¢Ð ¢–b€¢7F–ÆÄ6÷VçF–æp¢’°¢6WEF–ÖV÷WB€¢WFFRÀ¢ ¢“°¢Ð¢Ó° ¢WFFR‚“°¢Ð ¢gVæ7F–öâW'6—7E&W6÷W&6TF6†&ö&E7FFR€¢&ö÷@¢’°¢6öç7BF6†&ö&BÐ¢&ö÷CòçVW'•6VÆV7F÷#òâ€¢rçF×&W6÷W&6R×6V7F–öâp¢“° ¢–b‚F6†&ö&B’°¢&WGW&ã°¢Ð ¢6öç7BF6‚Ò°¢&W6÷W&6UöF6†&ö&Eö÷Vã ¢F6†&ö&Bæ÷VâÓÓÒG'VP¢Ó° ¢f÷"€¢6öç7BæVÀ¢öbF6†&ö&BçVW'•6VÆV7F÷$ÆÃòâ€¢u¶FF×F×&W6÷W&6R×æVÅÒp¢’ÇÂµÐ¢’°¢6öç7B&W6÷W&6RÐ¢æVÂævWDGG&–'WFR€¢vFF×F×&W6÷W&6R×æVÂp¢“° ¢–b€¢°¢vVæW&w’rÀ¢væW'fRrÀ¢v†–æW72p¢Òæ–æ6ÇVFW2‡&W6÷W&6R¢’°¢F6…¶&W6÷W&6UòG·&W6÷W&6WÕö÷VæÒÐ¢æVÂæ÷VâÓÓÒG'VS°¢Ð¢Ð ¢w&—FUV•6W76–öå7FFR‡F6‚“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòUDôÔD”2E$”ä”är4„T4µô”åB4ä%¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢6öç7BE$”ä”äuô4„T4µô”åEô4ä%•õ5Dõ$tUô´U’Ð¢wF÷&äæÇ—F–75G&–æ–æt6†V6·ö–çD6æ'•cs° ¢6öç7BE$”ä”äuô4„T4µô”åEõ44„TÔõdU%4”ôâÐ¢° ¢6öç7BE$”ä”äuô4„T4µô”åEõ$õUD”äUô”åDU%dÅôÕ2Ð¢3¢° ¢6öç7BE$”ä”äuô4„T4µô”åEõD”4µô”åDU%dÅôÕ2Ð¢R¢° ¢6öç7BE$”ä”äuô4„T4µô”åEõ$UõDôÔ…ôtUôÕ2Ð¢c¢° ¢6öç7BE$”ä”äuô4„T4µô”åEôÄ”Ô•BÐ¢#C° ¢6öç7BE$”ä”äuô4„T4µô”åEô”åDTåEôÄ”Ô•BÐ¢#C° ¢6öç7BE$”ä”äuô4„T4µô”åEô”åDTåEôÔ…ôtUôÕ2Ð¢3¢#B¢c¢c¢° ¢6öç7BE$”ä”äuô4„T4µô”åEô%U%5EôtôÕ2Ð¢R¢° ¢6öç7BE$”ä”äuô4„T4µô”åEôÄôuôÔD4…õDôÄU$ä4UôÕ2Ð¢R¢° ¢6öç7BE$”ä”äuô4„T4µô”åEô•õ4õU$4RÐ¢wF÷&åö•÷c%÷W6W%ö&'2s° ¢ÆWBG&–æ–æt6†V6·ö–çD6æ'”–ç7FÆÆVBÐ¢fÇ6S° ¢ÆWBG&–æ–æt6†V6·ö–çD6æ'•F–ÖW"Ð¢çVÆÃ° ¢ÆWBG&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡BÐ¢çVÆÃ° ¢ÆWBG&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢fÇ6S° ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•7F÷&vR‚’°¢G'’°¢&WGW&âÆö6Å7F÷&vS°¢Ò6F6‚…ò’°¢&WGW&âçVÆÃ°¢Ð¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢fÇVP¢’°¢–b€¢G—VöbfÇVRÓÐ¢vçVÖ&W"p¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7BçVÖ&W"Ð¢fÇVS° ¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢çVÖ&W ¢’b`¢çVÖ&W"ãÒ ¢òçVÖ&W ¢¢çVÆÃ°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T6†V6·ö–çB€¢6†V6·ö–ç@¢’°¢6öç7B&WVW7FVDBÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòç&WVW7FVEö@¢“° ¢6öç7B&V6V—fVDBÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòç&V6V—fVEö@¢“° ¢6öç7BVæW&w’Ð¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòæVæW&w“òæ7W'&Vç@¢“° ¢6öç7BVæW&w”Ö†–×VÒÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòæVæW&w“òæÖ†–×VÐ¢“° ¢6öç7B†–æW72Ð¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòæ†–æW73òæ7W'&Vç@¢“° ¢6öç7B†–æW74Ö†–×VÒÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢6†V6·ö–çCòæ†–æW73òæÖ†–×VÐ¢“° ¢–b€¢&WVW7FVDBÓÓÒçVÆÂÇÀ¢&WVW7FVDBÃÒÇÀ¢&V6V—fVDBÓÓÒçVÆÂÇÀ¢&V6V—fVDBÂ&WVW7FVDBÇÀ¢VæW&w’ÓÓÒçVÆÂÇÀ¢VæW&w”Ö†–×VÒÓÓÒçVÆÂÇÀ¢VæW&w”Ö†–×VÒÂÇÀ¢†–æW72ÓÓÒçVÆÂÇÀ¢†–æW74Ö†–×VÒÓÓÒçVÆÂÇÀ¢†–æW74Ö†–×VÒÂ¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B&V6öâÐ¢°¢v–æ—F–ÂrÀ¢w&÷WF–æRrÀ¢vw–ÕöVçG'’rÀ¢wf—6–&ÆRrÀ¢wvW6†÷rp¢Òæ–æ6ÇVFW2€¢6†V6·ö–çCòç&V6öà¢¢ò6†V6·ö–çBç&V6öà¢¢w&÷WF–æRs° ¢&WGW&â°¢–C ¢7G&–ær€¢6†V6·ö–çCòæ–BÇÀ¢G·&WVW7FVDGÒÒG·&V6V—fVDGÖ ¢¢ç6Æ–6R€¢À¢# ¢’À¢&V6öâÀ¢&WVW7FVEöC ¢&WVW7FVDBÀ¢&V6V—fVEöC ¢&V6V—fVDBÀ¢ÆFVæ7•ö×3 ¢ÖF‚æÖ‚€¢À¢&V6V—fVDBÐ¢&WVW7FVD@¢’À¢6÷W&6S ¢töff–6–ÂF÷&â’c"÷W6W"ö&'2rÀ¢vS ¢7G&–ær€¢6†V6·ö–çCòçvRÇÀ¢ròp¢¢ç6Æ–6R€¢À¢c ¢’À¢vUö—5öw–Ó ¢6†V6·ö–çCòçvUö—5öw–ÒÓÓÐ¢G'VRÀ¢VæW&w“¢°¢7W'&VçC ¢VæW&w’À¢Ö†–×VÓ ¢VæW&w”Ö†–×VÐ¢ÒÀ¢†–æW73¢°¢7W'&VçC ¢†–æW72À¢Ö†–×VÓ ¢†–æW74Ö†–×VÐ¢Ð¢Ó°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T–çFVçB€¢–çFVç@¢’°¢6öç7BFVDBÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢–çFVçCòçFVEö@¢“° ¢–b€¢FVDBÓÓÒçVÆÂÇÀ¢FVDBÃÒ ¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B6†V6·ö–çBÐ¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T6†V6·ö–çB€¢–çFVçCòæ6†V6·ö–ç@¢“° ¢6öç7B6ö×ÆWFVD&Vf÷&UFÐ¢&ööÆVâ€¢6†V6·ö–çBb`¢6†V6·ö–çBç&V6V—fVEöBÃÐ¢FVDBb`¢FVDBÐ¢6†V6·ö–çBç&V6V—fVEöBÃÐ¢E$”ä”äuô4„T4µô”åEõ$UõDôÔ…ôtUôÕ0¢“° ¢&WGW&â°¢–C ¢7G&–ær€¢–çFVçCòæ–BÇÀ¢FVD@¢¢ç6Æ–6R€¢À¢# ¢’À¢FVEöC ¢FVDBÀ¢7FC ¢°¢w7G&VæwF‚rÀ¢vFVfVç6RrÀ¢w7VVBrÀ¢vFW‡FW&—G’p¢Òæ–æ6ÇVFW2€¢–çFVçCòç7F@¢¢ò–çFVçBç7F@¢¢çVÆÂÀ¢G&–ç3 ¢G&–æ–æu6æ6†÷E÷6—F—fT–çFVvW"€¢–çFVçCòçG&–ç0¢’À¢w–Ó ¢G&–æ–æu6æ6†÷E÷6—F—fT–çFVvW"€¢–çFVçCòæw–Ð¢’À¢6†V6·ö–çE÷7FGW3 ¢6ö×ÆWFVD&Vf÷&UF ¢òv6ö×ÆWFVEö&Vf÷&U÷Fp¢¢wVæf–Æ&ÆRrÀ¢6†V6·ö–çEövUö×3 ¢6ö×ÆWFVD&Vf÷&UF ¢òFVDBÐ¢6†V6·ö–çBç&V6V—fVEö@¢¢çVÆÂÀ¢6†V6·ö–çC ¢6ö×ÆWFVD&Vf÷&UF ¢ò6†V6·ö–ç@¢¢çVÆÀ¢Ó°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢7FFRÀ¢æ÷tÖ–ÆÆ—6V6öæG2Ð¢FFRææ÷r‚¢’°¢6öç7B7WÆ–VE66†VÖfW'6–öâÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢7FFSòç7F÷&vU÷66†VÖ÷fW'6–öâóð¢7FFSòç66†VÖ÷fW'6–öà¢“° ¢6öç7B7F÷&vT6ö×F–&ÆRÐ¢7FFSòç7F÷&vUö6ö×F–&ÆRÓÐ¢fÇ6Rb`¢€¢7FFRÇÀ¢€¢7WÆ–VE66†VÖfW'6–öâÓÓÐ¢çVÆÂÇÀ¢7WÆ–VE66†VÖfW'6–öâÓÓÐ¢E$”ä”äuô4„T4µô”åEõ44„TÔõdU%4”ôà¢¢“° ¢6öç7BÖ–æ–×VÔ–çFVçEF–ÖRÐ¢ÖF‚æÖ‚€¢À¢çVÖ&W"€¢æ÷tÖ–ÆÆ—6V6öæG0¢’Ð¢E$”ä”äuô4„T4µô”åEô”åDTåEôÔ…ôtUôÕ0¢“° ¢6öç7B6†V6·ö–çG2Ð¢€¢7F÷&vT6ö×F–&ÆRb`¢'&’æ—4'&’€¢7FFSòæ6†V6·ö–çG0¢¢ò7FFRæ6†V6·ö–çG0¢¢µÐ¢¢æÖ€¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T6†V6·ö–ç@¢¢æf–ÇFW"€¢&ööÆVà¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBç&V6V—fVEöBÐ¢&–v‡Bç&V6V—fVEö@¢¢ç6Æ–6R€¢ÕE$”ä”äuô4„T4µô”åEôÄ”Ô•@¢“° ¢6öç7B–çFVçG2Ð¢€¢7F÷&vT6ö×F–&ÆRb`¢'&’æ—4'&’€¢7FFSòçG&–åö–çFVçG0¢¢ò7FFRçG&–åö–çFVçG0¢¢µÐ¢¢æÖ€¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T–çFVç@¢¢æf–ÇFW"€¢–çFVçBÓà¢–çFVçBb`¢–çFVçBçFVEöBãÐ¢Ö–æ–×VÔ–çFVçEF–ÖP¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBçFVEöBÐ¢&–v‡BçFVEö@¢¢ç6Æ–6R€¢ÕE$”ä”äuô4„T4µô”åEô”åDTåEôÄ”Ô•@¢“° ¢&WGW&â°¢66†VÖ÷fW'6–öã ¢E$”ä”äuô4„T4µô”åEõ44„TÔõdU%4”ôâÀ¢7F÷&vUö6ö×F–&ÆS ¢7F÷&vT6ö×F–&ÆRÀ¢7F÷&vU÷66†VÖ÷fW'6–öã ¢7WÆ–VE66†VÖfW'6–öâÀ¢fW'6–öã ¢dU%4”ôâÀ¢–ç7FÆÆVEöC ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢7FFSòæ–ç7FÆÆVEö@¢’ÇÀ¢çVÖ&W"€¢æ÷tÖ–ÆÆ—6V6öæG0¢’À¢Æ7EöGFV×EöC ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢7FFSòæÆ7EöGFV×Eö@¢’À¢Æ7E÷7FGW3 ¢7F÷&vT6ö×F–&ÆP¢òwVç7W÷'FVE÷66†VÖp¢¢°¢v–FÆRrÀ¢w&WVW7F–ærrÀ¢vf–Æ&ÆRrÀ¢væõö•ö¶W’rÀ¢vf–ÆVBp¢Òæ–æ6ÇVFW2€¢7FFSòæÆ7E÷7FGW0¢¢ò7FFRæÆ7E÷7FGW0¢¢v–FÆRrÀ¢Æ7EöW'&÷# ¢7F÷&vT6ö×F–&ÆP¢òu7F÷&VB6†V6·ö–çBWf–FVæ6RW6W2æWvW"Vç7W÷'FVB66†VÖâp¢¢G—Vöb7FFSòæÆ7EöW'&÷"ÓÓÐ¢w7G&–ærp¢ò†–æW746GW&T6æ'”W'&÷%FW‡B€¢7FFRæÆ7EöW'&÷ ¢¢¢çVÆÂÀ¢6†V6·ö–çG2À¢G&–åö–çFVçG3 ¢–çFVçG0¢Ó°¢Ð ¢gVæ7F–öâ&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚’°¢G'’°¢&WGW&âG&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢¥4ôâç'6R€¢G&–æ–æt6†V6·ö–çD6æ'•7F÷&vR‚“òævWD—FVÒ€¢E$”ä”äuô4„T4µô”åEô4ä%•õ5Dõ$tUô´U¢’ÇÀ¢vçVÆÂp¢¢“°¢Ò6F6‚…ò’°¢&WGW&âG&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢çVÆÀ¢“°¢Ð¢Ð ¢gVæ7F–öâw&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR€¢7FFP¢’°¢6öç7B6fRÐ¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢7FFP¢“° ¢–b€¢6fRç7F÷&vUö6ö×F–&ÆRÓÓÐ¢fÇ6P¢’°¢&WGW&â6fS°¢Ð ¢6öç7BW'6—7FVBÒ°¢ââç6fP¢Ó° ¢FVÆWFRW'6—7FVBç7F÷&vUö6ö×F–&ÆS°¢FVÆWFRW'6—7FVBç7F÷&vU÷66†VÖ÷fW'6–öã° ¢G'’°¢G&–æ–æt6†V6·ö–çD6æ'•7F÷&vR‚“òç6WD—FVÒ€¢E$”ä”äuô4„T4µô”åEô4ä%•õ5Dõ$tUô´U’À¢¥4ôâç7G&–æv–g’€¢W'6—7FV@¢¢“°¢Ò6F6‚…ò’°¢òò6æ'’Wf–FVæ6R—2÷F–öæÂæB×W7BæWfW"–çFW''WBF÷&âà¢Ð ¢&WGW&â6fS°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•vR€¢Æö6F–öåfÇVRÐ¢G—VöbÆö6F–öâÓÒwVæFVf–æVBp¢òÆö6F–öà¢¢çVÆÀ¢’°¢&WGW&â7G&–ær€¢Æö6F–öåfÇVSòçF†æÖRÇÀ¢ròp¢¢ç6Æ–6R€¢À¢c ¢“°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”Fö7VÖVçD7F—fR€¢Fö7VÖVçEfÇVRÐ¢G—VöbFö7VÖVçBÓÒwVæFVf–æVBp¢òFö7VÖVç@¢¢çVÆÀ¢’°¢&WGW&â&ööÆVâ€¢Fö7VÖVçEfÇVRb`¢Fö7VÖVçEfÇVRçf—6–&–Æ—G•7FFRÓÐ¢v†–FFVâp¢“°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”ÆFW7D&Vf÷&UF€¢6†V6·ö–çG2À¢FVD@¢’°¢6öç7B6fUFÐ¢G&–æ–æt6†V6·ö–çD6æ'”–çFVvW"€¢FVD@¢“° ¢–b€¢6fUFÓÓÒçVÆÂÇÀ¢6fUFÃÒ ¢’°¢&WGW&âçVÆÃ°¢Ð ¢&WGW&â€¢€¢'&’æ—4'&’€¢6†V6·ö–çG0¢¢ò6†V6·ö–çG0¢¢µÐ¢¢æÖ€¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T6†V6·ö–ç@¢¢æf–ÇFW"€¢6†V6·ö–çBÓà¢6†V6·ö–çBb`¢6†V6·ö–çBç&V6V—fVEöBÃÐ¢6fUFb`¢6fUFÐ¢6†V6·ö–çBç&V6V—fVEöBÃÐ¢E$”ä”äuô4„T4µô”åEõ$UõDôÔ…ôtUôÕ0¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢&–v‡Bç&V6V—fVEöBÐ¢ÆVgBç&V6V—fVEö@¢•³ÒÇÀ¢çVÆÀ¢“°¢Ð ¢7–æ2gVæ7F–öâ6GW&UG&–æ–æt6†V6·ö–çD6æ'’€¢&V6öâÒw&÷WF–æRrÀ¢f÷&6RÒfÇ6P¢’°¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”Fö7VÖVçD7F—fR‚¢’°¢&WGW&â°¢7FGW3 ¢v–æ7F—fRp¢Ó°¢Ð ¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡@¢’°¢&WGW&âv—BG&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡C°¢Ð ¢6öç7B÷W&F–öâÐ¢†7–æ2‚’Óâ°¢ÆWB7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢–b€¢7FFRç7F÷&vUö6ö×F–&ÆRÓÓÐ¢fÇ6P¢’°¢&WGW&â°¢7FGW3 ¢wVç7W÷'FVE÷66†VÖp¢Ó°¢Ð ¢6öç7B7F'FVDBÐ¢FFRææ÷r‚“° ¢–b€¢f÷&6Rb`¢7FFRæÆ7EöGFV×EöBÓÐ¢çVÆÂb`¢7F'FVDBÐ¢7FFRæÆ7EöGFV×EöBÀ¢E$”ä”äuô4„T4µô”åEõ$õUD”äUô”åDU%dÅôÕ0¢’°¢&WGW&â°¢7FGW3 ¢wF‡&÷GFÆVBp¢Ó°¢Ð ¢–b€¢'Vææ–ærÇÀ¢WFöÖF–4Æöu7–æ5'Vææ–æp¢’°¢&WGW&â°¢7FGW3 ¢v'W7’p¢Ó°¢Ð ¢7FFRÐ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââç7FFRÀ¢Æ7EöGFV×EöC ¢7F'FVDBÀ¢Æ7E÷7FGW3 ¢w&WVW7F–ærrÀ¢Æ7EöW'&÷# ¢çVÆÀ¢Ò“° ¢6öç7B”¶W’Ð¢v—BÆöE6V7W&T”¶W’‚“° ¢–b€¢”¶W¢’°¢6öç7B7W'&VçE7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââæ7W'&VçE7FFRÀ¢Æ7E÷7FGW3 ¢væõö•ö¶W’p¢Ò“° ¢&WGW&â°¢7FGW3 ¢væõö•ö¶W’p¢Ó°¢Ð ¢6öç7BvRÐ¢G&–æ–æt6†V6·ö–çD6æ'•vR‚“° ¢6öç7BvT—4w–ÒÐ¢G&–æ–æu6æ6†÷D—4w–ÕvR‚“° ¢G'’°¢6öç7B&W7VÇBÐ¢v—B'Vä†–æW746GW&T6æ'’€¢”¶W¢“° ¢6öç7B6†V6·ö–çBÐ¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T6†V6·ö–çB‡°¢–C ¢G·&W7VÇBç&WVW7FVEöGÒÒG·&W7VÇBç&V6V—fVEöGÒÒG·&V6öçÖÀ¢&V6öâÀ¢&WVW7FVEöC ¢&W7VÇBç&WVW7FVEöBÀ¢&V6V—fVEöC ¢&W7VÇBç&V6V—fVEöBÀ¢6÷W&6S ¢&W7VÇBç6÷W&6RÀ¢vRÀ¢vUö—5öw–Ó ¢vT—4w–ÒÀ¢VæW&w“ ¢&W7VÇBæVæW&w’À¢†–æW73 ¢&W7VÇBæ†–æW70¢Ò“° ¢–b€¢6†V6·ö–ç@¢’°¢F‡&÷ræWrW'&÷"€¢uF†RWFöÖF–26†V6·ö–çB&W7öç6Rv2–çfÆ–Bâp¢“°¢Ð ¢6öç7B7W'&VçE7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢6öç7BGWÆ–6FRÐ¢7W'&VçE7FFRæ6†V6·ö–çG0¢ç6öÖR€¢W†—7F–ærÓà¢W†—7F–æræ–BÓÓÐ¢6†V6·ö–çBæ–@¢“° ¢6öç7B6†V6·ö–çG2Ð¢GWÆ–6FP¢ò7W'&VçE7FFRæ6†V6·ö–çG0¢¢°¢ââæ7W'&VçE7FFRæ6†V6·ö–çG2À¢6†V6·ö–ç@¢Ó° ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââæ7W'&VçE7FFRÀ¢Æ7E÷7FGW3 ¢vf–Æ&ÆRrÀ¢Æ7EöW'&÷# ¢çVÆÂÀ¢6†V6·ö–çG0¢Ò“° ¢&WGW&â°¢7FGW3 ¢vf–Æ&ÆRrÀ¢6†V6·ö–ç@¢Ó°¢Ò6F6‚€¢W'&÷ ¢’°¢6öç7B6fTW'&÷"Ð¢†–æW746GW&T6æ'”W'&÷%FW‡B€¢W'&÷"À¢”¶W¢“° ¢6öç7B7W'&VçE7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââæ7W'&VçE7FFRÀ¢Æ7E÷7FGW3 ¢vf–ÆVBrÀ¢Æ7EöW'&÷# ¢6fTW'&÷ ¢Ò“° ¢&WGW&â°¢7FGW3 ¢vf–ÆVBrÀ¢&V6öã ¢6fTW'&÷ ¢Ó°¢Ð¢Ò’‚“° ¢G&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡BÐ¢÷W&F–öã° ¢G'’°¢&WGW&âv—B÷W&F–öã°¢Òf–æÆÇ’°¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡BÓÓÐ¢÷W&F–öà¢’°¢G&–æ–æt6†V6·ö–çD6æ'”–äfÆ–v‡BÐ¢çVÆÃ°¢Ð¢Ð¢Ð ¢gVæ7F–öâ&V6÷&EG&–æ–æt6†V6·ö–çD6æ'”–çFVçB€¢WfVçBÀ¢æ÷tÖ–ÆÆ—6V6öæG2Ð¢FFRææ÷r‚¢’°¢–b€¢G&–æ–æu6æ6†÷D—4w–ÕvR‚¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B–çFVçBÐ¢G&–æ–æu6æ6†÷EG&–æ–æt–çFVçB€¢WfVçCòçF&vW@¢“° ¢–b€¢–çFVç@¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢–b€¢7FFRç7F÷&vUö6ö×F–&ÆRÓÓÐ¢fÇ6P¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B6†V6·ö–çBÐ¢G&–æ–æt6†V6·ö–çD6æ'”ÆFW7D&Vf÷&UF€¢7FFRæ6†V6·ö–çG2À¢æ÷tÖ–ÆÆ—6V6öæG0¢“° ¢6öç7B&V6÷&BÐ¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦T–çFVçB‡°¢–C ¢G¶æ÷tÖ–ÆÆ—6V6öæG7ÒÒG¶–çFVçBç7FGÒÒGµ7G&–ær„ÖF‚ç&æFöÒ‚’’ç6Æ–6Rƒ"Â—ÖÀ¢FVEöC ¢æ÷tÖ–ÆÆ—6V6öæG2À¢7FC ¢–çFVçBç7FBÀ¢G&–ç3 ¢–çFVçBçG&–ç2À¢w–Ó ¢–çFVçBæw–ÒÀ¢6†V6·ö–ç@¢Ò“° ¢–b€¢&V6÷&@¢’°¢&WGW&âçVÆÃ°¢Ð ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââç7FFRÀ¢G&–åö–çFVçG3¢°¢ââç7FFRçG&–åö–çFVçG2À¢&V6÷&@¢Ð¢Ò“° ¢&WGW&â&V6÷&C°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”f÷&ÖDvR€¢Ö–ÆÆ—6V6öæG0¢’°¢6öç7B6fRÐ¢ÖF‚æÖ‚€¢À¢çVÖ&W"€¢Ö–ÆÆ—6V6öæG0¢’ÇÀ¢ ¢“° ¢–b€¢6fRÂ ¢’°¢&WGW&âG´ÖF‚ç&÷VæB‡6fR—Ò×6°¢Ð ¢&WGW&âG²‡6fRò’çFôf—†VBƒ—×6°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”'W'7G2€¢7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚¢’°¢6öç7B–çFVçG2Ð¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢7FFP¢¢çG&–åö–çFVçG0¢æf–ÇFW"€¢–çFVçBÓà¢–çFVçBæ6†V6·ö–çE÷7FGW2ÓÓÐ¢v6ö×ÆWFVEö&Vf÷&U÷Frb`¢–çFVçBæ6†V6·ö–çCòçvUö—5öw–ÒÓÓÐ¢G'VRb`¢&ööÆVâ€¢–çFVçBç7F@¢¢“° ¢6öç7B'W'7G2Ð¢µÓ° ¢f÷"€¢6öç7B–çFVç@¢öb–çFVçG0¢’°¢6öç7B&Wf–÷W2Ð¢'W'7G5°¢'W'7G2æÆVæwF‚Ð¢¢Ó°¢6öç7B6ÖT6†V6·ö–çBÐ¢&Wf–÷W3òæ6†V6·ö–çCòæ–BÓÓÐ¢–çFVçBæ6†V6·ö–çCòæ–C°¢6öç7B6ÖU7FBÐ¢&Wf–÷W3òç7FBÓÓÐ¢–çFVçBç7FC°¢6öç7B6ö×F–&ÆTw–ÒÐ¢&Wf–÷W3òæw–ÒÇÀ¢–çFVçBæw–ÒÇÀ¢&Wf–÷W2æw–ÒÓÓÐ¢–çFVçBæw–Ó°¢6öç7BvÐ¢&Wf–÷W0¢ò–çFVçBçFVEöBÐ¢&Wf–÷W2æVæFVEö@¢¢çVÆÃ° ¢–b€¢&Wf–÷W2b`¢6ÖT6†V6·ö–çBb`¢6ÖU7FBb`¢6ö×F–&ÆTw–Òb`¢vãÒb`¢vÃÐ¢E$”ä”äuô4„T4µô”åEô%U%5EôtôÕ0¢’°¢&Wf–÷W2æ–çFVçG2çW6‚€¢–çFVç@¢“°¢&Wf–÷W2æVæFVEöBÐ¢–çFVçBçFVEöC°¢&Wf–÷W2æw–ÒÐ¢&Wf–÷W2æw–ÒÇÀ¢–çFVçBæw–ÒÇÀ¢çVÆÃ° ¢6öçF–çVS°¢Ð ¢'W'7G2çW6‚‡°¢–C ¢G¶–çFVçBæ6†V6·ö–çBæ–GÒÒG¶–çFVçBçFVEöGÖÀ¢6†V6·ö–çC ¢–çFVçBæ6†V6·ö–çBÀ¢6†V6·ö–çEövUö×3 ¢–çFVçBæ6†V6·ö–çEövUö×2À¢7FC ¢–çFVçBç7FBÀ¢w–Ó ¢–çFVçBæw–ÒÀ¢7F'FVEöC ¢–çFVçBçFVEöBÀ¢VæFVEöC ¢–çFVçBçFVEöBÀ¢–çFVçG3¢°¢–çFVç@¢Ð¢Ò“°¢Ð ¢&WGW&â'W'7G3°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”ÖF6„'W'7B€¢7F–öç2À¢'W'7@¢’°¢6öç7Bf–Æ&ÆT7F–öç2Ð¢€¢'&’æ—4'&’€¢7F–öç0¢¢ò7F–öç0¢¢µÐ¢¢æf–ÇFW"€¢7F–öâÓà¢7F–öãòæÆ—fU÷6æ6†÷Còç7FGW2ÓÓÐ¢wVæf–Æ&ÆRrb`¢7F–öãòç7FBÓÓÐ¢'W'7Còç7FBb`¢€¢'W'7Còæw–ÒÇÀ¢7F–öãòæw–ÒÇÀ¢çVÖ&W"€¢7F–öâæw–Ð¢’ÓÓÐ¢çVÖ&W"€¢'W'7Bæw–Ð¢¢¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢çVÖ&W"€¢ÆVgBçF–ÖW7F× ¢’Ð¢çVÖ&W"€¢&–v‡BçF–ÖW7F× ¢’ÇÀ¢7G&–ær€¢ÆVgBæ–BÇÀ¢rp¢’æÆö6ÆT6ö×&R€¢7G&–ær€¢&–v‡Bæ–BÇÀ¢rp¢¢¢“° ¢6öç7BÖF6†W2Ð¢f–Æ&ÆT7F–öç0¢æf–ÇFW"€¢7F–öâÓâ°¢6öç7BF–ÖW7F×Ö–ÆÆ—6V6öæG2Ð¢çVÖ&W"€¢7F–öãòçF–ÖW7F× ¢’ ¢° ¢&WGW&âçVÖ&W"æ—56fT–çFVvW"€¢F–ÖW7F×Ö–ÆÆ—6V6öæG0¢’b`¢F–ÖW7F×Ö–ÆÆ—6V6öæG2ãÐ¢'W'7Bç7F'FVEöBÐ¢E$”ä”äuô4„T4µô”åEôÄôuôÔD4…õDôÄU$ä4UôÕ2b`¢F–ÖW7F×Ö–ÆÆ—6V6öæG2ÃÐ¢'W'7BæVæFVEöB°¢E$”ä”äuô4„T4µô”åEôÄôuôÔD4…õDôÄU$ä4UôÕ3°¢Ð¢“° ¢–b€¢ÖF6†W2æÆVæwF‚ÓÐ¢'W'7Còæ–çFVçG3òæÆVæwF€¢’°¢&WGW&âµÓ°¢Ð ¢6öç7BW‡V7FVEG&–ç2Ð¢'W'7Bæ–çFVçG0¢æÖ€¢–çFVçBÓà¢–çFVçBçG&–ç0¢¢æf–ÇFW"€¢&ööÆVà¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBÐ¢&–v‡@¢“° ¢–b€¢W‡V7FVEG&–ç2æÆVæwF‚ÓÓÐ¢'W'7Bæ–çFVçG2æÆVæwF€¢’°¢6öç7Bö'6W'fVEG&–ç2Ð¢ÖF6†W0¢æÖ€¢7F–öâÓà¢çVÖ&W"€¢7F–öãòçG&–ç0¢¢¢ç6÷'B€¢€¢ÆVgBÀ¢&–v‡@¢’Óà¢ÆVgBÐ¢&–v‡@¢“° ¢–b€¢W‡V7FVEG&–ç2ç6öÖR€¢€¢fÇVRÀ¢–æFW€¢’Óà¢fÇVRÓÐ¢ö'6W'fVEG&–ç5°¢–æFW€¢Ð¢¢’°¢&WGW&âµÓ°¢Ð¢Ð ¢6öç7BVæW&w•W6VBÐ¢ÖF6†W2ç&VGV6R€¢€¢F÷FÂÀ¢7F–öà¢’Óà¢F÷FÂ°¢çVÖ&W"€¢7F–öãòæVæW&w•÷W6VBÇÀ¢ ¢’À¢ ¢“° ¢–b€¢ÖF6†W2æÆVæwF‚ÓÐ¢'W'7Còæ–çFVçG3òæÆVæwF‚ÇÀ¢çVÖ&W"æ—4f–æ—FR€¢VæW&w•W6V@¢’ÇÀ¢VæW&w•W6VBÃÒÇÀ¢VæW&w•W6VBà¢çVÖ&W"€¢'W'7Còæ6†V6·ö–çCòæVæW&w“òæ7W'&VçBÇÀ¢ ¢¢’°¢&WGW&âµÓ°¢Ð ¢&WGW&âÖF6†W3°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'”GF6…Fô7F–öç2€¢7F–öç2À¢7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚¢’°¢6öç7B'W'7G2Ð¢G&–æ–æt6†V6·ö–çD6æ'”'W'7G2€¢7FFP¢“° ¢f÷"€¢6öç7B'W'7@¢öb'W'7G0¢’°¢6öç7BÖF6†W2Ð¢G&–æ–æt6†V6·ö–çD6æ'”ÖF6„'W'7B€¢7F–öç2À¢'W'7@¢“° ¢–b€¢ÖF6†W2æÆVæwF€¢’°¢6öçF–çVS°¢Ð ¢f÷"€¢6öç7B7F–öà¢öbÖF6†W0¢’°¢7F–öâæÆ—fU÷6æ6†÷BÒ°¢7FGW3 ¢w&WG&–åö•ö6†V6·ö–çBrÀ¢6GW&VEöC ¢ÖF‚æfÆö÷"€¢'W'7Bç7F'FVEöBð¢ ¢’À¢ö'6W'fVEöC ¢ÖF‚æfÆö÷"€¢'W'7Bæ6†V6·ö–çBç&V6V—fVEöBð¢ ¢’À¢6†V6·ö–çEövUö×3 ¢'W'7Bæ6†V6·ö–çEövUö×2À¢'W'7Eö–C ¢'W'7Bæ–BÀ¢'W'7E÷Fö6÷VçC ¢'W'7Bæ–çFVçG2æÆVæwF‚À¢'W'7E÷7F'FVEöC ¢'W'7Bç7F'FVEöBÀ¢'W'7EöVæFVEöC ¢'W'7BæVæFVEöBÀ¢VæW&w•ö&Vf÷&S ¢'W'7Bæ6†V6·ö–çBæVæW&w’æ7W'&VçBÀ¢†–æW75ö&Vf÷&S ¢'W'7Bæ6†V6·ö–çBæ†–æW72æ7W'&VçBÀ¢†–æW75öÖ†–×VÓ ¢'W'7Bæ6†V6·ö–çBæ†–æW72æÖ†–×VÒÀ¢6÷W&6S ¢E$”ä”äuô4„T4µô”åEô•õ4õU$4P¢Ó°¢Ð¢Ð ¢&WGW&â7F–öç3°¢Ð ¢gVæ7F–öâG&–æ–æt6†V6·ö–çD6æ'•7FGW5FW‡B€¢7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚’À¢æ÷tÖ–ÆÆ—6V6öæG2Ð¢FFRææ÷r‚¢’°¢6öç7B6fRÐ¢G&–æ–æt6†V6·ö–çD6æ'•6æ—F—¦U7FFR€¢7FFRÀ¢æ÷tÖ–ÆÆ—6V6öæG0¢“° ¢6öç7BÆFW7BÐ¢6fRæ6†V6·ö–çG5°¢6fRæ6†V6·ö–çG2æÆVæwF‚Ð¢¢Ó° ¢6öç7B–çFVçBÐ¢6fRçG&–åö–çFVçG5°¢6fRçG&–åö–çFVçG2æÆVæwF‚Ð¢¢Ó° ¢6öç7BÆ–æW2Ð¢°¢6fRç7F÷&vUö6ö×F–&ÆRÓÓÐ¢fÇ6P¢òt6GW&RVæv–æS¢W6VB6fVÇ’(	B7F÷&VBWf–FVæ6RW6W2æWvW"66†VÖâp¢¢t6GW&RVæv–æS¢&VG’(	Bf—6–&ÆRF÷&âvW2öæÇ“²&÷WF–æRÆ–Ö—B&WVW7Bò32âp¢Ó° ¢–b€¢ÆFW7@¢’°¢Æ–æW2çW6‚€¢ÆFW7B6†V6·ö–çC¢†–æW72G¶ÆFW7Bæ†–æW72æ7W'&VçBçFôÆö6ÆU7G&–ær‚—ÒòG¶ÆFW7Bæ†–æW72æÖ†–×VÒçFôÆö6ÆU7G&–ær‚—Ò+rVæW&w’G¶ÆFW7BæVæW&w’æ7W'&VçBçFôÆö6ÆU7G&–ær‚—ÒòG¶ÆFW7BæVæW&w’æÖ†–×VÒçFôÆö6ÆU7G&–ær‚—ÖÀ¢&V6V—fVC¢G¶æWrFFR†ÆFW7Bç&V6V—fVEöB’çFôÆö6ÆU7G&–ær‚—Ò+rG·G&–æ–æt6†V6·ö–çD6æ'”f÷&ÖDvR†æ÷tÖ–ÆÆ—6V6öæG2ÒÆFW7Bç&V6V—fVEöB—ÒvöÀ¢vS¢G¶ÆFW7BçvWÒ+r&V6öã¢G¶ÆFW7Bç&V6öâç&WÆ6R‚õòörÂrr—Ö ¢“°¢ÒVÇ6R–b€¢6fRæÆ7E÷7FGW2ÓÓÐ¢væõö•ö¶W’p¢’°¢Æ–æW2çW6‚€¢tÆFW7B6†V6·ö–çC¢æ÷Bf–Æ&ÆR(	B6fRF÷&â’¶W’–â6WGF–æw2f—'7Bâp¢“°¢ÒVÇ6R–b€¢6fRæÆ7E÷7FGW2ÓÓÐ¢vf–ÆVBp¢’°¢Æ–æW2çW6‚€¢ÆFW7B6†V6·ö–çC¢f–ÆVB6fVÇ’(	BG·6fRæÆ7EöW'&÷"ÇÂwVæ¶æ÷vâW'&÷"wÖ ¢“°¢ÒVÇ6R°¢Æ–æW2çW6‚€¢tÆFW7B6†V6·ö–çC¢v—F–ærf÷"F†Rf—'7BVÆ–v–&ÆR6GW&Râp¢“°¢Ð ¢–b€¢–çFVç@¢’°¢Æ–æW2çW6‚€¢–çFVçBæ6†V6·ö–çE÷7FGW2ÓÓÐ¢v6ö×ÆWFVEö&Vf÷&U÷Fp¢òÆ7BG&–âF¢6†V6·ö–çB6ö×ÆWFVBG·G&–æ–æt6†V6·ö–çD6æ'”f÷&ÖDvR†–çFVçBæ6†V6·ö–çEövUö×2—Ò&Vf÷&RF†RFæ ¢¢tÆ7BG&–âF¢æòVÆ–g––ær6†V6·ö–çB6ö×ÆWFVB&Vf÷&RF†RFâp¢“°¢ÒVÇ6R°¢Æ–æW2çW6‚€¢tÆ7BG&–âF¢æöæR&V6÷&FVB'’F†—26æ'’âp¢“°¢Ð ¢Æ–æW2çW6‚€¢u7FvS¢GG&–'WF–öâVæ&ÆVB(	BVÆ–g––ærWf–FVæ6RGF6†W2öæÇ’gFW"ÖF6†–ærG&–æ–ærÆör—26öÆÆV7FVBâp¢“° ¢&WGW&âÆ–æW2æ¦ö–â€¢uÆâp¢“°¢Ð ¢gVæ7F–öâ–ç7FÆÅG&–æ–æt6†V6·ö–çD6æ'’‚’°¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”–ç7FÆÆVBÇÀ¢G—VöbFö7VÖVçBÓÓÐ¢wVæFVf–æVBrÇÀ¢Fö7VÖVçBæFDWfVçDÆ—7FVæW ¢’°¢&WGW&âfÇ6S°¢Ð ¢w&—FUG&–æ–æt6†V6·ö–çD6æ'•7FFR‡°¢ââç&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚’À¢–ç7FÆÆVEöC ¢FFRææ÷r‚¢Ò“° ¢Fö7VÖVçBæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢WfVçBÓâ°¢&V6÷&EG&–æ–æt6†V6·ö–çD6æ'”–çFVçB€¢WfVç@¢“° ¢–b€¢G&–æ–æu6æ6†÷D—4w–Ôæf–vF–öâ€¢WfVçCòçF&vW@¢’b`¢G—Vöb6WEF–ÖV÷WBÓÓÐ¢vgVæ7F–öâp¢’°¢6WEF–ÖV÷WB€¢‚’Óâ°¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢fÇ6S° ¢–b€¢G&–æ–æu6æ6†÷D—4w–ÕvR‚¢’°¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢G'VS° ¢fö–B6GW&UG&–æ–æt6†V6·ö–çD6æ'’€¢vw–ÕöVçG'’rÀ¢G'VP¢“°¢Ð¢ÒÀ¢#S ¢“°¢Ð¢ÒÀ¢G'VP¢“° ¢6öç7BF–6²Ð¢&V6öâÓâ°¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”Fö7VÖVçD7F—fR‚¢’°¢&WGW&ã°¢Ð ¢6öç7Bw–ÕvRÐ¢G&–æ–æu6æ6†÷D—4w–ÕvR‚“° ¢–b€¢w–ÕvRb`¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–Ð¢’°¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢G'VS° ¢fö–B6GW&UG&–æ–æt6†V6·ö–çD6æ'’€¢vw–ÕöVçG'’rÀ¢G'VP¢“° ¢&WGW&ã°¢Ð ¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢w–ÕvS° ¢fö–B6GW&UG&–æ–æt6†V6·ö–çD6æ'’€¢&V6öâÀ¢fÇ6P¢“°¢Ó° ¢Fö7VÖVçBæFDWfVçDÆ—7FVæW"€¢wf—6–&–Æ—G–6†ævRrÀ¢‚’Óâ°¢–b€¢G&–æ–æt6†V6·ö–çD6æ'”Fö7VÖVçD7F—fR‚¢’°¢F–6²€¢wf—6–&ÆRp¢“°¢Ð¢ÒÀ¢²76—fS¢G'VRÐ¢“° ¢–b€¢G—Vöbv–æF÷rÓÐ¢wVæFVf–æVBp¢’°¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢wvW6†÷rrÀ¢‚’Óâ°¢F–6²€¢wvW6†÷rp¢“°¢ÒÀ¢²76—fS¢G'VRÐ¢“° ¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢w÷7FFRrÀ¢‚’Óâ°¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢fÇ6S° ¢F–6²€¢w&÷WF–æRp¢“°¢ÒÀ¢²76—fS¢G'VRÐ¢“° ¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢v†6†6†ævRrÀ¢‚’Óâ°¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢fÇ6S° ¢F–6²€¢w&÷WF–æRp¢“°¢ÒÀ¢²76—fS¢G'VRÐ¢“°¢Ð ¢G&–æ–æt6†V6·ö–çD6æ'”–ç7FÆÆVBÐ¢G'VS° ¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–ÒÐ¢G&–æ–æu6æ6†÷D—4w–ÕvR‚“° ¢fö–B6GW&UG&–æ–æt6†V6·ö–çD6æ'’€¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–Ð¢òvw–ÕöVçG'’p¢¢v–æ—F–ÂrÀ¢G&–æ–æt6†V6·ö–çD6æ'”Æ7EvUv4w–Ð¢“° ¢–b€¢G&–æ–æt6†V6·ö–çD6æ'•F–ÖW"ÓÓÐ¢çVÆÂb`¢G—Vöb6WD–çFW'fÂÓÓÐ¢vgVæ7F–öâp¢’°¢G&–æ–æt6†V6·ö–çD6æ'•F–ÖW"Ð¢6WD–çFW'fÂ€¢‚’Óâ°¢F–6²€¢w&÷WF–æRp¢“°¢ÒÀ¢E$”ä”äuô4„T4µô”åEõD”4µô”åDU%dÅôÕ0¢“°¢Ð ¢&WGW&âG'VS°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòÄ•dR$U4õU$4Rd”ÅU$RD”täõ5D”50¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢6öç7B&VæFW%&W6÷W&6TF6†&ö&Ev—F†÷WDF–væ÷7F–72Ð¢&VæFW%&W6÷W&6TF6†&ö&C° ¢gVæ7F–öâ&W6÷W&6TF6†&ö&DF–væ÷7F–5FW‡B€¢6æ6†÷@¢’°¢6öç7B&V6öâÐ¢7G&–ær€¢6æ6†÷Còç&V6öâÇÀ¢wVæ¶æ÷vâp¢“° ¢–b€¢&V6öâÓÓÐ¢v•ö¶W•÷Væf–Æ&ÆRp¢’°¢&WGW&âtæò’¶W’&V6†VBF†R÷W6W"ö&'2&WVW7Bâs°¢Ð ¢6öç7B&rÐ¢7G&–ær€¢6æ6†÷CòæÖW76vRÇÀ¢rp¢’çG&–Ò‚“° ¢–b€¢&p¢’°¢&WGW&â&'2f–ÇW&R&V6öã¢G·&V6öçÒæ°¢Ð ¢6öç7B&VF7FVBÐ¢&p¢ç&WÆ6R€¢ô”¶W•Ç2µµåÇ3ÃâeÒ²öv’À¢t”¶W’·&VF7FVEÒp¢¢ç&WÆ6R€¢ò…Æ&¶W“Ò•µâeÇ3ÅÒ²öv’À¢rC·&VF7FVEÒp¢“° ¢&WGW&âG·&V6öçÓ¢G·&VF7FVGÖ ¢ç6Æ–6R€¢À¢## ¢“°¢Ð ¢&VæFW%&W6÷W&6TF6†&ö&BÐ¢gVæ7F–öâ&VæFW%&W6÷W&6TF6†&ö&Ev—F„F–væ÷7F–72€¢fÆ÷rÀ¢&'56æ6†÷@¢’°¢6öç7B‡FÖÂÐ¢&VæFW%&W6÷W&6TF6†&ö&Ev—F†÷WDF–væ÷7F–72€¢fÆ÷rÀ¢&'56æ6†÷@¢“° ¢–b€¢‡FÖÂÇÀ¢&'56æ6†÷Còç7FGW2ÓÓÐ¢vf–Æ&ÆRp¢’°¢&WGW&â‡FÖÃ°¢Ð ¢6öç7BöÆEFW‡BÐ¢t†—7F÷&–6ÂF÷FÇ27F–ÆÂv÷&²âfÆ–B6fVB’¶W’—2æVVFVBf÷"7W'&VçB&'2æB&Vf–ÆÂF–ÖW2âs° ¢–b€¢‡FÖÂæ–æ6ÇVFW2€¢öÆEFW‡@¢¢’°¢&WGW&â‡FÖÃ°¢Ð ¢6öç7BF–væ÷7F–2Ð¢W66U&W6÷W&6TF6†&ö&D‡FÖÂ€¢&W6÷W&6TF6†&ö&DF–væ÷7F–5FW‡B€¢&'56æ6†÷@¢¢“° ¢&WGW&â‡FÖÂç&WÆ6R€¢öÆEFW‡BÀ¢t†—7F÷&–6ÂF÷FÇ27F–ÆÂv÷&²âF†RÆ—fR÷W6W"ö&'2&VF–ærf–ÆVBÂv†–ÆR÷F†W"æÇ—F–72&VÖ–âf–Æ&ÆRâr°¢Æ'#ãÆ#äF–væ÷7F–3£Âö#âG¶F–væ÷7F–7Ö ¢“°¢Ó°¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòdU$”d”TB$TD$ÄR„•5Dõ%’4U$”Ä•¤D”ôà¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢6öç7B„•5Dõ%•ôU…õ%Eôdõ$ÔBÐ¢wF÷&âÖæÇ—F–72×&VF&ÆRÖ†—7F÷'’s° ¢6öç7B„•5Dõ%•ôU…õ%Eôdõ$ÔEõdU%4”ôâÐ¢#° ¢gVæ7F–öâæ÷&ÖÆ—¦T†—7F÷'”W‡÷'D66÷VçB€¢66÷Vç@¢’°¢6öç7B–BÒæ÷&ÖÆ—¦U6–ævÆT66÷VçD–B€¢66÷VçCòæ–BÀ¢tWF†VçF–6FVBF÷&â66÷VçB”Bp¢“° ¢6öç7BæÖRÒ7G&–ær†66÷VçCòææÖRóòrr’çG&–Ò‚“° ¢–b‚æÖR’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B&WV—&W2fÆ–BWF†VçF–6FVBF÷&â66÷VçBâp¢“°¢Ð ¢&WGW&â²–BÂæÖRÓ°¢Ð ¢gVæ7F–öâ†—7F÷'”W‡÷'Df–ÆVæÖR€¢66÷VçD–BÀ¢FFRÒæWrFFR‚¢’°¢6öç7B–BÒæ÷&ÖÆ—¦U6–ævÆT66÷VçD–B€¢66÷VçD–BÀ¢t†—7F÷'’W‡÷'B66÷VçB”Bp¢“° ¢6öç7BF’ÒFFRçFô•4õ7G&–ær‚’ç6Æ–6RƒÂ“°¢&WGW&âF÷&äæÇ—F–72ÒG¶–GÒÖ†—7F÷'’ÒG¶F—Òæ§6öæ°¢Ð ¢7–æ2gVæ7F–öâ†—7F÷'”W‡÷'E6†#Sd†W‚€¢FW‡@¢’°¢–b€¢vÆö&ÅF†—2æ7'—Fóòç7V'FÆRÇÀ¢G—VöbFW‡DVæ6öFW"ÓÒvgVæ7F–öâp¢’°¢F‡&÷ræWrW'&÷"€¢u4„Ó#Sb—2Væf–Æ&ÆS²&VgW6–ærFò7&VFRâVçfW&–f–&ÆR&VF&ÆR†—7F÷'’W‡÷'Bâp¢“°¢Ð ¢6öç7BF–vW7BÒv—BvÆö&ÅF†—2æ7'—Fòç7V'FÆRæF–vW7B€¢u4„Ó#SbrÀ¢æWrFW‡DVæ6öFW"‚’æVæ6öFR…7G&–ær‡FW‡B’¢“° ¢&WGW&â'&’æg&öÒ€¢æWrV–çC„'&’†F–vW7B’À¢'—FRÓâ'—FRçFõ7G&–ærƒb’çE7F'Bƒ"Âsr¢’æ¦ö–â‚rr“°¢Ð ¢gVæ7F–öâ7VÖÖ&—¦T†—7F÷'”&6†—fU&÷fVææ6R€¢&V6÷&G0¢’°¢–b€¢'&’æ—4'&’€¢&V6÷&G0¢¢’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B&÷fVææ6R&WV—&W2fW&–f–VB&V6÷&B'&’âp¢“°¢Ð ¢ÆWB&u&V6÷&D6÷VçBÐ¢° ¢ÆWBÆVv7”æ÷&ÖÆ—¦VD6÷VçBÐ¢° ¢f÷"€¢6öç7B&V6÷&@¢öb&V6÷&G0¢’°¢6öç7B&rÐ¢fÆ–FFT†—7F÷'•&t&6†—fT&–æF–ær€¢&V6÷&@¢“° ¢–b€¢&p¢’°¢&u&V6÷&D6÷VçB²³°¢ÒVÇ6R°¢ÆVv7”æ÷&ÖÆ—¦VD6÷VçB²³°¢Ð¢Ð ¢&WGW&â°¢&u÷&V6÷&Eöf÷&ÖC ¢„•5Dõ%•õ$uô$4„•dUôdõ$ÔBÀ¢&u÷&V6÷&Eö6÷VçC ¢&u&V6÷&D6÷VçBÀ¢ÆVv7•öæ÷&ÖÆ—¦VEö6÷VçC ¢ÆVv7”æ÷&ÖÆ—¦VD6÷VçBÀ¢Æ÷76ÆW75÷&uö6ö×ÆWFS ¢&V6÷&G2æÆVæwF‚âb`¢&u&V6÷&D6÷VçBÓÓÒ&V6÷&G2æÆVæwF‚b`¢ÆVv7”æ÷&ÖÆ—¦VD6÷VçBÓÓÒ ¢Ó°¢Ð ¢gVæ7F–öâfÆ–FFT†—7F÷'”W‡÷'E&V6÷&E6WB€¢66÷VçD–BÀ¢66†VE&V6÷&G2À¢Æöw0¢’°¢6öç7B–BÒæ÷&ÖÆ—¦U6–ævÆT66÷VçD–B€¢66÷VçD–BÀ¢t†—7F÷'’W‡÷'B66÷VçB”Bp¢“° ¢–b‚'&’æ—4'&’†66†VE&V6÷&G2’ÇÂ66†VE&V6÷&G2æÆVæwF‚’°¢F‡&÷ræWrW'&÷"€¢æò7F÷&VBF÷&â†—7F÷'’W†—7G2f÷"WF†VçF–6FVB66÷VçBG¶–GÒæ ¢“°¢Ð ¢–b‚'&’æ—4'&’†Æöw2’ÇÂÆöw2æÆVæwF‚ÓÒ66†VE&V6÷&G2æÆVæwF‚’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'BfW&–f–6F–öâf–ÆVB&V6W6R7F÷&VB×&V6÷&BæBFV7'—FVBÖÆör6÷VçG2Fòæ÷BÖF6‚âp¢“°¢Ð ¢6öç7B&Vf—‚ÒG¶–GÓ¦° ¢f÷"†6öç7B&V6÷&Böb66†VE&V6÷&G2’°¢ÆWB&V6÷&D66÷VçD–C° ¢G'’°¢&V6÷&D66÷VçD–BÒæ÷&ÖÆ—¦U6–ævÆT66÷VçD–B€¢&V6÷&Còæ66÷VçEö–BÀ¢u7F÷&VBW‡÷'B&V6÷&B66÷VçB”Bp¢“°¢Ò6F6‚°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B&Æö6¶VB&V6W6R7F÷&VB&V6÷&Bf–ÆVBWF†VçF–6FVB66÷VçB&–æF–ærâp¢“°¢Ð ¢–b€¢&V6÷&D66÷VçD–BÓÒ–BÇÀ¢G—Vöb&V6÷&Còæ66†Uö¶W’ÓÒw7G&–ærrÇÀ¢&V6÷&Bæ66†Uö¶W’ç7F'G5v—F‚‡&Vf—‚¢’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B&Æö6¶VB&V6W6R7F÷&VB&V6÷&Bf–ÆVBWF†VçF–6FVB66÷VçB&–æF–ærâp¢“°¢Ð¢Ð ¢6öç7B6VVâÒæWr6WB‚“° ¢f÷"†6öç7BÆöröbÆöw2’°¢6öç7B&W&VBÒ&W&T66†VDÆör†–BÂÆör“° ¢–b‡6VVâæ†2‡&W&VBæ–B’’°¢F‡&÷ræWrW'&÷"€¢&VF&ÆR†—7F÷'’W‡÷'B&Æö6¶VB&V6W6RGWÆ–6FRF÷&âÆör–FVçF—G’G·&W&VBæ–GÒv2f÷VæBæ ¢“°¢Ð ¢6VVâæFB‡&W&VBæ–B“°¢Ð ¢&WGW&â²ââæÆöw5Òç6÷'B€¢†Â"’Óà¢çVÖ&W"†çF–ÖW7F×’ÒçVÖ&W"†"çF–ÖW7F×’ÇÀ¢7G&–ær†æ–B’æÆö6ÆT6ö×&R…7G&–ær†"æ–B’¢“°¢Ð ¢7–æ2gVæ7F–öâ'V–ÆE&VF&ÆT†—7F÷'”W‡÷'B€¢WF†VçF–6FVD66÷Vç@¢’°¢6öç7B66÷VçBÒæ÷&ÖÆ—¦T†—7F÷'”W‡÷'D66÷VçB†WF†VçF–6FVD66÷VçB“°¢6öç7B&÷FV7F–öâÒv—BvWD66÷VçD†—7F÷'•&÷FV7F–öå7FGW2†66÷VçBæ–B“° ¢–b‚&÷FV7F–öâæ6ö×ÆWFRÇÂ&÷FV7F–öâçÆ–çFW‡BÓÒ’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B—2f–Æ&ÆRöæÇ’gFW"ÆÂ7F÷&VBF÷&âÆöw2&R&÷FV7FVB'’Æö6Â†—7F÷'’&÷FV7F–öââp¢“°¢Ð ¢6öç7B66†VE&V6÷&G2Òv—BF$ÆöD66†VE&V6÷&G2†66÷VçBæ–B“° ¢–b†66†VE&V6÷&G2ç6öÖR‡&V6÷&BÓâ—5&÷FV7FVD†—7F÷'•&V6÷&B‡&V6÷&B’’’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'B&Æö6¶VB&V6W6RâVç&÷FV7FVB7F÷&VBF÷&âÆörv2FWFV7FVBâp¢“°¢Ð ¢6öç7BÆöw2Òv—BF$ÆöDÆöw2†66÷VçBæ–B“°¢6öç7B&V6÷&G2ÒfÆ–FFT†—7F÷'”W‡÷'E&V6÷&E6WB€¢66÷VçBæ–BÀ¢66†VE&V6÷&G2À¢Æöw0¢“° ¢6öç7B&6†—fU&÷fVææ6RÐ¢7VÖÖ&—¦T†—7F÷'”&6†—fU&÷fVææ6R€¢&V6÷&G0¢“° ¢6öç7Bf—'7EF–ÖW7F×ÒçVÖ&W"‡&V6÷&G5³ÓòçF–ÖW7F×“°¢6öç7BÆ7EF–ÖW7F×ÒçVÖ&W"‡&V6÷&G5·&V6÷&G2æÆVæwF‚ÒÓòçF–ÖW7F×“° ¢–b€¢çVÖ&W"æ—56fT–çFVvW"†f—'7EF–ÖW7F×’ÇÀ¢çVÖ&W"æ—56fT–çFVvW"†Æ7EF–ÖW7F×’ÇÀ¢f—'7EF–ÖW7F×ÂÇÀ¢Æ7EF–ÖW7F×Âf—'7EF–ÖW7F× ¢’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’W‡÷'BfW&–f–6F–öâf–ÆVB&V6W6RF†R†—7F÷'’6÷fW&vR—2–çfÆ–Bâp¢“°¢Ð ¢6öç7B–ÆöBÒ°¢f÷&ÖC¢„•5Dõ%•ôU…õ%Eôdõ$ÔBÀ¢f÷&ÖE÷fW'6–öã¢„•5Dõ%•ôU…õ%Eôdõ$ÔEõdU%4”ôâÀ¢66÷VçC¢°¢–C¢66÷VçBæ–BÀ¢æÖS¢66÷VçBææÖP¢ÒÀ¢6÷fW&vS¢°¢f—'7E÷F–ÖW7F×¢f—'7EF–ÖW7F×À¢f—'7Eö—6ó¢F–ÖW7F×Fô—6ò†f—'7EF–ÖW7F×’À¢Æ7E÷F–ÖW7F×¢Æ7EF–ÖW7F×À¢Æ7Eö—6ó¢F–ÖW7F×Fô—6ò†Æ7EF–ÖW7F×’À¢&V6÷&Eö6÷VçC¢&V6÷&G2æÆVæwF€¢ÒÀ¢&6†—fU÷&÷fVææ6S ¢&6†—fU&÷fVææ6RÀ¢6öÆÆV7F÷#¢°¢æÖS¢uF÷&âæÇ—F–72rÀ¢fW'6–öã¢dU%4”ôâÀ¢6÷W&6S¢vWF†VçF–6FVBÖ66÷VçB×66÷VBVæ7'—FVBÆö6Â†—7F÷'’p¢ÒÀ¢W‡÷'FVEöC¢æWrFFR‚’çFô•4õ7G&–ær‚’À¢&V6÷&G0¢Ó° ¢6öç7BF–vW7BÒv—B†—7F÷'”W‡÷'E6†#Sd†W‚€¢7F&ÆT†—7F÷'”§6öâ‡–ÆöB¢“° ¢6öç7B÷WGWBÒ°¢ââç–ÆöBÀ¢–çFVw&—G“¢°¢Æv÷&—F†Ó¢u4„Ó#SbrÀ¢6æöæ–6Æ—¦F–öã¢w7F&ÆRÖ§6öâ×crÀ¢66÷S¢vÆÂF÷ÖÆWfVÂf–VÆG2W†6WB–çFVw&—G’rÀ¢F–vW7@¢Ð¢Ó° ¢&WGW&â°¢66÷VçBÀ¢f–ÆVæÖS¢†—7F÷'”W‡÷'Df–ÆVæÖR†66÷VçBæ–B’À¢&V6÷&Eö6÷VçC¢&V6÷&G2æÆVæwF‚À¢f—'7E÷F–ÖW7F×¢f—'7EF–ÖW7F×À¢Æ7E÷F–ÖW7F×¢Æ7EF–ÖW7F×À¢&6†—fU÷&÷fVææ6S ¢&6†—fU&÷fVææ6RÀ¢F–vW7BÀ¢§6öã¢¥4ôâç7G&–æv–g’†÷WGWBÂçVÆÂÂ"¢Ó°¢Ð ¢7–æ2gVæ7F–öâ'V–ÆDWF†VçF–6FVE&VF&ÆT†—7F÷'”W‡÷'B€¢”¶W’À¢G&6¶W"ÒçVÆÀ¢’°¢6öç7B66÷VçEG&6¶W"ÒG&6¶W"ÇÂ°¢6WE7FvR‚’·ÒÀ¢–æ7&VÖVçE&WVW7B‚’·Ð¢Ó° ¢6öç7B66÷VçBÒv—BFWFV7D66÷VçB€¢”¶W’À¢66÷VçEG&6¶W ¢“° ¢v—B76W'DWF†VçF–6FVE6–ævÆT66÷VçD÷væW"€¢66÷VçBæ–@¢“° ¢&WGW&â'V–ÆE&VF&ÆT†—7F÷'”W‡÷'B€¢66÷Vç@¢“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòU„TÔU$Â$TD$ÄR„•5Dõ%’DõtäÄô@¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâG&–vvW%&VF&ÆT†—7F÷'”F÷væÆöB€¢&W7VÇ@¢’°¢–b€¢&W7VÇBÇÀ¢G—Vöb&W7VÇBæ§6öâÓÒw7G&–ærrÇÀ¢&W7VÇBæ§6öâæÆVæwF‚ÇÀ¢G—Vöb&W7VÇBæf–ÆVæÖRÓÒw7G&–ærrÇÀ¢õåF÷&äæÇ—F–72Õ³Ó•ÕÆB¢Ö†—7F÷'’ÕÆG³GÒÕÆG³'ÒÕÆG³'ÕÂæ§6öâBòçFW7B€¢&W7VÇBæf–ÆVæÖP¢¢’°¢F‡&÷ræWrW'&÷"€¢u&VF&ÆR†—7F÷'’F÷væÆöB&VgW6VBâ–çfÆ–BfW&–f–VBW‡÷'B&W7VÇBâp¢“°¢Ð ¢–b€¢G—Vöb&Æö"ÓÒvgVæ7F–öârÇÀ¢vÆö&ÅF†—2åU$Ãòæ7&VFTö&¦V7EU$ÂÇÀ¢vÆö&ÅF†—2åU$Ãòç&Wfö¶Tö&¦V7EU$À¢’°¢F‡&÷ræWrW'&÷"€¢uF†—2'&÷w6W"6ææ÷B7&VFRÆö6Â&VF&ÆR†—7F÷'’F÷væÆöB6fVÇ’âp¢“°¢Ð ¢6öç7B&Æö"ÒæWr&Æö"€¢·&W7VÇBæ§6öåÒÀ¢°¢G—S¢vÆ–6F–öâö§6öã¶6†'6WC×WFbÓ‚p¢Ð¢“° ¢6öç7Bö&¦V7EW&ÂÐ¢U$Âæ7&VFTö&¦V7EU$Â€¢&Æö ¢“° ¢6öç7Bæ6†÷"Ð¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢vp¢“° ¢æ6†÷"æ‡&VbÐ¢ö&¦V7EW&Ã° ¢æ6†÷"æF÷væÆöBÐ¢&W7VÇBæf–ÆVæÖS° ¢æ6†÷"ç&VÂÐ¢væö÷VæW"s° ¢æ6†÷"ç7G–ÆRæF—7Æ’Ð¢væöæRs° ¢G'’°¢òò¶VWF†Rö&¦V7BU$Â÷WBöbF÷&âw2vRDôÒâFWF6†VBæ6†÷"—0¢òò7Vff–6–VçBf÷"7FæF&G2Ö6ö×Æ–çB'&÷w6W'2æBfö–G2W‡÷6–ærF†P¢òòFV×÷&'’&VF&ÆRÖ†—7F÷'’U$ÂFòvRÖÆWfVÂDôÒö'6W'fW'2à¢æ6†÷"æ6Æ–6²‚“°¢Òf–æÆÇ’°¢æ6†÷"ç&VÖ÷fR‚“° ¢6WEF–ÖV÷WB€¢‚’Óâ°¢U$Âç&Wfö¶Tö&¦V7EU$Â€¢ö&¦V7EW&À¢“°¢ÒÀ¢ ¢“°¢Ð ¢&WGW&â°¢66÷VçC¢°¢–C¢&W7VÇBæ66÷VçBæ–BÀ¢æÖS¢&W7VÇBæ66÷VçBææÖP¢ÒÀ¢f–ÆVæÖS¢&W7VÇBæf–ÆVæÖRÀ¢&V6÷&Eö6÷VçC¢&W7VÇBç&V6÷&Eö6÷VçBÀ¢f—'7E÷F–ÖW7F×¢&W7VÇBæf—'7E÷F–ÖW7F×À¢Æ7E÷F–ÖW7F×¢&W7VÇBæÆ7E÷F–ÖW7F×À¢F–vW7C¢&W7VÇBæF–vW7@¢Ó°¢Ð ¢gVæ7F–öâ6†&U&W&VD†—7F÷'”W‡÷'B€¢&W7VÇ@¢’°¢–b€¢&W7VÇBÇÀ¢G—Vöb&W7VÇBæ§6öâÓÒw7G&–ærrÇÀ¢&W7VÇBæ§6öâæÆVæwF‚ÇÀ¢G—Vöb&W7VÇBæf–ÆVæÖRÓÒw7G&–ærrÇÀ¢õåF÷&äæÇ—F–72Õ³Ó•ÕÆB¢Ö†—7F÷'’ÕÆG³GÒÕÆG³'ÒÕÆG³'ÕÂæ§6öâBòçFW7B€¢&W7VÇBæf–ÆVæÖP¢¢’°¢F‡&÷ræWrW'&÷"€¢tæF—fR†—7F÷'’6†&R&VgW6VBâ–çfÆ–BfW&–f–VBW‡÷'B&W7VÇBâp¢“°¢Ð ¢–b€¢G—Vöbf–ÆRÓÒvgVæ7F–öârÇÀ¢G—VöbvÆö&ÅF†—2ææf–vF÷#òç6†&RÓÒvgVæ7F–öâp¢’°¢F‡&÷ræWrW'&÷"€¢tæF—fRf–ÆR6†&–ær—2Væf–Æ&ÆR–âF†—2F÷&åDö”õ2'&÷w6W"âæò&VF&ÆRW‡÷'Bv2W‡÷6VBFòF†RvRâp¢“°¢Ð ¢6öç7Bf–ÆRÒæWrf–ÆR€¢·&W7VÇBæ§6öåÒÀ¢&W7VÇBæf–ÆVæÖRÀ¢°¢G—S¢vÆ–6F–öâö§6öã¶6†'6WC×WFbÓ‚p¢Ð¢“° ¢6öç7B6†&TFFÒ°¢f–ÆW3¢¶f–ÆUÐ¢Ó° ¢–b€¢G—Vöbæf–vF÷"æ6å6†&RÓÓÒvgVæ7F–öârb`¢æf–vF÷"æ6å6†&R‡6†&TFF¢’°¢F‡&÷ræWrW'&÷"€¢uF†—2F÷&åDö”õ2'&÷w6W"6ææ÷B6fVÇ’6†&RF†R&W&VB¥4ôâf–ÆRâp¢“°¢Ð ¢6öç7B&V6V—BÒ°¢66÷VçC¢°¢–C¢&W7VÇBæ66÷VçBæ–BÀ¢æÖS¢&W7VÇBæ66÷VçBææÖP¢ÒÀ¢f–ÆVæÖS¢&W7VÇBæf–ÆVæÖRÀ¢&V6÷&Eö6÷VçC¢&W7VÇBç&V6÷&Eö6÷VçBÀ¢f—'7E÷F–ÖW7F×¢&W7VÇBæf—'7E÷F–ÖW7F×À¢Æ7E÷F–ÖW7F×¢&W7VÇBæÆ7E÷F–ÖW7F×À¢F–vW7C¢&W7VÇBæF–vW7@¢Ó° ¢òòæf–vF÷"ç6†&R‚’—2–çFVçF–öæÆÇ’–çfö¶VB7–æ6‡&öæ÷W6Ç’&Vf÷&RF†—0¢òògVæ7F–öâ––VÆG26òF†RF—&V7B6fRW‡÷'Bf–ÆRF&WF–ç2W6W ¢òò7F—fF–öâ–âvV$¶—BõtµvV%f–Wrà¢6öç7B6†&U&W7VÇBÒæf–vF÷"ç6†&R€¢6†&TFF¢“° ¢–b€¢6†&U&W7VÇBÇÀ¢G—Vöb6†&U&W7VÇBçF†VâÓÒvgVæ7F–öâp¢’°¢F‡&÷ræWrW'&÷"€¢tæF—fRf–ÆR6†&–ærF–Bæ÷B7F'B6÷'&V7FÇ’âp¢“°¢Ð ¢&WGW&â6†&U&W7VÇBçF†Vâ€¢‚’Óâ&V6V—@¢“°¢Ð ¢7–æ2gVæ7F–öâW‡÷'DWF†VçF–6FVD†—7F÷'•FôF÷væÆöB€¢”¶W’À¢G&6¶W"ÒçVÆÀ¢’°¢6öç7B&W7VÇBÐ¢v—B'V–ÆDWF†VçF–6FVE&VF&ÆT†—7F÷'”W‡÷'B€¢”¶W’À¢G&6¶W ¢“° ¢&WGW&âG&–vvW%&VF&ÆT†—7F÷'”F÷væÆöB€¢&W7VÇ@¢“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òò$TBÔôäÅ’„•5Dõ%’dõ$Tå4”50¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâ†—7F÷'”f÷&Vç6–5v–æF÷t6öæf–r‚’°¢&WGW&â°¢g&öÓ ¢sƒ#““ƒÀ ¢Fó ¢sƒ#“““#À ¢F&vWEö–C ¢w¤VæÆ¤4Vvcd–F†Ct‚rÀ ¢F&vWE÷F–ÖW7F× ¢sƒ#““ƒS`¢Ó°¢Ð ¢7–æ2gVæ7F–öâ'Vä†—7F÷'”f÷&Vç6–5v–æF÷t6†V6²€¢”¶W’À¢G&6¶W"ÒçVÆÂÀ¢&WVW7FVEF&vWD–BÒçVÆÀ¢’°¢6öç7BFVfVÇD6öæf–rÐ¢†—7F÷'”f÷&Vç6–5v–æF÷t6öæf–r‚“° ¢6öç7B66÷VçBÐ¢v—BFWFV7D66÷VçB€¢”¶W’À¢G&6¶W ¢“° ¢v—B76W'DWF†VçF–6FVE6–ævÆT66÷VçD÷væW"€¢66÷VçBæ–@¢“° ¢òòFVÆ–&W&FVÇ’Fòæ÷B7&VFR÷&Vg&W6‚&V6÷fW'’ÖWFFF÷"w&—FRç’66†P¢òò7FFR†W&RâF†—2F–væ÷7F–2×W7B&R&VBÖöæÇ’v—F‚&W7V7BFò†—7F÷'’à¢6öç7B7F÷&VDÆöw2Ð¢v—BF$ÆöDÆöw2€¢66÷VçBæ–@¢“° ¢6öç7B6öæf–rÐ¢&WVW7FVEF&vWD–BÓÓÐ¢çVÆÀ¢òFVfVÇD6öæf–p¢¢‚‚’Óâ°¢6öç7BF&vWBÐ¢&W6öÇfU7F÷&VD†—7F÷'•G&6UF&vWB€¢7F÷&VDÆöw2À¢&WVW7FVEF&vWD–@¢“° ¢&WGW&â°¢g&öÓ ¢F&vWBçF–ÖW7F×Ð¢cÀ¢Fó ¢F&vWBçF–ÖW7F×°¢cÀ¢F&vWEö–C ¢F&vWBæ–BÀ¢F&vWE÷F–ÖW7F× ¢F&vWBçF–ÖW7F× ¢Ó°¢Ò’‚“° ¢G&6¶W#òç6WE7FvR€¢u'Vææ–ærf÷&Vç6–2†—7F÷'’6†V6¾(
brÀ¢G¶6öæf–ræg&ö×Ò(i"G¶6öæf–rçF÷Ó²&VBÖöæÇ’F—&V7BF÷&âc"6ö×&—6öæ ¢“° ¢6öç7BW&ÂÐ¢G´•ô$4WÒ÷W6W"öÆöv°¢ög&öÓÒG¶Væ6öFUU$”6ö×öæVçB†6öæf–ræg&öÒ—Ö°¢gFóÒG¶Væ6öFUU$”6ö×öæVçB†6öæf–rçFò—Ö°¢fÆ–Ö—CÒG´•ôÄ”Ô•GÖ° ¢6öç7B§6öâÐ¢v—B”fWF6„§6öâ€¢W&ÂÀ¢”¶W’À¢G&6¶W"À¢À¢7&VFU&ævU6fWG•7FFR‚¢“° ¢6öç7B6÷W&6RÐ¢§6öãòæÆös° ¢–b€¢'&’æ—4'&’€¢6÷W&6P¢¢’°¢F‡&÷ræWrW'&÷"€¢uF†Rf÷&Vç6–2F÷&âc"&W7öç6RF–Bæ÷B6öçF–âfÆ–BÆör'&’âp¢“°¢Ð ¢6öç7BÆ–æ·2Ð¢§6öãòåöÖWFFFòæÆ–æ·3° ¢–b€¢6÷W&6RæÆVæwF‚ãÐ¢•ôÄ”Ô•BÇÀ¢Æ–æ·2ÇÀ¢G—VöbÆ–æ·2ÓÒvö&¦V7BrÇÀ¢'&’æ—4'&’€¢Æ–æ·0¢’ÇÀ¢ö&¦V7Bç&÷F÷G—Ræ†4÷vå&÷W'G’æ6ÆÂ€¢Æ–æ·2À¢w&Wbp¢’ÇÀ¢ö&¦V7Bç&÷F÷G—Ræ†4÷vå&÷W'G’æ6ÆÂ€¢Æ–æ·2À¢væW‡Bp¢’ÇÀ¢Æ–æ·2ç&WbÓÒçVÆÂÇÀ¢Æ–æ·2ææW‡BÓÒçVÆÀ¢’°¢F‡&÷ræWrW'&÷"€¢uF†Rf÷&Vç6–2v–æF÷r—26GW&FVB÷"v–æFVBÂ6òöæRF—&V7B&WVW7B6ææ÷B–æFWVæFVçFÇ’&÷fRF†—2v–æF÷râæò6öæ6ÇW6–öâv2G&vââp¢“°¢Ð ¢6öç7BÆ—fTÆöw2Ð¢æ÷&ÖÆ—¦Uc$Æöw2€¢§6öà¢“° ¢–b€¢Æ—fTÆöw2æÆVæwF‚ÓÐ¢6÷W&6RæÆVæwF€¢’°¢F‡&÷ræWrW'&÷"€¢uF†Rf÷&Vç6–2F÷&âc"&W7öç6R6öçF–æVBÖÆf÷&ÖVBÆörVçG'’âp¢“°¢Ð ¢f÷"€¢6öç7BÆöp¢öbÆ—fTÆöw0¢’°¢–b€¢çVÖ&W"æ—56fT–çFVvW"€¢ÆörçF–ÖW7F× ¢’ÇÀ¢ÆörçF–ÖW7F×ÃÐ¢6öæf–ræg&öÒÇÀ¢ÆörçF–ÖW7F×à¢6öæf–rçFð¢’°¢F‡&÷ræWrW'&÷"€¢F†Rf÷&Vç6–2F÷&âc"&W7öç6R&WGW&æVBÆörG¶Æöræ–GÒ÷WG6–FRF†RW†7BF–væ÷7F–2v–æF÷ræ ¢“°¢Ð¢Ð ¢6öç7B7F÷&VEv–æF÷rÐ¢7F÷&VDÆöw2æf–ÇFW"€¢ÆörÓà¢çVÖ&W"æ—56fT–çFVvW"€¢ÆösòçF–ÖW7F× ¢’b`¢ÆörçF–ÖW7F×à¢6öæf–ræg&öÒb`¢ÆörçF–ÖW7F×ÃÐ¢6öæf–rçFð¢“° ¢6öç7B7F÷&VD'”–BÐ¢æWrÖ€¢7F÷&VEv–æF÷ræÖ€¢ÆörÓâ°¢7G&–ær€¢Æöræ–@¢’À¢Æöp¢Ð¢¢“° ¢6öç7BÆ—fT'”–BÐ¢æWrÖ€¢Æ—fTÆöw2æÖ€¢ÆörÓâ°¢7G&–ær€¢Æöræ–@¢’À¢Æöp¢Ð¢¢“° ¢6öç7B7F÷&VDöæÇ”–G2Ð¢µÓ° ¢6öç7B”öæÇ”–G2Ð¢µÓ° ¢6öç7B6öæfÆ–7D–G2Ð¢µÓ° ¢ÆWB6öæf—&ÖVD7W'&VçBÐ¢° ¢f÷"€¢6öç7B°¢–BÀ¢7F÷&VDÆöp¢Ð¢öb7F÷&VD'”–@¢’°¢6öç7BÆ—fTÆörÐ¢Æ—fT'”–BævWB€¢–@¢“° ¢–b€¢Æ—fTÆöp¢’°¢7F÷&VDöæÇ”–G2çW6‚€¢–@¢“°¢6öçF–çVS°¢Ð ¢–b€¢†—7F÷'”Æöw4WVÂ€¢†—7F÷'”Æöuv—F†÷WE&t&6†—fR€¢7F÷&VDÆöp¢’À¢†—7F÷'”Æöuv—F†÷WE&t&6†—fR€¢Æ—fTÆöp¢¢¢’°¢6öæf—&ÖVD7W'&VçB²³°¢ÒVÇ6R°¢6öæfÆ–7D–G2çW6‚€¢–@¢“°¢Ð¢Ð ¢f÷"€¢6öç7B–@¢öbÆ—fT'”–Bæ¶W—2‚¢’°¢–b€¢7F÷&VD'”–Bæ†2€¢–@¢¢’°¢”öæÇ”–G2çW6‚€¢–@¢“°¢Ð¢Ð ¢7F÷&VDöæÇ”–G2ç6÷'B‚“°¢”öæÇ”–G2ç6÷'B‚“°¢6öæfÆ–7D–G2ç6÷'B‚“° ¢6öç7BF&vWE7F÷&VBÐ¢7F÷&VD'”–BævWB€¢6öæf–rçF&vWEö–@¢’ÇÀ¢çVÆÃ° ¢6öç7BF&vWDÆ—fRÐ¢Æ—fT'”–BævWB€¢6öæf–rçF&vWEö–@¢’ÇÀ¢çVÆÃ° ¢ÆWBF&vWE7FGW2Ð¢v'6VçEö&÷F‚s° ¢–b€¢F&vWE7F÷&VBb`¢F&vWDÆ—fP¢’°¢F&vWE7FGW2Ð¢†—7F÷'”Æöw4WVÂ€¢†—7F÷'”Æöuv—F†÷WE&t&6†—fR€¢F&vWE7F÷&V@¢’À¢†—7F÷'”Æöuv—F†÷WE&t&6†—fR€¢F&vWDÆ—fP¢¢¢òv6öæf—&ÖVEö7W'&VçBp¢¢v6öæfÆ–7Bs°¢ÒVÇ6R–b€¢F&vWE7F÷&V@¢’°¢F&vWE7FGW2Ð¢w7F÷&VEööæÇ’s°¢ÒVÇ6R–b€¢F&vWDÆ—fP¢’°¢F&vWE7FGW2Ð¢v•ööæÇ’s°¢Ð ¢6öç7B&W7VÇBÒ°¢66÷VçC¢°¢–C ¢66÷VçBæ–BÀ ¢æÖS ¢7G&–ær€¢66÷VçBææÖRóð¢rp¢¢ÒÀ ¢v–æF÷s¢°¢g&öÓ ¢6öæf–ræg&öÒÀ ¢Fó ¢6öæf–rçFð¢ÒÀ ¢6÷VçG3¢°¢7F÷&VC ¢7F÷&VEv–æF÷ræÆVæwF‚À ¢g&W6…÷c# ¢Æ—fTÆöw2æÆVæwF‚À ¢6öæf—&ÖVEö7W'&VçC ¢6öæf—&ÖVD7W'&VçBÀ ¢7F÷&VEööæÇ“ ¢7F÷&VDöæÇ”–G2æÆVæwF‚À ¢•ööæÇ“ ¢”öæÇ”–G2æÆVæwF‚À ¢6öæfÆ–7G3 ¢6öæfÆ–7D–G2æÆVæwF€¢ÒÀ ¢F&vWC¢°¢–C ¢6öæf–rçF&vWEö–BÀ ¢F–ÖW7F× ¢6öæf–rçF&vWE÷F–ÖW7F×À ¢7F÷&VE÷&W6VçC ¢&ööÆVâ€¢F&vWE7F÷&V@¢’À ¢g&W6…÷c%÷&W6VçC ¢&ööÆVâ€¢F&vWDÆ—fP¢’À ¢7FGW3 ¢F&vWE7FGW0¢ÒÀ ¢7F÷&VEööæÇ•ö–G3 ¢7F÷&VDöæÇ”–G2À ¢•ööæÇ•ö–G3 ¢”öæÇ”–G2À ¢6öæfÆ–7Eö–G3 ¢6öæfÆ–7D–G0¢Ó° ¢G&6¶W#òç6WE7FvR€¢tf÷&Vç6–26†V6²6ö×ÆWFRrÀ¢7F÷&VBG·&W7VÇBæ6÷VçG2ç7F÷&VGÒ+rg&W6‚c"G·&W7VÇBæ6÷VçG2æg&W6…÷c'Ò+rF&vWBG·&W7VÇBçF&vWBç7FGW7Ö ¢“° ¢&WGW&â&W7VÇC°¢Ð ¢gVæ7F–öâf÷&ÖD†—7F÷'”f÷&Vç6–5&W7VÇB€¢&W7VÇ@¢’°¢6öç7BF&vWE7FGW2Ð¢7G&–ær€¢&W7VÇCòçF&vWCòç7FGW2óð¢wVæ¶æ÷vâp¢¢ç&WÆ6TÆÂ€¢uòrÀ¢rp¢¢çFõWW$66R‚“° ¢6öç7B7F÷&VDöæÇ•&Wf–WrÐ¢&W7VÇBç7F÷&VEööæÇ•ö–G2æÆVæwF€¢ò&W7VÇBç7F÷&VEööæÇ•ö–G0¢ç6Æ–6R€¢À¢€¢¢æ¦ö–â‚rÂr¢¢tæöæRs° ¢6öç7B”öæÇ•&Wf–WrÐ¢&W7VÇBæ•ööæÇ•ö–G2æÆVæwF€¢ò&W7VÇBæ•ööæÇ•ö–G0¢ç6Æ–6R€¢À¢€¢¢æ¦ö–â‚rÂr¢¢tæöæRs° ¢6öç7B6öæfÆ–7E&Wf–WrÐ¢&W7VÇBæ6öæfÆ–7Eö–G2æÆVæwF€¢ò&W7VÇBæ6öæfÆ–7Eö–G0¢ç6Æ–6R€¢À¢€¢¢æ¦ö–â‚rÂr¢¢tæöæRs° ¢&WGW&â€¢u&VBÖöæÇ’†—7F÷'’f÷&Vç6–26†V6²6ö×ÆWFRåÆåÆâr°¢v–æF÷s¢G·&W7VÇBçv–æF÷ræg&ö×Ò(i"G·&W7VÇBçv–æF÷rçF÷ÕÆæ°¢7F÷&VB&V6÷&G3¢G·&W7VÇBæ6÷VçG2ç7F÷&VGÕÆæ°¢g&W6‚F÷&âc"&V6÷&G3¢G·&W7VÇBæ6÷VçG2æg&W6…÷c'ÕÆæ°¢6öæf—&ÖVB7W'&VçC¢G·&W7VÇBæ6÷VçG2æ6öæf—&ÖVEö7W'&VçGÕÆæ°¢7F÷&VBÖöæÇ“¢G·&W7VÇBæ6÷VçG2ç7F÷&VEööæÇ—ÕÆæ°¢g&W6‚ÖöæÇ“¢G·&W7VÇBæ6÷VçG2æ•ööæÇ—ÕÆæ°¢6öæfÆ–7G3¢G·&W7VÇBæ6÷VçG2æ6öæfÆ–7G7ÕÆåÆæ°¢F&vWBG·&W7VÇBçF&vWBæ–GÕÆæ°¢7F÷&VC¢G·&W7VÇBçF&vWBç7F÷&VE÷&W6VçBòu”U2r¢täòwÕÆæ°¢g&W6‚F÷&âc#¢G·&W7VÇBçF&vWBæg&W6…÷c%÷&W6VçBòu”U2r¢täòwÕÆæ°¢7FGW3¢G·F&vWE7FGW7ÕÆåÆæ°¢7F÷&VBÖöæÇ’”G3¢G·7F÷&VDöæÇ•&Wf–WwÕÆæ°¢g&W6‚ÖöæÇ’”G3¢G¶”öæÇ•&Wf–WwÕÆæ°¢6öæfÆ–7B”G3¢G¶6öæfÆ–7E&Wf–WwÕÆåÆæ°¢tæò7F÷&VB†—7F÷'’v2ÖöF–f–VBâp¢“°¢Ð ¢gVæ7F–öâ&W6öÇfU7F÷&VD†—7F÷'•G&6UF&vWB€¢7F÷&VDÆöw2À¢&WVW7FVEF&vWD–@¢’°¢6öç7BF&vWD–BÐ¢7G&–ær€¢&WVW7FVEF&vWD–Bóð¢rp¢’çG&–Ò‚“° ¢–b€¢F&vWD–@¢’°¢F‡&÷ræWrW'&÷"€¢tVçFW"F†RW†7BF÷&âÆör”B&W÷'FVB2Ö—76–ær'’gVÆÂ&V'V–ÆBâp¢“°¢Ð ¢6öç7B7F÷&VEF&vWBÐ¢7F÷&VDÆöw2æf–æB€¢ÆörÓà¢7G&–ær€¢Æösòæ–@¢’ÓÓÐ¢F&vWD–@¢“° ¢6öç7BF&vWEF–ÖW7F×Ð¢çVÖ&W"€¢7F÷&VEF&vWCòçF–ÖW7F× ¢“° ¢–b€¢7F÷&VEF&vWBÇÀ¢çVÖ&W"æ—56fT–çFVvW"€¢F&vWEF–ÖW7F× ¢’ÇÀ¢F&vWEF–ÖW7F×ÃÒ ¢’°¢F‡&÷ræWrW'&÷"€¢7F÷&VB†—7F÷'’FöW2æ÷B6öçF–âfÆ–BÆörv—F‚”BG·F&vWD–GÒæ ¢“°¢Ð ¢&WGW&â°¢–C ¢F&vWD–BÀ¢F–ÖW7F× ¢F&vWEF–ÖW7F× ¢Ó°¢Ð ¢7–æ2gVæ7F–öâ'Vä†—7F÷'•F&vWD6öÆÆV7F÷%G&6R€¢”¶W’À¢G&6¶W"ÒçVÆÂÀ¢&WVW7FVEF&vWD–BÒçVÆÀ¢’° ¢6öç7B66÷VçBÐ¢v—BFWFV7D66÷VçB€¢”¶W’À¢G&6¶W ¢“° ¢v—B76W'DWF†VçF–6FVE6–ævÆT66÷VçD÷væW"€¢66÷VçBæ–@¢“° ¢6öç7B7F÷&VDÆöw2Ð¢v—BF$ÆöDÆöw2€¢66÷VçBæ–@¢“° ¢6öç7BF&vWBÐ¢&W6öÇfU7F÷&VD†—7F÷'•G&6UF&vWB€¢7F÷&VDÆöw2À¢&WVW7FVEF&vWD–@¢“° ¢6öç7BF‡&÷Vv„FFRÐ¢FöF”Æö6Â‚“° ¢6öç7B6VvÖVçG2Ð¢7&VFU6VvÖVçG2€¢66÷VçBç6–vçWöÆö6ÅöFFRÀ¢F‡&÷Vv„FFP¢“° ¢ÆWBG&6VE6VvÖVçBÐ¢çVÆÃ°¢ÆWBG&6VDg&öÒÐ¢çVÆÃ°¢ÆWBG&6VEFòÐ¢çVÆÃ° ¢f÷"€¢6öç7B6VvÖVç@¢öb6VvÖVçG0¢’°¢6öç7Bg&öÒÐ¢ÖF‚æÖ‚€¢7F'DödF•F–ÖW7F×€¢6VvÖVçBæg&öÕöFFP¢’À¢66÷VçBç6–vçW÷F–ÖW7F×Ò¢“° ¢6öç7BFòÐ¢6VvÖVçBçFõöFFRÓÓÐ¢F‡&÷Vv„FFP¢òÖF‚æfÆö÷"€¢FFRææ÷r‚’ð¢ ¢¢¢VæDödF•F–ÖW7F×€¢6VvÖVçBçFõöFFP¢“° ¢–b€¢F&vWBçF–ÖW7F×à¢g&öÒb`¢F&vWBçF–ÖW7F×ÃÐ¢Fð¢’°¢G&6VE6VvÖVçBÐ¢6VvÖVçC°¢G&6VDg&öÒÐ¢g&öÓ°¢G&6VEFòÐ¢Fó°¢'&V³°¢Ð¢Ð ¢–b€¢G&6VE6VvÖVç@¢’°¢F‡&÷ræWrW'&÷"€¢uF†RF&vWBF÷&âÆörFöW2æ÷BfÆÂ–ç6–FRç’7W'&VçB†—7F÷'’Ö'V–ÆB6VvÖVçBâp¢“°¢Ð ¢G&6¶W#òç6WE7FvR€¢uG&6–ær&V'V–ÆB6öÆÆV7F÷.(
brÀ¢G·G&6VE6VvÖVçBæg&öÕöFFWÒ(i"G·G&6VE6VvÖVçBçFõöFFWÓ²&VBÖöæÇ’W†7B6öÆÆV7F÷"F† ¢“° ¢6öç7B6fWG•7FFRÐ¢7&VFU&ævU6fWG•7FFR‚“° ¢6fWG•7FFRæ†—7F÷'•÷F&vWE÷G&6RÐ¢7&VFT†—7F÷'•F&vWEG&6U7FFR€¢F&vWBæ–BÀ¢F&vWBçF–ÖW7F× ¢“° ¢6öç7B&W7VÇBÐ¢v—BfWF6„6ö×ÆWFU&ævR€¢”¶W’À¢G&6VDg&öÒÀ¢G&6VEFòÀ¢G&6¶W"À¢6fWG•7FFP¢“° ¢6öç7BG&6RÐ¢7VÖÖ&—¦T†—7F÷'•F&vWEG&6R€¢6fWG•7FFRæ†—7F÷'•÷F&vWE÷G&6RÀ¢&W7VÇBæÆöw0¢“° ¢6öç7B7F÷&VEF&vWBÐ¢7F÷&VDÆöw2ç6öÖR€¢ÆörÓà¢7G&–ær€¢Æösòæ–@¢’ÓÓÐ¢F&vWBæ–@¢“° ¢6öç7B÷WGWBÒ°¢66÷VçC¢°¢–C ¢66÷VçBæ–BÀ¢æÖS ¢7G&–ær€¢66÷VçBææÖRóð¢rp¢¢ÒÀ¢6VvÖVçC¢°¢g&öÕöFFS ¢G&6VE6VvÖVçBæg&öÕöFFRÀ¢FõöFFS ¢G&6VE6VvÖVçBçFõöFFRÀ¢g&öÕ÷F–ÖW7F× ¢G&6VDg&öÒÀ¢Fõ÷F–ÖW7F× ¢G&6VEFð¢ÒÀ¢7F÷&VE÷F&vWE÷&W6VçC ¢7F÷&VEF&vWBÀ¢6öÆÆV7F÷%÷&W7VÇEö6÷VçC ¢&W7VÇBæÆöw2æÆVæwF‚À¢6öÆÆV7F÷%÷&WVW7Eö6÷VçC ¢&W7VÇBç&WVW7Eö6÷VçBÀ¢6öÆÆV7F÷%÷7Æ—Eö6÷VçC ¢&W7VÇBç7Æ—Eö6÷VçBÀ¢G&6P¢Ó° ¢G&6¶W#òç6WE7FvR€¢t6öÆÆV7F÷"G&6R6ö×ÆWFRrÀ¢F&vWBG·G&6Ræ6Æ76–f–6F–öçÒ+rG·&W7VÇBç&WVW7Eö6÷VçGÒ&WVW7G2+rG·&W7VÇBç7Æ—Eö6÷VçGÒ7Æ—G6 ¢“° ¢&WGW&â÷WGWC°¢Ð ¢gVæ7F–öâf÷&ÖD†—7F÷'•F&vWD6öÆÆV7F÷%G&6R€¢&W7VÇ@¢’°¢6öç7BG&6RÐ¢&W7VÇBçG&6S° ¢6öç7B¶W”WfVçG2Ð¢G&6RæWfVçG0¢æf–ÇFW"€¢WfVçBÓà¢WfVçBç7FvRÓÓÒwvRrÇÀ¢WfVçBç7FvRÓÓÒwv–æF–öå÷7Æ—E÷&WV—&VBrÇÀ¢WfVçBç7FvRÓÓÒwv–æF–öå÷&ævUö6ö×ÆWFRrÇÀ¢WfVçBç7FvRÓÓÒw7Æ—EöÖW&vRp¢¢ç6Æ–6R€¢Ó ¢¢æÖ€¢WfVçBÓâ°¢–b€¢WfVçBç7FvRÓÓÒwvRp¢’°¢&WGW&â€¢tRG¶WfVçBç&WVW7Eög&ö×Þ(i"G¶WfVçBç&WVW7E÷F÷Ò°¢ãÒG¶WfVçBç&V6÷&Eö6÷VçGÒ6÷fW'3ÒG¶WfVçBæ6÷fW'5÷F&vWBòu’r¢tâwÒ°¢F&vWCÒG¶WfVçBç&WGW&æVE÷F&vWBòu’r¢tâwÖ ¢“°¢Ð ¢–b€¢WfVçBç7FvRÓÓÒwv–æF–öå÷7Æ—E÷&WV—&VBp¢’°¢&WGW&â€¢5Ä•B$UT•$TBG¶WfVçBç&ævUög&ö×Þ(i"G¶WfVçBç&ævU÷F÷Ò°¢F&vWBÖöâ×vSÒG¶WfVçBçvU÷&WGW&æVE÷F&vWBòu’r¢tâwÒ°¢&WF–æVBÖ&Vf÷&SÒG¶WfVçBç&WF–æVEö&Vf÷&U÷7Æ—Bòu’r¢tâwÖ ¢“°¢Ð ¢–b€¢WfVçBç7FvRÓÓÒwv–æF–öå÷&ævUö6ö×ÆWFRp¢’°¢&WGW&â€¢$ätR4ôÕÄUDRG¶WfVçBç&ævUög&ö×Þ(i"G¶WfVçBç&ævU÷F÷Ò°¢F&vWCÒG¶WfVçBç&WF–æVE÷F&vWBòu’r¢tâwÖ ¢“°¢Ð ¢&WGW&â€¢5Ä•BÔU$tRG¶WfVçBç&ævUög&ö×Þ(i"G¶WfVçBç&ævU÷F÷Ò°¢F&vWCÒG¶WfVçBç&WF–æVE÷F&vWBòu’r¢tâwÖ ¢“°¢Ð¢¢æ¦ö–â‚uÆâr“° ¢&WGW&â€¢u&VBÖöæÇ’&V'V–ÆB6öÆÆV7F÷"G&6R6ö×ÆWFRåÆåÆâr°¢6VvÖVçC¢G·&W7VÇBç6VvÖVçBæg&öÕöFFWÒ(i"G·&W7VÇBç6VvÖVçBçFõöFFWÕÆæ°¢7F÷&VBF&vWB&W6VçC¢G·&W7VÇBç7F÷&VE÷F&vWE÷&W6VçBòu”U2r¢täòwÕÆæ°¢vVV¶Ç’6öÆÆV7F÷"&V6÷&G3¢G·&W7VÇBæ6öÆÆV7F÷%÷&W7VÇEö6÷VçGÕÆæ°¢’&WVW7G3¢G·&W7VÇBæ6öÆÆV7F÷%÷&WVW7Eö6÷VçGÕÆæ°¢&ævR7Æ—G3¢G·&W7VÇBæ6öÆÆV7F÷%÷7Æ—Eö6÷VçGÕÆåÆæ°¢F&vWC¢G·G&6RçF&vWEö–GÕÆæ°¢6÷fW&–ær’vW3¢G·G&6Ræ6÷fW&–æu÷vUö6÷VçGÕÆæ°¢vW2F†B&WGW&æVBF&vWC¢G·G&6RçvU÷&WGW&æVE÷F&vWEö6÷VçGÕÆæ°¢v–æF–öâÖW&vR&WF–æVBF&vWC¢G·G&6Rçv–æF–öåöÖW&vU÷&WF–æVE÷F&vWBòu”U2r¢täòwÕÆæ°¢f–æÂvVV¶Ç’&W7VÇB&WF–æVBF&vWC¢G·G&6Ræf–æÅ÷&ævU÷&WF–æVE÷F&vWBòu”U2r¢täòwÕÆæ°¢6Æ76–f–6F–öã¢G·G&6Ræ6Æ76–f–6F–öâçFõWW$66R‚’ç&WÆ6TÆÂ‚uòrÂrr—ÕÆåÆæ°¢tÆ7B&VÆWfçBG&6RWfVçG3¥Æâr°¢G¶¶W”WfVçG2ÇÂtæöæRwÕÆåÆæ°¢tæò7F÷&VB†—7F÷'’v2ÖöF–f–VBâp¢“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òò550¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâ–æ¦V7E7G–ÆW2‚’° ¢–b€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢5E”ÄUô”@¢¢’°¢&WGW&ã°¢Ð ¢6öç7B7G–ÆRÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢w7G–ÆRp¢“° ¢7G–ÆRæ–BÐ¢5E”ÄUô”C° ¢7G–ÆRçFW‡D6öçFVçBÒ  ¢2G´%UEDôåô”GÒ°¢÷6—F–öã¢f—†VC°¢&–v‡C¢'ƒ°¢&÷GFöÓ¢“ƒ°¢¢Ö–æFWƒ¢““““““°¢FF–æs¢‚7ƒ°¢&÷&FW#¢°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3###°¢6öÆ÷#¢v†—FS°¢föçB×vV–v‡C¢s°¢&÷‚×6†F÷s¢'‚‚&v&ƒÃÃÂãCR“°¢7W'6÷#¢w&#°¢F÷V6‚Ö7F–öã¢æöæS°¢W6W"×6VÆV7C¢æöæS°¢×vV&¶—B×W6W"×6VÆV7C¢æöæS°¢Ð ¢2G´%UEDôåô”GÕ¶FFÖG&vv–æsÒ#%Ò°¢7W'6÷#¢w&&&–æs°¢Ð ¢2G´ÔôDÅô”GÒ°¢÷6—F–öã¢f—†VC°¢–ç6WC¢°¢¢Ö–æFWƒ¢°¢F—7Æ“¢fÆWƒ°¢§W7F–g’Ö6öçFVçC¢6VçFW#°¢Æ–vâÖ—FV×3¢6VçFW#°¢FF–æs¢'ƒ°¢&6¶w&÷VæC¢&v&ƒÃÃÂãƒB“°¢Ð ¢2G´ÔôDÅô”GÒæ6&B°¢F—7Æ“¢fÆWƒ°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢v–GFƒ¢Ö–âƒs#‚ÃR“°¢†V–v‡C¢“Gfƒ°¢Ö‚Ö†V–v‡C¢“Gfƒ°¢÷fW&fÆ÷s¢†–FFVã°¢FF–æs¢°¢&÷&FW"×&F—W3¢'ƒ°¢&6¶w&÷VæC¢3ƒƒƒ°¢6öÆ÷#¢6VVS°¢Ð ¢2G´ÔôDÅô”GÒƒ"°¢Ö&v–ã¢°¢föçB×6—¦S¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖöFÂÖ†VFW"°¢fÆWƒ¢WFó°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢'ƒ°¢FF–æs¢'‚gƒ°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B3333°¢&6¶w&÷VæC¢3###°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖöFÂÖ†VFW"ƒ"°¢fÆWƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖöFÂÖ6Æ÷6R°¢v–GFƒ¢WFó°¢Ö–â×v–GFƒ¢s'ƒ°¢Ö–âÖ†V–v‡C¢3‡ƒ°¢Ö&v–ã¢°¢FF–æs¢w‚'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖöFÂ×67&öÆÂ°¢Ö–âÖ†V–v‡C¢°¢÷fW&fÆ÷r×ƒ¢†–FFVã°¢÷fW&fÆ÷r×“¢WFó°¢FF–æs¢gƒ°¢÷fW'67&öÆÂÖ&V†f–÷#¢6öçF–ã°¢×vV&¶—BÖ÷fW&fÆ÷r×67&öÆÆ–æs¢F÷V6ƒ°¢Ð ¢2G´ÔôDÅô”GÒç7V"°¢Ö&v–âÖ&÷GFöÓ¢'ƒ°¢föçB×6—¦S¢7ƒ°¢Æ–æRÖ†V–v‡C¢ãS°¢÷6—G“¢ãsS°¢Ð ¢2G´ÔôDÅô”GÒçæVÂ°¢FF–æs¢ƒ°¢Ö&v–âÖ&÷GFöÓ¢ƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3°¢Ð ¢2G´ÔôDÅô”GÒ'WGFöâÀ¢2G´ÔôDÅô”GÒ–çWBÀ¢2G´ÔôDÅô”GÒ6VÆV7B°¢&÷‚×6—¦–æs¢&÷&FW"Ö&÷ƒ°¢v–GFƒ¢S°¢Ö–âÖ†V–v‡C¢C'ƒ°¢Ö&v–ã¢g‚—ƒ°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B3SSS°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3°¢6öÆ÷#¢6ffc°¢Ð ¢2G´ÔôDÅô”GÒ'WGFöâ°¢&6¶w&÷VæC¢3333°¢föçB×vV–v‡C¢s°¢Ð ¢2G´ÔôDÅô”GÒ'WGFöã¦F—6&ÆVB°¢÷6—G“¢ãC°¢Ð ¢2G´ÔôDÅô”GÒæ7F–öç2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g"g#°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF÷°¢F—7Æ“¢fÆWƒ°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢föçB×vV–v‡C¢s°¢Ð ¢2G´ÔôDÅô”GÒçG&6²°¢†V–v‡C¢'ƒ°¢Ö&v–ã¢‡‚°¢&÷&FW"×&F—W3¢““—ƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&6¶w&÷VæC¢3#“#“#“°¢Ð ¢2G´ÔôDÅô”GÒæf–ÆÂ°¢v–GFƒ¢S°¢†V–v‡C¢S°¢&6¶w&÷VæC¢6°¢G&ç6—F–öã¢v–GF‚ã'2V6S°¢Ð ¢2G´ÔôDÅô”GÒç7FG2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g"g#°¢v¢W‚'ƒ°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒç6ÖÆÂ°¢Ö&v–ã¢g‚°¢föçB×6—¦S¢'ƒ°¢÷6—G“¢ãsƒ°¢Ð ¢2G´ÔôDÅô”GÒç6WGW°¢FF–æs¢'ƒ°¢Ö&v–âÖ&÷GFöÓ¢ƒ°¢&÷&FW#¢‚6öÆ–B3SSS°¢&÷&FW"×&F—W3¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâ°¢Ö&v–ã¢'‚°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B3666°¢&÷&FW"×&F—W3¢ƒ°¢&6¶w&÷VæC¢3°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâ×7VÖÖ'’×&÷r°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢ƒ°¢Ö–âÖ†V–v‡C¢Cgƒ°¢FF–æs¢‚'ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢W6W"×6VÆV7C¢æöæS°¢×vV&¶—B×W6W"×6VÆV7C¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâ×7VÖÖ'’×&÷s£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâ×7VÖÖ'’×&÷s£¦gFW"°¢6öçFVçC¢~)kâs°¢Ö&v–âÖÆVgC¢'ƒ°¢föçB×6—¦S¢7ƒ°¢÷6—G“¢ãs°¢G&ç6—F–öã¢G&ç6f÷&ÒãW2V6S°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öã¦æ÷B…¶÷VåÒ’çF×6V7F–öâ×7VÖÖ'’×&÷s£¦gFW"°¢G&ç6f÷&Ó¢&÷FFR‚Ó“FVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâ×F—FÆR°¢föçB×6—¦S¢Wƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâÖÖWF°¢Ö&v–âÖÆVgC¢WFó°¢FW‡BÖÆ–vã¢&–v‡C°¢föçB×6—¦S¢'ƒ°¢÷6—G“¢ãcS°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâÖ&öG’°¢FF–æs¢'‚'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76RÖ&öG’°¢FF–ær×F÷¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76RÖ&öG’âçF×6V7F–öâ°¢Ö&v–ã¢‡‚°¢&÷&FW"Ö6öÆ÷#¢3333°¢&6¶w&÷VæC¢3333°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76RÖ&öG’âçF×6V7F–öã¦Æ7BÖ6†–ÆB°¢Ö&v–âÖ&÷GFöÓ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76RÖ&öG’âçF×6V7F–öâçF×6V7F–öâ×F—FÆR°¢föçB×6—¦S¢Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×6V7F–öâçF×6V7F–öâÖ&öG’°¢FF–ær×F÷¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×6V7F–öâçFÖWFöÖF–2×7–æ2Ö'W7’çF×6V7F–öâÖ&öG’°¢÷6—G“¢ãcƒ°¢ö–çFW"ÖWfVçG3¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2Öw&÷W²çF×6WGF–æw2Öw&÷W°¢Ö&v–â×F÷¢'ƒ°¢FF–ær×F÷¢'ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3333°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖÆ&VÂ°¢F—7Æ“¢&Æö6³°¢Ö&v–âÖ&÷GFöÓ¢Gƒ°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢÷6—G“¢ãsS°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×7FGW2×7G&—°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢FF–æs¢—‚ƒ°¢&÷&FW#¢‚6öÆ–B3336°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SS#°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×7FGW2×7G&—â"°¢fÆWƒ¢WFó°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×7FGW2×7G&—âç6ÖÆÂ°¢Ö&v–ã¢°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒæ7F–öç2çF×6WGF–æw2×&–Ö'’Ö7F–öç2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢wƒ°¢Ö&v–â×F÷¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×&–Ö'’Ö7F–öç2â'WGFöâ°¢Ö–âÖ†V–v‡C¢Cƒ°¢Ö&v–ã¢°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2Ö7F–öâ×v–FR°¢w&–BÖ6öÇVÖã¢òÓ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB°¢Ö&v–â×F÷¢'ƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B33C3C6S°¢&÷&FW"×&F—W3¢—ƒ°¢&6¶w&÷VæC¢3##ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢—ƒ°¢Ö–âÖ†V–v‡C¢C‡ƒ°¢FF–æs¢—‚ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"À¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂâ7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'’â7â°¢F—7Æ“¢w&–C°¢v¢'ƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'’6ÖÆÂ°¢÷fW&fÆ÷s¢†–FFVã°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢S°¢÷6—G“¢ãc#°¢FW‡BÖ÷fW&fÆ÷s¢VÆÆ—6—3°¢v†—FR×76S¢æ÷w&°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'’â7G&öær°¢Ö&v–âÖÆVgC¢WFó°¢FF–æs¢G‚wƒ°¢&÷&FW#¢‚6öÆ–B36SS“Cs°¢&÷&FW"×&F—W3¢““—ƒ°¢&6¶w&÷VæC¢3S#“°¢6öÆ÷#¢6#–C†3°¢föçB×6—¦S¢ƒ°¢v†—FR×76S¢æ÷w&°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(ÈBs°¢6öÆ÷#¢6°¢föçB×6—¦S¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VE¶÷VåÒâçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'“£¦gFW"°¢G&ç6f÷&Ó¢&÷FFRƒƒFVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VE¶÷VåÒâçF×6WGF–æw2ÖGfæ6VB×7VÖÖ'’°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B3336°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2ÖGfæ6VBÖ&öG’°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢FF–æs¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖF–væ÷7F–72Ö÷fW'f–Wr°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B33CC36°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3“C°¢Ð ¢2G´ÔôDÅô”GÒçFÖF–væ÷7F–72Ö÷fW'f–Wrâ'WGFöâ°¢Ö–âÖ†V–v‡C¢3‡ƒ°¢Ö&v–ã¢w‚°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B3333ƒ°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SS°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂâ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢Ö–âÖ†V–v‡C¢C'ƒ°¢FF–æs¢—ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂâ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(ÈBs°¢Ö&v–âÖÆVgC¢WFó°¢6öÆ÷#¢3“““°¢föçB×6—¦S¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÅ¶÷VåÒâ7VÖÖ'“£¦gFW"°¢G&ç6f÷&Ó¢&÷FFRƒƒFVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂÖ&öG’°¢FF–æs¢—ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3&C&C3S°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂÖ&öG’â'WGFöâ°¢Ö–âÖ†V–v‡C¢Cƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×FööÂÖF—f–FW"°¢Ö&v–ã¢‚°¢&÷&FW"×F÷¢‚6öÆ–B3333ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×6æ6†÷BÖ6†V6²Ö÷WGWBÀ¢2G´ÔôDÅô”GÒçFÖ†–æW72Ö6GW&RÖ÷WGWBÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6†V6·ö–çBÖ6æ'’Ö÷WGWB°¢Ö&v–â×F÷¢‡ƒ°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B36#CcS°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3s#°¢6öÆ÷#¢6CvS&Sƒ°¢Æ–æRÖ†V–v‡C¢ãS°¢v†—FR×76S¢&RÖÆ–æS°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâÖ–çG&ò°¢Ö&v–ã¢'ƒ°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ãS°¢÷6—G“¢ãcS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7FGW2À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&ö¦V7F–öâ°¢Ö&v–ã¢'ƒ°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SSS°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×ÆâÖ6&B°¢Ö&v–ã¢'ƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B3V#C“3°¢&÷&FW"ÖÆVgC¢G‚6öÆ–B63ƒ–#CS°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3ƒCc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×Æâ×–6¶W"°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢FF–æs¢‡‚ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×Æâ×–6¶W"â7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖæW‡B×7FWâ7â°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ãVVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢÷6—G“¢ãc#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×Æâ×–6¶W"6VÆV7B°¢&÷‚×6—¦–æs¢&÷&FW"Ö&÷ƒ°¢v–GFƒ¢Ö–âƒ“‚ÂS‚R“°¢Ö–âÖ†V–v‡C¢3gƒ°¢FF–æs¢w‚—ƒ°¢&÷&FW#¢‚6öÆ–B3ccSS3c°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3###°¢6öÆ÷#¢6ffc°¢föçC¢–æ†W&—C°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢s°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖæW‡B×7FW°¢F—7Æ“¢w&–C°¢v¢7ƒ°¢FF–æs¢‡‚‚ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3C3Cc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖæW‡B×7FW7G&öær°¢föçB×6—¦S¢Gƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖæW‡B×7FW6ÖÆÂ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢÷6—G“¢ãsC°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢FF–æs¢ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3C3Cc°¢&6¶w&÷VæC¢&v&ƒÂÂÂã"“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×W'÷6RÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FRÖæ÷FRÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2°¢Ö&v–ã¢°¢6öÆ÷#¢6C–C–C“°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×W'÷6R7G&öær°¢F—7Æ“¢&Æö6³°¢Ö&v–âÖ&÷GFöÓ¢'ƒ°¢6öÆ÷#¢6ccc°¢föçB×6—¦S¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FRÖÆ—7BÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2VÂÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6RöÂ°¢Ö&v–ã¢°¢FF–æs¢°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×&÷r°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒ“g‚Âãvg"’Ö–æÖ‚ƒÂã6g"“°¢v¢‡ƒ°¢FF–æs¢w‚°¢&÷&FW"×F÷¢‚6öÆ–B&v&ƒ#SRÂ#SRÂ#SRÂãr“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×&÷râ7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2Æ’â7â°¢6öÆ÷#¢6°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×&÷râ"À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2Æ’â"°¢6öÆ÷#¢6SVSVSS°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FRÖ6ö×ÆWFRâ"°¢6öÆ÷#¢3ƒ63“–3°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FRÖ7F–öââ"°¢6öÆ÷#¢6SF&#cƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖwV–FR×Væ¶æ÷vââ"°¢6öÆ÷#¢3–&&&C°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6R°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B&v&ƒ#ÂSRÂc’Âã3"“°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢&v&ƒÂÂÂã‚“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6Râ7G&öær°¢F—7Æ“¢&Æö6³°¢Ö&v–âÖ&÷GFöÓ¢gƒ°¢6öÆ÷#¢6Sf3cƒ°¢föçB×6—¦S¢ƒ°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6RöÂ°¢F—7Æ“¢w&–C°¢v¢Wƒ°¢6÷VçFW"×&W6WC¢FÖ§V××7FW°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6RÆ’°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢#‚Ö–æÖ‚ƒÂg"“°¢v¢gƒ°¢6öÆ÷#¢6FFC°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢6÷VçFW"Ö–æ7&VÖVçC¢FÖ§V××7FW°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××6WVVæ6RÆ“£¦&Vf÷&R°¢6öçFVçC¢6÷VçFW"‡FÖ§V××7FW“°¢6öÆ÷#¢63–f°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2°¢&÷&FW"×F÷¢‚6öÆ–B&v&ƒ#SRÂ#SRÂ#SRÂã‚“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2â7VÖÖ'’À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö–âÖ†V–v‡C¢C'ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2â7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââ7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2â7VÖÖ'’â7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââ7VÖÖ'’â7â°¢6öÆ÷#¢6SVSVSS°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2â7VÖÖ'’â"À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââ7VÖÖ'’â"°¢6öÆ÷#¢6°¢föçB×6—¦S¢ƒ°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2VÂ°¢FF–ærÖ&÷GFöÓ¢wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2Æ’°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"’WFó°¢v¢7‚‡ƒ°¢FF–æs¢g‚°¢&÷&FW"×F÷¢‚6öÆ–B&v&ƒ#SRÂ#SRÂ#SRÂãb“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7WÆ–W2Æ’â6ÖÆÂ°¢w&–BÖ6öÇVÖã¢òÓ°¢6öÆ÷#¢3“““°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öâ°¢&÷&FW"×F÷¢‚6öÆ–B3C3Cc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öââ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö–âÖ†V–v‡C¢C'ƒ°¢FF–æs¢ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öââ7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öââ7VÖÖ'’â7â°¢6öÆ÷#¢6S†S†Sƒ°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öââ7VÖÖ'’â"°¢6öÆ÷#¢63–f°¢föçB×6—¦S¢ƒ°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öââ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(ÈBs°¢6öÆ÷#¢6°¢föçB×6—¦S¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"ÖW‡ÆæF–öå¶÷VåÒâ7VÖÖ'“£¦gFW"°¢G&ç6f÷&Ó¢&÷FFRƒƒFVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"Ö&öG’°¢F—7Æ“¢w&–C°¢v¢°¢FF–æs¢‚—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"×&÷r°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢sg‚Ö–æÖ‚ƒÂg"“°¢v¢‡ƒ°¢FF–æs¢w‚°¢&÷&FW"×F÷¢‚6öÆ–B&v&ƒ#SRÂ#SRÂ#SRÂãr“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"×&÷râ7â°¢6öÆ÷#¢63–f°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"×&÷râ°¢Ö&v–ã¢°¢6öÆ÷#¢6FFC°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC#°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢v†—FR×76S¢&RÖÆ–æS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×Æâ×&VG’°¢&÷&FW"ÖÆVgBÖ6öÆ÷#¢6CfƒFS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×Æâ×v—B°¢&÷&FW"ÖÆVgBÖ6öÆ÷#¢3–cv#6#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×ÆâÖ–æfò°¢&÷&FW"ÖÆVgBÖ6öÆ÷#¢3cc“–&#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢ƒ°¢Ö&v–ã¢'‚°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ2Æ&VÂÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&ö¦V7F–öâ°¢F—7Æ“¢w&–C°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ2Æ&VÂâ7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&ö¦V7F–öââ7â°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãcƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ26VÆV7BÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ2–çWB°¢&÷‚×6—¦–æs¢&÷&FW"Ö&÷ƒ°¢v–GFƒ¢S°¢Ö–âÖ†V–v‡C¢Cƒ°¢FF–æs¢‡ƒ°¢&÷&FW#¢‚6öÆ–B3SSS°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3###°¢6öÆ÷#¢6ffc°¢föçC¢–æ†W&—C°¢Ð ¢ÖVF–†Ö‚×v–GFƒ¢S#‚’°¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6öçG&öÇ2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖGf—6÷"×&÷r°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢c‡‚Ö–æÖ‚ƒÂg"“°¢Ð¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2Ö6öçG&öÂ°¢Ö&v–ã¢'ƒ°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2×F÷Æ–æR°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2×F÷Æ–æRâ7â°¢fÆWƒ¢WFó°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2Ö÷F–öç2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g"g#°¢v¢gƒ°¢v–GFƒ¢Ö–âƒ3#‚ÂsR“°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2Ö÷F–öç2'WGFöâ°¢v–GFƒ¢S°¢Ö–âÖ†V–v‡C¢3gƒ°¢Ö&v–ã¢°¢FF–æs¢w‚—ƒ°¢&÷&FW"Ö6öÆ÷#¢3CCC°¢föçB×6—¦S¢'ƒ°¢÷6—G“¢ãs#°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2Ö÷F–öç2'WGFöâçF×F–ÖRÖ&6—2Ö7F—fR°¢&÷&FW"Ö6öÆ÷#¢6°¢&6¶w&÷VæC¢3CCC°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×F–ÖRÖ&6—2Ö6öçFW‡B°¢Ö&v–â×F÷¢wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢÷6—G“¢ãs°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2Öw&–B°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢v¢wƒ°¢Ö&v–âÖ&÷GFöÓ¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2Ö6&B°¢Ö–â×v–GFƒ¢°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B3&c&c&c°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3ccc°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2ÖÆ&VÂ°¢föçB×6—¦S¢ƒ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢ÆWGFW"×76–æs¢ãFVÓ°¢÷6—G“¢ãSS°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2×fÇVR°¢Ö&v–â×F÷¢7ƒ°¢föçB×6—¦S¢wƒ°¢föçB×vV–v‡C¢ƒ°¢Æ–æRÖ†V–v‡C¢ã°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2Öæ÷FR°¢Ö&v–â×F÷¢Wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢÷6—G“¢ãSƒ°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6&B°¢Ö&v–â×F÷¢‡ƒ°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B3&c&c&c°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3CCC°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ†VF–ær°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö&v–âÖ&÷GFöÓ¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ†VF–ær7ã¦f—'7BÖ6†–ÆB°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ†VF–ær7ã¦Æ7BÖ6†–ÆB°¢FW‡BÖÆ–vã¢&–v‡C°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãSS°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×67&öÆÂ°¢÷fW&fÆ÷s¢†–FFVã°¢FF–ærÖ&÷GFöÓ¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖç2°¢F—7Æ“¢w&–C°¢Æ–vâÖ—FV×3¢VæC°¢v¢Gƒ°¢v–GFƒ¢S°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢#gƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖç2ÖF–Ç’À¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖç2Ö†÷W&Ç’°¢v–GFƒ¢S°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖâ°¢F—7Æ“¢fÆWƒ°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢§W7F–g’Ö6öçFVçC¢fÆW‚ÖVæC°¢Ö–â×v–GFƒ¢°¢†V–v‡C¢3'ƒ°¢&÷&FW"×&F—W3¢Wƒ°¢FW‡BÖÆ–vã¢6VçFW#°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖå¶FF×FÖFWF–ÅÒ°¢7W'6÷#¢ö–çFW#°¢F÷V6‚Ö7F–öã¢Öæ—VÆF–öã°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖå¶FF×FÖFWF–ÅÓ¦fö7W2×f—6–&ÆR°¢÷WFÆ–æS¢‚6öÆ–B3ƒƒƒ°¢÷WFÆ–æRÖöfg6WC¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖâÖ7F—fRçFÖ6†'B×&–Â°¢÷WFÆ–æS¢‚6öÆ–B3ƒƒƒ°¢÷WFÆ–æRÖöfg6WC¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ6öÇVÖâ×'F–ÂçFÖ6†'B×&–Â°¢&÷&FW#¢‚F6†VB3ccc°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×fÇVR°¢Ö–âÖ†V–v‡C¢gƒ°¢Ö&v–âÖ&÷GFöÓ¢7ƒ°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãc#°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×&–Â°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢fÆW‚ÖVæC°¢§W7F–g’Ö6öçFVçC¢6VçFW#°¢†V–v‡C¢s‡ƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW"×&F—W3¢Gƒ°¢&6¶w&÷VæC¢3CCC°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖ&"°¢v–GFƒ¢c‚S°¢Ö–âÖ†V–v‡C¢°¢&÷&FW"×&F—W3¢7‚7‚°¢&6¶w&÷VæC¢3“““°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖÆ&VÂ°¢Ö&v–â×F÷¢Gƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã#°¢v†—FR×76S¢æ÷w&°¢÷6—G“¢ãSƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×&ævRÖÆ&VÂ°¢Ö–âÖ†V–v‡C¢#Wƒ°¢föçB×6—¦S¢—ƒ°¢v†—FR×76S¢æ÷&ÖÃ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×&ævRÖÆ&VÂ7â°¢F—7Æ“¢&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'B×'F–ÂÖ&FvR°¢F—7Æ“¢&Æö6³°¢Ö&v–â×F÷¢'ƒ°¢föçB×6—¦S¢‡ƒ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ã&VÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢÷6—G“¢ãs#°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6†'BÖFWF–Â°¢Ö–âÖ†V–v‡C¢#ƒ°¢Ö&v–â×F÷¢‡ƒ°¢FF–æs¢‡‚ƒ°¢&÷&FW#¢‚6öÆ–B3#“#“#“°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢3°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢÷6—G“¢ãsƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×÷7BÖ6†'BÖ6öçG&öÇ2°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢Ö&v–â×F÷¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×÷7BÖ6†'BÖ6öçG&öÇ2çF×7FB×F÷FÂÖ6öçG&öÇ2À¢2G´ÔôDÅô”GÒçF×7FB×÷7BÖ6†'BÖ6öçG&öÇ2çF×7FBÖv–â×66÷R°¢Ö&v–ã¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2°¢Ö&v–ã¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2Æ&VÂ°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒc‡‚ÂWFò’Ö–æÖ‚ƒÂg"“°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢‡ƒ°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ26VÆV7B°¢Ö–âÖ†V–v‡C¢3Gƒ°¢FF–æs¢g‚‡ƒ°¢&÷&FW#¢‚6öÆ–B3CCC°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢3sss°¢6öÆ÷#¢–æ†W&—C°¢föçC¢–æ†W&—C°¢Ð¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷R°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢Ö&v–ã¢‚°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷RÖ6öçG&öÇ2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷RÖ6öçG&öÇ2'WGFöâ°¢Ö–âÖ†V–v‡C¢3Gƒ°¢Ö&v–ã¢°¢FF–æs¢g‚‡ƒ°¢&÷&FW"Ö6öÆ÷#¢3CCC°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãs°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷RÖ6öçG&öÇ2'WGFöâçF×7FBÖv–â×66÷RÖ7F—fR°¢&÷&FW"Ö6öÆ÷#¢6FFC°¢&6¶w&÷VæC¢3666°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×&–Ö'’°¢Ö–âÖ†V–v‡C¢sGƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÖ÷&RÖFWF–Ç2°¢Ö&v–â×F÷¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2'WGFöâ°¢Ö–âÖ†V–v‡C¢3Gƒ°¢Ö&v–ã¢°¢FF–æs¢g‚‡ƒ°¢&÷&FW"Ö6öÆ÷#¢3CCC°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãs°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2'WGFöâçF×7FB×F÷FÂÖfö7W2Ö7F—fR°¢&÷&FW"Ö6öÆ÷#¢6FFC°¢&6¶w&÷VæC¢3666°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂ×7fr°¢F—7Æ“¢&Æö6³°¢v–GFƒ¢S°¢†V–v‡C¢WFó°¢÷fW&fÆ÷s¢f—6–&ÆS°¢7W'6÷#¢ö–çFW#°¢F÷V6‚Ö7F–öã¢Öæ—VÆF–öã°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ†—2°¢7G&ö¶S¢3SSS°¢7G&ö¶R×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖwV–FR°¢7G&ö¶S¢3CSCSCS°¢7G&ö¶R×v–GFƒ¢°¢7G&ö¶RÖF6†'&“¢RS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ&"°¢f–ÆÃ¢3sss°¢÷6—G“¢ãsƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ&"×†æ‚°¢f–ÆÃ¢3Fc–F6S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ&"×ö–çB×&Vf–ÆÂ°¢f–ÆÃ¢3–svCC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ&"ÖÖ—†VB°¢f–ÆÃ¢W&Â‚7F×7FBÖÖ—†VBÖVæW&w’“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ&"×6÷W&6R×Væ6ÆV"°¢f–ÆÃ¢3sss°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ&"×6÷W&6R×Væf–Æ&ÆR°¢f–ÆÃ¢3FcS“c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ†’Ö§V×ÖÖ&¶W"°¢f–ÆÃ¢6cF3sf#°¢7G&ö¶S¢3&#C3°¢7G&ö¶R×v–GFƒ¢#°¢ö–çFW"ÖWfVçG3¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ&"çF×7FB×6W76–öâÖ7F—fR°¢÷6—G“¢°¢7G&ö¶S¢6ffSS°¢7G&ö¶R×v–GFƒ¢#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ–æR°¢f–ÆÃ¢æöæS°¢7G&ö¶S¢6c&c&c#°¢7G&ö¶R×v–GFƒ¢3°¢7G&ö¶RÖÆ–æV6¢&÷VæC°¢7G&ö¶RÖÆ–æV¦ö–ã¢&÷VæC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂ×ö–çB°¢f–ÆÃ¢6c&c&c#°¢ö–çFW"ÖWfVçG3¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂ×ö–çBçF×7FB×6W76–öâÖ7F—fR°¢f–ÆÃ¢6F&ƒSC°¢7G&ö¶S¢6ffcC°¢7G&ö¶R×v–GFƒ¢3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ†—BÀ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ&"Ö†—B°¢f–ÆÃ¢G&ç7&VçC°¢7W'6÷#¢ö–çFW#°¢F÷V6‚Ö7F–öã¢Öæ—VÆF–öã°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ†—C¦fö7W2×f—6–&ÆR°¢f–ÆÃ¢&v&ƒ#SRÂ#SRÂ#SRÂãb“°¢÷WFÆ–æS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ&"Ö†—B°¢ö–çFW"ÖWfVçG3¢ÆÃ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ&VÂ°¢f–ÆÃ¢6°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆVvVæB°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢v¢g‚ƒ°¢Ö&v–â×F÷¢Gƒ°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãƒ#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆVvVæB7â°¢F—7Æ“¢–æÆ–æRÖfÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆVvVæB’°¢F—7Æ“¢–æÆ–æRÖ&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ–æRÖ¶W’°¢v–GFƒ¢gƒ°¢†V–v‡C¢7ƒ°¢&÷&FW"×&F—W3¢—ƒ°¢&6¶w&÷VæC¢6c&c&c#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’À¢2G´ÔôDÅô”GÒçF×7FBÖ†’Ö§V×Ö¶W’°¢v–GFƒ¢ƒ°¢†V–v‡C¢ƒ°¢&÷&FW"×&F—W3¢'ƒ°¢&6¶w&÷VæC¢3sss°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’×†æ‚°¢&6¶w&÷VæC¢3Fc–F6S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’×ö–çB×&Vf–ÆÂ°¢&6¶w&÷VæC¢3–svCC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’ÖÖ—†VB°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3Fc–F6RC‚RÂ3–svCBS"RR“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’×6÷W&6R×Væ6ÆV"°¢&6¶w&÷VæC¢3sss°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’×6÷W&6R×Væf–Æ&ÆR°¢&6¶w&÷VæC¢3FcS“c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ†’Ö§V×Ö¶W’°¢v–GFƒ¢‡ƒ°¢†V–v‡C¢‡ƒ°¢&÷&FW#¢'‚6öÆ–B3&#C3°¢&÷&FW"×&F—W3¢SS°¢&6¶w&÷VæC¢6cF3sf#°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’ÖÆ—7B°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’×F÷Æ–æR°¢F—7Æ“¢fÆWƒ°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢Ö&v–âÖ&÷GFöÓ¢Gƒ°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’×F÷Æ–æR7ã¦f—'7BÖ6†–ÆB°¢Ö–â×v–GFƒ¢°¢÷fW&fÆ÷s¢†–FFVã°¢FW‡BÖ÷fW&fÆ÷s¢VÆÆ—6—3°¢v†—FR×76S¢æ÷w&°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’×F÷Æ–æR7ã¦Æ7BÖ6†–ÆB°¢fÆWƒ¢WFó°¢÷6—G“¢ãSƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’×G&6²°¢†V–v‡C¢wƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW"×&F—W3¢““—ƒ°¢&6¶w&÷VæC¢3###°¢Ð ¢2G´ÔôDÅô”GÒçFÖ6FVv÷'’Öf–ÆÂ°¢†V–v‡C¢S°¢&÷&FW"×&F—W3¢–æ†W&—C°¢&6¶w&÷VæC¢3ƒƒƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g"g#°¢v¢wƒ°¢Ö&v–â×F÷¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–BâF—b°¢FF–æs¢‡ƒ°¢&÷&FW#¢‚6öÆ–B3&#&#&#°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3333°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B7âÀ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B"°¢F—7Æ“¢&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B7â°¢Ö&v–âÖ&÷GFöÓ¢Gƒ°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãS°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B"°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw&–B°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢‡ƒ°¢Ö&v–ã¢‚°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&B°¢Ö–â×v–GFƒ¢°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&B×F—FÆR°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖv–â°¢Ö&v–ã¢W‚—ƒ°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢Æ–æRÖ†V–v‡C¢ã°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖw&–B°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g"g#°¢v¢w‚ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖw&–B7âÀ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖw&–B"°¢F—7Æ“¢&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖw&–B7â°¢Ö&v–âÖ&÷GFöÓ¢'ƒ°¢föçB×6—¦S¢ƒ°¢÷6—G“¢ãSS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6&BÖw&–B"°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆR×w&°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B33336°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3Sc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆR°¢v–GFƒ¢S°¢&÷&FW"Ö6öÆÆ6S¢6öÆÆ6S°¢F&ÆRÖÆ–÷WC¢f—†VC°¢6öÆ÷#¢6SvSvSs°¢föçB×6—¦S¢ƒ°¢föçB×f&–çBÖçVÖW&–3¢F'VÆ"ÖçV×3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆR6F–öâ°¢÷6—F–öã¢'6öÇWFS°¢v–GFƒ¢ƒ°¢†V–v‡C¢ƒ°¢FF–æs¢°¢÷fW&fÆ÷s¢†–FFVã°¢6Æ—¢&V7BƒÂÂÂ“°¢v†—FR×76S¢æ÷w&°¢&÷&FW#¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF‚À¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRFB°¢FF–æs¢w‚gƒ°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B3#“&33#°¢FW‡BÖÆ–vã¢&–v‡C°¢fW'F–6ÂÖÆ–vã¢Ö–FFÆS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRFƒ¦f—'7BÖ6†–ÆB°¢v–GFƒ¢3S°¢FW‡BÖÆ–vã¢ÆVgC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF†VBF‚°¢6öÆ÷#¢3–fVC°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ã3VVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’F‚À¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’FB°¢6öÆ÷#¢6SvSvSr–×÷'FçC°¢föçB×vV–v‡C¢sS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’G#¦Æ7BÖ6†–ÆB°¢&6¶w&÷VæC¢3C##°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’G#¦Æ7BÖ6†–ÆBF‚À¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’G#¦Æ7BÖ6†–ÆBFB°¢&÷&FW"Ö&÷GFöÓ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’F‚7âÀ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’F‚6ÖÆÂ°¢F—7Æ“¢&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF&öG’F‚6ÖÆÂ°¢Ö&v–â×F÷¢'ƒ°¢6öÆ÷#¢3“c–6S°¢föçB×6—¦S¢‡ƒ°¢föçB×vV–v‡C¢c°¢Æ–æRÖ†V–v‡C¢ã#S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öâ°¢Ö&v–â×F÷¢—ƒ°¢&÷&FW#¢‚6öÆ–B3&S&S&S°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3333°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öââ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢Ö–âÖ†V–v‡C¢C'ƒ°¢FF–æs¢—‚ƒ°¢7W'6÷#¢ö–çFW#°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öââ7VÖÖ'’7â°¢FW‡BÖÆ–vã¢&–v‡C°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢C°¢÷6—G“¢ãSƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öâÖ&öG’°¢FF–æs¢‚ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×&÷r°¢FF–æs¢—‚°¢&÷&FW"×F÷¢‚6öÆ–B3#“#“#“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×&÷s¦f—'7BÖ6†–ÆB°¢&÷&FW"×F÷¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×F÷Æ–æRÀ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×fÇVW2°¢F—7Æ“¢fÆWƒ°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×F÷Æ–æR°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×F÷Æ–æR7ã¦Æ7BÖ6†–ÆBÀ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×fÇVW27ã¦Æ7BÖ6†–ÆB°¢fÆWƒ¢WFó°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×fÇVW2°¢Ö&v–â×F÷¢Wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢÷6—G“¢ãcƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–ÒÖæ÷FR°¢Ö&v–â×F÷¢Wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢÷6—G“¢ãSS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×VÆ—G’ÖÆ–æR°¢Ö&v–â×F÷¢gƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢÷6—G“¢ãs#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×VÆ—G’×v&æ–ær°¢&÷&FW"Ö6öÆ÷#¢3ccS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fRÖw&–BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ†—7F÷'’Öw&–B°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fRÖw&–B°¢Ö&v–âÖ&÷GFöÓ¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fRÖ6&BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ†—7F÷'’Ö6&BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆRÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ–Ö—BÖæ÷FR°¢Ö–â×v–GFƒ¢°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×F÷Æ–æR°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×F÷Æ–æR7âÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ†—7F÷'’×F—FÆR°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×F÷Æ–æR"°¢FW‡BÖÆ–vã¢&–v‡C°¢föçB×6—¦S¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×G&6²°¢†V–v‡C¢—ƒ°¢Ö&v–ã¢—‚°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW"×&F—W3¢““—ƒ°¢&6¶w&÷VæC¢3#“#“#“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×G&6²âF—b°¢†V–v‡C¢S°¢&÷&FW"×&F—W3¢–æ†W&—C°¢&6¶w&÷VæC¢6°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×7F6²×7FGW2°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö&v–ã¢‡ƒ°¢FF–æs¢g‚‡ƒ°¢&÷&FW#¢‚6öÆ–B333C3F°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢3ƒ#°¢6öÆ÷#¢6#–&c°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×7F6²×7FGW2â7â°¢fÆWƒ¢WFó°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×7F6²×7FGW2â"°¢Ö–â×v–GFƒ¢°¢6öÆ÷#¢6CVSVV#°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×7F6²×7FGW2æ—2Ö7F—fR°¢&÷&FW"Ö6öÆ÷#¢3CssƒC°¢&6¶w&÷VæC¢33##s°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖWF°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×&FRÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖg&W6†æW72À¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR7âÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ–Ö—BÖæ÷FRÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖV×G’°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢÷6—G“¢ãcS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×&FR°¢Ö&v–â×F÷¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖg&W6†æW72°¢Ö&v–âÖ&÷GFöÓ¢ƒ°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR°¢Ö&v–âÖ&÷GFöÓ¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR"À¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR7â°¢F—7Æ“¢&Æö6³°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR7â°¢Ö&v–â×F÷¢Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ†—7F÷'’×F—FÆR°¢Ö&v–âÖ&÷GFöÓ¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2Öw&–B°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2Öv–âÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2×W6RÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2ÖÆ÷72°¢&÷‚×6†F÷s¢–ç6WB7‚f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2Öv–â°¢Ò×F×&W6÷W&6RÖ66VçC¢3s&#“†S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2×W6R°¢Ò×F×&W6÷W&6RÖ66VçC¢6CVc°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2ÖÆ÷72°¢Ò×F×&W6÷W&6RÖ66VçC¢66csCsC°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2Öv–âçFÖÖWG&–2×fÇVRÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2×W6RçFÖÖWG&–2×fÇVRÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÖWG&–2ÖÆ÷72çFÖÖWG&–2×fÇVR°¢6öÆ÷#¢f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—7BÖ†VF–ær°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢gƒ°¢Ö&v–ã¢7‚wƒ°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢ÆWGFW"×76–æs¢ã6VÓ°¢6öÆ÷#¢f"‚Ò×F×&W6÷W&6RÖ66VçBÂ6“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—7BÖ†VF–æs£¦&Vf÷&R°¢v–GFƒ¢wƒ°¢†V–v‡C¢wƒ°¢fÆWƒ¢WFó°¢&÷&FW"×&F—W3¢““—ƒ°¢&6¶w&÷VæC¢7W'&VçD6öÆ÷#°¢6öçFVçC¢rs°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—7BÖ†VF–ærÖv–â°¢Ò×F×&W6÷W&6RÖ66VçC¢3s&#“†S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—7BÖ†VF–ær×W6R°¢Ò×F×&W6÷W&6RÖ66VçC¢6CVc°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—7BÖ†VF–ærÖÆ÷72°¢Ò×F×&W6÷W&6RÖ66VçC¢66csCsC°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ°¢Ò×F×&W6÷W&6RÖ66VçC¢6°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖv–â°¢Ò×F×&W6÷W&6RÖ66VçC¢3s&#“†S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×W6R°¢Ò×F×&W6÷W&6RÖ66VçC¢6CVc°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖÆ÷72°¢Ò×F×&W6÷W&6RÖ66VçC¢66csCsC°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö&v–âÖ&÷GFöÓ¢wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢÷6—G“¢ãs°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×7VÖÖ'’"°¢fÆWƒ¢WFó°¢6öÆ÷#¢f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖÆ—7B°¢F—7Æ“¢w&–C°¢v¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×&÷r°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢#G‚Ö–æÖ‚ƒÂg"“°¢v¢‡ƒ°¢Ö–â×v–GFƒ¢°¢FF–æs¢‡ƒ°¢&÷&FW#¢‚6öÆ–B3#“#“#“°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×&æ²°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢6VçFW#°¢v–GFƒ¢#Gƒ°¢†V–v‡C¢#Gƒ°¢&÷&FW#¢‚6öÆ–Bf"‚Ò×F×&W6÷W&6RÖ66VçB“°¢&÷&FW"×&F—W3¢““—ƒ°¢6öÆ÷#¢f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖÖ–â°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×F÷Æ–æR°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖÆ&VÂ°¢Ö–â×v–GFƒ¢°¢÷fW&fÆ÷s¢†–FFVã°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢Æ–æRÖ†V–v‡C¢ã3S°¢FW‡BÖ÷fW&fÆ÷s¢VÆÆ—6—3°¢v†—FR×76S¢æ÷w&°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×fÇVW2°¢F—7Æ“¢fÆWƒ°¢fÆWƒ¢WFó°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢Wƒ°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×fÇVW2â7â°¢Ö–â×v–GFƒ¢3Wƒ°¢FF–æs¢'‚Wƒ°¢&÷&FW#¢‚6öÆ–Bf"‚Ò×F×&W6÷W&6RÖ66VçB“°¢&÷&FW"×&F—W3¢““—ƒ°¢6öÆ÷#¢f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢FW‡BÖÆ–vã¢6VçFW#°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×G&6²°¢†V–v‡C¢Wƒ°¢Ö&v–â×F÷¢gƒ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW"×&F—W3¢““—ƒ°¢&6¶w&÷VæC¢3#c#c#c°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×G&6²âF—b°¢†V–v‡C¢S°¢Ö–â×v–GFƒ¢'ƒ°¢&÷&FW"×&F—W3¢–æ†W&—C°¢&6¶w&÷VæC¢f"‚Ò×F×&W6÷W&6RÖ66VçB“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâÖWfVçG2°¢Ö&v–â×F÷¢Gƒ°¢föçB×6—¦S¢—ƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢÷6—G“¢ãSS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ–Ö—BÖæ÷FR°¢Ö&v–â×F÷¢ƒ°¢Ð ¢ò¢c"ã‚ãs¢&W7G&–æVB6öÆ÷"†–W&&6‡’Âv—F‚Æ–v‡FW"æW7FVBG&–æ–ær&–Ç2â¢ð¢2G´ÔôDÅô”GÒçF×6V7F–öâ°¢&÷‚×6†F÷s¢–ç6WB7‚3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×6V7F–öâ°¢&÷&FW"Ö6öÆ÷#¢33ƒS3C3°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3#‚RÂ3C"R“°¢&÷‚×6†F÷s¢–ç6WB7‚3FfSf#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76R×6V7F–öâÀ¢2G´ÔôDÅô”GÒçF×7FBÖw&÷wF‚×6V7F–öâÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&VF–æW72×6V7F–öâ°¢&÷&FW"Ö6öÆ÷#¢3V#C“3°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3#RÂ3C"R“°¢&÷‚×6†F÷s¢–ç6WB7‚6C3F#°¢Ð ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’×6V7F–öâ°¢&÷&FW"Ö6öÆ÷#¢33CC“VC°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3##RRÂ3C"R“°¢&÷‚×6†F÷s¢–ç6WB7‚3c“v3c°¢Ð ¢2G´ÔôDÅô”GÒçF×6WGF–æw2×6V7F–öâ°¢&÷&FW"Ö6öÆ÷#¢3F#F#Sc°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3ƒƒ#RÂ3C"R“°¢&÷‚×6†F÷s¢–ç6WB7‚3“ƒ“†°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öâ°¢&÷&FW"ÖÆVgC¢'‚6öÆ–B3VCs&#°¢&6¶w&÷VæC¢3C#c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öââ7VÖÖ'’°¢&6¶w&÷VæC¢&v&ƒ#SRÂ#SRÂ#SRÂã#R“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7V'6V7F–öå¶÷VåÒâ7VÖÖ'’°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B&v&ƒ#’Âc2ÂsRÂã‚“°¢Ð ¢ò¢c"ã‚ãs¢F‡&VR6öæ6—6RÂ–æFWVæFVçFÇ’W‡æF&ÆR&W6÷W&6RG&vW'2â¢ð¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂÖÆ—7B°¢F—7Æ“¢w&–C°¢v¢wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂ°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö–âÖ†V–v‡C¢Cgƒ°¢FF–æs¢ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'’â7â°¢6öÆ÷#¢6VfVfVc°¢föçB×6—¦S¢Gƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'’â"°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢6öÆ÷#¢66f6f6c°¢föçB×6—¦S¢7ƒ°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(ÈBs°¢Ö&v–âÖÆVgC¢Gƒ°¢6öÆ÷#¢3“““°¢föçB×6—¦S¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÅ¶÷VåÒâ7VÖÖ'“£¦gFW"°¢G&ç6f÷&Ó¢&÷FFRƒƒFVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂÖ&öG’°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢FF–æs¢—‚—ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3&&&°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂÖ&öG’âçF×&W6÷W&6RÖÆ—fRÖ6&BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂÖ&öG’âçF×&W6÷W&6RÖ†—7F÷'’Ö6&BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂÖ&öG’âçF×&W6÷W&6RÖÆ—fR×Væf–Æ&ÆR°¢Ö&v–â×F÷¢—ƒ°¢Ð¢ÖVF–†Ö‚×v–GFƒ£S#‚’° ¢2G´ÔôDÅô”GÒæ7F–öç2À¢2G´ÔôDÅô”GÒç7FG2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢Ð ¢2G´ÔôDÅô”GÒçFÖÖWG&–2Öw&–B°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢Ð ¢2G´ÔôDÅô”GÒçFÖFWF–ÂÖw&–B°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢Ð ¢2G´ÔôDÅô”GÒçF×6V7F–öâÖÖWF°¢Ö‚×v–GFƒ¢C‚S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw&–BÀ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷rÖw&–BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖÆ—fRÖw&–BÀ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ†—7F÷'’Öw&–B°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×F÷Æ–æRÀ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×fÇVW2°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢v¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×F÷Æ–æR7ã¦Æ7BÖ6†–ÆBÀ¢2G´ÔôDÅô”GÒçF×7FBÖw–Ò×fÇVW27ã¦Æ7BÖ6†–ÆB°¢FW‡BÖÆ–vã¢ÆVgC°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ'&V¶F÷vâ×F÷Æ–æR°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢Ð¢Ð  ¢ò¢c"ãrã3¢G&–æ–ær&VF&–Æ—G’†–W&&6‡’f÷"6ö×7B†öæRÆ–÷WG2â¢ð¢2G´ÔôDÅô”GÒçF×7FBÖw&÷wF‚×6V7F–öâçF×6V7F–öâÖ–çG&ò°¢Ö&v–ã¢ƒ°¢FF–æs¢ƒ°¢6öÆ÷#¢6°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ãC#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'B°¢FF–æs¢'ƒ°¢&÷&FW"Ö6öÆ÷#¢3666°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒƒFVrÂ3ssrRÂ3##"R“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖ†VF–ær°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢v¢‡ƒ°¢Ö&v–âÖ&÷GFöÓ¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖ†VF–ærâ7ã¦f—'7BÖ6†–ÆB°¢6öÆ÷#¢6c&c&c#°¢föçB×6—¦S¢gƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ÒãVÓ°¢Æ–æRÖ†V–v‡C¢ãƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖ†VF–ærâ7ã¦Æ7BÖ6†–ÆB°¢Ö‚×v–GFƒ¢CbS°¢6öÆ÷#¢6&&#°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢÷6—G“¢ãsƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2°¢Ö&v–ã¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2Æ&VÂ°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢‡ƒ°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢s°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ26VÆV7B°¢Ö–âÖ†V–v‡C¢3‡ƒ°¢FF–æs¢w‚3G‚w‚ƒ°¢föçB×6—¦S¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ&VÂ°¢f–ÆÃ¢63V3V3S°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆVvVæB°¢v¢Gƒ°¢Ö&v–â×F÷¢wƒ°¢6öÆ÷#¢6CCC°¢föçB×6—¦S¢7ƒ°¢÷6—G“¢ãƒc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ–æRÖ¶W’°¢v–GFƒ¢#ƒ°¢†V–v‡C¢Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6÷W&6RÖ¶W’°¢v–GFƒ¢'ƒ°¢†V–v‡C¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ†’Ö§V×Ö¶W’°¢v–GFƒ¢—ƒ°¢†V–v‡C¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖFWF–Â°¢Ö&v–â×F÷¢ƒ°¢FF–æs¢‚ƒ°¢&÷&FW"Ö6öÆ÷#¢3633C#ƒ°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B6F&ƒSC°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3“sS°¢6öÆ÷#¢6SSS°¢föçB×6—¦S¢Gƒ°¢Æ–æRÖ†V–v‡C¢ãC#°¢Ð ¢ÖVF–†Ö‚×v–GFƒ£S#‚’°¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'B°¢FF–æs¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖ†VF–ærâ7ã¦f—'7BÖ6†–ÆB°¢föçB×6—¦S¢wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BçFÖ6†'BÖ†VF–ærâ7ã¦Æ7BÖ6†–ÆB°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖÆ&VÂ°¢föçB×6—¦S¢Gƒ°¢Ð¢Ð  ¢ò¢c"ãrãC¢6ö×7BÂvÆæ6V&ÆRG&–æ–ær7VÖÖ'’F–ÆW2â¢ð¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2çFÖÖWG&–2Ö6&B°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢“'ƒ°¢Ö&v–ã¢°¢FF–æs¢ƒ°¢&÷&FW"×&F—W3¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2çFÖÖWG&–2ÖÆ&VÂ°¢föçB×6—¦S¢ƒ°¢ÆWGFW"×76–æs¢ãCVVÓ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2çFÖÖWG&–2×fÇVR°¢Ö&v–â×F÷¢Wƒ°¢föçB×6—¦S¢#'ƒ°¢Æ–æRÖ†V–v‡C¢ãƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2çFÖÖWG&–2Öæ÷FR°¢Ö&v–â×F÷¢Wƒ°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×G&–æ–ærÖ7F–öç2×F–ÆR°¢&÷&FW"Ö6öÆ÷#¢33C3C3C°¢&6¶w&÷VæC¢3ccc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×G&–æ–ærÖ7F–öç2×F–ÆRçFÖÖWG&–2×fÇVR°¢6öÆ÷#¢6S&S&S#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂ×66ÆR°¢Ö&v–â×F÷¢Gƒ°¢6öÆ÷#¢63fVS°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢c°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6öçFW‡B×7VÖÖ'’°¢F—7Æ“¢w&–C°¢v¢7ƒ°¢Ö&v–â×F÷¢‡ƒ°¢FF–æs¢—‚ƒ°¢&÷&FW#¢‚6öÆ–B33S3#s°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B63s“cC#°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3sS°¢6öÆ÷#¢6C6C6C3°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6öçFW‡B×7VÖÖ'’7G&öær°¢6öÆ÷#¢6ccc°¢föçB×6—¦S¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6öçFW‡B×7VÖÖ'’6ÖÆÂ°¢6öÆ÷#¢6°¢föçB×6—¦S¢ƒ°¢Ð ¢ò¢c"ã‚ã##¢6ö×7B6VÆV7FVB×6W76–öâ7VÖÖ'’v—F‚Wf–FVæ6R&FvW2â¢ð¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ–ç7V7F÷"°¢F—7Æ“¢w&–C°¢v¢gƒ°¢Ö&v–â×F÷¢ƒ°¢FF–æs¢‡ƒ°¢&÷&FW#¢‚6öÆ–B36#6#6#°¢&÷&FW"×&F—W3¢—ƒ°¢&6¶w&÷VæC¢3CCC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ†VFW"°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢3'‚Ö–æÖ‚ƒÂg"’3'ƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢wƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ†VFW"âF—b°¢F—7Æ“¢w&–C°¢v¢'ƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâ×7FW°¢v–GFƒ¢3'ƒ°¢Ö–â×v–GFƒ¢3'ƒ°¢†V–v‡C¢3gƒ°¢Ö–âÖ†V–v‡C¢3gƒ°¢Ö&v–ã¢°¢FF–æs¢°¢&÷&FW#¢‚6öÆ–B3V#F33S°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3#C#“°¢6öÆ÷#¢6c33fC°¢föçB×6—¦S¢#Gƒ°¢föçB×vV–v‡C¢ƒ°¢Æ–æRÖ†V–v‡C¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâ×7FW¦F—6&ÆVB°¢&÷&FW"Ö6öÆ÷#¢3333°¢&6¶w&÷VæC¢3“““°¢6öÆ÷#¢3ccc°¢÷6—G“¢ãs#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖW–V'&÷r°¢6öÆ÷#¢6°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ãvVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ†VFW"7G&öær°¢6öÆ÷#¢6c6c6c3°¢föçB×6—¦S¢‡ƒ°¢Æ–æRÖ†V–v‡C¢ã#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFFR°¢6öÆ÷#¢6°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâ×V–6¶Æ–æR°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢v¢7‚gƒ°¢6öÆ÷#¢3–S–S–S°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâ×V–6¶Æ–æR7G&öær°¢6öÆ÷#¢6FVFVFS°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ&FvW2°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvRÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ6öçFW‡BÖ&FvRÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ§V×Ö&FvR°¢FF–æs¢G‚wƒ°¢&÷&FW#¢‚6öÆ–B3FFF°¢&÷&FW"×&F—W3¢““—ƒ°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢Æ–æRÖ†V–v‡C¢ã#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvR°¢&÷&FW"Ö6öÆ÷#¢33SSf°¢&6¶w&÷VæC¢3C#3°¢6öÆ÷#¢6#–F&V°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvU¶FF×F×7FBÖVæW&w’×6÷W&6SÒ'ö–çE÷&Vf–ÆÅöö'6W'fVB%Ò°¢&÷&FW"Ö6öÆ÷#¢3ccSƒC°¢&6¶w&÷VæC¢33s#S°¢6öÆ÷#¢6C†36c#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvU¶FF×F×7FBÖVæW&w’×6÷W&6SÒ&Ö—†VE÷6÷W&6W5öö'6W'fVB%Ò°¢&÷&FW"Ö6öÆ÷#¢3FCf3s3°¢&6¶w&÷VæC¢Æ–æV"Öw&F–VçBƒ“FVrÂ3C#2SRÂ33s#RSRR“°¢6öÆ÷#¢6CfSvVC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvU¶FF×F×7FBÖVæW&w’×6÷W&6SÒ&æõöVæW&w•÷6÷W&6Uöö'6W'fVB%ÒÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’Ö&FvU¶FF×F×7FBÖVæW&w’×6÷W&6SÒ&VæW&w•ö6öçFW‡E÷Væf–Æ&ÆR%Ò°¢&÷&FW"Ö6öÆ÷#¢3F#F#F#°¢&6¶w&÷VæC¢3°¢6öÆ÷#¢63&3&3#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ6öçFW‡BÖ&FvR°¢&÷&FW"Ö6öÆ÷#¢3S“Cƒ#“°¢&6¶w&÷VæC¢3###°¢6öÆ÷#¢6S&&Css°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ§V×Ö&FvR°¢&÷&FW"Ö6öÆ÷#¢6#ƒƒ3°¢&6¶w&÷VæC¢3&#C3°¢6öÆ÷#¢6c63CfC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ§V×Ö&FvS¦V×G’°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ§V××&V6°¢Ö&v–ã¢°¢FF–ærÖÆVgC¢‡ƒ°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B63s“cC#°¢6öÆ÷#¢6C–3†S°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ§V××&V6¶†–FFVåÒ°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2À¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6R°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B33C3C3C°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3sss°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6R°¢&÷&FW"Ö6öÆ÷#¢33C“SS°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B3Vc“ƒ°¢&6¶w&÷VæC¢3#“C°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2â7VÖÖ'’À¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'’°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢‡ƒ°¢Ö–âÖ†V–v‡C¢3Gƒ°¢FF–æs¢W‚‡ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2â7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"À¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2â7VÖÖ'’â7âÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'’â7â°¢6öÆ÷#¢6††ƒ°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2â7VÖÖ'’â7G&öærÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'’â7G&öær°¢Ö&v–âÖÆVgC¢WFó°¢6öÆ÷#¢6FVFVFS°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'’â7G&öær°¢6öÆ÷#¢6C–VFcS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2â7VÖÖ'“£¦gFW"À¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6Râ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~)k‚s°¢6öÆ÷#¢3“““°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç5¶÷VåÒâ7VÖÖ'“£¦gFW"À¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6U¶÷VåÒâ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~)kâs°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖFWF–Ç2âF—bÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6RâF—b°¢F—7Æ“¢w&–C°¢v¢wƒ°¢FF–æs¢‡ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3333°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6RâF—b°¢v¢7ƒ°¢&÷&FW"×F÷Ö6öÆ÷#¢&v&ƒ“RÂCRÂc‚Âã#"“°¢6öÆ÷#¢6C&C&C#°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖf7G2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢v¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖf7G27â°¢F—7Æ“¢w&–C°¢v¢'ƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖf7G2’°¢6öÆ÷#¢3“c“c“c°¢föçB×6—¦S¢—ƒ°¢föçB×7G–ÆS¢æ÷&ÖÃ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ã6VÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖf7G2"°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢6öÆ÷#¢6S6S6S3°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ6öçFW‡B°¢F—7Æ“¢w&–C°¢v¢7ƒ°¢FF–æs¢w‚‡ƒ°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B63s“cC#°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢3“s3°¢6öÆ÷#¢6C&C&C#°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ã3ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ6öçFW‡B7G&öær°¢6öÆ÷#¢6ccc°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ6öçFW‡B6ÖÆÂ°¢6öÆ÷#¢6°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6RâF—bâ7G&öær°¢6öÆ÷#¢6SfccS°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖVæW&w’ÖWf–FVæ6RâF—bâ6ÖÆÂ°¢6öÆ÷#¢3–fV#C°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢ò¢c"ã‚ãC¢öæRFVç6R7W&f6Rf÷"6†&VBÖfö7W27FBw&÷wF‚FWF–Ââ¢ð¢2G´ÔôDÅô”GÒçF×7FBÖFWF–Ç2×66÷RÀ¢2G´ÔôDÅô”GÒçF×7FB×&V6VçB×æVÂ°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw&÷wF‚Ö6ö×7BÖÖWG&–72°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢÷fW&fÆ÷s¢†–FFVã°¢&÷&FW#¢‚6öÆ–B33336°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3Sc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2°¢Ö–â×v–GFƒ¢°¢Ö&v–ã¢°¢&÷&FW#¢°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B3#“&33#°¢&÷&FW"×&F—W3¢°¢&6¶w&÷VæC¢G&ç7&VçC°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–3¦çF‚Ö6†–ÆB†öFB’°¢&÷&FW"×&–v‡C¢‚6öÆ–B3#“&33#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–3¦çF‚ÖÆ7BÖ6†–ÆB‚Öâ³"’°¢&÷&FW"Ö&÷GFöÓ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'’°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"’WFòƒ°¢v¢gƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢Ö–âÖ†V–v‡C¢Sƒ°¢FF–æs¢‡‚—ƒ°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'“£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'“£¦gFW"°¢6öçFVçC¢r²s°¢6öÆ÷#¢3ƒ3†#“S°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢FW‡BÖÆ–vã¢6VçFW#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–5¶÷VåÒâ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(	2s°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'’7â°¢6öÆ÷#¢6V#F&3°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ã#VVÓ°¢Æ–æRÖ†V–v‡C¢ã#°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'’7G&öær°¢6öÆ÷#¢6cc&cC°¢föçB×6—¦S¢gƒ°¢föçB×vV–v‡C¢ƒS°¢föçB×f&–çBÖçVÖW&–3¢F'VÆ"ÖçV×3°¢Æ–æRÖ†V–v‡C¢ã°¢FW‡BÖÆ–vã¢&–v‡C°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â6ÖÆÂ°¢F—7Æ“¢&Æö6³°¢FF–æs¢—‚—ƒ°¢6öÆ÷#¢3–FFC°¢föçB×6—¦S¢—ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–5¶÷VåÒ°¢&6¶w&÷VæC¢3C##°¢Ð ¢ò¢c"ã‚ãCC¢7F—fRÖÆæR6ÆVæF"æf–vF–öâv—F‚W†7B6W76–öâ67'V&&–ærâ¢ð¢2G´ÔôDÅô”GÒçF×7FB×÷7BÖ6†'BÖ6öçG&öÇ2°¢v¢wƒ°¢Ö&v–â×F÷¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷RÖ6öçG&öÇ2°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖv–â×66÷RÖ6öçG&öÇ2'WGFöâ°¢Ö–âÖ†V–v‡C¢3ƒ°¢FF–æs¢W‚wƒ°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"’Ö–æÖ‚ƒÂg"’Ö–æÖ‚ƒS‚Âã3Vg"“°¢v¢gƒ°¢Æ–vâÖ—FV×3¢VæC°¢Ö&v–ã¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2ÖÆÂ°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂã–g"’Ö–æÖ‚ƒs‚Âã&g"“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2Æ&VÂÀ¢2G´ÔôDÅô”GÒçF×7FB×&ævRÖ6öçG&öÂ°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢v¢7ƒ°¢Ö–â×v–GFƒ¢°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2Æ&VÂâ7âÀ¢2G´ÔôDÅô”GÒçF×7FB×&ævRÖ6öçG&öÂâ7â°¢6öÆ÷#¢3–fVC°¢föçB×6—¦S¢‡ƒ°¢ÆWGFW"×76–æs¢ãSVVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ26VÆV7B°¢v–GFƒ¢S°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢3ƒ°¢FF–æs¢W‚#'‚W‚wƒ°¢&÷&FW"×&F—W3¢gƒ°¢6öÆ÷#¢6S†S†Sƒ°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢sS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×&ævRÖ6öçG&öÂâF—b°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒBÂÖ–æÖ‚ƒÂg"’“°¢v¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×&ævRÖ6öçG&öÂ'WGFöâ°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢3ƒ°¢Ö&v–ã¢°¢FF–æs¢G‚7ƒ°¢&÷&FW#¢‚6öÆ–B36SC#C“°¢&÷&FW"×&F—W3¢Wƒ°¢&6¶w&÷VæC¢3s“C°¢6öÆ÷#¢6V#F&3°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒS°¢÷6—G“¢ãsƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×&ævRÖ6öçG&öÂ'WGFöâçF×7FB×&ævRÖ7F—fR°¢&÷&FW"Ö6öÆ÷#¢6C&CVF°¢&6¶w&÷VæC¢366CC3°¢6öÆ÷#¢6ffc°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6†'BâçF×7FB×6W76–öâÖ–ç7V7F÷"°¢Ö&v–â×F÷¢‡ƒ°¢&÷&FW"Ö6öÆ÷#¢3FC3°¢&÷&FW"ÖÆVgC¢7‚6öÆ–B6CF#Fc°¢&6¶w&÷VæC¢3sS#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ&6¶w&÷VæB°¢f–ÆÃ¢3Ss#°¢7G&ö¶S¢333C6°¢7G&ö¶R×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"ÖÖöFRçF×7FBÖÆæR°¢G&ç6—F–öã¢÷6—G’ãG2V6S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"ÖÖöFRçF×7FBÖÆæRÖ×WFVB°¢÷6—G“¢ãSƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"ÖÖöFRçF×7FBÖÆæRÖ7F—fRçF×7FBÖÆæRÖ&6¶w&÷VæB°¢7G&ö¶S¢6#S†#Cƒ°¢7G&ö¶R×v–GFƒ¢ãƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"ÖÖöFRçF×7FBÖÆæRÖ7F—fRçF×7FBÖÆæRÖÆ–æR°¢7G&ö¶R×v–GFƒ¢2ã°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ–æR°¢f–ÆÃ¢æöæS°¢7G&ö¶R×v–GFƒ¢"ãC°¢7G&ö¶RÖÆ–æV6¢&÷VæC°¢7G&ö¶RÖÆ–æV¦ö–ã¢&÷VæC°¢ö–çFW"ÖWfVçG3¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ–æRçF×7FBÖÆæR×7G&VæwF‚°¢7G&ö¶S¢6SS†#sS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ–æRçF×7FBÖÆæRÖFVfVç6R°¢7G&ö¶S¢3s&vSƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ–æRçF×7FBÖÆæR×7VVB°¢7G&ö¶S¢3cV3v3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ–æRçF×7FBÖÆæRÖFW‡FW&—G’°¢7G&ö¶S¢6#†&Sƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çB°¢ö–çFW"ÖWfVçG3¢æöæS°¢7G&ö¶S¢3°¢7G&ö¶R×v–GFƒ¢ã#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çBçF×7FBÖÆæR×7G&VæwF‚°¢f–ÆÃ¢6SS†#sS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çBçF×7FBÖÆæRÖFVfVç6R°¢f–ÆÃ¢3s&vSƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çBçF×7FBÖÆæR×7VVB°¢f–ÆÃ¢3cV3v3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çBçF×7FBÖÆæRÖFW‡FW&—G’°¢f–ÆÃ¢6#†&Sƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×ö–çBçF×7FB×6W76–öâÖ7F—fR°¢#¢Rã'ƒ°¢7G&ö¶S¢6ffc6CC°¢7G&ö¶R×v–GFƒ¢"ãc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÖ&¶W"Ö†–FFVâ°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÖ&¶W"Ö†–FFVâçF×7FB×6W76–öâÖ7F—fR°¢÷6—G“¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ&VÂÀ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×F÷FÂ°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒS°¢ö–çFW"ÖWfVçG3¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ&VÂçF×7FBÖÆæR×7G&VæwF‚°¢f–ÆÃ¢6c†C°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ&VÂçF×7FBÖÆæRÖFVfVç6R°¢f–ÆÃ¢3“&Fc#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ&VÂçF×7FBÖÆæR×7VVB°¢f–ÆÃ¢3ƒ6Cv#“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆ&VÂçF×7FBÖÆæRÖFW‡FW&—G’°¢f–ÆÃ¢63vVVc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×F÷FÂ°¢f–ÆÃ¢6#v&&3°¢föçB×6—¦S¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆVvVæB°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢v¢W‚ƒ°¢Ö&v–â×F÷¢gƒ°¢6öÆ÷#¢63V3–6c°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖÆVvVæB7â°¢F—7Æ“¢–æÆ–æRÖfÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×6VÆV7F÷"°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒBÂÖ–æÖ‚ƒÂg"’“°¢v¢Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×6VÆV7F÷"'WGFöâ°¢F—7Æ“¢–æÆ–æRÖfÆWƒ°¢Æ–vâÖ—FV×3¢6VçFW#°¢§W7F–g’Ö6öçFVçC¢6VçFW#°¢v¢Wƒ°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢3Gƒ°¢Ö&v–ã¢°¢FF–æs¢W‚7ƒ°¢&÷&FW#¢‚6öÆ–B33S3“C°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢3s“C°¢6öÆ÷#¢6#–&V3c°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæR×6VÆV7F÷"'WGFöå¶&–×&W76VCÒ'G'VR%Ò°¢&÷&FW"Ö6öÆ÷#¢633–SS°¢&6¶w&÷VæC¢3&##C“°¢6öÆ÷#¢6ffc6c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"°¢F—7Æ“¢w&–C°¢v¢'ƒ°¢Ö&v–â×F÷¢wƒ°¢FF–æs¢w‚—‚gƒ°¢&÷&FW#¢‚6öÆ–B3FC3°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3sS#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"Ö†VF–ær°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢‡ƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"Ö†VF–ær7G&öær°¢6öÆ÷#¢6cCC–S°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"Ö†VF–ær7â°¢÷fW&fÆ÷s¢†–FFVã°¢6öÆ÷#¢6#f#f#c°¢föçB×6—¦S¢ƒ°¢FW‡BÖ÷fW&fÆ÷s¢VÆÆ—6—3°¢v†—FR×76S¢æ÷w&°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"–çWE·G—SÒ'&ævR%Ò°¢v–GFƒ¢S°¢Ö–âÖ†V–v‡C¢3'ƒ°¢Ö&v–ã¢°¢FF–æs¢°¢&÷&FW#¢°¢&6¶w&÷VæC¢G&ç7&VçC°¢66VçBÖ6öÆ÷#¢6CF#Fc°¢F÷V6‚Ö7F–öã¢â×“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ÆVæF"Öæf–vF÷"6ÖÆÂ°¢6öÆ÷#¢3“c“c“c°¢föçB×6—¦S¢—ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢FW‡BÖÆ–vã¢6VçFW#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ¶W’°¢v–GFƒ¢'ƒ°¢†V–v‡C¢7ƒ°¢&÷&FW"×&F—W3¢““—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ¶W’çF×7FBÖÆæR×7G&VæwF‚°¢&6¶w&÷VæC¢6SS†#sS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ¶W’çF×7FBÖÆæRÖFVfVç6R°¢&6¶w&÷VæC¢3s&vSƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ¶W’çF×7FBÖÆæR×7VVB°¢&6¶w&÷VæC¢3cV3v3°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖÆæRÖ¶W’çF×7FBÖÆæRÖFW‡FW&—G’°¢&6¶w&÷VæC¢6#†&Sƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6ö×7B×7VÖÖ'’°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢FF–æs¢'ƒ°¢&÷&FW#¢‚6öÆ–B3CsCsCs°¢&÷&FW"×&F—W3¢'ƒ°¢&6¶w&÷VæC¢3sss°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’Ö†VFW"°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’Ö†VFW"âF—b°¢F—7Æ“¢w&–C°¢v¢7ƒ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’Ö¶–6¶W"À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×W&–öBâ7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öââ7â°¢6öÆ÷#¢6663°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’Ö†VFW"7G&öær°¢6öÆ÷#¢6ccc°¢föçB×6—¦S¢‡ƒ°¢Æ–æRÖ†V–v‡C¢ã#S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×W&–öB°¢F—7Æ“¢w&–C°¢v¢7ƒ°¢fÆWƒ¢WFó°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×W&–öB6VÆV7B°¢Ö–âÖ†V–v‡C¢3Gƒ°¢FF–æs¢W‚#‡‚W‚—ƒ°¢&÷&FW#¢‚6öÆ–B3SSS°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3#“#“#“°¢6öÆ÷#¢6c&c&c#°¢föçC¢–æ†W&—C°¢föçB×6—¦S¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’ÖGf–6RÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öâ°¢Ö&v–ã¢°¢6öÆ÷#¢6FVFVFS°¢föçB×6—¦S¢Gƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öâ°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢v¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öâÖ6öçFW‡B°¢fÆWƒ¢S°¢6öÆ÷#¢6°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’ÖÖWF°¢6öÆ÷#¢3–C–C–C°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ã3S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ6ö×7B×7VÖÖ'’âçF×G&–æ–ærÖwV–FR°¢Ö&v–ã¢Ó'ƒ°¢FF–æs¢‚'ƒ°¢&÷&FW"×F÷¢‚6öÆ–B36C3C#C°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B36C3C#C°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öâ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢—ƒ°¢&6¶w&÷VæC¢3###°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââ7VÖÖ'’°¢Ö–âÖ†V–v‡C¢CGƒ°¢FF–æs¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'BÖ6öçG&öÇ2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ"ÂÖ–æÖ‚ƒÂg"’“°¢v¢‡ƒ°¢FF–æs¢ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3333°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&VF–7F–öâÖ6öçG&öÇ2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââçF×G&–æ–ær×&V6À¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öâ°¢&÷&FW"×F÷¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢—‚—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'B×6V7F–öââçF×G&–æ–ær×7VÖÖ'’×&VF–7F–öâ°¢FF–æs¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××&V6°¢F—7Æ“¢w&–C°¢v¢Gƒ°¢Ö&v–ã¢°¢FF–æs¢—‚ƒ°¢&÷&FW"×F÷¢‚6öÆ–B36C3C#C°¢&6¶w&÷VæC¢3ƒSc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××&V6â7â°¢6öÆ÷#¢66f“Vc°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢ƒ°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖ§V××&V6â"°¢6öÆ÷#¢6SFC6S°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢S°¢Æ–æRÖ†V–v‡C¢ãC#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6°¢÷6—F–öã¢&VÆF—fS°¢F—7Æ“¢w&–C°¢v¢Wƒ°¢v–GFƒ¢S°¢Ö&v–ã¢°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–BG&ç7&VçC°¢&÷&FW"×&F—W3¢ƒ°¢&6¶w&÷VæC¢3###°¢6öÆ÷#¢6FVFVFS°¢FW‡BÖÆ–vã¢ÆVgC°¢föçC¢–æ†W&—C°¢7W'6÷#¢ö–çFW#°¢×vV&¶—B×FÖ†–v†Æ–v‡BÖ6öÆ÷#¢G&ç7&VçC°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6â7âÀ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6â6ÖÆÂ°¢6öÆ÷#¢6663°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ãFVÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6â"°¢6öÆ÷#¢6SSS°¢föçB×6—¦S¢Gƒ°¢föçB×vV–v‡C¢C°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6â6ÖÆÃ¦V×G’°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¶FF×FÖ6÷’×7FFSÒ&&ÖVB%Ò°¢&÷&FW"Ö6öÆ÷#¢6C3F#°¢&6¶w&÷VæC¢3cc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¶FF×FÖ6÷’×7FFSÒ&&ÖVB%Òâ6ÖÆÂ°¢6öÆ÷#¢6C–#ScS°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¶FF×FÖ6÷’×7FFSÒ&6÷–VB%Ò°¢&÷&FW"Ö6öÆ÷#¢3cVsvS°¢&6¶w&÷VæC¢3S°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¶FF×FÖ6÷’×7FFSÒ&6÷–VB%Òâ6ÖÆÂ°¢6öÆ÷#¢3vf3c“c°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¶FF×FÖ6÷’×7FFSÒ&W'&÷"%Ò°¢&÷&FW"Ö6öÆ÷#¢6#“cc°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×&V6¦fö7W2×f—6–&ÆR°¢÷WFÆ–æS¢'‚6öÆ–B6C3F#°¢÷WFÆ–æRÖöfg6WC¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖFWF–Ç2×6V7F–öâ°¢Ö&v–â×F÷¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ærÖFWF–Ç2Ö&öG’°¢F—7Æ“¢w&–C°¢v¢ƒ°¢Ð ¢ò¢c"ã‚ãCƒ¢6ö×7BWfW'–F’7VÖÖ&–W3²¶VWWf–FVæ6Rf–Æ&ÆRöâFVÖæBâ¢ð¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×6VÆV7F÷'2°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢fÆWƒ¢WFó°¢v¢wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7BÖ&öG’À¢2G´ÔôDÅô”GÒçFÖ7F—f—G’Ö6ö×7BÖ&öG’À¢2G´ÔôDÅô”GÒçF×7FBÖw&÷wF‚Ö6ö×7BÖ&öG’°¢v¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'’°¢Ö–âÖ†V–v‡C¢SGƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6R×æVÂâ7VÖÖ'’âçF×&W6÷W&6RÖ6ö×7B×7FGW2°¢F—7Æ“¢w&–C°¢§W7F–g’Ö—FV×3¢VæC°¢v¢ƒ°¢Ö–â×v–GFƒ¢°¢6öÆ÷#¢66f6f6c°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×7FGW2â"°¢6öÆ÷#¢6VfVfVc°¢föçB×6—¦S¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×7FGW2â6ÖÆÂ°¢6öÆ÷#¢3“c“c“c°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢c°¢Æ–æRÖ†V–v‡C¢ã#S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×7FGW2â6ÖÆÂæ—2Ö7F—fR°¢6öÆ÷#¢3ƒ&3–°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7BÖ†—7F÷'’°¢F—7Æ“¢w&–C°¢v¢wƒ°¢FF–æs¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×F÷FÇ2°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢v¢gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×F÷FÇ2â7â°¢F—7Æ“¢w&–C°¢v¢'ƒ°¢Ö–â×v–GFƒ¢°¢FF–æs¢wƒ°¢&÷&FW#¢‚6öÆ–B3333°¢&÷&FW"×&F—W3¢wƒ°¢&6¶w&÷VæC¢3SSS°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×F÷FÇ26ÖÆÂ°¢6öÆ÷#¢3†c†c†c°¢föçB×6—¦S¢—ƒ°¢föçB×vV–v‡C¢s°¢ÆWGFW"×76–æs¢ã6VÓ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7B×F÷FÇ2"°¢÷fW&fÆ÷r×w&¢ç—v†W&S°¢6öÆ÷#¢6V6V6V3°¢föçB×6—¦S¢7ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7BÖfÆ÷r°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢3G‚Ö–æÖ‚ƒÂg"“°¢v¢wƒ°¢Æ–vâÖ—FV×3¢7F'C°¢FF–ær×F÷¢gƒ°¢&÷&FW"×F÷¢‚6öÆ–B3&C&C&C°¢6öÆ÷#¢6&F&F&C°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢2G´ÔôDÅô”GÒçF×&W6÷W&6RÖ6ö×7BÖfÆ÷r"°¢6öÆ÷#¢6C3F#°¢föçB×6—¦S¢ƒ°¢FW‡B×G&ç6f÷&Ó¢WW&66S°¢Ð ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’Ö6ö×7B×7VÖÖ'’°¢F—7Æ“¢w&–C°¢v¢gƒ°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B33ƒF3VS°¢&÷&FW"×&F—W3¢ƒ°¢&6¶w&÷VæC¢3##°¢Ð ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’Ö6ö×7B×7VÖÖ'’7G&öær°¢6öÆ÷#¢6V6V6V3°¢föçB×6—¦S¢Gƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’Ö6ö×7B×7VÖÖ'’7âÀ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’Ö6ö×7BÖæ÷FR°¢6öÆ÷#¢3–c–c–c°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢ò¢c"ã‚ãS¢öæRV–WBvVV¶Ç’7W&f6R&WÆ6W2Gvò6ö×WF–ærF6†&ö&G2â¢ð¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†–v†Æ–v‡G2×6V7F–öâ°¢&÷&FW"Ö6öÆ÷#¢36CSƒF°¢&÷‚×6†F÷s¢–ç6WBG‚3cVsvS°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†–v†Æ–v‡G2Ö&öG’À¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†—7F÷'’Ö&öG’°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†—7F÷'’Ö&öG’°¢FF–ær×F÷¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†–v†Æ–v‡B×7VÖÖ'’°¢F—7Æ“¢w&–C°¢v¢wƒ°¢FF–æs¢ƒ°¢&÷&FW#¢‚6öÆ–B33cSC3°¢&÷&FW"×&F—W3¢ƒ°¢&6¶w&÷VæC¢3S°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†–v†Æ–v‡B×7VÖÖ'’°¢Ö&v–ã¢°¢6öÆ÷#¢6FVFVFS°¢föçB×6—¦S¢7ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†–v†Æ–v‡B×7VÖÖ'’æ—2Öæ÷F&ÆR°¢6öÆ÷#¢6Cvcs°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†—7F÷'’Ö&öG’â6V7F–öâ°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†—7F÷'’Ö&öG’â6V7F–öâ²6V7F–öâ°¢FF–ær×F÷¢ƒ°¢&÷&FW"×F÷¢‚6öÆ–B3&S&S&S°¢Ð ¢2G´ÔôDÅô”GÒçF×vVV¶Ç’Ö†—7F÷'’Ö&öG’ƒB°¢Ö&v–ã¢°¢6öÆ÷#¢6C–C–C“°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçFÖ7F—f—G’ÖFWF–Ç2Ö&öG’°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ö×7BÖVff–6–Væ7’°¢F—7Æ“¢fÆWƒ°¢fÆW‚×w&¢w&°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢v¢G‚‡ƒ°¢FF–æs¢—ƒ°¢&÷&FW#¢‚6öÆ–B33C3C3C°¢&÷&FW"×&F—W3¢‡ƒ°¢&6¶w&÷VæC¢3ccc°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ö×7BÖVff–6–Væ7’7G&öær°¢6öÆ÷#¢6V6V6V3°¢föçB×6—¦S¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖ6ö×7BÖVff–6–Væ7’7â°¢6öÆ÷#¢3–C–C–C°¢föçB×6—¦S¢ƒ°¢Æ–æRÖ†V–v‡C¢ãC°¢Ð ¢ò¢c"ã‚ãSc¢F—&V7B7FG2f–Ww2&WÆ6RæW7FVBæÇ—F–72G&vW'2â¢ð¢2G´ÔôDÅô”GÒçF×G&–æ–ær×v÷&·76RÖ&öG’°¢F—7Æ“¢w&–C°¢v¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–WrÖæb°¢F—7Æ“¢w&–C°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢&WVBƒ2ÂÖ–æÖ‚ƒÂg"’“°¢v¢7ƒ°¢FF–æs¢7ƒ°¢&÷&FW#¢‚6öÆ–B3CS6#ƒ°¢&÷&FW"×&F—W3¢—ƒ°¢&6¶w&÷VæC¢3S3c°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–WrÖæb'WGFöâ°¢Ö–â×v–GFƒ¢°¢Ö–âÖ†V–v‡C¢Cƒ°¢FF–æs¢w‚‡ƒ°¢&÷&FW#¢°¢&÷&FW"×&F—W3¢gƒ°¢&6¶w&÷VæC¢G&ç7&VçC°¢6öÆ÷#¢3–c–“°¢föçC¢–æ†W&—C°¢föçB×6—¦S¢'ƒ°¢föçB×vV–v‡C¢ƒ°¢7W'6÷#¢ö–çFW#°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–WrÖæb'WGFöâçF×7FG2×f–WrÖ7F—fR°¢&6¶w&÷VæC¢333#ƒs°¢6öÆ÷#¢6c6cƒs°¢&÷‚×6†F÷s¢–ç6WB‚&v&ƒ#’Âc2ÂsRÂã3R“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–WrÖæb'WGFöã¦fö7W2×f—6–&ÆR°¢÷WFÆ–æS¢'‚6öÆ–B6C3F#°¢÷WFÆ–æRÖöfg6WC¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–Wr×æVÂ°¢Ö–â×v–GFƒ¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2ÖV×G’×7FFR°¢FF–æs¢G‚ƒ°¢&÷&FW"×F÷¢‚6öÆ–B33C3&°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B33C3&°¢6öÆ÷#¢6C–°¢föçB×6—¦S¢'ƒ°¢Æ–æRÖ†V–v‡C¢ãCS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2ÖFFÖÆ—7B°¢F—7Æ“¢w&–C°¢&÷&FW"×F÷¢‚6öÆ–B33C3&°¢&÷&FW"Ö&÷GFöÓ¢‚6öÆ–B33C3&°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ&Æö6²°¢F—7Æ“¢w&–C°¢v¢—ƒ°¢Ö–â×v–GFƒ¢°¢FF–æs¢'‚Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ&Æö6²²çF×7FBÖFFÖ&Æö6²°¢&÷&FW"×F÷¢‚6öÆ–B33&3#S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ†VF–ær°¢F—7Æ“¢fÆWƒ°¢Æ–vâÖ—FV×3¢&6VÆ–æS°¢§W7F–g’Ö6öçFVçC¢76RÖ&WGvVVã°¢v¢—ƒ°¢6öÆ÷#¢6SvSCs°¢föçB×6—¦S¢7ƒ°¢föçB×vV–v‡C¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ†VF–ærâ7ã¦Æ7BÖ6†–ÆB°¢6öÆ÷#¢3“†#ƒ#°¢föçB×6—¦S¢ƒ°¢föçB×vV–v‡C¢s°¢FW‡BÖÆ–vã¢&–v‡C°¢Ð ¢2G´ÔôDÅô”GÒ7VÖÖ'’çF×7FBÖFFÖ†VF–ær°¢7W'6÷#¢ö–çFW#°¢Æ—7B×7G–ÆS¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒ7VÖÖ'’çF×7FBÖFFÖ†VF–æs£¢×vV&¶—BÖFWF–Ç2ÖÖ&¶W"°¢F—7Æ“¢æöæS°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–ÒÖ'&V¶F÷vââ7VÖÖ'“£¦gFW"°¢6öçFVçC¢~(¢s°¢6öÆ÷#¢6s–C†°¢föçB×6—¦S¢‡ƒ°¢Æ–æRÖ†V–v‡C¢°¢G&ç6f÷&Ó¢&÷FFRƒ“FVr“°¢G&ç6—F–öã¢G&ç6f÷&ÒãW2V6S°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–ÒÖ'&V¶F÷vå¶÷VåÒâ7VÖÖ'“£¦gFW"°¢G&ç6f÷&Ó¢&÷FFR‚Ó“FVr“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖw–ÒÖ'&V¶F÷vã¦æ÷B…¶÷VåÒ’°¢v¢°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ&öG’°¢F—7Æ“¢w&–C°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ&Æö6²çF×7FB×VÆ—G’×v&æ–ær°¢&÷‚×6†F÷s¢–ç6WB7‚6cf#C3°¢FF–ærÖÆVgC¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖVæW&w’ÖÆÆö6F–öâçFÖ6FVv÷'’ÖÆ—7B°¢FF–æs¢°¢&÷&FW#¢°¢&6¶w&÷VæC¢G&ç7&VçC°¢Ð ¢ÖVF–†Ö‚×v–GFƒ£S#‚’°¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’Ö†VFW"°¢Æ–vâÖ—FV×3¢7G&WF6ƒ°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢v¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×W&–öB°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢WFòÖ–æÖ‚ƒÂg"“°¢Æ–vâÖ—FV×3¢6VçFW#°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×6VÆV7F÷'2°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7W÷'BÖ6öçG&öÇ2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"“°¢Ð ¢2G´ÔôDÅô”GÒçF×G&–æ–ær×7VÖÖ'’×W&–öB6VÆV7B°¢v–GFƒ¢S°¢Ð¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ–ç7V7F÷"°¢FF–æs¢‡ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖ†VFW"7G&öær°¢föçB×6—¦S¢wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâ×V–6¶Æ–æR7G&öærÀ¢2G´ÔôDÅô”GÒçF×7FB×6W76–öâÖf7G2"°¢föçB×6—¦S¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆR°¢föçB×6—¦S¢ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRF‚À¢2G´ÔôDÅô”GÒçF×7FB×v–æF÷r×F&ÆRFB°¢FF–æs¢w‚Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'’°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂg"’WFò—ƒ°¢v¢Gƒ°¢FF–æs¢‡‚wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFVç6RÖÖWG&–2â7VÖÖ'’7G&öær°¢föçB×6—¦S¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂã“Vg"’Ö–æÖ‚ƒÂã“Vg"’Ö–æÖ‚ƒ3'‚Âã#Vg"“°¢v¢Gƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ2ÖÆÂ°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢Ö–æÖ‚ƒÂã–g"’Ö–æÖ‚ƒCW‚Âã&g"“°¢Ð ¢2G´ÔôDÅô”GÒçF×7FB×F÷FÂÖ6öçG&öÇ26VÆV7B°¢FF–ær×&–v‡C¢wƒ°¢föçB×6—¦S¢—ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FG2×f–WrÖæb'WGFöâ°¢Ö–âÖ†V–v‡C¢3‡ƒ°¢FF–ærÖ–æÆ–æS¢Wƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ†VF–ær°¢Æ–vâÖ—FV×3¢fÆW‚×7F'C°¢fÆW‚ÖF—&V7F–öã¢6öÇVÖã°¢v¢'ƒ°¢Ð ¢2G´ÔôDÅô”GÒçF×7FBÖFFÖ†VF–ærâ7ã¦Æ7BÖ6†–ÆB°¢FW‡BÖÆ–vã¢ÆVgC°¢Ð¢Ð ¢ÖVF–†Ö‚×v–GFƒ£3c‚’°¢2G´ÔôDÅô”GÒçF×7FB×7VÖÖ'’×F–ÆW2°¢w&–B×FV×ÆFRÖ6öÇVÖç3¢g#°¢Ð¢Ð ¢° ¢Fö7VÖVçBæ†VBæVæD6†–ÆB€¢7G–ÆP¢“°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòÔôDÀ¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâ6†÷VÆE&W7F÷&U7F÷&VDæÇ—6—2€¢&W7F÷&U7FFRÀ¢66†VBÀ¢æÇ—¦T'WGFöà¢’°¢fö–B&W7F÷&U7FFS° ¢&WGW&â&ööÆVâ€¢66†VCòæ66÷VçEö–Bb`¢66†VBæ6÷VçBb`¢æÇ—¦T'WGFöâb`¢WFöÖF–4Æöu7–æ5'Vææ–æp¢“°¢Ð ¢gVæ7F–öâ7F÷&VD†—7F÷'•7VÖÖ'”‡FÖÂ€¢66†V@¢’°¢–b€¢66†VCòæ66÷VçEö–BÇÀ¢66†VBæ6÷Vç@¢’°¢&WGW&ârs°¢Ð ¢&WGW&â ¢G¶66†VBæ66÷VçEöæÖWÐ¢²G¶66†VBæ66÷VçEö–GÕÐ¢Æ'#à¢G¶66†VBæ6÷VçBçFôÆö6ÆU7G&–ær‚—Ð¢Æöw0¢Æ'#à¢G·F–ÖW7F×FôÆö6ÄFFR†66†VBæf—'7E÷F–ÖW7F×—Ð¢(i ¢G·F–ÖW7F×FôÆö6ÄFFR†66†VBæÆ7E÷F–ÖW7F×—Ð¢°¢Ð ¢7–æ2gVæ7F–öâ÷VäÖöFÂ€¢÷F–öç2Ò·Ð¢’° ¢–b€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢ÔôDÅô”@¢¢’°¢&WGW&ã°¢Ð ¢–æ¦V7E7G–ÆW2‚“° ¢6öç7B66†VBÐ¢v—BvWDÆ7D66†TÖWF‚“° ¢6öç7B'V–ÆE7FFRÐ¢66†VCòæ66÷VçEö–@¢òv—BvWD'V–ÆE7FFR€¢66†VBæ66÷VçEö–@¢¢¢çVÆÃ° ¢6öç7B6fVD¶W’Ð¢v—BÆöE6V7W&T”¶W’‚“° ¢6öç7BÖöFÂÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢vF—bp¢“° ¢ÖöFÂæ–BÐ¢ÔôDÅô”C° ¢ÆWB†—7F÷'•6V7F–öã° ¢–b€¢66†VCòæ66÷VçEö–Bb`¢66†VBæ6÷Vç@¢’° ¢†—7F÷'•6V7F–öâÒ  ¢ÆF—b6Æ73Ò'æVÂ#à ¢Æ#à¢7F÷&VB†—7F÷'¢Âö#à ¢ÆF—`¢–CÒ'F×7F÷&VBÖ†—7F÷'’×7VÖÖ'’ ¢6Æ73Ò'6ÖÆÂ ¢à¢G·7F÷&VD†—7F÷'•7VÖÖ'”‡FÖÂ†66†VB—Ð¢ÂöF—cà ¢ÂöF—cà ¢° ¢ÒVÇ6R° ¢†—7F÷'•6V7F–öâÒ  ¢ÆF—b6Æ73Ò'6WGW#à ¢Æ#à¢–æ—F–Â6WGW&WV—&V@¢Âö#à ¢ÆF—b6Æ73Ò'6ÖÆÂ#à ¢æò7F÷&VB†—7F÷'’W†—7G2öâF†—2FWf–6R–WBà ¢–÷W"f—'7B†—7F÷'’'V–ÆBv–ÆÂF÷væÆöB–÷W"F÷&à¢W'6öæÂÆöw2æB6fRV6‚6ö×ÆWFVB6V7F–öà¢–ÖÖVF–FVÇ’à ¢gFW"F†—2ÂgWGW&RæÇ—F–72WFFW2v–ÆÂæ÷&ÖÆÇ¢W6RF†R7F÷&VB†—7F÷'’–ç7FVBöbF÷væÆöF–æp¢WfW'—F†–ærv–âà ¢ÂöF—cà ¢ÂöF—cà ¢°¢Ð ¢ÖöFÂæ–ææW$…DÔÂÒ  ¢ÆF—b6Æ73Ò&6&B#à ¢ÆF—b6Æ73Ò'FÖÖöFÂÖ†VFW"#à¢Æƒ#à¢F÷&âæÇ—F–72bGµdU%4”ôçÐ¢Âöƒ#à ¢Æ'WGFöà¢–CÒ'FÖ6Æ÷6R ¢6Æ73Ò'FÖÖöFÂÖ6Æ÷6R ¢G—SÒ&'WGFöâ ¢à¢6Æ÷6P¢Âö'WGFöãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'FÖÖöFÂ×67&öÆÂ#à ¢ÆF—b6Æ73Ò'7V"#à ¢–÷W"&rF÷&âÆör†—7F÷'’—27F÷&VBÆö6ÆÇ’–â–æFW†VDD ¢æB&VÖ–ç2f–Æ&ÆRv†VâF†RW6W'67&—B6öFR—2&WÆ6V@¢'’gWGW&R6ö×F–&ÆRfW'6–öç2à ¢ÂöF—cà ¢G¶†—7F÷'•6V7F–öçÐ ¢ÆFWF–Ç26Æ73Ò'F×6V7F–öâF×6WGF–æw2×6V7F–öâ#à¢Ç7VÖÖ'’6Æ73Ò'F×6V7F–öâ×7VÖÖ'’×&÷r#à¢Ç7â6Æ73Ò'F×6V7F–öâ×F—FÆR#å6WGF–æw3Â÷7ãà¢Ç7â6Æ73Ò'F×6V7F–öâÖÖWF#ä7F–öç2f×²&VfW&Væ6W3Â÷7ãà¢Â÷7VÖÖ'“à ¢ÆF—b6Æ73Ò'F×6V7F–öâÖ&öG’#à¢ÆF—b6Æ73Ò'F×6WGF–æw2×&–Ö'’#à¢ÆF—b6Æ73Ò'F×6WGF–æw2×7FGW2×7G&—#à¢Æ#äWFöÖF–2WFFW3Âö#à¢Ç7à¢–CÒ'FÖWFöÖF–2×7–æ2×7FGW2 ¢6Æ73Ò'6ÖÆÂ ¢à¢G¶WFöÖF–4Æöu7–æ57FGW5FW‡B†66†VB—Ð¢Â÷7ãà¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×6WGF–æw2Öw&÷W#à¢ÆÆ&VÂ6Æ73Ò'F×6WGF–æw2ÖÆ&VÂ"f÷#Ò'FÖ¶W’#à¢’¶W¢ÂöÆ&VÃà ¢Æ–çW@¢–CÒ'FÖ¶W’ ¢G—SÒ'77v÷&B ¢WFö6ö×ÆWFSÒ&öfb ¢fÇVSÒ" ¢Æ6V†öÆFW#Ò"G·6fVD¶W’òu6fVB6V7W&VÇ’(	BÆVfR&Ææ²Fò&WW6Rr¢tVçFW"F÷&â’¶W’wÒ ¢à¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×6WGF–æw2Öw&÷W#à¢G·&VæFW$7F—f—G•F–ÖT&6—46öçG&öÂ‚—Ð¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×6WGF–æw2Öw&÷W#à¢Æ#äFFf×²æÇ—6—3Âö#à ¢ÆF—`¢–CÒ'FÖÖ–âÖ7F–öç2 ¢6Æ73Ò&7F–öç2F×6WGF–æw2×&–Ö'’Ö7F–öç2 ¢à¢G°¢66†VCòæ66÷VçEö–@¢ò ¢Æ'WGFöâ–CÒ'F×WFFR#à¢WFFRÆöw0¢Âö'WGFöãà ¢Æ'WGFöâ–CÒ'FÖæÇ—¦R#à¢&VæÇ—¦P¢Âö'WGFöãà ¢Æ'WGFöà¢–CÒ'FÖW‡÷'BÖ†—7F÷'’ ¢6Æ73Ò'F×6WGF–æw2Ö7F–öâ×v–FR ¢à¢W‡÷'B†—7F÷'¢Âö'WGFöãà ¢Æ'WGFöà¢–CÒ'F×6fRÖW‡÷'B ¢6Æ73Ò'F×6WGF–æw2Ö7F–öâ×v–FR ¢7G–ÆSÒ&F—7Æ“¦æöæR ¢à¢6fRW‡÷'Bf–ÆP¢Âö'WGFöãà ¢ÆF—b6Æ73Ò'6ÖÆÂF×6WGF–æw2Ö7F–öâ×v–FR#à¢W‡÷'B7&VFW2&VF&ÆR&—fFR6÷’v—F†÷WB¢÷"Væ7'—F–öâ¶W—2à¢ÂöF—cà¢ ¢¢ ¢Æ'WGFöà¢–CÒ'FÖ'V–ÆB ¢6Æ73Ò'F×6WGF–æw2Ö7F–öâ×v–FR ¢à¢'V–ÆB×’†—7F÷'¢Âö'WGFöãà¢ ¢Ð¢ÂöF—cà¢ÂöF—cà¢ÂöF—cà ¢ÆFWF–Ç0¢–CÒ'FÖF–væ÷7F–72×&V6÷fW'’ ¢6Æ73Ò'F×6WGF–æw2ÖGfæ6VB ¢à¢Ç7VÖÖ'’6Æ73Ò'F×6WGF–æw2ÖGfæ6VB×7VÖÖ'’#à¢Ç7ãà¢Æ#äF–væ÷7F–72f×²&V6÷fW'“Âö#à¢Ç6ÖÆÂ–CÒ'FÖF–væ÷7F–72×7VÖÖ'’ÖÖWF#à¢6†V6·2æBGfæ6VBFööÇ0¢Â÷6ÖÆÃà¢Â÷7ãà ¢Ç7G&öær–CÒ'FÖF–væ÷7F–72×7FGW2#à¢6†V6¶–æ~(
`¢Â÷7G&öæsà¢Â÷7VÖÖ'“à ¢ÆF—`¢–CÒ'FÖF–væ÷7F–72×&V6÷fW'’Ö&öG’ ¢6Æ73Ò'F×6WGF–æw2ÖGfæ6VBÖ&öG’ ¢à¢ÆF—b6Æ73Ò'FÖF–væ÷7F–72Ö÷fW'f–Wr#à¢Æ"–CÒ'FÖF–væ÷7F–72Ö÷fW'f–Wr×F—FÆR#à¢7—7FVÒ7FGW3¢6†V6¶–æ~(
`¢Âö#à ¢ÆF—`¢–CÒ'FÖF–væ÷7F–72Ö÷fW'f–WrÖÖWF ¢6Æ73Ò'6ÖÆÂ ¢à¢&VF–ærÆö6ÂF–væ÷7F–27FGW2à¢ÂöF—cà ¢Æ'WGFöà¢–CÒ'F×&Vg&W6‚ÖF–væ÷7F–72 ¢G—SÒ&'WGFöâ ¢à¢&Vg&W6‚F–væ÷7F–70¢Âö'WGFöãà¢ÂöF—cà ¢ÆFWF–Ç26Æ73Ò'F×6WGF–æw2×FööÂ#à¢Ç7VÖÖ'“åG&–æ–ær6GW&R6†V6·3Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×6WGF–æw2×FööÂÖ&öG’#à¢Æ#å6æ6†÷B66W73Âö#à ¢ÆF—b6Æ73Ò'6ÖÆÂ#à¢&VBÖöæÇ’vR6&–Æ—G’6†V6²â—BFöW2æ÷BG&–âÀ¢7VæBVæW&w’ÂW6Râ—FVÒÂ÷"Ö¶Râ’&WVW7Bà¢ÂöF—cà ¢ÆF—`¢–CÒ'F×G&–æ–ær×6æ6†÷BÖ6†V6²Ö÷WGWB ¢6Æ73Ò'6ÖÆÂF×G&–æ–ær×6æ6†÷BÖ6†V6²Ö÷WGWB ¢&–ÖÆ—fSÒ'öÆ—FR ¢à¢æ÷B6†V6¶VBöâF†—2vR–WBà¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×6WGF–æw2×FööÂÖF—f–FW"#ãÂöF—cà ¢Æ#ä†–æW72’6†V6³Âö#à ¢ÆF—b6Æ73Ò'6ÖÆÂ#à¢Ö¶W2öæRöff–6–Â&VBÖöæÇ’F÷&â’&'2&WVW7Bâ—@¢FöW2æ÷BöÆÂÂG&–âÂ7VæBVæW&w’ÂW6Râ—FVÒÂ÷"6fP¢F†Rö'6W'fVB&'2à¢ÂöF—cà ¢Æ'WGFöà¢–CÒ'FÖ†–æW72Ö6GW&RÖ6†V6² ¢G—SÒ&'WGFöâ ¢à¢6†V6²†–æW72’66W70¢Âö'WGFöãà ¢ÆF—`¢–CÒ'FÖ†–æW72Ö6GW&RÖ÷WGWB ¢6Æ73Ò'6ÖÆÂFÖ†–æW72Ö6GW&RÖ÷WGWB ¢&–ÖÆ—fSÒ'öÆ—FR ¢à¢æ÷B6†V6¶VB–âF†—2ÖöFÂ6W76–öâà¢ÂöF—cà¢ÂöF—cà¢ÂöFWF–Ç3à ¢ÆFWF–Ç26Æ73Ò'F×6WGF–æw2×FööÂ#à¢Ç7VÖÖ'“äFWF–ÆVB†VÇF‚&W÷'G3Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×6WGF–æw2×FööÂÖ&öG’#à¢Æ#å&R×G&–æ–ær6†V6·ö–çG3Âö#à ¢ÆF—`¢–CÒ'F×G&–æ–ærÖ6†V6·ö–çBÖ÷WGWB ¢6Æ73Ò'6ÖÆÂF×G&–æ–ærÖ6†V6·ö–çBÖ6æ'’Ö÷WGWB ¢&–ÖÆ—fSÒ'öÆ—FR ¢à¢ÆöF–ær6†V6·ö–çB7FGW>(
`¢ÂöF—cà ¢ÆF—b6Æ73Ò'F×6WGF–æw2×FööÂÖF—f–FW"#ãÂöF—cà ¢Æ#å&VÆ–&–Æ—G’†VÇFƒÂö#à ¢ÆF—b6Æ73Ò'6ÖÆÂ#à¢&÷VæFVB7FGW2öæÇž(	FæWfW"’¶W—2Â†—7F÷'’¶W—2Â÷ ¢ÆörFFà¢ÂöF—cà ¢ÆF—`¢–CÒ'F×&VÆ–&–Æ—G’Ö†VÇF‚Ö÷WGWB ¢6Æ73Ò'6ÖÆÂF×G&–æ–ærÖ6†V6·ö–çBÖ6æ'’Ö÷WGWB ¢&–ÖÆ—fSÒ'öÆ—FR ¢à¢ÆöF–ær&VÆ–&–Æ—G’7FGW>(
`¢ÂöF—cà¢ÂöF—cà¢ÂöFWF–Ç3à ¢ÆFWF–Ç26Æ73Ò'F×6WGF–æw2×FööÂ#à¢Ç7VÖÖ'“ä†—7F÷'’F–væ÷7F–72f×²&V6÷fW'“Â÷7VÖÖ'“à¢ÆF—b6Æ73Ò'F×6WGF–æw2×FööÂÖ&öG’FÖ†—7F÷'’×FööÇ2#à¢G°¢66†VCòæ66÷VçEö–@¢ò ¢Æ'WGFöâ–CÒ'FÖf÷&Vç6–2Ö†—7F÷'’#à¢'Vâ†—7F÷'’F–væ÷7F–0¢Âö'WGFöãà ¢Æ'WGFöâ–CÒ'F×G&6RÖ†—7F÷'’#à¢G&6R&V'V–ÆB6öÆÆV7F÷ ¢Âö'WGFöãà ¢Æ'WGFöâ–CÒ'F×&V'V–ÆB#à¢&V'V–ÆBgVÆÂ†—7F÷'¢Âö'WGFöãà ¢ÆF—b6Æ73Ò'6ÖÆÂ#à¢gVÆÂ&V'V–ÆB&V6öÆÆV7G2æBfW&–f–W2&WÆ6VÖVç@¢&Vf÷&RFöÖ–6ÆÇ’&öÖ÷F–ær—Bà¢ÂöF—cà¢ ¢¢ ¢ÆF—b6Æ73Ò'6ÖÆÂ#à¢†—7F÷'’FööÇ2&V6öÖRf–Æ&ÆRgFW"F†R–æ—F–À¢†—7F÷'’'V–ÆBà¢ÂöF—cà¢ ¢Ð¢ÂöF—cà¢ÂöFWF–Ç3à¢ÂöF—cà¢ÂöFWF–Ç3à¢ÂöF—cà¢ÂöFWF–Ç3à ¢ÆF—b6Æ73Ò'æVÂ#à ¢ÆF—b6Æ73Ò'F÷#à ¢Ç7â–CÒ'F×7FvR#à¢&VG¢Â÷7ãà ¢Ç7â–CÒ'F×W&6VçB#à¢P¢Â÷7ãà ¢ÂöF—cà ¢ÆF—b6Æ73Ò'G&6²#à ¢ÆF—`¢–CÒ'FÖf–ÆÂ ¢6Æ73Ò&f–ÆÂ ¢ãÂöF—cà ¢ÂöF—cà ¢ÆF—`¢–CÒ'FÖFWF–Â ¢6Æ73Ò'6ÖÆÂ ¢à ¢G°¢66†VCòæ66÷VçEö–@¢òu7F÷&VB†—7F÷'’—2&VG’âp¢¢tVçFW"–÷W"’¶W’æB'V–ÆB–÷W"†—7F÷'’öæ6Râp¢Ð ¢ÂöF—cà ¢ÆF—b6Æ73Ò'7FG2#à ¢ÆF—cà¢Æöw3 ¢Æ"–CÒ'FÖÆöw2#à¢G¶66†VCòæ6÷VçCòçFôÆö6ÆU7G&–ær‚’óòswÐ¢Âö#à¢ÂöF—cà ¢ÆF—cà¢UD ¢Æ"–CÒ'FÖWF#à¢(	@¢Âö#à¢ÂöF—cà ¢ÆF—cà¢VÆ6VC ¢Æ"–CÒ'FÖVÆ6VB#à¢0¢Âö#à¢ÂöF—cà ¢ÆF—cà¢’&WVW7G3 ¢Æ"–CÒ'F×&WVW7G2#à¢ ¢Âö#à¢ÂöF—cà ¢ÆF—cà¢&ævR7Æ—G3 ¢Æ"–CÒ'F×7Æ—G2#à¢ ¢Âö#à¢ÂöF—cà ¢ÂöF—cà ¢ÂöF—cà ¢ÆF—b–CÒ'F×7FGW2#ãÂöF—cà ¢ÂöF—cà ¢ÂöF—cà¢° ¢Fö7VÖVçBæ&öG’æVæD6†–ÆB€¢ÖöFÀ¢“° ¢6öç7BBÐ¢6VÆV7F÷"Óà¢ÖöFÂçVW'•6VÆV7F÷"€¢6VÆV7F÷ ¢“° ¢6öç7B¶W”–çWBÐ¢B‚r7FÖ¶W’r“° ¢6öç7B6Æ÷6T'WGFöâÐ¢B‚r7FÖ6Æ÷6Rr“° ¢6öç7B67&öÆÄ6öçF–æW"Ð¢B‚rçFÖÖöFÂ×67&öÆÂr“° ¢6öç7BæÇ—6—4†÷7BÐ¢B‚r7F×7FGW2r“° ¢6öç7BG&–æ–æu6æ6†÷D6†V6´÷WGWBÐ¢B‚r7F×G&–æ–ær×6æ6†÷BÖ6†V6²Ö÷WGWBr“° ¢6öç7B†–æW746GW&T6†V6´'WGFöâÐ¢B‚r7FÖ†–æW72Ö6GW&RÖ6†V6²r“° ¢6öç7B†–æW746GW&T÷WGWBÐ¢B‚r7FÖ†–æW72Ö6GW&RÖ÷WGWBr“° ¢6öç7BG&–æ–æt6†V6·ö–çD÷WGWBÐ¢B‚r7F×G&–æ–ærÖ6†V6·ö–çBÖ÷WGWBr“° ¢6öç7B&VÆ–&–Æ—G”†VÇF„÷WGWBÐ¢B‚r7F×&VÆ–&–Æ—G’Ö†VÇF‚Ö÷WGWBr“° ¢6öç7BF–væ÷7F–756V7F–öâÐ¢B‚r7FÖF–væ÷7F–72×&V6÷fW'’r“° ¢6öç7BF–væ÷7F–75&Vg&W6„'WGFöâÐ¢B‚r7F×&Vg&W6‚ÖF–væ÷7F–72r“° ¢6öç7BF–væ÷7F–757FGW2Ð¢B‚r7FÖF–væ÷7F–72×7FGW2r“° ¢6öç7BF–væ÷7F–757VÖÖ'”ÖWFÐ¢B‚r7FÖF–væ÷7F–72×7VÖÖ'’ÖÖWFr“° ¢6öç7BF–væ÷7F–74÷fW'f–WuF—FÆRÐ¢B‚r7FÖF–væ÷7F–72Ö÷fW'f–Wr×F—FÆRr“° ¢6öç7BF–væ÷7F–74÷fW'f–WtÖWFÐ¢B‚r7FÖF–væ÷7F–72Ö÷fW'f–WrÖÖWFr“° ¢gVæ7F–öâ&Vg&W6…G&–æ–æu6æ6†÷D6&–Æ—G”6†V6²‚’°¢–b€¢G&–æ–æu6æ6†÷D6†V6´÷WGW@¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B&ö&RÐ¢G&–æ–æu6æ6†÷D6&–Æ—G•&ö&R‚“° ¢G&–æ–æu6æ6†÷D6†V6´÷WGWBçFW‡D6öçFVçBÐ¢G&–æ–æu6æ6†÷D6&–Æ—G•FW‡B€¢&ö&P¢“° ¢&WGW&â&ö&S°¢Ð ¢&Vg&W6…G&–æ–æu6æ6†÷D6&–Æ—G”6†V6²‚“° ¢–b€¢†–æW746GW&T6†V6´'WGFöà¢’°¢†–æW746GW&T6†V6´'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢7–æ2‚’Óâ°¢–b€¢†–æW746GW&T÷WGWBÇÀ¢†–æW746GW&T6†V6´'WGFöâæF—6&ÆV@¢’°¢&WGW&ã°¢Ð ¢†–æW746GW&T6†V6´'WGFöâæF—6&ÆVBÐ¢G'VS° ¢†–æW746GW&T÷WGWBçFW‡D6öçFVçBÐ¢t6†V6¶–ærF†Röff–6–ÂF÷&â’öæ6^(
bs° ¢ÆWB”¶W’Ð¢rs° ¢G'’°¢”¶W’Ð¢v—BvWD÷F–öæÄ”¶W’‚“° ¢–b€¢”¶W¢’°¢†–æW746GW&T÷WGWBçFW‡D6öçFVçBÐ¢tæ÷B'Vâ(	B6fRF÷&â’¶W’–â6WGF–æw2f—'7Bâs° ¢&WGW&ã°¢Ð ¢6öç7B&W7VÇBÐ¢v—B'Vä†–æW746GW&T6æ'’€¢”¶W¢“° ¢†–æW746GW&T÷WGWBçFW‡D6öçFVçBÐ¢†–æW73¢G·&W7VÇBæ†–æW72æ7W'&VçBçFôÆö6ÆU7G&–ær‚—ÒòG·&W7VÇBæ†–æW72æÖ†–×VÒçFôÆö6ÆU7G&–ær‚—ÕÆæ°¢VæW&w“¢G·&W7VÇBæVæW&w’æ7W'&VçBçFôÆö6ÆU7G&–ær‚—ÒòG·&W7VÇBæVæW&w’æÖ†–×VÒçFôÆö6ÆU7G&–ær‚—ÕÆæ°¢6÷W&6S¢G·&W7VÇBç6÷W&6WÕÆæ°¢&WVW7FVC¢G¶æWrFFR‡&W7VÇBç&WVW7FVEöB’çFôÆö6ÆU7G&–ær‚—ÕÆæ°¢&V6V—fVC¢G¶æWrFFR‡&W7VÇBç&V6V—fVEöB’çFôÆö6ÆU7G&–ær‚—ÕÆæ°¢&W7öç6RF–ÖS¢G·&W7VÇBæÆFVæ7•ö×2çFôÆö6ÆU7G&–ær‚—Ò×6°¢Ò6F6‚€¢W'&÷ ¢’°¢†–æW746GW&T÷WGWBçFW‡D6öçFVçBÐ¢6GW&Rf–ÆVB6fVÇ’(	BG¶†–æW746GW&T6æ'”W'&÷%FW‡B†W'&÷"Â”¶W’—Ö°¢Òf–æÆÇ’°¢†–æW746GW&T6†V6´'WGFöâæF—6&ÆVBÐ¢fÇ6S°¢Ð¢Ð¢“°¢Ð ¢gVæ7F–öâ&Vg&W6…G&–æ–æt6†V6·ö–çD6æ'•7FGW2‚’°¢–b€¢G&–æ–æt6†V6·ö–çD÷WGW@¢’°¢&WGW&âçVÆÃ°¢Ð ¢6öç7B7FFRÐ¢&VEG&–æ–æt6†V6·ö–çD6æ'•7FFR‚“° ¢G&–æ–æt6†V6·ö–çD÷WGWBçFW‡D6öçFVçBÐ¢G&–æ–æt6†V6·ö–çD6æ'•7FGW5FW‡B€¢7FFP¢“° ¢&WGW&â7FFS°¢Ð ¢&Vg&W6…G&–æ–æt6†V6·ö–çD6æ'•7FGW2‚“° ¢gVæ7F–öâ&Vg&W6…&VÆ–&–Æ—G”†VÇF…&W÷'B‚’°¢–b€¢&VÆ–&–Æ—G”†VÇF„÷WGW@¢’°¢&WGW&âçVÆÃ°¢Ð ¢G'’°¢6öç7B&W÷'BÐ¢'V–ÆE&VÆ–&–Æ—G”†VÇF…&W÷'B‚“° ¢&VÆ–&–Æ—G”†VÇF„÷WGWBçFW‡D6öçFVçBÐ¢&VÆ–&–Æ—G”†VÇF…&W÷'EFW‡B€¢&W÷'@¢“° ¢&WGW&â&W÷'C°¢Ò6F6‚…ò’°¢&VÆ–&–Æ—G”†VÇF„÷WGWBçFW‡D6öçFVçBÐ¢u&VÆ–&–Æ—G’&W÷'BVæf–Æ&ÆRâF†RÆVæ6†W"&VÖ–ç2–æFWVæFVçBâs° ¢&WGW&âçVÆÃ°¢Ð¢Ð ¢&Vg&W6…&VÆ–&–Æ—G”†VÇF…&W÷'B‚“° ¢gVæ7F–öâ&Vg&W6„F–væ÷7F–74÷fW'f–Wr‚’°¢6öç7B&ö&RÐ¢&Vg&W6…G&–æ–æu6æ6†÷D6&–Æ—G”6†V6²‚“° ¢6öç7B6†V6·ö–çBÐ¢&Vg&W6…G&–æ–æt6†V6·ö–çD6æ'•7FGW2‚“° ¢6öç7B&W÷'BÐ¢&Vg&W6…&VÆ–&–Æ—G”†VÇF…&W÷'B‚“° ¢6öç7B6†V6·ö–çE7FGW2Ð¢6†V6·ö–çCòæÆ7E÷7FGW2ÇÀ¢wVæf–Æ&ÆRs° ¢6öç7BÆVæ6†W%&VG’Ð¢°¢w&VG’rÀ¢vÖöFÅö÷Vå÷&WVW7FVBp¢Òæ–æ6ÇVFW2€¢&W÷'CòæÆVæ6†W#òç7FvP¢“° ¢6öç7B6†V6·ö–çD†VÇF‡’Ð¢6†V6·ö–çCòç7F÷&vUö6ö×F–&ÆRÓÐ¢fÇ6Rb`¢°¢vf–ÆVBrÀ¢wVç7W÷'FVE÷66†VÖp¢Òæ–æ6ÇVFW2€¢6†V6·ö–çE7FGW0¢“° ¢6öç7BæVVG4”¶W’Ð¢6†V6·ö–çE7FGW2ÓÓÐ¢væõö•ö¶W’s° ¢6öç7B†VÇF‡’Ð¢ÆVæ6†W%&VG’b`¢6†V6·ö–çD†VÇF‡’b`¢æVVG4”¶W“° ¢6öç7B7FGW4Æ&VÂÐ¢†VÇF‡¢òt†VÇF‡’p¢¢æVVG4”¶W¢òu6WGWæVVFVBp¢¢u&Wf–Wrs° ¢6öç7B7FGW5F—FÆRÐ¢†VÇF‡¢òu7—7FVÒ7FGW3¢†VÇF‡’p¢¢æVVG4”¶W¢òu7—7FVÒ7FGW3¢’¶W’æVVFVBp¢¢u7—7FVÒ7FGW3¢&Wf–WrF–væ÷7F–72s° ¢6öç7B6†V6·ö–çD6÷VçBÐ¢'&’æ—4'&’€¢6†V6·ö–çCòæ6†V6·ö–çG0¢¢ò6†V6·ö–çBæ6†V6·ö–çG2æÆVæwF€¢¢° ¢6öç7B–çFVçD6÷VçBÐ¢'&’æ—4'&’€¢6†V6·ö–çCòçG&–åö–çFVçG0¢¢ò6†V6·ö–çBçG&–åö–çFVçG2æÆVæwF€¢¢° ¢6öç7B6æ6†÷D66W72Ð¢&ö&Sòç&W6÷W&6Uö&'2ÓÓÐ¢w&VG’p¢òwvR6æ6†÷Bf–Æ&ÆRp¢¢t’6†V6·ö–çBfÆÆ&6²7F—fRs° ¢–b€¢F–væ÷7F–757FGW0¢’°¢F–væ÷7F–757FGW2çFW‡D6öçFVçBÐ¢7FGW4Æ&VÃ°¢Ð ¢–b€¢F–væ÷7F–757VÖÖ'”ÖWF¢’°¢F–væ÷7F–757VÖÖ'”ÖWFçFW‡D6öçFVçBÐ¢G¶6†V6·ö–çD6÷VçBçFôÆö6ÆU7G&–ær‚—Ò6†V6·ö–çG2+rG¶–çFVçD6÷VçBçFôÆö6ÆU7G&–ær‚—ÒG&–âF6°¢Ð ¢–b€¢F–væ÷7F–74÷fW'f–WuF—FÆP¢’°¢F–væ÷7F–74÷fW'f–WuF—FÆRçFW‡D6öçFVçBÐ¢7FGW5F—FÆS°¢Ð ¢–b€¢F–væ÷7F–74÷fW'f–WtÖWF¢’°¢F–væ÷7F–74÷fW'f–WtÖWFçFW‡D6öçFVçBÐ¢ÆVæ6†W"G·&W÷'CòæÆVæ6†W#òç7FvRÇÂwVæf–Æ&ÆRwÒ+r6†V6·ö–çBVæv–æRG¶6†V6·ö–çE7FGW2ç&WÆ6R‚õòörÂrr—Ò+rG·6æ6†÷D66W77Òæ°¢Ð ¢&WGW&â°¢†VÇF‡’À¢6†V6·ö–çBÀ¢&W÷'BÀ¢&ö&P¢Ó°¢Ð ¢–b€¢F–væ÷7F–75&Vg&W6„'WGFöà¢’°¢F–væ÷7F–75&Vg&W6„'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢&Vg&W6„F–væ÷7F–74÷fW'f–Wp¢“°¢Ð ¢F–væ÷7F–756V7F–öãòæFDWfVçDÆ—7FVæW"€¢wFövvÆRrÀ¢‚’Óâ°¢–b€¢F–væ÷7F–756V7F–öâæ÷Và¢’°¢&Vg&W6„F–væ÷7F–74÷fW'f–Wr‚“°¢Ð¢Ð¢“° ¢&Vg&W6„F–væ÷7F–74÷fW'f–Wr‚“° ¢f÷"€¢6öç7B'WGFöà¢öbÖöFÂçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×F–ÖRÖ&6—5Òp¢¢’°¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢‚’Óâ°¢6öç7BæW‡BÐ¢7F—f—G”F6†&ö&DÇ•F–ÖT&6—2€¢æÇ—6—4†÷7BÀ¢'WGFöâævWDGG&–'WFR€¢vFF×F×F–ÖRÖ&6—2p¢¢“° ¢f÷"€¢6öç7B÷F–öà¢öbÖöFÂçVW'•6VÆV7F÷$ÆÂ€¢u¶FF×F×F–ÖRÖ&6—5Òp¢¢’°¢6öç7B7F—fRÐ¢÷F–öâævWDGG&–'WFR€¢vFF×F×F–ÖRÖ&6—2p¢’ÓÓÒæW‡C° ¢÷F–öâæ6Æ74Æ—7BçFövvÆR€¢wF×F–ÖRÖ&6—2Ö7F—fRrÀ¢7F—fP¢“° ¢÷F–öâç6WDGG&–'WFR€¢v&–×&W76VBrÀ¢7F—fP¢òwG'VRp¢¢vfÇ6Rp¢“°¢Ð ¢6öç7BF–ÖT&6—46öçFW‡BÐ¢ÖöFÂçVW'•6VÆV7F÷"€¢rçF×6WGF–æw2×6V7F–öâçF×F–ÖRÖ&6—2Ö6öçFW‡Bp¢“° ¢–b€¢F–ÖT&6—46öçFW‡@¢’°¢6öç7BÆö6ÅF–ÖW¦öæRÐ¢7F—f—G”F6†&ö&EF–ÖW¦öæT6öçFW‡B€¢æWrFFR‚’À¢vÆö6Âp¢“° ¢F–ÖT&6—46öçFW‡BçFW‡D6öçFVçBÐ¢æW‡BÓÓÒwF7Bp¢òuD5BW6W2UD26ÆVæF"ÖF’æB6Æö6²Ö†÷W"&÷VæF&–W2âp¢¢FWf–6RÆö6ÂW6W2G¶Æö6ÅF–ÖW¦öæRæÆ&VÇÒæ°¢Ð¢Ð¢“°¢Ð ¢ÆWBVæF–æt†—7F÷'”W‡÷'BÐ¢çVÆÃ° ¢6öç7B6WGF–æw56V7F–öâÐ¢B‚rçF×6WGF–æw2×6V7F–öâr“° ¢ÆWB&W7F÷&TæÇ—6—4gFW$WFöÖF–57–æ2Ð¢&ööÆVâ€¢WFöÖF–4Æöu7–æ5'Vææ–ærb`¢66†VCòæ66÷VçEö–Bb`¢66†VBæ6÷Vç@¢“° ¢gVæ7F–öâÇ”WFöÖF–4Æöu7–æ4ÖöFÅ7FFR€¢7–æ5'Vææ–ærÒWFöÖF–4Æöu7–æ5'Vææ–æp¢’°¢6WGF–æw56V7F–öãòæ6Æ74Æ—7BçFövvÆR€¢wFÖWFöÖF–2×7–æ2Ö'W7’rÀ¢7–æ5'Vææ–ærÓÓÐ¢G'VP¢“° ¢6WGF–æw56V7F–öãòç6WDGG&–'WFR€¢v&–Ö'W7’rÀ¢7–æ5'Vææ–æp¢òwG'VRp¢¢vfÇ6Rp¢“°¢Ð ¢gVæ7F–öâ&Vg&W6„WFöÖF–4Æöu7–æ57FGW2€¢ÖWF¢’°¢6öç7B7FGW2Ð¢B‚r7FÖWFöÖF–2×7–æ2×7FGW2r“° ¢–b€¢7FGW0¢’°¢7FGW2çFW‡D6öçFVçBÐ¢WFöÖF–4Æöu7–æ57FGW5FW‡B€¢ÖWF¢“°¢Ð¢Ð ¢7–æ2gVæ7F–öâ&Vg&W6…7F÷&VD†—7F÷'•7VÖÖ'’‚’°¢6öç7B&Vg&W6†VD66†VBÐ¢v—BvWDÆ7D66†TÖWF‚“° ¢6öç7B7F÷&VD†—7F÷'•7VÖÖ'’Ð¢B‚r7F×7F÷&VBÖ†—7F÷'’×7VÖÖ'’r“° ¢–b€¢7F÷&VD†—7F÷'•7VÖÖ'’b`¢&Vg&W6†VD66†VCòæ66÷VçEö–Bb`¢&Vg&W6†VD66†VBæ6÷Vç@¢’°¢7F÷&VD†—7F÷'•7VÖÖ'’æ–ææW$…DÔÂÐ¢7F÷&VD†—7F÷'•7VÖÖ'”‡FÖÂ€¢&Vg&W6†VD66†V@¢“°¢Ð ¢&Vg&W6„WFöÖF–4Æöu7–æ57FGW2€¢&Vg&W6†VD66†V@¢“° ¢ÖöFÂæF—7F6„WfVçB€¢æWrWfVçB€¢wFÖ†—7F÷'’×WFFVBp¢¢“° ¢&WGW&â&Vg&W6†VD66†VC°¢Ð ¢6öç7BWFöÖF–4Æöu7–æ57FFTÆ—7FVæW"Ð¢WfVçBÓâ°¢6öç7B7–æ5'Vææ–ærÐ¢WfVçCòæFWF–Ãòç'Vææ–ærÓÓÐ¢G'VS° ¢Ç”WFöÖF–4Æöu7–æ4ÖöFÅ7FFR€¢7–æ5'Vææ–æp¢“° ¢&Vg&W6„WFöÖF–4Æöu7–æ57FGW2€¢66†V@¢“° ¢–b€¢7–æ5'Vææ–æp¢’°¢&WGW&ã°¢Ð ¢fö–B†7–æ2‚’Óâ°¢6öç7B&Vg&W6†VBÐ¢v—B&Vg&W6…7F÷&VD†—7F÷'•7VÖÖ'’‚“° ¢&Vg&W6„WFöÖF–4Æöu7–æ57FGW2€¢&Vg&W6†V@¢“° ¢–b€¢&W7F÷&TæÇ—6—4gFW$WFöÖF–57–æ0¢’°¢&W7F÷&TæÇ—6—4gFW$WFöÖF–57–æ2Ð¢fÇ6S° ¢v—B'Vå7F÷&VDæÇ—6—2€¢fÇ6RÀ¢çVÆÀ¢“°¢Ð¢Ò’‚’æ6F6‚€¢W'&÷"Óâ°¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò6÷VÆBæ÷B&Vg&W6‚F†RÖöFÂgFW"WFöÖF–27–æ6‡&öæ—¦F–öã¢rÀ¢W'&÷ ¢“°¢Ð¢“°¢Ó° ¢Fö7VÖVçBæFDWfVçDÆ—7FVæW"€¢UDôÔD”5ôÄôuõ5”ä5õ5DDUôUdTåBÀ¢WFöÖF–4Æöu7–æ57FFTÆ—7FVæW ¢“° ¢Ç”WFöÖF–4Æöu7–æ4ÖöFÅ7FFR‚“° ¢6öç7B&W7F÷&U7FFRÐ¢÷F–öç3òç&W7F÷&U7FFRÇÀ¢çVÆÃ° ¢Ö&µV”ÖöFÄ÷VæVB€¢&W7F÷&U7FFP¢“° ¢–b€¢67&öÆÄ6öçF–æW ¢’°¢ÆWB67&öÆÅ6fUVæF–ærÒfÇ6S° ¢67&öÆÄ6öçF–æW"æFDWfVçDÆ—7FVæW"€¢w67&öÆÂrÀ¢‚’Óâ°¢–b€¢67&öÆÅ6fUVæF–æp¢’°¢&WGW&ã°¢Ð ¢67&öÆÅ6fUVæF–ærÒG'VS° ¢&WVW7Dæ–ÖF–öäg&ÖR€¢‚’Óâ°¢67&öÆÅ6fUVæF–ærÒfÇ6S°¢w&—FUV•6W76–öå7FFR‡°¢67&öÆÅ÷F÷¢67&öÆÄ6öçF–æW"ç67&öÆÅF÷ ¢Ò“°¢Ð¢“°¢ÒÀ¢²76—fS¢G'VRÐ¢“°¢Ð ¢6öç7BG&6¶W"Ð¢æWr&öw&W75G&6¶W"€¢–æfòÓâ° ¢B‚r7F×7FvRr¢çFW‡D6öçFVçBÐ¢–æfòç7FvS° ¢B‚r7F×W&6VçBr¢çFW‡D6öçFVçBÐ¢G´ÖF‚ç&÷VæB†–æfòçW&6VçB—ÒV° ¢B‚r7FÖf–ÆÂr¢ç7G–ÆRçv–GF‚Ð¢G¶–æfòçW&6VçGÒV° ¢B‚r7FÖFWF–Âr¢çFW‡D6öçFVçBÐ¢–æfòæFWF–ÂÇÀ¢rs° ¢B‚r7FÖÆöw2r¢çFW‡D6öçFVçBÐ¢çVÖ&W"€¢–æfòæÆöw46öÆÆV7FV@¢’çFôÆö6ÆU7G&–ær‚“° ¢B‚r7FÖWFr¢çFW‡D6öçFVçBÐ¢–æfòçW&6VçBãÐ¢ ¢òt6ö×ÆWFRp¢¢–æfòæWF° ¢B‚r7FÖVÆ6VBr¢çFW‡D6öçFVçBÐ¢–æfòæVÆ6VC° ¢B‚r7F×&WVW7G2r¢çFW‡D6öçFVçBÐ¢çVÖ&W"€¢–æfòæ•&WVW7G0¢’çFôÆö6ÆU7G&–ær‚“° ¢B‚r7F×7Æ—G2r¢çFW‡D6öçFVçBÐ¢çVÖ&W"€¢–æfòç7Æ—D6÷Vç@¢’çFôÆö6ÆU7G&–ær‚“°¢Ð¢“° ¢gVæ7F–öâ6WD'W7’€¢'W7¢’° ¢'Vææ–ærÐ¢'W7“° ¢f÷"€¢6öç7B'WGFöà¢öbÖöFÂçVW'•6VÆV7F÷$ÆÂ€¢v'WGFöâp¢¢’° ¢–b€¢'WGFöâæ–BÓÐ¢wFÖ6Æ÷6Rp¢’°¢'WGFöâæF—6&ÆVBÐ¢'W7“°¢Ð¢Ð ¢¶W”–çWBæF—6&ÆVBÐ¢'W7“° ¢6Æ÷6T'WGFöâæF—6&ÆVBÐ¢'W7“°¢Ð ¢7–æ2gVæ7F–öâvWD”¶W’‚’° ¢6öç7BVçFW&VD¶W’Ð¢¶W”–çWBçfÇVP¢çG&–Ò‚“° ¢6öç7B”¶W’Ð¢VçFW&VD¶W’ÇÀ¢v—BÆöE6V7W&T”¶W’‚“° ¢–b€¢”¶W¢’° ¢ÆW'B€¢tVçFW"–÷W"F÷&â’¶W’âp¢“° ¢&WGW&âçVÆÃ°¢Ð ¢–b€¢VçFW&VD¶W¢’°¢v—B6fU6V7W&T”¶W’€¢VçFW&VD¶W¢“°¢Ð ¢¶W”–çWBçfÇVRÐ¢rs° ¢&WGW&â”¶W“°¢Ð ¢7–æ2gVæ7F–öâvWD÷F–öæÄ”¶W’‚’°¢6öç7BVçFW&VD¶W’Ð¢¶W”–çWBçfÇVP¢çG&–Ò‚“° ¢–b€¢VçFW&VD¶W¢’°¢v—B6fU6V7W&T”¶W’€¢VçFW&VD¶W¢“° ¢¶W”–çWBçfÇVRÐ¢rs° ¢&WGW&âVçFW&VD¶W“°¢Ð ¢&WGW&âv—BÆöE6V7W&T”¶W’‚“°¢Ð ¢6öç7B'V–ÆD'WGFöâÐ¢B‚r7FÖ'V–ÆBr“° ¢–b€¢'V–ÆD'WGFöà¢’° ¢'V–ÆD'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ° ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’° ¢6öç7B66÷VçBÐ¢v—BFWFV7D66÷VçB€¢”¶W’À¢G&6¶W ¢“° ¢6öç7BW†—7F–æu7FFRÐ¢v—BvWD'V–ÆE7FFR€¢66÷VçBæ–@¢“° ¢–b€¢W†—7F–æu7FFP¢òæ–å÷&öw&W70¢’° ¢6öç7B&W7VÖRÐ¢6öæf—&Ò€¢âVæf–æ—6†VB†—7F÷'’'V–ÆBv2f÷VæBåÆåÆæ°¢6ö×ÆWFVBF‡&÷Vvƒ¢G¶W†—7F–æu7FFRæ6ö×ÆWFVE÷F‡&÷Vv‚óòwVæ¶æ÷vâwÕÆåÆæ°¢&W7VÖRv†W&R—BÆVgBöfcö ¢“° ¢–b€¢&W7VÖP¢’° ¢6öç7B&W7F'BÐ¢6öæf—&Ò€¢u7F'B÷fW"g&öÒ66÷VçB7&VF–öâ–ç7FVCòp¢“° ¢–b€¢&W7F'@¢’°¢&WGW&ã°¢Ð ¢v—B'V–ÆD†—7F÷'’€¢”¶W’À¢G&6¶W"À¢G'VP¢“° ¢ÒVÇ6R° ¢v—B'V–ÆD†—7F÷'’€¢”¶W’À¢G&6¶W"À¢fÇ6P¢“°¢Ð ¢ÒVÇ6R° ¢v—B'V–ÆD†—7F÷'’€¢”¶W’À¢G&6¶W"À¢fÇ6P¢“°¢Ð ¢ÆW'B€¢t†—7F÷'’'V–ÆB6ö×ÆWFRåÆåÆâr°¢u–÷W"Æöw2&Ræ÷r6fVBÆö6ÆÇ’æB6â&R&WW6VB'’gWGW&R6ö×F–&ÆR67&—BWFFW2âp¢“° ¢Ò6F6‚€¢W'&÷ ¢’° ¢6öç6öÆRæW'&÷"€¢W'&÷ ¢“° ¢G&6¶W"ç6WE7FvR€¢t'V–ÆB–çFW''WFVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢†—7F÷'’'V–ÆB7F÷VC¥ÆåÆâG¶W'&÷"æÖW76vWÕÆåÆæ°¢6ö×ÆWFVB6VvÖVçG2vW&RÇ&VG’6fVBâ–÷R6â&W7VÖRÆFW"æ ¢“° ¢Òf–æÆÇ’° ¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢6öç7BæÇ—¦T'WGFöâÐ¢B‚r7FÖæÇ—¦Rr“° ¢7–æ2gVæ7F–öâ'Vå7F÷&VDæÇ—6—2€¢6†÷t6ö×ÆWF–öäÆW'BÒG'VRÀ¢&W7F÷&U67&öÆÅF÷ÒçVÆÀ¢’°¢6WD'W7’€¢G'VP¢“° ¢G'’°¢6öç7B÷F–öæÄ”¶W’Ð¢v—BvWD÷F–öæÄ”¶W’‚“° ¢v—BæÇ—¦U7F÷&VDÆöw2€¢G&6¶W"À¢÷F–öæÄ”¶W¢“° ¢v—B&Vg&W6…7F÷&VD†—7F÷'•7VÖÖ'’‚“° ¢w&—FUV•6W76–öå7FFR‡°¢æÇ—6—5÷f—6–&ÆS¢G'VRÀ¢÷&–VçFF–öå÷&Vg&W6…÷VæF–æs¢fÇ6P¢Ò“° ¢–b€¢67&öÆÄ6öçF–æW"b`¢&W7F÷&U67&öÆÅF÷ÓÒçVÆÀ¢’°¢&WVW7Dæ–ÖF–öäg&ÖR€¢‚’Óâ°¢67&öÆÄ6öçF–æW"ç67&öÆÅF÷Ð¢ÖF‚æÖ‚€¢À¢çVÖ&W"‡&W7F÷&U67&öÆÅF÷’ÇÀ¢ ¢“°¢Ð¢“°¢Ð ¢–b€¢6†÷t6ö×ÆWF–öäÆW'@¢’°¢ÆW'B€¢G¶ÆFW7DÆöw2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—Ò7F÷&VBÆöw2æÇ—¦VBåÆåÆäæògVÆÂW‡÷'Bv2æVVFVBæ ¢“°¢Ð ¢&WGW&âG'VS° ¢Ò6F6‚€¢W'&÷ ¢’°¢w&—FUV•6W76–öå7FFR‡°¢æÇ—6—5÷f—6–&ÆS ¢6†÷t6ö×ÆWF–öäÆW'@¢òfÇ6P¢¢G'VP¢Ò“° ¢G&6¶W"ç6WE7FvR€¢tæÇ—6—2f–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢–b€¢6†÷t6ö×ÆWF–öäÆW'@¢’°¢ÆW'B€¢W'&÷"æÖW76vP¢“°¢ÒVÇ6R°¢6öç6öÆRæW'&÷"€¢W'&÷ ¢“°¢Ð ¢&WGW&âfÇ6S° ¢Òf–æÆÇ’°¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ð ¢–b€¢æÇ—¦T'WGFöà¢’°¢æÇ—¦T'WGFöâæöæ6Æ–6²Ð¢‚’Óà¢'Vå7F÷&VDæÇ—6—2€¢G'VRÀ¢çVÆÀ¢“°¢Ð ¢6öç7BWFFT'WGFöâÐ¢B‚r7F×WFFRr“° ¢–b€¢WFFT'WGFöà¢’° ¢WFFT'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ° ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’° ¢6öç7B&W7VÇBÐ¢v—BWFFTÆöw2€¢”¶W’À¢G&6¶W ¢“° ¢v—B&Vg&W6…7F÷&VD†—7F÷'•7VÖÖ'’‚“° ¢6öç7BæÇ—6—5&Vg&W6†VBÐ¢v—B'Vå7F÷&VDæÇ—6—2€¢fÇ6RÀ¢çVÆÀ¢“° ¢ÆW'B€¢WFFR6ö×ÆWFRåÆåÆæ°¢G·&W7VÇBæFFVBçFôÆö6ÆU7G&–ær‚—ÒæWrÆöw2FFVBåÆæ°¢G·&W7VÇBæÆöw2æÆVæwF‚çFôÆö6ÆU7G&–ær‚—Ò7F÷&VBF÷FÂåÆæ°¢€¢æÇ—6—5&Vg&W6†V@¢òtF6†&ö&B&Vg&W6†VBWFöÖF–6ÆÇ’âp¢¢tÆöw2vW&R6fVBÂ'WBF†RF6†&ö&B&Vg&W6‚f–ÆVBâp¢¢“° ¢Ò6F6‚€¢W'&÷ ¢’° ¢G&6¶W"ç6WE7FvR€¢uWFFRf–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢W'&÷"æÖW76vP¢“° ¢Òf–æÆÇ’° ¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢6öç7BW‡÷'D'WGFöâÐ¢B‚r7FÖW‡÷'BÖ†—7F÷'’r“° ¢6öç7B6fTW‡÷'D'WGFöâÐ¢B‚r7F×6fRÖW‡÷'Br“° ¢–b€¢W‡÷'D'WGFöà¢’°¢W‡÷'D'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ°¢6öç7B6öæf—&ÖVBÐ¢6öæf—&Ò€¢tW‡÷'B†—7F÷'’¥4ôâ7&VFW2&VF&ÆRFV7'—FVB6÷’öb–÷W"F÷&â7F—f—G’†—7F÷'’åÆåÆâr°¢t¶VWF†—2f–ÆR&—fFRâ—Bv–ÆÂæ÷B–æ6ÇVFR–÷W"F÷&â’¶W’÷"F÷&âæÇ—F–72Væ7'—F–öâ÷&V6÷fW'’¶W—2åÆåÆâr°¢uF†RW‡÷'Bv–ÆÂg&W6†Ç’WF†VçF–6FR–÷W"F÷&â66÷VçBæB&–æBF†Rf–ÆVæÖRæBÖæ–fW7BFòF†BfW&–f–VBF÷&â”BåÆåÆâr°¢t6öçF–çVSòp¢“° ¢–b€¢6öæf—&ÖV@¢’°¢&WGW&ã°¢Ð ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢VæF–æt†—7F÷'”W‡÷'BÐ¢çVÆÃ° ¢–b€¢6fTW‡÷'D'WGFöà¢’°¢6fTW‡÷'D'WGFöâç7G–ÆRæF—7Æ’Ð¢væöæRs°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’°¢G&6¶W"ç6WE7FvR€¢u&W&–ærW‡÷'N(
brÀ¢tg&W6†Ç’WF†VçF–6F–ær–÷W"F÷&â66÷VçBæBfW&–g––ær&÷FV7FVBÆö6Â†—7F÷'’âââp¢“° ¢6öç7B&W7VÇBÐ¢v—B'V–ÆDWF†VçF–6FVE&VF&ÆT†—7F÷'”W‡÷'B€¢”¶W’À¢G&6¶W ¢“° ¢VæF–æt†—7F÷'”W‡÷'BÐ¢&W7VÇC° ¢–b€¢6fTW‡÷'D'WGFöà¢’°¢6fTW‡÷'D'WGFöâç7G–ÆRæF—7Æ’Ð¢rs°¢Ð ¢G&6¶W"ç6WE7FvR€¢tW‡÷'B&W&VBrÀ¢G·&W7VÇBç&V6÷&Eö6÷VçBçFôÆö6ÆU7G&–ær‚—ÒÆöw2+rF÷&â”BG·&W7VÇBæ66÷VçBæ–GÒ+rF6fRW‡÷'Bf–ÆV ¢“° ¢ÆW'B€¢†—7F÷'’¥4ôâ&W&VB6V7W&VÇ’åÆåÆæ°¢F÷&â”C¢G·&W7VÇBæ66÷VçBæ–GÕÆæ°¢&V6÷&G3¢G·&W7VÇBç&V6÷&Eö6÷VçBçFôÆö6ÆU7G&–ær‚—ÕÆæ°¢f–ÆVæÖS¢G·&W7VÇBæf–ÆVæÖWÕÆåÆæ°¢F6fRW‡÷'Bf–ÆRæW‡Bâ”õ26†÷VÆB÷Vâ—G26†&R6†VWC²6†ö÷6R6fRFòf–ÆW2åÆåÆæ°¢F†R&VF&ÆR¥4ôâ&VÖ–ç2–âÖVÖ÷'’öæÇ’VçF–ÂF†B6fR7FWæ ¢“°¢Ò6F6‚€¢W'&÷ ¢’°¢VæF–æt†—7F÷'”W‡÷'BÐ¢çVÆÃ° ¢G&6¶W"ç6WE7FvR€¢tW‡÷'Bf–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢W'&÷"æÖW76vP¢“°¢Òf–æÆÇ’°¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢–b€¢6fTW‡÷'D'WGFöà¢’°¢6fTW‡÷'D'WGFöâæöæ6Æ–6²Ð¢‚’Óâ°¢6öç7B&W&VBÐ¢VæF–æt†—7F÷'”W‡÷'C° ¢–b€¢&W&V@¢’°¢ÆW'B€¢u&W&RF†R†—7F÷'’W‡÷'Bf—'7Bâp¢“°¢&WGW&ã°¢Ð ¢ÆWB6†&U&öÖ—6S° ¢G'’°¢òòF†—26ÆÂ×W7B&VÖ–âF—&V7FÇ’–ç6–FRF†R6Æ–6²†æFÆW"v—F‚æð¢òòv—B&Vf÷&R—BâvV$¶—B&WV—&W2G&ç6–VçBW6W"7F—fF–öâf÷ ¢òòæf–vF÷"ç6†&R‚’à¢6†&U&öÖ—6RÐ¢6†&U&W&VD†—7F÷'”W‡÷'B€¢&W&V@¢“°¢Ò6F6‚€¢W'&÷ ¢’°¢VæF–æt†—7F÷'”W‡÷'BÐ¢çVÆÃ°¢6fTW‡÷'D'WGFöâç7G–ÆRæF—7Æ’Ð¢væöæRs° ¢G&6¶W"ç6WE7FvR€¢u6fRf–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢W'&÷"æÖW76vP¢“°¢&WGW&ã°¢Ð ¢VæF–æt†—7F÷'”W‡÷'BÐ¢çVÆÃ°¢6fTW‡÷'D'WGFöâç7G–ÆRæF—7Æ’Ð¢væöæRs° ¢G&6¶W"ç6WE7FvR€¢v”õ26†&R6†VWB÷VæVBrÀ¢t6†ö÷6R6fRFòf–ÆW2Fò¶VWF†R66÷VçBÖ&÷VæB¥4ôâW‡÷'Bâp¢“° ¢&öÖ—6Rç&W6öÇfR€¢6†&U&öÖ—6P¢’çF†Vâ€¢&V6V—BÓâ°¢G&6¶W"ç6WE7FvR€¢tW‡÷'B6fVB÷6†&VBrÀ¢G·&V6V—Bç&V6÷&Eö6÷VçBçFôÆö6ÆU7G&–ær‚—ÒÆöw2+rF÷&â”BG·&V6V—Bæ66÷VçBæ–GÖ ¢“° ¢ÆW'B€¢†—7F÷'’¥4ôâ†æFVBFò”õ2åÆåÆæ°¢F÷&â”C¢G·&V6V—Bæ66÷VçBæ–GÕÆæ°¢&V6÷&G3¢G·&V6V—Bç&V6÷&Eö6÷VçBçFôÆö6ÆU7G&–ær‚—ÕÆæ°¢f–ÆVæÖS¢G·&V6V—Bæf–ÆVæÖWÕÆåÆæ°¢–b–÷R6†÷6R6fRFòf–ÆW2ÂWÆöBF†BVæ6†ævVB¥4ôâf÷"fW&–f–6F–öâæ ¢“°¢Ð¢’æ6F6‚€¢W'&÷"Óâ°¢G&6¶W"ç6WE7FvR€¢u6fR6æ6VÆÆVB÷"f–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢F†R&W&VBW‡÷'Bv2æ÷B6fVBåÆåÆâG¶W'&÷"æÖW76vWÖ ¢“°¢Ð¢“°¢Ó°¢Ð ¢6öç7Bf÷&Vç6–4'WGFöâÐ¢B‚r7FÖf÷&Vç6–2Ö†—7F÷'’r“° ¢–b€¢f÷&Vç6–4'WGFöà¢’°¢f÷&Vç6–4'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ°¢6öç7B&WVW7FVEF&vWD–BÐ¢&ö×B€¢tVçFW"F†RW†7BF÷&âÆör”BFò6†V6²F—&V7FÇ’v–ç7BF÷&âc"åÆåÆâr°¢uF†—2F–væ÷7F–2—2&VBÖöæÇ’æBv–ÆÂæ÷BÖöF–g’7F÷&VB†—7F÷'’ârÀ¢rp¢“° ¢–b€¢&WVW7FVEF&vWD–BÓÓÐ¢çVÆÀ¢’°¢&WGW&ã°¢Ð ¢6öç7Bæ÷&ÖÆ—¦VEF&vWD–BÐ¢7G&–ær€¢&WVW7FVEF&vWD–@¢’çG&–Ò‚“° ¢–b€¢æ÷&ÖÆ—¦VEF&vWD–@¢’°¢ÆW'B€¢tVçFW"F†RW†7BF÷&âÆör”Bâp¢“°¢&WGW&ã°¢Ð ¢6öç7B6öæf—&ÖVBÐ¢6öæf—&Ò€¢F—&V7FÇ’6†V6²F÷&âc"f÷"ÆörG¶æ÷&ÖÆ—¦VEF&vWD–GÓõÆåÆæ°¢uF†—2Ö¶W2öæR&VBÖöæÇ’&WVW7Bf÷"F†RGvòÖÖ–çWFRv–æF÷r&÷VæB—G27F÷&VBF–ÖW7F×â—Bv–ÆÂæ÷B&V'V–ÆBÂ&WÆ6RÂÖW&vRÂFVÆWFRÂ÷"ÖöF–g’7F÷&VB†—7F÷'’åÆåÆâr°¢t6öçF–çVSòp¢“° ¢–b€¢6öæf—&ÖV@¢’°¢&WGW&ã°¢Ð ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’°¢6öç7B&W7VÇBÐ¢v—B'Vä†—7F÷'”f÷&Vç6–5v–æF÷t6†V6²€¢”¶W’À¢G&6¶W"À¢æ÷&ÖÆ—¦VEF&vWD–@¢“° ¢ÆW'B€¢f÷&ÖD†—7F÷'”f÷&Vç6–5&W7VÇB€¢&W7VÇ@¢¢“°¢Ò6F6‚€¢W'&÷ ¢’°¢G&6¶W"ç6WE7FvR€¢tf÷&Vç6–26†V6²f–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢f÷&Vç6–2†—7F÷'’6†V6²f–ÆVC¥ÆåÆâG¶W'&÷"æÖW76vWÕÆåÆäæò7F÷&VB†—7F÷'’v2ÖöF–f–VBæ ¢“°¢Òf–æÆÇ’°¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢6öç7BG&6T'WGFöâÐ¢B‚r7F×G&6RÖ†—7F÷'’r“° ¢–b€¢G&6T'WGFöà¢’°¢G&6T'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ°¢6öç7B&WVW7FVEF&vWD–BÐ¢&ö×B€¢tVçFW"F†RW†7BF÷&âÆör”B&W÷'FVB2Ö—76–ær'’gVÆÂ&V'V–ÆBåÆåÆâr°¢uF†—2G&6R—2&VBÖöæÇ’æBv–ÆÂæ÷BÖöF–g’7F÷&VB†—7F÷'’ârÀ¢rp¢“° ¢–b€¢&WVW7FVEF&vWD–BÓÓÐ¢çVÆÀ¢’°¢&WGW&ã°¢Ð ¢6öç7Bæ÷&ÖÆ—¦VEF&vWD–BÐ¢7G&–ær€¢&WVW7FVEF&vWD–@¢’çG&–Ò‚“° ¢–b€¢æ÷&ÖÆ—¦VEF&vWD–@¢’°¢ÆW'B€¢tVçFW"F†RW†7BÖ—76–ærF÷&âÆör”Bâp¢“°¢&WGW&ã°¢Ð ¢6öç7B6öæf—&ÖVBÐ¢6öæf—&Ò€¢G&6RgVÆÂ&V'V–ÆBf÷"Ö—76–ærÆörG¶æ÷&ÖÆ—¦VEF&vWD–GÓõÆåÆæ°¢uF†—2—2&VBÖöæÇ’â—BÖ’Ö¶RÖç’F÷&â’&WVW7G2&V6W6R—BW6W2F†R6ÖRv–æF–öâæBFVfVç6—fR7Æ—GF–ærF‚2gVÆÂ&V'V–ÆBÂ'WB—Bv–ÆÂæ÷B&WÆ6RÂÖW&vRÂFVÆWFRÂ÷"ÖöF–g’7F÷&VB†—7F÷'’åÆåÆâr°¢t6öçF–çVSòp¢“° ¢–b€¢6öæf—&ÖV@¢’°¢&WGW&ã°¢Ð ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’°¢6öç7B&W7VÇBÐ¢v—B'Vä†—7F÷'•F&vWD6öÆÆV7F÷%G&6R€¢”¶W’À¢G&6¶W"À¢æ÷&ÖÆ—¦VEF&vWD–@¢“° ¢ÆW'B€¢f÷&ÖD†—7F÷'•F&vWD6öÆÆV7F÷%G&6R€¢&W7VÇ@¢¢“°¢Ò6F6‚€¢W'&÷ ¢’°¢G&6¶W"ç6WE7FvR€¢t6öÆÆV7F÷"G&6Rf–ÆVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢&V'V–ÆB6öÆÆV7F÷"G&6Rf–ÆVC¥ÆåÆâG¶W'&÷"æÖW76vWÕÆåÆäæò7F÷&VB†—7F÷'’v2ÖöF–f–VBæ ¢“°¢Òf–æÆÇ’°¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢6öç7B&V'V–ÆD'WGFöâÐ¢B‚r7F×&V'V–ÆBr“° ¢–b€¢&V'V–ÆD'WGFöà¢’° ¢&V'V–ÆD'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ° ¢6öç7B”¶W’Ð¢v—BvWD”¶W’‚“° ¢–b€¢”¶W¢’°¢&WGW&ã°¢Ð ¢6öç7B6öæf—&ÖVBÐ¢6öæf—&Ò€¢tgVÆÂ&V'V–ÆBv–ÆÂ6öÆÆV7B6ö×ÆWFR&WÆ6VÖVçBg&öÒ66÷VçB7&VF–öâv†–ÆR¶VW–ær–÷W"7W'&VçB7F÷&VB†—7F÷'’–çF7BåÆåÆâr°¢uF÷&âæÇ—F–72v–ÆÂ&WÆ6RF†R7F÷&VB†—7F÷'’öæÇ’gFW"F†R&WÆ6VÖVçB—26ö×ÆWFRæBfW&–f–VBâ–b6öÆÆV7F–öâ÷"fW&–f–6F–öâf–Ç2ÂF†R7W'&VçB7F÷&VB†—7F÷'’7F—2Væ6†ævVBåÆåÆâr°¢uW6RF†—2Ö–æÇ’v†VâF†R6öÆÆV7F÷"6†ævW2÷"–÷R–çFVçF–öæÆÇ’vçB6ö×ÆWFRfÆ–FF–öâ'VâåÆåÆâr°¢t6öçF–çVSòp¢“° ¢–b€¢6öæf—&ÖV@¢’°¢&WGW&ã°¢Ð ¢6WD'W7’€¢G'VP¢“° ¢G'’° ¢v—B'V–ÆD†—7F÷'’€¢”¶W’À¢G&6¶W"À¢G'VP¢“° ¢v—B&Vg&W6…7F÷&VD†—7F÷'•7VÖÖ'’‚“° ¢ÆW'B€¢tgVÆÂ†—7F÷'’&V'V–ÆB6ö×ÆWFRâp¢“° ¢Ò6F6‚€¢W'&÷ ¢’° ¢G&6¶W"ç6WE7FvR€¢t'V–ÆB–çFW''WFVBrÀ¢W'&÷"æÖW76vP¢“° ¢ÆW'B€¢'V–ÆB–çFW''WFVC¥ÆåÆâG¶W'&÷"æÖW76vWÕÆåÆæ°¢–÷W"W†—7F–ær7F÷&VB†—7F÷'’&VÖ–ç2–çF7Bâæò'F–Â&V'V–ÆBv2&öÖ÷FVBæ ¢“° ¢Òf–æÆÇ’° ¢6WD'W7’€¢fÇ6P¢“°¢Ð¢Ó°¢Ð ¢–b€¢6†÷VÆE&W7F÷&U7F÷&VDæÇ—6—2€¢&W7F÷&U7FFRÀ¢66†VBÀ¢æÇ—¦T'WGFöà¢¢’°¢G&6¶W"ç6WE7FvR€¢u&W7F÷&–ærF6†&ö&BrÀ¢tÆöF–ær7F÷&VB†—7F÷'’æB&Vg&W6†–ærÆ—fR&W6÷W&6W2âââp¢“° ¢v—B'Vå7F÷&VDæÇ—6—2€¢fÇ6RÀ¢&W7F÷&U7FFSòç67&öÆÅ÷F÷óòçVÆÀ¢“°¢ÒVÇ6R–b€¢67&öÆÄ6öçF–æW"b`¢&W7F÷&U7FFSòç67&öÆÅ÷F÷ ¢’°¢&WVW7Dæ–ÖF–öäg&ÖR€¢‚’Óâ°¢67&öÆÄ6öçF–æW"ç67&öÆÅF÷Ð¢ÖF‚æÖ‚€¢À¢çVÖ&W"€¢&W7F÷&U7FFRç67&öÆÅ÷F÷ ¢’ÇÀ¢ ¢“°¢Ð¢“°¢Ð ¢6Æ÷6T'WGFöâæöæ6Æ–6²Ð¢‚’Óâ° ¢–b€¢'Vææ–æp¢’°¢&WGW&ã°¢Ð ¢òò6fRF†R7GVÂ&VæFW&VBG&vW"7FFW2–ÖÖVF–FVÇ’&Vf÷&RF÷&åD¢òò&VÖ÷fW2F†—2ÖöFÃ²F†—2—2F†R&VÆ–&ÆRfÆÆ&6²f÷"F÷V6‚vV$¶—Bà¢W'6—7E&W6÷W&6TF6†&ö&E7FFR€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢wF×7FGW2p¢¢“° ¢w&—FUV•6W76–öå7FFR‡°¢ÖöFÅö÷Vã¢fÇ6RÀ¢æÇ—6—5÷f—6–&ÆS¢fÇ6RÀ¢67&öÆÅ÷F÷¢ÖF‚æÖ‚€¢À¢çVÖ&W"€¢67&öÆÄ6öçF–æW#òç67&öÆÅF÷ ¢’ÇÀ¢ ¢’À¢÷&–VçFF–öå÷&Vg&W6…÷VæF–æs¢fÇ6P¢Ò“° ¢Fö7VÖVçBç&VÖ÷fTWfVçDÆ—7FVæW"€¢UDôÔD”5ôÄôuõ5”ä5õ5DDUôUdTåBÀ¢WFöÖF–4Æöu7–æ57FFTÆ—7FVæW ¢“° ¢ÖöFÂç&VÖ÷fR‚“° ¢66†VGVÆTWFöÖF–4Æöu7–æ2€¢UDõõ5”ä5ô”ä•D”ÅôDTÄ•ôÕ0¢“°¢Ó°¢Ð¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òò„•5Dõ%’$õDT5D”ôâT¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢6öç7B÷VäÖöFÅv—F†÷WD†—7F÷'•&÷FV7F–öâÐ¢÷VäÖöFÃ° ¢÷VäÖöFÂÐ¢7–æ2gVæ7F–öâ†÷F–öç2Ò·Ò’°¢v—B÷VäÖöFÅv—F†÷WD†—7F÷'•&÷FV7F–öâ†÷F–öç2“° ¢6öç7BÖöFÂÐ¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢ÔôDÅô”@¢“° ¢–b€¢ÖöFÂÇÀ¢ÖöFÂçVW'•6VÆV7F÷"€¢r7FÖ†—7F÷'’×&÷FV7F–öâ×æVÂp¢¢’°¢&WGW&ã°¢Ð ¢6öç7B66†VBÐ¢v—BvWDÆ7D66†TÖWF‚“° ¢–b€¢66†VCòæ66÷VçEö–BÇÀ¢66†VCòæ6÷Vç@¢’°¢&WGW&ã°¢Ð ¢6öç7B6WGF–æw4&öG’Ð¢ÖöFÂçVW'•6VÆV7F÷"€¢r7FÖF–væ÷7F–72×&V6÷fW'’çFÖ†—7F÷'’×FööÇ2p¢“° ¢–b€¢6WGF–æw4&öG¢’°¢&WGW&ã°¢Ð ¢6öç7BæVÂÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢vF—bp¢“° ¢æVÂæ–BÐ¢wFÖ†—7F÷'’×&÷FV7F–öâ×æVÂs° ¢æVÂæ6Æ74æÖRÐ¢wF×6WGF–æw2Öw&÷Ws° ¢6öç7B†VF–ærÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢v"p¢“° ¢†VF–ærçFW‡D6öçFVçBÐ¢tÆö6Â†—7F÷'’&÷FV7F–öâs° ¢6öç7BFWF–ÂÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢vF—bp¢“° ¢FWF–Âæ6Æ74æÖRÐ¢w6ÖÆÂs° ¢FWF–Âç7G–ÆRæÖ&v–åF÷Ð¢s‡‚s° ¢6öç7B'WGFöâÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢v'WGFöâp¢“° ¢'WGFöâæ–BÐ¢wF×&÷FV7BÖ†—7F÷'’s° ¢'WGFöâçFW‡D6öçFVçBÐ¢u&÷FV7B7F÷&VB†—7F÷'’s° ¢'WGFöâç7G–ÆRæÖ&v–åF÷Ð¢s‚s° ¢6öç7BfW&–g”'WGFöâÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢v'WGFöâp¢“° ¢fW&–g”'WGFöâæ–BÐ¢wF×fW&–g’Ö†—7F÷'’×&V6÷fW'’s° ¢fW&–g”'WGFöâçFW‡D6öçFVçBÐ¢ufW&–g’&V6÷fW'’s° ¢fW&–g”'WGFöâç7G–ÆRæÖ&v–åF÷Ð¢s‚s° ¢æVÂæVæD6†–ÆB€¢†VF–æp¢“° ¢æVÂæVæD6†–ÆB€¢FWF–À¢“° ¢æVÂæVæD6†–ÆB€¢'WGFöà¢“° ¢æVÂæVæD6†–ÆB€¢fW&–g”'WGFöà¢“° ¢6WGF–æw4&öG’æVæD6†–ÆB€¢æVÀ¢“° ¢7–æ2gVæ7F–öâ&Vg&W6…&÷FV7F–öåæVÂ‚’°¢G'’°¢6öç7BfW&–f–6F–öâÐ¢v—BfW&–g”†—7F÷'•&÷FV7F–öåW'6—7FVæ6R‚“° ¢–b€¢fW&–f–6F–öâç7FGW2ÓÓÐ¢vf–ÆVBp¢’°¢FWF–ÂçFW‡D6öçFVçBÐ¢&÷FV7F–öâVæf–Æ&ÆS¢G·fW&–f–6F–öâç&V6öâÇÂwfW&–f–6F–öâf–ÆVBâwÖ° ¢'WGFöâæF—6&ÆVBÐ¢G'VS° ¢fW&–g”'WGFöâæF—6&ÆVBÐ¢G'VS° ¢&WGW&ã°¢Ð ¢6öç7B7FGW2Ð¢v—BvWD66÷VçD†—7F÷'•&÷FV7F–öå7FGW2€¢66†VBæ66÷VçEö–@¢“° ¢–b€¢7FGW2æ6ö×ÆWFP¢’°¢FWF–ÂçFW‡D6öçFVçBÐ¢G·7FGW2ç&÷FV7FVBçFôÆö6ÆU7G&–ær‚—Ò7F÷&VBF÷&âÆöw2&RVæ7'—FVBB&W7Bâ°¢töæÇ’66÷VçBÂ&V6÷&B–FVçF—G’ÂæBF–ÖW7F×–æFW†W2&VÖ–â÷WG6–FRF†RVæ7'—FVB–ÆöBâr°¢u&V6÷fW'’fW&–f–6F–öâ—2æöâÖFW7G'V7F—fRâs° ¢'WGFöâçFW‡D6öçFVçBÐ¢u7F÷&VB†—7F÷'’&÷FV7FVBs° ¢'WGFöâæF—6&ÆVBÐ¢G'VS° ¢fW&–g”'WGFöâæF—6&ÆVBÐ¢fÇ6S° ¢&WGW&ã°¢Ð ¢–b€¢fW&–f–6F–öâç7FGW2ÓÓÐ¢v–æ—F–Æ—¦VBp¢’°¢FWF–ÂçFW‡D6öçFVçBÐ¢uF†RÆö6ÂVæ7'—F–öâ¶W’†2&VVâ–æ—F–Æ—¦VBâ&V÷VâF÷&â&Vf÷&RÖ–w&F–ærW†—7F–ær†—7F÷'’6òF†R¶W’6â&RfW&–f–VB7&÷72g&W6‚W6W'67&—B'Vââs° ¢'WGFöâæF—6&ÆVBÐ¢G'VS° ¢fW&–g”'WGFöâæF—6&ÆVBÐ¢G'VS° ¢&WGW&ã°¢Ð ¢FWF–ÂçFW‡D6öçFVçBÐ¢G·7FGW2çÆ–çFW‡BçFôÆö6ÆU7G&–ær‚—ÒöbG·7FGW2çF÷FÂçFôÆö6ÆU7G&–ær‚—Ò7F÷&VBÆöw2&R7F–ÆÂÆ–çFW‡Bâ°¢u&÷FV7F–öâ—2&W7VÖ&ÆS²6Æ÷6–ærF†RÖ–BÖÖ–w&F–öâv–ÆÂæ÷B–çfÆ–FFR&V6÷&G2Ç&VG’6ö×ÆWFVBâs° ¢'WGFöâçFW‡D6öçFVçBÐ¢7FGW2ç&÷FV7FVBâ ¢òu&W7VÖR†—7F÷'’&÷FV7F–öâp¢¢u&÷FV7B7F÷&VB†—7F÷'’s° ¢'WGFöâæF—6&ÆVBÐ¢fÇ6S° ¢fW&–g”'WGFöâæF—6&ÆVBÐ¢G'VS° ¢Ò6F6‚†W'&÷"’°¢FWF–ÂçFW‡D6öçFVçBÐ¢&÷FV7F–öâ7FGW26†V6²f–ÆVC¢G¶W'&÷"æÖW76vWÖ° ¢'WGFöâæF—6&ÆVBÐ¢G'VS° ¢fW&–g”'WGFöâæF—6&ÆVBÐ¢G'VS°¢Ð¢Ð ¢'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ°¢6öç7B6öæf—&ÖVBÐ¢6öæf—&Ò€¢u&÷FV7BF†RÆö6ÆÇ’7F÷&VBF÷&âÆör–ÆöG2æ÷sõÆåÆâr°¢uF†—2FöW2æ÷B&V'V–ÆB÷"FVÆWFR–÷W"†—7F÷'’âV6‚Æ–çFW‡B&V6÷&B—2Væ7'—FVBæBfW&–f–VB&Vf÷&R—B&WÆ6W2F†B6ÖR–æFW†VDD"&V6÷&Bâ–bF÷&åD6Æ÷6W2Ö–Gv’ÂF†RÖ–w&F–öâ6â6fVÇ’&W7VÖRÆFW"âp¢“° ¢–b€¢6öæf—&ÖV@¢’°¢&WGW&ã°¢Ð ¢6öç7BÆÄ'WGFöç2Ð¢'&’æg&öÒ€¢ÖöFÂçVW'•6VÆV7F÷$ÆÂ€¢v'WGFöâp¢¢“° ¢f÷"€¢6öç7B6öçG&öÀ¢öbÆÄ'WGFöç0¢’°¢6öçG&öÂæF—6&ÆVBÐ¢G'VS°¢Ð ¢FWF–ÂçFW‡D6öçFVçBÐ¢u&W&–ær&÷FV7FVBÖ†—7F÷'’Ö–w&F–öî(
bs° ¢G'’°¢6öç7B&W7VÇBÐ¢v—BÖ–w&FT66÷VçD†—7F÷'•&÷FV7F–öâ€¢66†VBæ66÷VçEö–BÀ¢&öw&W72Óâ°¢FWF–ÂçFW‡D6öçFVçBÐ¢&÷FV7F–ær7F÷&VB†—7F÷'“¢G·&öw&W72ç&÷FV7FVBçFôÆö6ÆU7G&–ær‚—ÒòG·&öw&W72çF÷FÂçFôÆö6ÆU7G&–ær‚—ÒÆöw2‚G´ÖF‚ç&÷VæB‡&öw&W72çW&6VçB—ÒR’â°¢G·&öw&W72çÆ–çFW‡BçFôÆö6ÆU7G&–ær‚—ÒÆ–çFW‡B&V6÷&G2&VÖ–âæ°¢Ð¢“° ¢FWF–ÂçFW‡D6öçFVçBÐ¢G·&W7VÇBçF÷FÂçFôÆö6ÆU7G&–ær‚—Ò7F÷&VBF÷&âÆöw2&R&÷FV7FVBâ°¢G·&W7VÇBæÖ–w&FVBçFôÆö6ÆU7G&–ær‚—Ò&V6÷&G2vW&RVæ7'—FVBGW&–ærF†—2'Vâæ° ¢'WGFöâçFW‡D6öçFVçBÐ¢u7F÷&VB†—7F÷'’&÷FV7FVBs° ¢ÆW'B€¢u7F÷&VB†—7F÷'’&÷FV7F–öâ6ö×ÆWFRåÆåÆâr°¢G·&W7VÇBçF÷FÂçFôÆö6ÆU7G&–ær‚—ÒF÷&âÆöw2&Ræ÷rVæ7'—FVBB&W7BåÆæ°¢tæò†—7F÷'’&V'V–ÆBv2&WV—&VBâp¢“° ¢Ò6F6‚†W'&÷"’°¢6öç6öÆRæW'&÷"€¢uµF÷&âæÇ—F–75Ò†—7F÷'’&÷FV7F–öâÖ–w&F–öâf–ÆVC¢rÀ¢W'&÷ ¢“° ¢FWF–ÂçFW‡D6öçFVçBÐ¢†—7F÷'’&÷FV7F–öâ7F÷VB6fVÇ“¢G¶W'&÷"æÖW76vWÖ° ¢ÆW'B€¢t†—7F÷'’&÷FV7F–öâ7F÷VB6fVÇ’åÆåÆâr°¢G¶W'&÷"æÖW76vWÕÆåÆæ°¢u&V6÷&G26ö×ÆWFVB&Vf÷&RF†R–çFW''WF–öâ&VÖ–âfÆ–BÂæB&VÖ–æ–ærÆ–çFW‡B&V6÷&G26â&R&W7VÖVBÆFW"âp¢“° ¢Òf–æÆÇ’°¢f÷"€¢6öç7B6öçG&öÀ¢öbÆÄ'WGFöç0¢’°¢6öçG&öÂæF—6&ÆVBÐ¢fÇ6S°¢Ð ¢v—B&Vg&W6…&÷FV7F–öåæVÂ‚“°¢Ð¢Ó° ¢fW&–g”'WGFöâæöæ6Æ–6²Ð¢7–æ2‚’Óâ°¢6öç7BÆÄ'WGFöç2Ð¢'&’æg&öÒ€¢ÖöFÂçVW'•6VÆV7F÷$ÆÂ€¢v'WGFöâp¢¢“° ¢f÷"€¢6öç7B6öçG&öÀ¢öbÆÄ'WGFöç0¢’°¢6öçG&öÂæF—6&ÆVBÐ¢G'VS°¢Ð ¢FWF–ÂçFW‡D6öçFVçBÐ¢ufW&–g––ær&÷FV7FVBÖ†—7F÷'’&V6÷fW'’VçfVÆ÷^(
bs° ¢G'’°¢6öç7B”¶W’Ð¢v—BÆöE6V7W&T”¶W’‚“° ¢–b€¢”¶W¢’°¢F‡&÷ræWrW'&÷"€¢tæòF÷&â’¶W’—2f–Æ&ÆR–âF†—2W6W'67&—B6W76–öââp¢“°¢Ð ¢6öç7B&W7VÇBÐ¢v—BfW&–g”WF†VçF–6FVD†—7F÷'•&V6÷fW'”VçfVÆ÷R€¢”¶W’À¢66†VBæ66÷VçEö–@¢“° ¢–b€¢&W7VÇBç7FGW2ÓÐ¢wfW&–f–VBrÇÀ¢&W7VÇBæ6†ævVBÓÐ¢fÇ6P¢’°¢F‡&÷ræWrW'&÷"€¢u&V6÷fW'’fW&–f–6F–öâ&WGW&æVBâVæW‡V7FVB&W7VÇBâp¢“°¢Ð ¢6öç7BæF—fT¶W•&W6VçBÐ¢&W7VÇBææF—fUö¶W•÷&W6VçBÓÓÐ¢G'VP¢òu–W2p¢¢tæòs° ¢6öç7BæF—fT¶W”ÖF6‚Ð¢&W7VÇBæÖF6†W5öæF—fUö¶W’ÓÓÐ¢G'VP¢òu–W2p¢¢&W7VÇBæÖF6†W5öæF—fUö¶W’ÓÓÐ¢fÇ6P¢òtæòp¢¢tæ÷Bf–Æ&ÆRs° ¢ÆW'B€¢u&÷FV7FVBÖ†—7F÷'’&V6÷fW'’fW&–f–VBåÆåÆâr°¢u&V6÷fW'’VçfVÆ÷S¢WF†VçF–6FVEÆâr°¢66÷VçB&–æF–æs¢G·&W7VÇBæ66÷VçEö–GÒfW&–f–VEÆæ°¢t6æ'’WF†VçF–6F–öã¢76VEÆâr°¢æF—fR†—7F÷'’¶W’&W6VçC¢G¶æF—fT¶W•&W6VçGÕÆæ°¢&V6÷fW&VB¶W’ÖF6†W2æF—fR¶W“¢G¶æF—fT¶W”ÖF6‡ÕÆæ°¢FF6†ævVC¢G·&W7VÇBæ6†ævVBòu–W2r¢tæòwÕÆåÆæ°¢tæòVæ7'—F–öâ¶W—2÷"F÷&âÆöw2vW&R6†ævVBâp¢“° ¢Ò6F6‚†W'&÷"’°¢6öç6öÆRæW'&÷"€¢uµF÷&âæÇ—F–75Ò&V6÷fW'’fW&–f–6F–öâf–ÆVC¢rÀ¢W'&÷ ¢“° ¢ÆW'B€¢u&V6÷fW'’fW&–f–6F–öâf–ÆVBåÆåÆâr°¢G¶W'&÷"æÖW76vWÕÆåÆæ°¢tæòVæ7'—F–öâ¶W—2÷"F÷&âÆöw2vW&R6†ævVBâp¢“° ¢Òf–æÆÇ’°¢f÷"€¢6öç7B6öçG&öÀ¢öbÆÄ'WGFöç0¢’°¢6öçG&öÂæF—6&ÆVBÐ¢fÇ6S°¢Ð ¢v—B&Vg&W6…&÷FV7F–öåæVÂ‚“°¢Ð¢Ó° ¢ÖöFÂæFDWfVçDÆ—7FVæW"€¢wFÖ†—7F÷'’×WFFVBrÀ¢‚’Óâ°¢fö–B&Vg&W6…&÷FV7F–öåæVÂ‚“°¢Ð¢“° ¢v—B&Vg&W6…&÷FV7F–öåæVÂ‚“°¢Ó°¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ¢òòtR%UEDôà¢òòÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÓÐ ¢gVæ7F–öâ&VÖ÷fU7FÆUF÷&äæÇ—F–75V’‚’°¢f÷"€¢6öç7B–@¢öb°¢ÔôDÅô”BÀ¢%UEDôåô”BÀ¢5E”ÄUô”@¢Ð¢’°¢6öç7B7FÆTæöFRÐ¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢–@¢“° ¢7FÆTæöFSòç&VÖ÷fSòâ‚“°¢Ð¢Ð ¢gVæ7F–öâ–ç7FÆÄ'WGFöâ‚’° ¢6öç7BW†—7F–æt'WGFöâÐ¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢%UEDôåô”@¢“° ¢–b€¢W†—7F–æt'WGFöà¢’°¢&WGW&âW†—7F–æt'WGFöã°¢Ð ¢6öç7B'WGFöâÐ¢Fö7VÖVçBæ7&VFTVÆVÖVçB€¢v'WGFöâp¢“° ¢'WGFöâæ–BÐ¢%UEDôåô”C° ¢'WGFöâçFW‡D6öçFVçBÐ¢uF÷&âæÇ—F–72s° ¢'WGFöâçG—RÐ¢v'WGFöâs° ¢'WGFöâæFF6WBçfW'6–öâÐ¢dU%4”ôã° ¢'WGFöâç6WDGG&–'WFSòâ€¢v&–ÖÆ&VÂrÀ¢÷VâF÷&âæÇ—F–72GµdU%4”ôçÖ ¢“° ¢òò7&—F–6ÂÆVæ6†W"7G–ÆW2&R–æÆ–æR6òF†R&V6÷fW'’6öçG&öÂ7F—0¢òòf—6–&ÆRWfVâ–bF†RÆ&vW"÷F–öæÂ7G–ÆW6†VWB6ææ÷B&R–ç7FÆÆVBà¢ö&¦V7Bæ76–vâ€¢'WGFöâç7G–ÆRÀ¢°¢÷6—F–öã¢vf—†VBrÀ¢&–v‡C¢s'‚rÀ¢&÷GFöÓ¢s“‚rÀ¢¤–æFWƒ¢s“““““’rÀ¢FF–æs¢s‚7‚rÀ¢&÷&FW#¢srÀ¢&÷&FW%&F—W3¢s‡‚rÀ¢&6¶w&÷VæC¢r3##"rÀ¢6öÆ÷#¢r6ffbrÀ¢föçEvV–v‡C¢ssp¢Ð¢“° ¢'WGFöâæFDWfVçDÆ—7FVæW"€¢v6Æ–6²rÀ¢7–æ2‚’Óâ°¢G'’°¢&V6÷&E7F'GW†VÇF‚€¢vÖöFÅö÷Vå÷&WVW7FVBp¢“° ¢v—B÷VäÖöFÂ‡°¢&W7F÷&U7FFS ¢&VEV•6W76–öå7FFR‚¢Ò“° ¢&V6÷&E7F'GW†VÇF‚€¢w&VG’p¢“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vÖöFÅö÷Våöf–ÆVBrÀ¢W'&÷ ¢“° ¢'WGFöâçFW‡D6öçFVçBÐ¢uF÷&âæÇ—F–72)ªs° ¢'WGFöâçF—FÆRÐ¢uF÷&âæÇ—F–726÷VÆBæ÷B÷Vââ&VÆöBF†—2F÷&âF"æBG'’v–ââs°¢Ð¢Ð¢“° ¢Fö7VÖVçBæ&öG’æVæD6†–ÆB€¢'WGFöà¢“° ¢G'’°¢–æ¦V7E7G–ÆW2‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vÆVæ6†W%÷7G–ÆW5öf–ÆVBrÀ¢W'&÷ ¢“°¢Ð ¢G'’°¢Ö¶TfÆöF–æt'WGFöäÖ÷f&ÆR€¢'WGFöâÀ¢%UEDôåõõ4•D”ôåô´U¢“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vÆVæ6†W%÷÷6—F–öåöf–ÆVBrÀ¢W'&÷ ¢“°¢Ð ¢&V6÷&E7F'GW†VÇF‚€¢vÆVæ6†W%ö–ç7FÆÆVBp¢“° ¢&WGW&â'WGFöã°¢Ð ¢6öç7BÄTä4„U%ô$ôõEõ$UE%•ôDTÄ•ôÕ2Ð¢#S° ¢6öç7BÄTä4„U%ô$ôõEôÔ…ôEDTÕE2Ð¢C° ¢6öç7BT•ôõ$”TåDD”ôåõd”Uuõ%Eõ4UEDÄUôÕ2Ð¢#S° ¢ÆWBV”ÖöFÅv5&W6VçBÐ¢fÇ6S° ¢ÆWBV”ÖöFÅ&W7F÷&U&öÖ—6RÐ¢çVÆÃ° ¢ÆWBV•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'4–ç7FÆÆVBÐ¢fÇ6S° ¢7–æ2gVæ7F–öâ&W7F÷&T÷VäÖöFÄgFW$FöÕ&WÆ6VÖVçB€¢&W7F÷&U7FFRÒçVÆÀ¢’°¢–b€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢ÔôDÅô”@¢¢’°¢V”ÖöFÅv5&W6VçBÐ¢G'VS° ¢&WGW&âG'VS°¢Ð ¢–b€¢V”ÖöFÅ&W7F÷&U&öÖ—6P¢’°¢&WGW&âV”ÖöFÅ&W7F÷&U&öÖ—6S°¢Ð ¢6öç7B7FFRÐ¢&W7F÷&U7FFRÇÀ¢&VEV•6W76–öå7FFR‚“° ¢–b€¢7FFSòæÖöFÅö÷Và¢’°¢&WGW&âfÇ6S°¢Ð ¢6öç7B÷W&F–öâÐ¢†7–æ2‚’Óâ°¢v—B÷VäÖöFÂ‡°¢&W7F÷&U7FFS ¢7FFP¢Ò“° ¢6öç7B&W7F÷&VBÐ¢&ööÆVâ€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢ÔôDÅô”@¢¢“° ¢V”ÖöFÅv5&W6VçBÐ¢&W7F÷&VC° ¢&WGW&â&W7F÷&VC°¢Ò’‚“° ¢V”ÖöFÅ&W7F÷&U&öÖ—6RÐ¢÷W&F–öã° ¢G'’°¢&WGW&âv—B÷W&F–öã°¢Ò6F6‚†W'&÷"’°¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò6÷VÆBæ÷B&W7F÷&RF†R÷VâÖöFÂgFW"vR&WÆ6VÖVçC¢rÀ¢W'&÷ ¢“° ¢&WGW&âfÇ6S°¢Òf–æÆÇ’°¢–b€¢V”ÖöFÅ&W7F÷&U&öÖ—6RÓÓÐ¢÷W&F–öà¢’°¢V”ÖöFÅ&W7F÷&U&öÖ—6RÐ¢çVÆÃ°¢Ð¢Ð¢Ð ¢gVæ7F–öâ–ç7FÆÅV•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'2‚’°¢–b€¢V•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'4–ç7FÆÆVBÇÀ¢G—Vöbv–æF÷rÓÓÐ¢wVæFVf–æVBp¢’°¢&WGW&ã°¢Ð ¢V•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'4–ç7FÆÆVBÐ¢G'VS° ¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢v÷&–VçFF–öæ6†ævRrÀ¢Ö&µV”÷&–VçFF–öå&Vg&W6…VæF–ærÀ¢²76—fS¢G'VRÐ¢“° ¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢wvV†–FRrÀ¢Ö&µV”÷&–VçFF–öå&Vg&W6…VæF–ærÀ¢²76—fS¢G'VRÐ¢“° ¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢w&W6—¦RrÀ¢Ö&µV”÷&–VçFF–öå&Vg&W6…VæF–ærÀ¢²76—fS¢G'VRÐ¢“°¢Ð ¢gVæ7F–öâ&W7F÷&UV”gFW%f–Ww÷'E6WGFÆW2‚’°¢–b€¢G—Vöbv–æF÷rÓÓÐ¢wVæFVf–æVBp¢’°¢–ç7FÆÅV•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'2‚“°¢&WGW&ã°¢Ð ¢ÆWBf–æ—6†VBÐ¢fÇ6S° ¢ÆWB6WGFÆUF–ÖW"Ð¢çVÆÃ° ¢6öç7BFV×÷&'”WfVçG2Ò°¢v÷&–VçFF–öæ6†ævRrÀ¢w&W6—¦RrÀ¢wvW6†÷rp¢Ó° ¢6öç7Bf–æ—6…&W7F÷&RÐ¢‚’Óâ°¢–b€¢f–æ—6†V@¢’°¢&WGW&ã°¢Ð ¢f–æ—6†VBÐ¢G'VS° ¢f÷"€¢6öç7BWfVçDæÖP¢öbFV×÷&'”WfVçG0¢’°¢v–æF÷rç&VÖ÷fTWfVçDÆ—7FVæW#òâ€¢WfVçDæÖRÀ¢v—Df÷%f–Ww÷'E–ç@¢“°¢Ð ¢–b€¢6WGFÆUF–ÖW"ÓÐ¢çVÆÂb`¢G—Vöb6ÆV%F–ÖV÷WBÓÓÐ¢vgVæ7F–öâp¢’°¢6ÆV%F–ÖV÷WB€¢6WGFÆUF–ÖW ¢“°¢Ð ¢ÆWB6WGFÆVE&W7F÷&U7FFRÐ¢çVÆÃ° ¢G'’°¢6WGFÆVE&W7F÷&U7FFRÐ¢6öç7VÖUV”÷&–VçFF–öå&W7F÷&U7FFR‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢wV•ö÷&–VçFF–öå÷6WGFÆU÷&W7F÷&Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò6÷VÆBæ÷B&W7F÷&RF†R&–÷"T’gFW"f–Ww÷'B6WGFÆVÖVçC¢rÀ¢W'&÷ ¢“°¢Ð ¢–ç7FÆÅV•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'2‚“° ¢–b€¢6WGFÆVE&W7F÷&U7FFP¢’°¢fö–B&W7F÷&T÷VäÖöFÄgFW$FöÕ&WÆ6VÖVçB€¢6WGFÆVE&W7F÷&U7FFP¢“°¢Ð¢Ó° ¢6öç7Bv—Df÷%f–Ww÷'E–çBÐ¢‚’Óâ°¢–b€¢f–æ—6†V@¢’°¢&WGW&ã°¢Ð ¢–b€¢G—Vöb&WVW7Dæ–ÖF–öäg&ÖRÓÓÐ¢vgVæ7F–öâp¢’°¢&WVW7Dæ–ÖF–öäg&ÖR€¢‚’Óâ°¢&WVW7Dæ–ÖF–öäg&ÖR€¢f–æ—6…&W7F÷&P¢“°¢Ð¢“°¢ÒVÇ6R°¢f–æ—6…&W7F÷&R‚“°¢Ð¢Ó° ¢f÷"€¢6öç7BWfVçDæÖP¢öbFV×÷&'”WfVçG0¢’°¢v–æF÷ræFDWfVçDÆ—7FVæW"€¢WfVçDæÖRÀ¢v—Df÷%f–Ww÷'E–çBÀ¢²76—fS¢G'VRÐ¢“°¢Ð ¢–b€¢G—Vöb6WEF–ÖV÷WBÓÓÐ¢vgVæ7F–öâp¢’°¢6WGFÆUF–ÖW"Ð¢6WEF–ÖV÷WB€¢v—Df÷%f–Ww÷'E–çBÀ¢T•ôõ$”TåDD”ôåõd”Uuõ%Eõ4UEDÄUôÕ0¢“°¢ÒVÇ6R°¢v—Df÷%f–Ww÷'E–çB‚“°¢Ð¢Ð ¢gVæ7F–öâ–æ—F–Æ—¦R‚’° ¢òòF†RÆVæ6†W"—2F†R&V6÷fW'’F‚f÷"WfW'’÷F†W"fVGW&Râ–ç7FÆÂ—@¢òò&Vf÷&R÷F–öæÂ÷&–VçFF–öâ÷6W76–öâ&W7F÷&F–öâ6òæöâÖ7&—F–6À¢òò7F'GWf–ÇW&R6ææ÷BÆVfRF÷&âæÇ—F–72–æ66W76–&ÆRà¢&VÖ÷fU7FÆUF÷&äæÇ—F–75V’‚“° ¢–ç7FÆÄ'WGFöâ‚“° ¢&V6÷&E7F'GW†VÇF‚€¢vÆVæ6†W%ö–æ—F–Æ—¦VBp¢“° ¢ÆWB&W7F÷&U7FFRÐ¢çVÆÃ° ¢G'’°¢&W7F÷&U7FFRÐ¢6öç7VÖUV”÷&–VçFF–öå&W7F÷&U7FFR‡°¢FVfW%÷Væ6†ævVEö÷&–VçFF–öã ¢G'VP¢Ò“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢wV•÷6W76–öå÷&W7F÷&Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò6÷VÆBæ÷B&W7F÷&RF†R&–÷"T’6W76–öã¢rÀ¢W'&÷ ¢“°¢Ð ¢–b€¢&W7F÷&U7FFRÓÓÐ¢VæFVf–æV@¢’°¢&W7F÷&UV”gFW%f–Ww÷'E6WGFÆW2‚“°¢ÒVÇ6R°¢–ç7FÆÅV•6W76–öäÆ–fV7–6ÆTÆ—7FVæW'2‚“° ¢–b€¢&W7F÷&U7FFP¢’°¢fö–B&W7F÷&T÷VäÖöFÄgFW$FöÕ&WÆ6VÖVçB€¢&W7F÷&U7FFP¢“°¢Ð¢Ð ¢G'’°¢–ç7FÆÅ76—fUG&–æ–æu6æ6†÷D6GW&R‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢wG&–æ–æuö6GW&Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢òò6æ6†÷B6GW&R—2÷F–öæÂæB×W7BæWfW"–çFW&fW&Rv—F‚F÷&âà¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò76—fRG&–æ–ær6æ6†÷G26÷VÆBæ÷B&RVæ&ÆVC¢rÀ¢W'&÷ ¢“°¢Ð ¢G'’°¢–ç7FÆÅG&–æ–æt6†V6·ö–çD6æ'’‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢wG&–æ–æuö6†V6·ö–çEö6æ'•öf–ÆVBrÀ¢W'&÷ ¢“° ¢òòF†R6†V6·ö–çB6æ'’—2÷F–öæÂæB6ææ÷B&Æö6²F†RÆVæ6†W"À¢òòG&–æ–ærÂ÷"W†—7F–æræÇ—F–72à¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75ÒWFöÖF–26†V6·ö–çB6æ'’6÷VÆBæ÷B&RVæ&ÆVC¢rÀ¢W'&÷ ¢“°¢Ð ¢G'’°¢–ç7FÆÄWFöÖF–4Æöu7–æ566†VGVÆW"‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vWFöÖF–5÷7–æ5öf–ÆVBrÀ¢W'&÷ ¢“° ¢òòWFöÖF–27–æ6‡&öæ—¦F–öâ—2÷F–öæÂâ—B×W7BæWfW"–çFW&fW&Rv—F€¢òòF†RÆVæ6†W"÷"F†RW6W"w2&–Æ—G’Fò'VâÖçVÂfW&–f–VBWFFRà¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75ÒWFöÖF–2Æör7–æ6‡&öæ—¦F–öâ6÷VÆBæ÷B&R66†VGVÆVC¢rÀ¢W'&÷ ¢“°¢Ð ¢–b€¢G—Vöb×WFF–öäö'6W'fW"ÓÓÐ¢vgVæ7F–öârb`¢Fö7VÖVçBæFö7VÖVçDVÆVÖVç@¢’°¢æWr×WFF–öäö'6W'fW"€¢‚’Óâ° ¢–b€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢%UEDôåô”@¢¢’°¢G'’°¢–ç7FÆÄ'WGFöâ‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vÆVæ6†W%÷&W7F÷&Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75Ò6÷VÆBæ÷B&W7F÷&RF†RÆVæ6†W"gFW"vRWFFS¢rÀ¢W'&÷ ¢“°¢Ð¢Ð ¢6öç7BÖöFÅ&W6VçBÐ¢&ööÆVâ€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢ÔôDÅô”@¢¢“° ¢–b€¢ÖöFÅ&W6Vç@¢’°¢V”ÖöFÅv5&W6VçBÐ¢G'VS°¢ÒVÇ6R–b€¢V”ÖöFÅv5&W6Vç@¢’°¢òò6Æ÷6–ærw&—FW2ÖöFÅö÷VãÖfÇ6R&Vf÷&R&VÖ÷fÂÂ6òF†—2öæÇ¢òò&W7F÷&W2ÖöFÂF†BF÷&åD&VÖ÷fVBv†–ÆRF†R6ÖRF"7F–ÆÀ¢òòW‡V7FVB—BFò&R÷Vâà¢V”ÖöFÅv5&W6VçBÐ¢fÇ6S° ¢fö–B&W7F÷&T÷VäÖöFÄgFW$FöÕ&WÆ6VÖVçB‚“°¢Ð¢Ð¢’æö'6W'fR€¢Fö7VÖVçBæFö7VÖVçDVÆVÖVçBÀ¢°¢6†–ÆDÆ—7C ¢G'VRÀ ¢7V'G&VS ¢G'VP¢Ð¢“°¢Ð ¢&V6÷&E7F'GW†VÇF‚€¢w&VG’p¢“°¢Ð ¢gVæ7F–öâ–æ—F–Æ—¦Uv†VäFö7VÖVçE&VG’€¢GFV×BÒ ¢’°¢6öç7BFö7VÖVçE&VG’Ð¢G—VöbFö7VÖVçBÓÐ¢wVæFVf–æVBrb`¢Fö7VÖVçBæFö7VÖVçDVÆVÖVçBb`¢Fö7VÖVçBæ†VBb`¢Fö7VÖVçBæ&öG“° ¢–b€¢Fö7VÖVçE&VG¢’°¢–b€¢GFV×BÀ¢ÄTä4„U%ô$ôõEôÔ…ôEDTÕE2b`¢G—Vöb6WEF–ÖV÷WBÓÓÐ¢vgVæ7F–öâp¢’°¢6WEF–ÖV÷WB€¢‚’Óâ°¢–æ—F–Æ—¦Uv†VäFö7VÖVçE&VG’€¢GFV×B²¢“°¢ÒÀ¢ÄTä4„U%ô$ôõEõ$UE%•ôDTÄ•ôÕ0¢“°¢Ð ¢&WGW&ã°¢Ð ¢G'’°¢–æ—F–Æ—¦R‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vÆVæ6†W%ö–æ—F–Æ—¦Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75ÒÆVæ6†W"7F'GWv2FVÆ–VC¢rÀ¢W'&÷ ¢“° ¢–b€¢Fö7VÖVçBævWDVÆVÖVçD'”–B€¢%UEDôåô”@¢’b`¢GFV×BÀ¢ÄTä4„U%ô$ôõEôÔ…ôEDTÕE2b`¢G—Vöb6WEF–ÖV÷WBÓÓÐ¢vgVæ7F–öâp¢’°¢6WEF–ÖV÷WB€¢‚’Óâ°¢–æ—F–Æ—¦Uv†VäFö7VÖVçE&VG’€¢GFV×B²¢“°¢ÒÀ¢ÄTä4„U%ô$ôõEõ$UE%•ôDTÄ•ôÕ0¢“°¢Ð¢Ð¢Ð ¢òò7F'BF†R&V6÷fW'’ÆVæ6†W"&Vf÷&R÷F–öæÂ6GW&Rv÷&²âF†—2&W6W'fW0¢òò66W72FòF÷&âæÇ—F–72WfVâv†VâæöâÖ7&—F–6ÂfVGW&Rf–Ç2à¢–æ—F–Æ—¦Uv†VäFö7VÖVçE&VG’‚“° ¢G'’°¢–ç7FÆÅ76—fUG&–æ–æu6æ6†÷D6GW&R‚“°¢Ò6F6‚†W'&÷"’°¢ÆVæ6†W%7F'GWf–ÇW&R€¢vV&Ç•÷G&–æ–æuö6GW&Uöf–ÆVBrÀ¢W'&÷ ¢“° ¢6öç6öÆRçv&â€¢uµF÷&âæÇ—F–75ÒV&Ç’76—fRG&–æ–ær6GW&R6÷VÆBæ÷B&RVæ&ÆVC¢rÀ¢W'&÷ ¢“°¢Ð §Ò’‚“°