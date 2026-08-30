// ==UserScript==
// @name         Torn Analytics — Independent Upper-Boundary Probe
// @namespace    chatgpt.openai.com/torn-tools
// @version      1.0.0
// @description  One-time, read-only check of the final Torn Analytics history timestamp against a one-second-expanded Torn API range.
// @author       Personal use
// @match        https://www.torn.com/*
// @match        https://torn.com/*
// @grant        GM_xmlhttpRequest
// @connect      api.torn.com
// @run-at       document-idle
// ==/UserScript==

(() => {
  'use strict';

  const PROBE_VERSION = '1.0.0';
  const HISTORY_FORMAT = 'torn-analytics-readable-history';
  const HISTORY_VERSION = 2;
  const HISTORY_RAW_FORMAT = 'torn-api-v2-user-log-record-v1';
  const API_ORIGIN = 'https://api.torn.com';
  const PAGE_LIMIT = 100;
  const REQUEST_GAP_MS = 500;
  const REQUEST_TIMEOUT_MS = 30000;
  const API_KEY_MARKER = '###PDA-APIKEY###';
  const injectedKey = API_KEY_MARKER.includes('PDA-APIKEY')
    ? ''
    : API_KEY_MARKER.trim();

  class ProbeError extends Error {
    constructor(message) {
      super(message);
      this.name = 'ProbeError';
    }
  }

  function stableJson(value) {
    if (Array.isArray(value)) return `[${value.map(stableJson).join(',')}]`;
    if (value && typeof value === 'object') {
      return `{${Object.keys(value)
        .sort()
        .map(key => `${JSON.stringify(key)}:${stableJson(value[key])}`)
        .join(',')}}`;
    }
    return JSON.stringify(value);
  }

  async function sha256Hex(text) {
    if (!globalThis.crypto?.subtle || typeof TextEncoder !== 'function') {
      throw new ProbeError('SHA-256 is unavailable in this browser.');
    }
    const digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(String(text)));
    return Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, '0')).join('');
  }

  function positiveInteger(value, label) {
    const number = Number(value);
    if (!Number.isSafeInteger(number) || number <= 0) {
      throw new ProbeError(`${label} must be a positive integer.`);
    }
    return number;
  }

  function canonicalId(value) {
    if (typeof value !== 'string' && typeof value !== 'number') return null;
    if (typeof value === 'number' && !Number.isSafeInteger(value)) return null;
    const raw = String(value);
    return raw && raw === raw.trim() ? raw : null;
  }

  function extractRaw(record) {
    const id = canonicalId(record?.id);
    const timestamp = positiveInteger(record?.timestamp, 'History record timestamp');
    const archive = record?._archive;
    const raw = archive?.raw;
    if (
      !id ||
      archive?.format !== HISTORY_RAW_FORMAT ||
      !raw ||
      typeof raw !== 'object' ||
      Array.isArray(raw) ||
      canonicalId(raw.id) !== id ||
      Number(raw.timestamp) !== timestamp
    ) {
      throw new ProbeError(`History record ${id || '(unknown)'} has an invalid raw archive binding.`);
    }
    return { id, timestamp, raw, canonical: stableJson(raw) };
  }

  async function validateHistoryExport(payload) {
    if (
      !payload ||
      payload.format !== HISTORY_FORMAT ||
      Number(payload.format_version) !== HISTORY_VERSION ||
      !Array.isArray(payload.records) ||
      payload.records.length === 0
    ) {
      throw new ProbeError('This is not a supported Torn Analytics readable-history export.');
    }
    const accountId = positiveInteger(payload.account?.id, 'History account ID');
    const last = positiveInteger(payload.coverage?.last_timestamp, 'Coverage end');
    if (Number(payload.coverage?.record_count) !== payload.records.length) {
      throw new ProbeError('The history record count does not match its coverage metadata.');
    }
    if (
      payload.archive_provenance?.raw_record_format !== HISTORY_RAW_FORMAT ||
      Number(payload.archive_provenance?.raw_record_count) !== payload.records.length ||
      payload.archive_provenance?.lossless_raw_complete !== true
    ) {
      throw new ProbeError('The selected history is not a complete lossless raw archive.');
    }
    const integrity = payload.integrity;
    if (
      integrity?.algorithm !== 'SHA-256' ||
      integrity?.canonicalization !== 'stable-json-v1' ||
      integrity?.scope !== 'all top-level fields except integrity' ||
      !/^[a-f0-9]{64}$/.test(String(integrity?.digest || ''))
    ) {
      throw new ProbeError('The history integrity declaration is missing or unsupported.');
    }
    const unsigned = { ...payload };
    delete unsigned.integrity;
    const digest = await sha256Hex(stableJson(unsigned));
    if (digest !== integrity.digest) {
      throw new ProbeError('The history SHA-256 integrity digest does not match.');
    }
    const finalRecords = [];
    const finalIds = new Set();
    for (const record of payload.records) {
      const extracted = extractRaw(record);
      if (extracted.timestamp !== last) continue;
      if (finalIds.has(extracted.id)) {
        throw new ProbeError(`Duplicate final-timestamp identity ${extracted.id}.`);
      }
      finalIds.add(extracted.id);
      finalRecords.push(extracted);
    }
    if (!finalRecords.length || Number(payload.records.at(-1)?.timestamp) !== last) {
      throw new ProbeError('The coverage end does not contain a final history record.');
    }
    return {
      accountId,
      accountName: String(payload.account?.name || '').trim(),
      last,
      digest,
      finalRecords
    };
  }

  function approvedApiUrl(url, endpoint, expectedRange = null) {
    let parsed;
    try {
      parsed = new URL(url);
    } catch {
      throw new ProbeError('Refusing an invalid Torn API URL.');
    }
    if (
      parsed.protocol !== 'https:' ||
      parsed.hostname !== 'api.torn.com' ||
      parsed.port ||
      parsed.username ||
      parsed.password ||
      parsed.hash ||
      parsed.pathname !== endpoint ||
      parsed.searchParams.has('key')
    ) {
      throw new ProbeError('Refusing to send credentials to an unapproved destination.');
    }
    if (endpoint === '/v2/user/profile') {
      if ([...parsed.searchParams.keys()].length) {
        throw new ProbeError('The profile request must not include query parameters.');
      }
      return parsed.toString();
    }
    const keys = [...parsed.searchParams.keys()];
    if (keys.some(key => !['from', 'to', 'limit'].includes(key))) {
      throw new ProbeError('The boundary request unexpectedly changed API scope.');
    }
    const from = Number(parsed.searchParams.get('from'));
    const to = Number(parsed.searchParams.get('to'));
    const limit = Number(parsed.searchParams.get('limit'));
    if (
      !Number.isSafeInteger(from) ||
      !Number.isSafeInteger(to) ||
      !Number.isSafeInteger(limit) ||
      from < 0 ||
      to <= from ||
      limit !== PAGE_LIMIT ||
      parsed.searchParams.getAll('from').length !== 1 ||
      parsed.searchParams.getAll('to').length !== 1 ||
      parsed.searchParams.getAll('limit').length !== 1 ||
      (expectedRange && (from !== expectedRange.from || to !== expectedRange.to))
    ) {
      throw new ProbeError('The boundary request has invalid or altered bounds.');
    }
    return parsed.toString();
  }

  function apiError(json) {
    if (!json?.error) return null;
    if (typeof json.error === 'string') return json.error;
    return `Torn API error ${json.error.code ?? '?'}: ${json.error.error ?? json.error.message ?? 'Unknown error'}`;
  }

  function createTransport(apiKey, hooks = {}) {
    const state = { requests: 0, lastStartedAt: 0 };
    const sleep = hooks.sleep || (ms => new Promise(resolve => setTimeout(resolve, ms)));
    const requestImpl = hooks.request || (options => new Promise((resolve, reject) => {
      if (typeof GM_xmlhttpRequest !== 'function') {
        reject(new ProbeError('Secure userscript transport is unavailable.'));
        return;
      }
      GM_xmlhttpRequest({
        ...options,
        onload: resolve,
        onerror: () => reject(new ProbeError('The Torn API network request failed.')),
        ontimeout: () => reject(new ProbeError('The Torn API network request timed out.'))
      });
    }));

    async function getJson(url, endpoint, expectedRange = null) {
      if (!apiKey) throw new ProbeError('A Torn API key is required.');
      if (state.requests >= 2) throw new ProbeError('The two-request safety limit was reached.');
      const safeUrl = approvedApiUrl(url, endpoint, expectedRange);
      const elapsed = Date.now() - state.lastStartedAt;
      if (elapsed < REQUEST_GAP_MS) await sleep(REQUEST_GAP_MS - elapsed);
      state.lastStartedAt = Date.now();
      state.requests += 1;
      hooks.onRequest?.(state.requests);
      const response = await requestImpl({
        method: 'GET',
        url: safeUrl,
        headers: { Authorization: `ApiKey ${apiKey}`, Accept: 'application/json' },
        timeout: REQUEST_TIMEOUT_MS,
        anonymous: true
      });
      if (Number(response?.status) < 200 || Number(response?.status) >= 300) {
        throw new ProbeError(`Torn API returned HTTP ${response?.status ?? 'unknown'}.`);
      }
      let json;
      try {
        json = JSON.parse(response.responseText);
      } catch {
        throw new ProbeError('Torn API returned invalid JSON.');
      }
      const error = apiError(json);
      if (error) throw new ProbeError(error);
      return json;
    }
    return { state, getJson };
  }

  async function runBoundaryProbe(historyPayload, apiKey, hooks = {}) {
    const source = await validateHistoryExport(historyPayload);
    const transport = createTransport(apiKey, hooks);
    const profile = await transport.getJson(`${API_ORIGIN}/v2/user/profile`, '/v2/user/profile');
    const actualId = positiveInteger(profile?.profile?.id, 'Authenticated Torn account ID');
    if (actualId !== source.accountId) {
      throw new ProbeError(`API key account ${actualId} does not match history account ${source.accountId}.`);
    }
    const from = source.last - 1;
    const to = source.last + 1;
    const url = `${API_ORIGIN}/v2/user/log?from=${from}&to=${to}&limit=${PAGE_LIMIT}`;
    const json = await transport.getJson(url, '/v2/user/log', { from, to });
    if (!Array.isArray(json?.log)) throw new ProbeError('Torn API returned an invalid boundary log page.');
    const links = json?._metadata?.links;
    if (!links || !Object.prototype.hasOwnProperty.call(links, 'prev')) {
      throw new ProbeError('Torn API omitted required boundary pagination metadata.');
    }
    const returned = new Map();
    for (const raw of json.log) {
      const id = canonicalId(raw?.id);
      const timestamp = positiveInteger(raw?.timestamp, 'API record timestamp');
      if (!id || timestamp < from || timestamp > to) {
        throw new ProbeError('Torn API returned an invalid or out-of-range boundary record.');
      }
      const canonical = stableJson(raw);
      const existing = returned.get(id);
      if (existing && existing.canonical !== canonical) {
        throw new ProbeError(`Torn API returned conflicting payloads for log ${id}.`);
      }
      returned.set(id, { id, timestamp, raw, canonical });
    }
    const exact = [];
    const missing = [];
    const mismatched = [];
    for (const target of source.finalRecords) {
      const candidate = returned.get(target.id);
      if (!candidate) missing.push(target.id);
      else if (candidate.canonical !== target.canonical) mismatched.push(target.id);
      else exact.push(target.id);
    }
    const saturated = json.log.length >= PAGE_LIMIT || links.prev !== null;
    const outcome = mismatched.length
      ? 'FAIL'
      : missing.length === 0
        ? 'CONFIRMED'
        : 'INCONCLUSIVE';
    return {
      outcome,
      explanation: outcome === 'CONFIRMED'
        ? 'Every final-timestamp history record returned exactly when the API range extended one second beyond the original upper bound.'
        : outcome === 'FAIL'
          ? 'One or more final-timestamp identities returned with different raw payloads.'
          : saturated
            ? 'The expanded boundary page was saturated or paginated before every target could be proven.'
            : 'The expanded boundary page did not return every final-timestamp history record.',
      account: { id: actualId, name: String(profile?.profile?.name || source.accountName).trim() },
      history_digest: source.digest,
      final_timestamp: source.last,
      final_iso: new Date(source.last * 1000).toISOString(),
      requested_range: { from, to },
      requests: transport.state.requests,
      api_page_records: json.log.length,
      saturated,
      target_count: source.finalRecords.length,
      exact_count: exact.length,
      missing_count: missing.length,
      mismatch_count: mismatched.length,
      exact_ids: exact,
      missing_ids: missing,
      mismatch_ids: mismatched
    };
  }

  const testApi = {
    ProbeError,
    stableJson,
    sha256Hex,
    validateHistoryExport,
    approvedApiUrl,
    createTransport,
    runBoundaryProbe
  };
  if (globalThis.__TA_BOUNDARY_PROBE_TEST_HOOK__) {
    globalThis.__TA_BOUNDARY_PROBE_TEST_EXPORTS__ = testApi;
    return;
  }

  const ROOT_ID = 'ta-independent-boundary-probe-root';
  const STYLE_ID = `${ROOT_ID}-style`;
  let selectedPayload = null;

  function installStyle() {
    if (document.getElementById(STYLE_ID)) return;
    const style = document.createElement('style');
    style.id = STYLE_ID;
    style.textContent = `
      #${ROOT_ID}, #${ROOT_ID} * { box-sizing: border-box; }
      #${ROOT_ID} { position: fixed; inset: 0; z-index: 2147483647; display: flex; align-items: center; justify-content: center; padding: 16px; background: rgba(0,0,0,.8); color: #eee; font: 15px/1.4 Arial,sans-serif; }
      #${ROOT_ID} .ta-b-card { width: min(720px,100%); max-height: 92vh; overflow: auto; padding: 18px; border: 1px solid #555; border-radius: 14px; background: #191919; }
      #${ROOT_ID} h2 { margin: 0 0 8px; color: #fff; font-size: 22px; }
      #${ROOT_ID} p { margin: 8px 0; }
      #${ROOT_ID} .ta-b-safe { padding: 10px 12px; border-left: 4px solid #d5a84e; border-radius: 6px; background: #211d16; }
      #${ROOT_ID} label { display: block; margin-top: 14px; color: #fff; font-weight: 700; }
      #${ROOT_ID} input { width: 100%; margin-top: 6px; padding: 12px; border: 1px solid #666; border-radius: 8px; background: #101010; color: #fff; }
      #${ROOT_ID} .ta-b-actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 16px; }
      #${ROOT_ID} button { min-height: 44px; padding: 10px 16px; border: 1px solid #777; border-radius: 8px; background: #373737; color: #fff; font-weight: 700; }
      #${ROOT_ID} button.ta-b-primary { border-color: #deb85e; background: #a87924; }
      #${ROOT_ID} button:disabled { opacity: .45; }
      #${ROOT_ID} .ta-b-status { min-height: 24px; font-weight: 700; }
      #${ROOT_ID} .ta-b-ok { color: #72db92; }
      #${ROOT_ID} .ta-b-fail { color: #ff8b82; }
      #${ROOT_ID} pre { max-height: 340px; overflow: auto; padding: 12px; border: 1px solid #444; border-radius: 8px; background: #0c0c0c; color: #ddd; white-space: pre-wrap; overflow-wrap: anywhere; }
    `;
    document.head.appendChild(style);
  }

  function mount() {
    if (document.getElementById(ROOT_ID)) return;
    installStyle();
    const root = document.createElement('div');
    root.id = ROOT_ID;
    root.innerHTML = `
      <section class="ta-b-card" role="dialog" aria-modal="true" aria-labelledby="ta-b-title">
        <h2 id="ta-b-title">Independent Upper-Boundary Probe v${PROBE_VERSION}</h2>
        <p class="ta-b-safe">Read-only and temporary: two GET requests only—one account check and one two-second boundary window. It does not open, change, repair, or store Torn Analytics history.</p>
        <p>Select the same readable-history JSON used for the fresh API export. The probe checks every record at its final timestamp using a range extended one second beyond the original endpoint.</p>
        <label>History export<input id="ta-b-file" type="file" accept="application/json,.json"></label>
        ${injectedKey ? '' : '<label>Session-only Torn API key<input id="ta-b-key" type="password" autocomplete="off" autocapitalize="off" spellcheck="false"></label>'}
        <div class="ta-b-actions">
          <button id="ta-b-run" class="ta-b-primary" disabled>Run read-only boundary probe</button>
          <button id="ta-b-close">Close</button>
        </div>
        <p id="ta-b-status" class="ta-b-status">Choose the history export.</p>
        <pre id="ta-b-output" hidden></pre>
      </section>`;
    document.body.appendChild(root);

    const fileInput = root.querySelector('#ta-b-file');
    const keyInput = root.querySelector('#ta-b-key');
    const run = root.querySelector('#ta-b-run');
    const close = root.querySelector('#ta-b-close');
    const status = root.querySelector('#ta-b-status');
    const output = root.querySelector('#ta-b-output');

    fileInput.addEventListener('change', async () => {
      selectedPayload = null;
      run.disabled = true;
      output.hidden = true;
      const file = fileInput.files?.[0];
      if (!file) return;
      status.className = 'ta-b-status';
      status.textContent = 'Validating the complete history digest and final timestamp…';
      try {
        selectedPayload = JSON.parse(await file.text());
        const source = await validateHistoryExport(selectedPayload);
        status.className = 'ta-b-status ta-b-ok';
        status.textContent = `Validated account ${source.accountId}; ${source.finalRecords.length} record(s) at ${new Date(source.last * 1000).toISOString()}.`;
        run.disabled = false;
      } catch (error) {
        selectedPayload = null;
        status.className = 'ta-b-status ta-b-fail';
        status.textContent = `History validation failed: ${error.message}`;
      }
    });

    run.addEventListener('click', async () => {
      const key = String(injectedKey || keyInput?.value || '').trim();
      if (!selectedPayload || !key) {
        status.className = 'ta-b-status ta-b-fail';
        status.textContent = 'Choose a valid history export and provide the session-only API key.';
        return;
      }
      run.disabled = true;
      output.hidden = true;
      status.className = 'ta-b-status';
      status.textContent = 'Running the two read-only GET requests…';
      try {
        const result = await runBoundaryProbe(selectedPayload, key, {
          onRequest(count) { status.textContent = `Read-only API request ${count} of 2…`; }
        });
        status.className = `ta-b-status ${result.outcome === 'CONFIRMED' ? 'ta-b-ok' : 'ta-b-fail'}`;
        status.textContent = `Outcome: ${result.outcome}`;
        output.textContent = JSON.stringify(result, null, 2);
        output.hidden = false;
      } catch (error) {
        status.className = 'ta-b-status ta-b-fail';
        status.textContent = `Probe stopped safely: ${error.message}`;
      } finally {
        if (keyInput) keyInput.value = '';
        run.disabled = false;
      }
    });

    close.addEventListener('click', () => {
      if (keyInput) keyInput.value = '';
      selectedPayload = null;
      root.remove();
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', mount, { once: true });
  } else {
    mount();
  }
})();
