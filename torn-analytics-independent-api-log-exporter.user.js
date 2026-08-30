// ==UserScript==
// @name         Torn Analytics — Independent API Log Exporter
// @namespace    chatgpt.openai.com/torn-tools
// @version      1.0.0
// @description  One-time, read-only export of fresh Torn API logs over an existing Torn Analytics history coverage period.
// @author       Personal use
// @match        https://www.torn.com/*
// @match        https://torn.com/*
// @grant        GM_xmlhttpRequest
// @connect      api.torn.com
// @run-at       document-idle
// ==/UserScript==

(() => {
  'use strict';

  const EXPORTER_VERSION = '1.0.0';
  const HISTORY_FORMAT = 'torn-analytics-readable-history';
  const HISTORY_VERSION = 2;
  const HISTORY_RAW_FORMAT = 'torn-api-v2-user-log-record-v1';
  const API_EXPORT_FORMAT = 'torn-independent-api-log-export';
  const API_EXPORT_VERSION = 1;
  const API_ORIGIN = 'https://api.torn.com';
  const PAGE_LIMIT = 100;
  const SPLIT_THRESHOLD = 90;
  const REQUEST_GAP_MS = 850;
  const REQUEST_TIMEOUT_MS = 30000;
  const REQUEST_LIMIT = 2000;
  const API_KEY_MARKER = '###PDA-APIKEY###';
  const injectedKey = API_KEY_MARKER.includes('PDA-APIKEY')
    ? ''
    : API_KEY_MARKER.trim();

  class ExporterError extends Error {
    constructor(message, diagnostic = null) {
      super(message);
      this.name = 'ExporterError';
      this.diagnostic = diagnostic;
    }
  }

  function canonicalId(value) {
    if (typeof value !== 'string' && typeof value !== 'number') return null;
    if (typeof value === 'number' && !Number.isSafeInteger(value)) return null;
    const raw = String(value);
    const trimmed = raw.trim();
    return trimmed && raw === trimmed ? trimmed : null;
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
      throw new ExporterError('SHA-256 is unavailable in this browser.');
    }
    const digest = await crypto.subtle.digest(
      'SHA-256',
      new TextEncoder().encode(String(text))
    );
    return Array.from(new Uint8Array(digest), byte =>
      byte.toString(16).padStart(2, '0')
    ).join('');
  }

  function positiveSafeInteger(value, label) {
    const number = Number(value);
    if (!Number.isSafeInteger(number) || number <= 0) {
      throw new ExporterError(`${label} must be a positive integer.`);
    }
    return number;
  }

  function nonnegativeSafeInteger(value, label) {
    const number = Number(value);
    if (!Number.isSafeInteger(number) || number < 0) {
      throw new ExporterError(`${label} must be a non-negative integer.`);
    }
    return number;
  }

  function extractHistoryRaw(record) {
    if (!record || typeof record !== 'object' || Array.isArray(record)) {
      throw new ExporterError('The history export contains a malformed record.');
    }
    const id = canonicalId(record.id);
    const timestamp = nonnegativeSafeInteger(record.timestamp, 'History record timestamp');
    const archive = record._archive;
    const raw = archive?.raw;
    if (
      !id ||
      !archive ||
      archive.format !== HISTORY_RAW_FORMAT ||
      !raw ||
      typeof raw !== 'object' ||
      Array.isArray(raw) ||
      canonicalId(raw.id) !== id ||
      nonnegativeSafeInteger(raw.timestamp, 'Archived raw timestamp') !== timestamp
    ) {
      throw new ExporterError(
        `History record ${id || '(unknown)'} does not have a valid lossless raw binding.`
      );
    }
    return { id, timestamp };
  }

  async function validateHistoryExport(payload) {
    if (!payload || typeof payload !== 'object' || Array.isArray(payload)) {
      throw new ExporterError('The selected file is not a JSON export object.');
    }
    if (payload.format !== HISTORY_FORMAT || Number(payload.format_version) !== HISTORY_VERSION) {
      throw new ExporterError('This is not a supported Torn Analytics readable-history export.');
    }
    const accountId = positiveSafeInteger(payload.account?.id, 'History account ID');
    const accountName = String(payload.account?.name || '').trim();
    const first = positiveSafeInteger(payload.coverage?.first_timestamp, 'Coverage start');
    const last = nonnegativeSafeInteger(payload.coverage?.last_timestamp, 'Coverage end');
    if (last < first) throw new ExporterError('The history coverage bounds are reversed.');
    if (!Array.isArray(payload.records) || payload.records.length === 0) {
      throw new ExporterError('The history export contains no records.');
    }
    if (Number(payload.coverage?.record_count) !== payload.records.length) {
      throw new ExporterError('The history record count does not match its coverage metadata.');
    }
    if (
      payload.archive_provenance?.raw_record_format !== HISTORY_RAW_FORMAT ||
      Number(payload.archive_provenance?.raw_record_count) !== payload.records.length ||
      Number(payload.archive_provenance?.legacy_normalized_count) !== 0 ||
      payload.archive_provenance?.lossless_raw_complete !== true
    ) {
      throw new ExporterError('The selected history is not a complete lossless raw archive.');
    }
    const integrity = payload.integrity;
    if (
      integrity?.algorithm !== 'SHA-256' ||
      integrity?.canonicalization !== 'stable-json-v1' ||
      integrity?.scope !== 'all top-level fields except integrity' ||
      !/^[a-f0-9]{64}$/.test(String(integrity?.digest || ''))
    ) {
      throw new ExporterError('The history integrity declaration is missing or unsupported.');
    }
    const unsigned = { ...payload };
    delete unsigned.integrity;
    const computedDigest = await sha256Hex(stableJson(unsigned));
    if (computedDigest !== integrity.digest) {
      throw new ExporterError('The history SHA-256 integrity digest does not match.');
    }
    const identities = new Set();
    let previousTimestamp = -1;
    let previousId = '';
    for (const record of payload.records) {
      const item = extractHistoryRaw(record);
      if (identities.has(item.id)) {
        throw new ExporterError(`Duplicate history log identity ${item.id}.`);
      }
      if (
        item.timestamp < previousTimestamp ||
        (item.timestamp === previousTimestamp && item.id.localeCompare(previousId) < 0)
      ) {
        throw new ExporterError('History records are not in canonical timestamp and ID order.');
      }
      identities.add(item.id);
      previousTimestamp = item.timestamp;
      previousId = item.id;
    }
    if (
      Number(payload.records[0].timestamp) !== first ||
      Number(payload.records.at(-1).timestamp) !== last
    ) {
      throw new ExporterError('Coverage endpoints do not match the first and last history records.');
    }
    return {
      accountId,
      accountName,
      first,
      last,
      count: payload.records.length,
      digest: computedDigest,
      collectorVersion: String(payload.collector?.version || 'unknown'),
      exportedAt: String(payload.exported_at || '')
    };
  }

  function approvedApiUrl(url, endpoint, bounds = null) {
    let parsed;
    try {
      parsed = new URL(url);
    } catch {
      throw new ExporterError('Refusing an invalid Torn API URL.');
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
      throw new ExporterError('Refusing to send credentials to an unapproved destination.');
    }
    if (endpoint === '/v2/user/profile') {
      if ([...parsed.searchParams.keys()].length) {
        throw new ExporterError('The profile request must not include query parameters.');
      }
      return parsed.toString();
    }
    const cursorMode = bounds?.cursor === true;
    const allowed = new Set(cursorMode
      ? ['from', 'to', 'limit', 'sort', 'order']
      : ['from', 'to', 'limit']);
    if ([...parsed.searchParams.keys()].some(key => !allowed.has(key))) {
      throw new ExporterError('The log request unexpectedly changed API scope.');
    }
    const fromValues = parsed.searchParams.getAll('from');
    const toValues = parsed.searchParams.getAll('to');
    const limitValues = parsed.searchParams.getAll('limit');
    if (
      fromValues.length !== 1 ||
      toValues.length !== 1 ||
      (!cursorMode && limitValues.length !== 1) ||
      (cursorMode && limitValues.length > 1)
    ) {
      throw new ExporterError('The log request has malformed range parameters.');
    }
    const from = nonnegativeSafeInteger(fromValues[0], 'Request start');
    const to = nonnegativeSafeInteger(toValues[0], 'Request end');
    const limit = limitValues.length
      ? positiveSafeInteger(limitValues[0], 'Request limit')
      : PAGE_LIMIT;
    if (to < from || limit > PAGE_LIMIT || (!cursorMode && limit !== PAGE_LIMIT)) {
      throw new ExporterError('The log request has invalid bounds or page size.');
    }
    if (bounds && (from < bounds.from || to > bounds.to)) {
      throw new ExporterError('A pagination request escaped its assigned range.');
    }
    for (const name of ['sort', 'order']) {
      const values = parsed.searchParams.getAll(name);
      if (values.length > 1 || (values.length === 1 && values[0] && !/^(asc|desc)$/i.test(values[0]))) {
        throw new ExporterError('A pagination request used invalid ordering metadata.');
      }
    }
    return parsed.toString();
  }

  function buildLogUrl(from, to) {
    return approvedApiUrl(
      `${API_ORIGIN}/v2/user/log?from=${encodeURIComponent(from)}&to=${encodeURIComponent(to)}&limit=${PAGE_LIMIT}`,
      '/v2/user/log',
      { from, to, cursor: false }
    );
  }

  function apiError(json) {
    if (!json?.error) return null;
    if (typeof json.error === 'string') return json.error;
    return `Torn API error ${json.error.code ?? '?'}: ${json.error.error ?? json.error.message ?? 'Unknown error'}`;
  }

  function createTransport(apiKey, hooks = {}) {
    const state = { requests: 0, lastStartedAt: 0, cancelled: false };
    const sleep = hooks.sleep || (ms => new Promise(resolve => setTimeout(resolve, ms)));
    const requestImpl = hooks.request || (options => new Promise((resolve, reject) => {
      if (typeof GM_xmlhttpRequest !== 'function') {
        reject(new ExporterError('Secure userscript transport is unavailable.'));
        return;
      }
      GM_xmlhttpRequest({
        ...options,
        onload: resolve,
        onerror: () => reject(new ExporterError('The Torn API network request failed.')),
        ontimeout: () => reject(new ExporterError('The Torn API network request timed out.'))
      });
    }));

    async function getJson(url, endpoint, bounds = null) {
      if (state.cancelled) throw new ExporterError('The API export was cancelled.');
      if (!apiKey) throw new ExporterError('A Torn API key is required.');
      if (state.requests >= REQUEST_LIMIT) {
        throw new ExporterError(`Stopped at the ${REQUEST_LIMIT}-request safety limit.`);
      }
      const safeUrl = approvedApiUrl(url, endpoint, bounds);
      const elapsed = Date.now() - state.lastStartedAt;
      if (elapsed < REQUEST_GAP_MS) await sleep(REQUEST_GAP_MS - elapsed);
      if (state.cancelled) throw new ExporterError('The API export was cancelled.');
      state.lastStartedAt = Date.now();
      state.requests += 1;
      hooks.onRequest?.(state.requests, safeUrl);
      const response = await requestImpl({
        method: 'GET',
        url: safeUrl,
        headers: { Authorization: `ApiKey ${apiKey}`, Accept: 'application/json' },
        timeout: REQUEST_TIMEOUT_MS,
        anonymous: true
      });
      if (Number(response?.status) < 200 || Number(response?.status) >= 300) {
        throw new ExporterError(`Torn API returned HTTP ${response?.status ?? 'unknown'}.`);
      }
      let json;
      try {
        json = JSON.parse(response.responseText);
      } catch {
        throw new ExporterError('Torn API returned invalid JSON.');
      }
      const error = apiError(json);
      if (error) throw new ExporterError(error);
      return json;
    }

    return {
      state,
      getJson,
      cancel() { state.cancelled = true; }
    };
  }

  function normalizeApiPage(json, from, to) {
    if (!Array.isArray(json?.log)) {
      throw new ExporterError('Torn API returned an invalid log page.');
    }
    const records = [];
    const boundaryRecords = [];
    const seen = new Set();
    const responseCount = json.log.length;
    let boundaryOverlapCount = 0;
    for (const raw of json.log) {
      if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
        throw new ExporterError('Torn API returned a malformed log record.');
      }
      const id = canonicalId(raw.id);
      const timestamp = nonnegativeSafeInteger(raw.timestamp, 'API record timestamp');
      if (!id) throw new ExporterError('Torn API returned a log with an invalid identity.');
      if (timestamp < from || timestamp > to) {
        throw new ExporterError(
          `Torn API returned log ${id} outside the requested range.`,
          {
            range_from: from,
            range_to: to,
            offending_log_id: id,
            offending_timestamp: timestamp
          }
        );
      }
      if (seen.has(id)) {
        throw new ExporterError(`Torn API duplicated log identity ${id} within one page.`);
      }
      seen.add(id);
      const prepared = {
        id,
        timestamp,
        raw,
        canonical: stableJson(raw)
      };
      if (timestamp === from) {
        boundaryOverlapCount += 1;
        boundaryRecords.push(prepared);
      } else {
        records.push(prepared);
      }
    }
    const links = json?._metadata?.links;
    if (!links || !Object.prototype.hasOwnProperty.call(links, 'prev') || !Object.prototype.hasOwnProperty.call(links, 'next')) {
      throw new ExporterError('Torn API omitted required pagination metadata.');
    }
    if (links.prev !== null && typeof links.prev !== 'string') {
      throw new ExporterError('Torn API returned invalid previous-page metadata.');
    }
    if (links.next !== null && typeof links.next !== 'string') {
      throw new ExporterError('Torn API returned invalid next-page metadata.');
    }
    return {
      records,
      boundaryRecords,
      responseCount,
      boundaryOverlapCount,
      prev: links.prev,
      next: links.next
    };
  }

  function mergeUnique(target, incoming) {
    for (const record of incoming) {
      const existing = target.get(record.id);
      if (existing && existing.canonical !== record.canonical) {
        throw new ExporterError(`Torn API returned conflicting payloads for log ${record.id}.`);
      }
      target.set(record.id, record);
    }
  }

  function assertParentSurvives(parentRecords, childRecords) {
    for (const record of parentRecords) {
      const child = childRecords.get(record.id);
      if (!child || child.canonical !== record.canonical) {
        throw new ExporterError(
          `Independent child ranges did not reproduce parent-page log ${record.id}.`
        );
      }
    }
  }

  function pageCollection(page) {
    return {
      records: new Map(page.records.map(record => [record.id, record])),
      fromBoundary: new Map(page.boundaryRecords.map(record => [record.id, record]))
    };
  }

  async function collectSingleSecondDetailed(from, to, firstPage, transport, progress) {
    const collected = pageCollection(firstPage);
    let cursor = firstPage.prev;
    const visited = new Set();
    if (!cursor && firstPage.responseCount >= PAGE_LIMIT) {
      throw new ExporterError('A full one-second API page had no older-page continuation link.');
    }
    while (cursor) {
      const safeCursor = approvedApiUrl(cursor, '/v2/user/log', { from, to, cursor: true });
      if (visited.has(safeCursor)) {
        throw new ExporterError('Torn API repeated a one-second pagination cursor.');
      }
      visited.add(safeCursor);
      const json = await transport.getJson(safeCursor, '/v2/user/log', { from, to, cursor: true });
      const page = normalizeApiPage(json, from, to);
      mergeUnique(collected.records, page.records);
      mergeUnique(collected.fromBoundary, page.boundaryRecords);
      if (page.responseCount >= PAGE_LIMIT && page.prev === null) {
        throw new ExporterError('A full terminal one-second page had no older-page continuation link.');
      }
      cursor = page.prev;
      progress?.({ from, to, accepted: collected.records.size, mode: 'one-second pagination' });
    }
    return collected;
  }

  async function collectRangeDetailed(from, to, transport, progress, depth = 0) {
    if (depth > 32 || to <= from) {
      throw new ExporterError('The independent timestamp split reached an invalid depth or range.');
    }
    try {
      const json = await transport.getJson(buildLogUrl(from, to), '/v2/user/log', { from, to });
      const page = normalizeApiPage(json, from, to);
      const width = to - from;
      const mustSplit = width > 1 && (
        page.responseCount >= SPLIT_THRESHOLD ||
        page.prev !== null
      );
      if (!mustSplit) {
        if (width === 1 && (page.prev !== null || page.responseCount >= PAGE_LIMIT)) {
          return await collectSingleSecondDetailed(from, to, page, transport, progress);
        }
        if (page.prev !== null || (width > 1 && page.responseCount >= SPLIT_THRESHOLD)) {
          throw new ExporterError('An unsplit API range remained saturated or paginated.');
        }
        const accepted = pageCollection(page);
        progress?.({ from, to, accepted: accepted.records.size, mode: 'terminal range' });
        return accepted;
      }
      const midpoint = from + Math.floor(width / 2);
      if (midpoint <= from || midpoint >= to) {
        throw new ExporterError('The API range could not be divided safely.');
      }
      progress?.({ from, to, accepted: 0, mode: 'splitting dense range' });
      const left = await collectRangeDetailed(from, midpoint, transport, progress, depth + 1);
      const right = await collectRangeDetailed(midpoint, to, transport, progress, depth + 1);
      const mergedRecords = new Map(left.records);
      mergeUnique(mergedRecords, right.records.values());
      mergeUnique(mergedRecords, right.fromBoundary.values());
      assertParentSurvives(page.records, mergedRecords);
      const parentBoundary = new Map(left.fromBoundary);
      mergeUnique(parentBoundary, page.boundaryRecords);
      return { records: mergedRecords, fromBoundary: parentBoundary };
    } catch (error) {
      if (error instanceof ExporterError) {
        error.diagnostic = {
          range_from: from,
          range_to: to,
          range_from_iso: new Date(from * 1000).toISOString(),
          range_to_iso: new Date(to * 1000).toISOString(),
          split_depth: depth,
          ...(error.diagnostic || {})
        };
        throw error;
      }
      throw new ExporterError(String(error?.message || error));
    }
  }

  async function collectRange(from, to, transport, progress) {
    const collected = await collectRangeDetailed(from, to, transport, progress, 0);
    return collected.records;
  }

  async function confirmAccount(transport, expectedAccountId) {
    const json = await transport.getJson(
      approvedApiUrl(`${API_ORIGIN}/v2/user/profile`, '/v2/user/profile'),
      '/v2/user/profile'
    );
    const actualId = positiveSafeInteger(json?.profile?.id, 'Authenticated Torn account ID');
    if (actualId !== expectedAccountId) {
      throw new ExporterError(
        `API key account ${actualId} does not match history account ${expectedAccountId}.`
      );
    }
    return { id: actualId, name: String(json?.profile?.name || '').trim() };
  }

  function orderedRawRecords(records) {
    return [...records.values()]
      .sort((a, b) => a.timestamp - b.timestamp || a.id.localeCompare(b.id))
      .map(record => record.raw);
  }

  async function buildFreshApiExport({ source, account, records, requests, startedAt, finishedAt }) {
    const rawRecords = orderedRawRecords(records);
    const payload = {
      format: API_EXPORT_FORMAT,
      format_version: API_EXPORT_VERSION,
      exporter: {
        name: 'Torn Analytics Independent API Log Exporter',
        version: EXPORTER_VERSION
      },
      generated_at: finishedAt,
      account: { id: account.id, name: account.name || source.accountName },
      source_history: {
        integrity_sha256: source.digest,
        collector_version: source.collectorVersion,
        exported_at: source.exportedAt,
        record_count: source.count
      },
      coverage: {
        semantics: '(from, to]',
        request_from: source.first - 1,
        first_timestamp: source.first,
        last_timestamp: source.last,
        record_count: rawRecords.length
      },
      collection: {
        started_at: startedAt,
        finished_at: finishedAt,
        api_requests: requests,
        complete: true,
        strategy: 'Recursive timestamp bisection with exact-from quarantine, internal midpoint promotion, parent-child reproduction checks, and fail-closed saturation handling'
      },
      raw_record_format: HISTORY_RAW_FORMAT,
      records: rawRecords
    };
    const digest = await sha256Hex(stableJson(payload));
    return {
      ...payload,
      integrity: {
        algorithm: 'SHA-256',
        canonicalization: 'stable-json-v1',
        scope: 'all top-level fields except integrity',
        digest
      }
    };
  }

  async function validateFreshApiExport(payload) {
    if (
      !payload ||
      payload.format !== API_EXPORT_FORMAT ||
      Number(payload.format_version) !== API_EXPORT_VERSION ||
      payload.collection?.complete !== true ||
      payload.raw_record_format !== HISTORY_RAW_FORMAT ||
      !Array.isArray(payload.records) ||
      Number(payload.coverage?.record_count) !== payload.records.length
    ) {
      throw new ExporterError('The prepared fresh API export is incomplete or malformed.');
    }
    const accountId = positiveSafeInteger(payload.account?.id, 'API export account ID');
    const identities = new Set();
    let previousTimestamp = -1;
    let previousId = '';
    for (const raw of payload.records) {
      if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
        throw new ExporterError('The prepared fresh API export contains a malformed record.');
      }
      const id = canonicalId(raw.id);
      const timestamp = nonnegativeSafeInteger(raw.timestamp, 'Fresh API record timestamp');
      if (!id || identities.has(id)) {
        throw new ExporterError('The prepared fresh API export contains an invalid or duplicate identity.');
      }
      if (
        timestamp < previousTimestamp ||
        (timestamp === previousTimestamp && id.localeCompare(previousId) < 0)
      ) {
        throw new ExporterError('Fresh API records are not in canonical timestamp and ID order.');
      }
      identities.add(id);
      previousTimestamp = timestamp;
      previousId = id;
    }
    const integrity = payload.integrity;
    if (
      integrity?.algorithm !== 'SHA-256' ||
      integrity?.canonicalization !== 'stable-json-v1' ||
      integrity?.scope !== 'all top-level fields except integrity' ||
      !/^[a-f0-9]{64}$/.test(String(integrity?.digest || ''))
    ) {
      throw new ExporterError('The fresh API export integrity declaration is invalid.');
    }
    const unsigned = { ...payload };
    delete unsigned.integrity;
    const digest = await sha256Hex(stableJson(unsigned));
    if (digest !== integrity.digest) {
      throw new ExporterError('The fresh API export integrity digest does not match.');
    }
    return { accountId, count: payload.records.length, digest };
  }

  async function runApiExport(historyPayload, apiKey, hooks = {}) {
    const startedAt = new Date().toISOString();
    const source = await validateHistoryExport(historyPayload);
    const transport = createTransport(apiKey, hooks);
    hooks.onTransport?.(transport);
    const account = await confirmAccount(transport, source.accountId);
    const records = await collectRange(source.first - 1, source.last, transport, hooks.onProgress);
    const finishedAt = new Date().toISOString();
    const payload = await buildFreshApiExport({
      source,
      account,
      records,
      requests: transport.state.requests,
      startedAt,
      finishedAt
    });
    await validateFreshApiExport(payload);
    return { payload, transport };
  }

  function filenameForApiExport(payload) {
    const day = new Date(payload.generated_at).toISOString().slice(0, 10);
    return `TornAnalytics-${payload.account.id}-fresh-api-${day}.json`;
  }

  function triggerJsonDownload(text, filename, hooks = {}) {
    if (typeof text !== 'string' || !text.length || !/^[A-Za-z0-9._-]+\.json$/.test(filename)) {
      throw new ExporterError('Refusing an invalid JSON download.');
    }
    const BlobImpl = hooks.Blob || globalThis.Blob;
    const urlApi = hooks.URL || globalThis.URL;
    const doc = hooks.document || globalThis.document;
    const defer = hooks.setTimeout || globalThis.setTimeout;
    if (
      typeof BlobImpl !== 'function' ||
      typeof urlApi?.createObjectURL !== 'function' ||
      typeof urlApi?.revokeObjectURL !== 'function' ||
      typeof doc?.createElement !== 'function'
    ) {
      throw new ExporterError('This browser cannot create a normal JSON download.');
    }
    const blob = new BlobImpl([text], { type: 'application/json;charset=utf-8' });
    const objectUrl = urlApi.createObjectURL(blob);
    const anchor = doc.createElement('a');
    anchor.href = objectUrl;
    anchor.download = filename;
    anchor.rel = 'noopener';
    anchor.style.display = 'none';
    try {
      anchor.click();
    } finally {
      anchor.remove?.();
      defer(() => urlApi.revokeObjectURL(objectUrl), 1000);
    }
    return { filename, bytes: new TextEncoder().encode(text).byteLength };
  }

  function triggerPreflightDownload(hooks = {}) {
    const payload = {
      test: 'torn-independent-api-log-export-download',
      exporter_version: EXPORTER_VERSION,
      created_at: new Date().toISOString(),
      message: 'If this file is in Downloads, the full fresh API export can be saved normally.'
    };
    return triggerJsonDownload(
      JSON.stringify(payload, null, 2),
      `TornAnalytics-download-test-${new Date().toISOString().slice(0, 10)}.json`,
      hooks
    );
  }

  const testApi = {
    ExporterError,
    stableJson,
    sha256Hex,
    validateHistoryExport,
    approvedApiUrl,
    buildLogUrl,
    createTransport,
    normalizeApiPage,
    collectRange,
    collectRangeDetailed,
    buildFreshApiExport,
    validateFreshApiExport,
    runApiExport,
    filenameForApiExport,
    triggerJsonDownload,
    triggerPreflightDownload,
    constants: {
      HISTORY_FORMAT,
      HISTORY_VERSION,
      API_EXPORT_FORMAT,
      API_EXPORT_VERSION,
      PAGE_LIMIT,
      SPLIT_THRESHOLD,
      REQUEST_LIMIT
    }
  };
  if (globalThis.__TA_API_EXPORTER_TEST_HOOK__) {
    globalThis.__TA_API_EXPORTER_TEST_EXPORTS__ = testApi;
    return;
  }

  const STYLE_ID = 'ta-independent-api-exporter-style';
  const ROOT_ID = 'ta-independent-api-exporter-root';
  let selectedPayload = null;
  let selectedSource = null;
  let activeTransport = null;
  let preparedExport = null;
  let preflightConfirmed = false;

  function installStyle() {
    if (document.getElementById(STYLE_ID)) return;
    const style = document.createElement('style');
    style.id = STYLE_ID;
    style.textContent = `
      #${ROOT_ID}, #${ROOT_ID} * { box-sizing: border-box; }
      #${ROOT_ID} { position: fixed; inset: 0; z-index: 2147483647; background: rgba(0,0,0,.78); color: #eee; font: 15px/1.4 Arial,sans-serif; display: flex; align-items: center; justify-content: center; padding: 16px; }
      #${ROOT_ID} .ta-e-card { width: min(760px,100%); max-height: 92vh; overflow: auto; background: #191919; border: 1px solid #555; border-radius: 14px; padding: 18px; box-shadow: 0 20px 60px #000; }
      #${ROOT_ID} h2 { margin: 0 0 8px; font-size: 22px; color: #fff; }
      #${ROOT_ID} p { margin: 8px 0; }
      #${ROOT_ID} .ta-e-note { color: #c8c8c8; }
      #${ROOT_ID} .ta-e-safe { border-left: 4px solid #d5a84e; background: #211d16; padding: 10px 12px; border-radius: 6px; }
      #${ROOT_ID} label { display: block; margin-top: 14px; font-weight: 700; color: #fff; }
      #${ROOT_ID} input[type=file], #${ROOT_ID} input[type=password] { width: 100%; margin-top: 6px; padding: 12px; border-radius: 8px; border: 1px solid #666; background: #101010; color: #fff; }
      #${ROOT_ID} .ta-e-confirm { display: flex; align-items: flex-start; gap: 10px; padding: 10px 0; font-weight: 600; }
      #${ROOT_ID} .ta-e-confirm input { width: 22px; height: 22px; margin: 0; flex: 0 0 auto; }
      #${ROOT_ID} .ta-e-actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 16px; }
      #${ROOT_ID} button { min-height: 44px; padding: 10px 16px; border-radius: 8px; border: 1px solid #777; background: #373737; color: #fff; font-weight: 700; }
      #${ROOT_ID} button.ta-e-primary { background: #a87924; border-color: #deb85e; color: #fff; }
      #${ROOT_ID} button:disabled { opacity: .45; }
      #${ROOT_ID} .ta-e-status { font-weight: 700; min-height: 24px; }
      #${ROOT_ID} .ta-e-ok { color: #72db92; }
      #${ROOT_ID} .ta-e-fail { color: #ff8b82; }
      #${ROOT_ID} pre { white-space: pre-wrap; overflow-wrap: anywhere; background: #0c0c0c; border: 1px solid #444; border-radius: 8px; padding: 12px; max-height: 200px; overflow: auto; color: #ddd; }
    `;
    document.head.appendChild(style);
  }

  function refreshRunState(runButton) {
    runButton.disabled = !selectedPayload || !selectedSource || !preflightConfirmed || Boolean(activeTransport);
  }

  function mount() {
    if (document.getElementById(ROOT_ID)) return;
    installStyle();
    const root = document.createElement('div');
    root.id = ROOT_ID;
    root.innerHTML = `
      <section class="ta-e-card" role="dialog" aria-modal="true" aria-labelledby="ta-e-title">
        <h2 id="ta-e-title">Independent API Log Exporter v${EXPORTER_VERSION}</h2>
        <p class="ta-e-safe">Read-only: this temporary tool makes GET requests only and creates a fresh JSON download. It does not compare, repair, open, change, or store Torn Analytics history.</p>
        <p class="ta-e-note">First test that a normal JSON download reaches Downloads. Then choose the readable-history export so the fresh API scan uses the exact same account and coverage.</p>
        <div class="ta-e-actions">
          <button id="ta-e-test-download">1. Test JSON download</button>
        </div>
        <label class="ta-e-confirm"><input id="ta-e-test-confirm" type="checkbox">I found the test JSON in Downloads</label>
        <label>History export<input id="ta-e-file" type="file" accept="application/json,.json"></label>
        ${injectedKey ? '' : '<label>Session-only Torn API key<input id="ta-e-key" type="password" autocomplete="off" autocapitalize="off" spellcheck="false"></label>'}
        <div class="ta-e-actions">
          <button id="ta-e-run" class="ta-e-primary" disabled>2. Collect fresh API logs</button>
          <button id="ta-e-cancel" disabled>Cancel</button>
          <button id="ta-e-download" disabled>3. Download fresh API JSON</button>
          <button id="ta-e-close">Close</button>
        </div>
        <p id="ta-e-status" class="ta-e-status">Run the tiny download test first.</p>
        <pre id="ta-e-output" hidden></pre>
      </section>`;
    document.body.appendChild(root);

    const testDownload = root.querySelector('#ta-e-test-download');
    const testConfirm = root.querySelector('#ta-e-test-confirm');
    const fileInput = root.querySelector('#ta-e-file');
    const keyInput = root.querySelector('#ta-e-key');
    const run = root.querySelector('#ta-e-run');
    const cancel = root.querySelector('#ta-e-cancel');
    const download = root.querySelector('#ta-e-download');
    const close = root.querySelector('#ta-e-close');
    const status = root.querySelector('#ta-e-status');
    const output = root.querySelector('#ta-e-output');

    testDownload.addEventListener('click', () => {
      try {
        const receipt = triggerPreflightDownload();
        status.className = 'ta-e-status';
        status.textContent = `Download requested: ${receipt.filename}. Confirm it exists before continuing.`;
      } catch (error) {
        status.className = 'ta-e-status ta-e-fail';
        status.textContent = `Test download failed: ${error.message}`;
      }
    });

    testConfirm.addEventListener('change', () => {
      preflightConfirmed = testConfirm.checked;
      refreshRunState(run);
      if (preflightConfirmed) {
        status.className = 'ta-e-status ta-e-ok';
        status.textContent = 'Download path confirmed. Choose and validate the history export.';
      }
    });

    fileInput.addEventListener('change', async () => {
      selectedPayload = null;
      selectedSource = null;
      preparedExport = null;
      download.disabled = true;
      output.hidden = true;
      const file = fileInput.files?.[0];
      if (!file) {
        status.textContent = 'Choose the Torn Analytics readable-history JSON.';
        refreshRunState(run);
        return;
      }
      status.className = 'ta-e-status';
      status.textContent = 'Reading and validating the history export…';
      try {
        selectedPayload = JSON.parse(await file.text());
        selectedSource = await validateHistoryExport(selectedPayload);
        status.className = 'ta-e-status ta-e-ok';
        status.textContent = `Validated ${selectedSource.count.toLocaleString()} history records for account ${selectedSource.accountId}.`;
      } catch (error) {
        selectedPayload = null;
        selectedSource = null;
        status.className = 'ta-e-status ta-e-fail';
        status.textContent = `History validation failed: ${error.message}`;
      }
      refreshRunState(run);
    });

    run.addEventListener('click', async () => {
      const key = String(injectedKey || keyInput?.value || '').trim();
      if (!selectedPayload || !selectedSource || !preflightConfirmed || !key) {
        status.className = 'ta-e-status ta-e-fail';
        status.textContent = 'Confirm the test download, choose a valid history export, and provide the session-only API key.';
        return;
      }
      run.disabled = true;
      cancel.disabled = false;
      download.disabled = true;
      preparedExport = null;
      output.hidden = true;
      status.className = 'ta-e-status';
      status.textContent = 'Confirming the API key account…';
      try {
        const result = await runApiExport(selectedPayload, key, {
          onTransport(transport) { activeTransport = transport; },
          onRequest(count) { status.textContent = `Read-only API request ${count.toLocaleString()}…`; },
          onProgress(info) {
            status.textContent = `Request ${activeTransport?.state.requests || 0}: ${info.mode} ${new Date(info.from * 1000).toISOString()} → ${new Date(info.to * 1000).toISOString()}`;
          }
        });
        preparedExport = result.payload;
        const check = await validateFreshApiExport(preparedExport);
        status.className = 'ta-e-status ta-e-ok';
        status.textContent = `Fresh API export ready: ${check.count.toLocaleString()} records.`;
        output.textContent = [
          `Account: ${preparedExport.account.name || '(unknown)'} [${preparedExport.account.id}]`,
          `Coverage: ${new Date(preparedExport.coverage.first_timestamp * 1000).toISOString()} to ${new Date(preparedExport.coverage.last_timestamp * 1000).toISOString()}`,
          `Fresh records: ${check.count.toLocaleString()}`,
          `API requests: ${preparedExport.collection.api_requests.toLocaleString()}`,
          `SHA-256: ${check.digest}`,
          'Click Download fresh API JSON. The prepared file remains in memory until this window closes.'
        ].join('\n');
        output.hidden = false;
        download.disabled = false;
      } catch (error) {
        status.className = 'ta-e-status ta-e-fail';
        status.textContent = `API export stopped: ${error.message}`;
        output.textContent = error.diagnostic
          ? JSON.stringify(error.diagnostic, null, 2)
          : 'No export file was created because complete coverage could not be proven.';
        output.hidden = false;
      } finally {
        activeTransport = null;
        if (keyInput) keyInput.value = '';
        cancel.disabled = true;
        refreshRunState(run);
      }
    });

    cancel.addEventListener('click', () => activeTransport?.cancel());
    download.addEventListener('click', async () => {
      if (!preparedExport) return;
      try {
        const check = await validateFreshApiExport(preparedExport);
        const filename = filenameForApiExport(preparedExport);
        const receipt = triggerJsonDownload(JSON.stringify(preparedExport, null, 2), filename);
        status.className = 'ta-e-status ta-e-ok';
        status.textContent = `Download requested: ${receipt.filename} · ${check.count.toLocaleString()} records. Keep this window open until the file is visible.`;
      } catch (error) {
        status.className = 'ta-e-status ta-e-fail';
        status.textContent = `Could not download the fresh API JSON: ${error.message}`;
      }
    });
    close.addEventListener('click', () => {
      activeTransport?.cancel();
      if (keyInput) keyInput.value = '';
      selectedPayload = null;
      selectedSource = null;
      preparedExport = null;
      root.remove();
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', mount, { once: true });
  } else {
    mount();
  }
})();
