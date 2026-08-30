// ==UserScript==
// @name         Torn Analytics — Independent Log Reconciler
// @namespace    chatgpt.openai.com/torn-tools
// @version      1.0.3
// @description  One-time, read-only comparison of a Torn Analytics history export against fresh Torn API log responses.
// @author       Personal use
// @match        https://www.torn.com/*
// @match        https://torn.com/*
// @grant        GM_xmlhttpRequest
// @connect      api.torn.com
// @run-at       document-idle
// ==/UserScript==

(() => {
  'use strict';

  const VERIFIER_VERSION = '1.0.3';
  const EXPORT_FORMAT = 'torn-analytics-readable-history';
  const EXPORT_VERSION = 2;
  const RAW_FORMAT = 'torn-api-v2-user-log-record-v1';
  const API_ORIGIN = 'https://api.torn.com';
  const PAGE_LIMIT = 100;
  const SPLIT_THRESHOLD = 90;
  const REQUEST_GAP_MS = 850;
  const REQUEST_TIMEOUT_MS = 30000;
  const REQUEST_LIMIT = 2000;
  const DETAIL_LIMIT = 200;
  const API_KEY_MARKER = '###PDA-APIKEY###';
  const injectedKey = API_KEY_MARKER.includes('PDA-APIKEY')
    ? ''
    : API_KEY_MARKER.trim();

  class ReconciliationError extends Error {
    constructor(message, outcome = 'INCONCLUSIVE', diagnostic = null) {
      super(message);
      this.name = 'ReconciliationError';
      this.outcome = outcome;
      this.diagnostic = diagnostic;
    }
  }

  function safeDiagnostic(error) {
    const source = error?.diagnostic;
    if (!source || typeof source !== 'object' || Array.isArray(source)) return null;
    const output = {};
    for (const key of [
      'phase',
      'range_from',
      'range_to',
      'range_from_iso',
      'range_to_iso',
      'split_depth',
      'page_record_count',
      'logical_record_count',
      'boundary_overlap_count',
      'offending_log_id',
      'offending_timestamp',
      'offending_iso',
      'boundary_relation',
      'prev_present',
      'next_present'
    ]) {
      const value = source[key];
      if (typeof value === 'string' || typeof value === 'boolean' || Number.isSafeInteger(value)) {
        output[key] = value;
      }
    }
    return Object.keys(output).length ? output : null;
  }

  function canonicalId(value) {
    if (typeof value !== 'string' && typeof value !== 'number') return null;
    if (typeof value === 'number' && !Number.isSafeInteger(value)) return null;
    const raw = String(value);
    const trimmed = raw.trim();
    return trimmed && raw === trimmed ? trimmed : null;
  }

  function stableJson(value) {
    if (Array.isArray(value)) {
      return `[${value.map(stableJson).join(',')}]`;
    }
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
      throw new ReconciliationError('SHA-256 is unavailable in this browser.');
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
      throw new ReconciliationError(`${label} must be a positive integer.`, 'FAIL');
    }
    return number;
  }

  function nonnegativeSafeInteger(value, label) {
    const number = Number(value);
    if (!Number.isSafeInteger(number) || number < 0) {
      throw new ReconciliationError(`${label} must be a non-negative integer.`, 'FAIL');
    }
    return number;
  }

  function extractRaw(record) {
    if (!record || typeof record !== 'object' || Array.isArray(record)) {
      throw new ReconciliationError('The export contains a malformed record.', 'FAIL');
    }
    const id = canonicalId(record.id);
    const timestamp = nonnegativeSafeInteger(record.timestamp, 'Record timestamp');
    const archive = record._archive;
    const raw = archive?.raw;
    if (
      !id ||
      !archive ||
      archive.format !== RAW_FORMAT ||
      !raw ||
      typeof raw !== 'object' ||
      Array.isArray(raw) ||
      canonicalId(raw.id) !== id ||
      nonnegativeSafeInteger(raw.timestamp, 'Archived raw timestamp') !== timestamp
    ) {
      throw new ReconciliationError(
        `Record ${id || '(unknown)'} does not have a valid lossless raw binding.`,
        'FAIL'
      );
    }
    return { id, timestamp, raw };
  }

  async function validateExport(payload) {
    if (!payload || typeof payload !== 'object' || Array.isArray(payload)) {
      throw new ReconciliationError('The selected file is not a JSON export object.', 'FAIL');
    }
    if (payload.format !== EXPORT_FORMAT || Number(payload.format_version) !== EXPORT_VERSION) {
      throw new ReconciliationError('This is not a supported Torn Analytics readable-history export.', 'FAIL');
    }

    const accountId = positiveSafeInteger(payload.account?.id, 'Export account ID');
    const accountName = String(payload.account?.name || '').trim();
    const first = positiveSafeInteger(payload.coverage?.first_timestamp, 'Coverage start');
    const last = nonnegativeSafeInteger(payload.coverage?.last_timestamp, 'Coverage end');
    if (last < first) {
      throw new ReconciliationError('The export coverage bounds are reversed.', 'FAIL');
    }
    if (!Array.isArray(payload.records) || payload.records.length === 0) {
      throw new ReconciliationError('The export contains no records.', 'FAIL');
    }
    if (Number(payload.coverage?.record_count) !== payload.records.length) {
      throw new ReconciliationError('The export record count does not match its coverage metadata.', 'FAIL');
    }
    if (
      payload.archive_provenance?.raw_record_format !== RAW_FORMAT ||
      Number(payload.archive_provenance?.raw_record_count) !== payload.records.length ||
      Number(payload.archive_provenance?.legacy_normalized_count) !== 0 ||
      payload.archive_provenance?.lossless_raw_complete !== true
    ) {
      throw new ReconciliationError('The export is not a complete lossless raw archive.', 'FAIL');
    }

    const integrity = payload.integrity;
    if (
      integrity?.algorithm !== 'SHA-256' ||
      integrity?.canonicalization !== 'stable-json-v1' ||
      integrity?.scope !== 'all top-level fields except integrity' ||
      !/^[a-f0-9]{64}$/.test(String(integrity?.digest || ''))
    ) {
      throw new ReconciliationError('The export integrity declaration is missing or unsupported.', 'FAIL');
    }
    const unsigned = { ...payload };
    delete unsigned.integrity;
    const computedDigest = await sha256Hex(stableJson(unsigned));
    if (computedDigest !== integrity.digest) {
      throw new ReconciliationError('The export SHA-256 integrity digest does not match.', 'FAIL');
    }

    const records = new Map();
    let previousTimestamp = -1;
    let previousId = '';
    for (const record of payload.records) {
      const item = extractRaw(record);
      if (records.has(item.id)) {
        throw new ReconciliationError(`Duplicate exported log identity ${item.id}.`, 'FAIL');
      }
      if (
        item.timestamp < previousTimestamp ||
        (item.timestamp === previousTimestamp && item.id.localeCompare(previousId) < 0)
      ) {
        throw new ReconciliationError('Export records are not in canonical timestamp and ID order.', 'FAIL');
      }
      previousTimestamp = item.timestamp;
      previousId = item.id;
      records.set(item.id, {
        id: item.id,
        timestamp: item.timestamp,
        title: String(item.raw?.details?.title || ''),
        raw: item.raw,
        canonical: stableJson(item.raw)
      });
    }
    const ordered = [...records.values()];
    if (ordered[0].timestamp !== first || ordered.at(-1).timestamp !== last) {
      throw new ReconciliationError('Coverage endpoints do not match the first and last exported records.', 'FAIL');
    }

    return {
      accountId,
      accountName,
      first,
      last,
      count: records.size,
      digest: computedDigest,
      collectorVersion: String(payload.collector?.version || 'unknown'),
      exportedAt: String(payload.exported_at || ''),
      records
    };
  }

  function approvedApiUrl(url, endpoint, bounds = null) {
    let parsed;
    try {
      parsed = new URL(url);
    } catch {
      throw new ReconciliationError('Refusing an invalid Torn API URL.');
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
      throw new ReconciliationError('Refusing to send credentials to an unapproved destination.');
    }
    if (endpoint === '/v2/user/profile') {
      if ([...parsed.searchParams.keys()].length) {
        throw new ReconciliationError('The profile request must not include query parameters.');
      }
      return parsed.toString();
    }
    const cursorMode = bounds?.cursor === true;
    const allowed = new Set(cursorMode
      ? ['from', 'to', 'limit', 'sort', 'order']
      : ['from', 'to', 'limit']);
    if ([...parsed.searchParams.keys()].some(key => !allowed.has(key))) {
      throw new ReconciliationError('The log request unexpectedly changed API scope.');
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
      throw new ReconciliationError('The log request has malformed range parameters.');
    }
    const from = nonnegativeSafeInteger(fromValues[0], 'Request start');
    const to = nonnegativeSafeInteger(toValues[0], 'Request end');
    const limit = limitValues.length
      ? positiveSafeInteger(limitValues[0], 'Request limit')
      : PAGE_LIMIT;
    if (to < from || limit > PAGE_LIMIT || (!cursorMode && limit !== PAGE_LIMIT)) {
      throw new ReconciliationError('The log request has invalid bounds or page size.');
    }
    if (bounds && (from < bounds.from || to > bounds.to)) {
      throw new ReconciliationError('A pagination request escaped its assigned range.');
    }
    for (const name of ['sort', 'order']) {
      const values = parsed.searchParams.getAll(name);
      if (values.length > 1 || (values.length === 1 && values[0] && !/^(asc|desc)$/i.test(values[0]))) {
        throw new ReconciliationError('A pagination request used invalid ordering metadata.');
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
        reject(new ReconciliationError('Secure userscript transport is unavailable.'));
        return;
      }
      GM_xmlhttpRequest({
        ...options,
        onload: resolve,
        onerror: () => reject(new ReconciliationError('The Torn API network request failed.')),
        ontimeout: () => reject(new ReconciliationError('The Torn API network request timed out.'))
      });
    }));

    async function getJson(url, endpoint, bounds = null) {
      if (state.cancelled) throw new ReconciliationError('Reconciliation was cancelled.');
      if (!apiKey) throw new ReconciliationError('A Torn API key is required.');
      if (state.requests >= REQUEST_LIMIT) {
        throw new ReconciliationError(`Stopped at the ${REQUEST_LIMIT}-request safety limit.`);
      }
      const safeUrl = approvedApiUrl(url, endpoint, bounds);
      const elapsed = Date.now() - state.lastStartedAt;
      if (elapsed < REQUEST_GAP_MS) await sleep(REQUEST_GAP_MS - elapsed);
      if (state.cancelled) throw new ReconciliationError('Reconciliation was cancelled.');
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
        throw new ReconciliationError(`Torn API returned HTTP ${response?.status ?? 'unknown'}.`);
      }
      let json;
      try {
        json = JSON.parse(response.responseText);
      } catch {
        throw new ReconciliationError('Torn API returned invalid JSON.');
      }
      const error = apiError(json);
      if (error) throw new ReconciliationError(error);
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
      throw new ReconciliationError('Torn API returned an invalid log page.');
    }
    const records = [];
    const boundaryRecords = [];
    const seen = new Set();
    const responseCount = json.log.length;
    let boundaryOverlapCount = 0;
    for (const raw of json.log) {
      if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
        throw new ReconciliationError('Torn API returned a malformed log record.');
      }
      const id = canonicalId(raw.id);
      const timestamp = nonnegativeSafeInteger(raw.timestamp, 'API record timestamp');
      if (!id) {
        throw new ReconciliationError('Torn API returned a log with an invalid identity.');
      }
      if (timestamp < from || timestamp > to) {
        const boundaryRelation = timestamp < from ? 'below_from' : 'above_to';
        throw new ReconciliationError(
          `Torn API returned log ${id} ${boundaryRelation === 'below_from' ? 'below the from boundary' : 'above the to boundary'}.`,
          'INCONCLUSIVE',
          {
            phase: 'page_validation',
            page_record_count: responseCount,
            offending_log_id: id,
            offending_timestamp: timestamp,
            offending_iso: new Date(timestamp * 1000).toISOString(),
            boundary_relation: boundaryRelation
          }
        );
      }
      if (seen.has(id)) {
        throw new ReconciliationError(`Torn API duplicated log identity ${id} within one page.`);
      }
      seen.add(id);
      const prepared = {
        id,
        timestamp,
        title: String(raw?.details?.title || ''),
        raw,
        canonical: stableJson(raw)
      };
      // Quarantine exact-from echoes. They remain available to the parent
      // merge, where a right child's from boundary is the parent's internal
      // midpoint. The root boundary is never promoted into comparison data.
      if (timestamp === from) {
        boundaryOverlapCount += 1;
        boundaryRecords.push(prepared);
        continue;
      }
      records.push(prepared);
    }
    const links = json?._metadata?.links;
    if (!links || !Object.prototype.hasOwnProperty.call(links, 'prev') || !Object.prototype.hasOwnProperty.call(links, 'next')) {
      throw new ReconciliationError('Torn API omitted required pagination metadata.');
    }
    if (links.prev !== null && typeof links.prev !== 'string') {
      throw new ReconciliationError('Torn API returned invalid previous-page metadata.');
    }
    if (links.next !== null && typeof links.next !== 'string') {
      throw new ReconciliationError('Torn API returned invalid next-page metadata.');
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
        throw new ReconciliationError(`Torn API returned conflicting payloads for log ${record.id}.`);
      }
      target.set(record.id, record);
    }
  }

  function assertParentSurvives(parentRecords, childRecords) {
    for (const record of parentRecords) {
      const child = childRecords.get(record.id);
      if (!child || child.canonical !== record.canonical) {
        throw new ReconciliationError(
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
      throw new ReconciliationError(
        'A full one-second API page had no older-page continuation link; completeness cannot be proven.',
        'INCONCLUSIVE',
        {
          phase: 'one_second_pagination',
          page_record_count: firstPage.responseCount,
          logical_record_count: firstPage.records.length,
          boundary_overlap_count: firstPage.boundaryOverlapCount,
          prev_present: false,
          next_present: firstPage.next !== null
        }
      );
    }
    while (cursor) {
      const safeCursor = approvedApiUrl(cursor, '/v2/user/log', { from, to, cursor: true });
      if (visited.has(safeCursor)) {
        throw new ReconciliationError('Torn API repeated a one-second pagination cursor.');
      }
      visited.add(safeCursor);
      const json = await transport.getJson(safeCursor, '/v2/user/log', { from, to, cursor: true });
      const page = normalizeApiPage(json, from, to);
      mergeUnique(collected.records, page.records);
      mergeUnique(collected.fromBoundary, page.boundaryRecords);
      if (page.responseCount >= PAGE_LIMIT && page.prev === null) {
        throw new ReconciliationError(
          'A full terminal one-second page had no older-page continuation link; completeness cannot be proven.',
          'INCONCLUSIVE',
          {
            phase: 'one_second_pagination',
            page_record_count: page.responseCount,
            logical_record_count: page.records.length,
            boundary_overlap_count: page.boundaryOverlapCount,
            prev_present: false,
            next_present: page.next !== null
          }
        );
      }
      cursor = page.prev;
      progress?.({ from, to, accepted: collected.records.size, mode: 'one-second pagination' });
    }
    return collected;
  }

  async function collectRangeDetailedCore(from, to, transport, progress, depth = 0) {
    if (depth > 32 || to <= from) {
      throw new ReconciliationError('The independent timestamp split reached an invalid depth or range.');
    }
    const json = await transport.getJson(buildLogUrl(from, to), '/v2/user/log', { from, to });
    const page = normalizeApiPage(json, from, to);
    const width = to - from;
    // Torn returns descending log pages. `prev` is the evidence-bearing link
    // toward older records; `next` is a forward-navigation link and can be
    // present even on an otherwise terminal direct range response. Validate
    // its metadata shape above, but never treat `next` alone as missing older
    // history or follow it during reconciliation.
    const mustSplit = width > 1 && (
      page.responseCount >= SPLIT_THRESHOLD ||
      page.prev !== null
    );
    if (!mustSplit) {
      if (width === 1 && (page.prev !== null || page.responseCount >= PAGE_LIMIT)) {
        return await collectSingleSecondDetailed(from, to, page, transport, progress);
      }
      if (
        page.prev !== null ||
        (width > 1 && page.responseCount >= SPLIT_THRESHOLD)
      ) {
        throw new ReconciliationError(
          'An unsplit API range retained an older-page link or remained saturated.',
          'INCONCLUSIVE',
          {
            phase: 'terminal_range',
            page_record_count: page.responseCount,
            logical_record_count: page.records.length,
            boundary_overlap_count: page.boundaryOverlapCount,
            prev_present: page.prev !== null,
            next_present: page.next !== null
          }
        );
      }
      const accepted = pageCollection(page);
      progress?.({ from, to, accepted: accepted.records.size, mode: 'terminal range' });
      return accepted;
    }

    const midpoint = from + Math.floor(width / 2);
    if (midpoint <= from || midpoint >= to) {
      throw new ReconciliationError('The API range could not be divided safely.');
    }
    progress?.({ from, to, accepted: 0, mode: 'splitting dense range' });
    const left = await collectRangeDetailed(from, midpoint, transport, progress, depth + 1);
    const right = await collectRangeDetailed(midpoint, to, transport, progress, depth + 1);

    const mergedRecords = new Map(left.records);
    mergeUnique(mergedRecords, right.records.values());
    // A right child's exact-from boundary is this parent's midpoint, which is
    // inside the parent logical range. Promote that independently observed
    // boundary only after exact-ID/content conflict checks.
    mergeUnique(mergedRecords, right.fromBoundary.values());
    assertParentSurvives(page.records, mergedRecords);

    const parentBoundary = new Map(left.fromBoundary);
    mergeUnique(parentBoundary, page.boundaryRecords);
    return {
      records: mergedRecords,
      fromBoundary: parentBoundary
    };
  }

  async function collectRangeDetailed(from, to, transport, progress, depth = 0) {
    try {
      return await collectRangeDetailedCore(from, to, transport, progress, depth);
    } catch (error) {
      const diagnostic = {
        phase: 'range_collection',
        range_from: from,
        range_to: to,
        range_from_iso: new Date(from * 1000).toISOString(),
        range_to_iso: new Date(to * 1000).toISOString(),
        split_depth: depth,
        ...(safeDiagnostic(error) || {})
      };
      if (error instanceof ReconciliationError) {
        error.diagnostic = diagnostic;
        throw error;
      }
      throw new ReconciliationError(
        String(error?.message || error),
        'INCONCLUSIVE',
        diagnostic
      );
    }
  }

  async function collectRange(from, to, transport, progress) {
    const collected = await collectRangeDetailed(from, to, transport, progress, 0);
    // Deliberately return only logical records. The root's exact-from boundary
    // sits one second before exported coverage and remains quarantined.
    return collected.records;
  }

  async function confirmAccount(transport, expectedAccountId) {
    const json = await transport.getJson(
      approvedApiUrl(`${API_ORIGIN}/v2/user/profile`, '/v2/user/profile'),
      '/v2/user/profile'
    );
    const actualId = positiveSafeInteger(json?.profile?.id, 'Authenticated Torn account ID');
    if (actualId !== expectedAccountId) {
      throw new ReconciliationError(
        `API key account ${actualId} does not match export account ${expectedAccountId}.`,
        'FAIL'
      );
    }
    return {
      id: actualId,
      name: String(json?.profile?.name || '').trim()
    };
  }

  function compareRecords(exported, fresh) {
    const matched = [];
    const mismatched = [];
    const apiOnly = [];
    const exportOnly = [];
    for (const [id, apiRecord] of fresh) {
      const exportRecord = exported.get(id);
      if (!exportRecord) {
        apiOnly.push(apiRecord);
      } else if (exportRecord.canonical !== apiRecord.canonical) {
        mismatched.push({ exported: exportRecord, api: apiRecord });
      } else {
        matched.push(id);
      }
    }
    for (const [id, exportRecord] of exported) {
      if (!fresh.has(id)) exportOnly.push(exportRecord);
    }
    const sort = (a, b) => a.timestamp - b.timestamp || a.id.localeCompare(b.id);
    apiOnly.sort(sort);
    exportOnly.sort(sort);
    mismatched.sort((a, b) => sort(a.api, b.api));
    return { matched, mismatched, apiOnly, exportOnly };
  }

  function safeDetail(record) {
    return {
      id: record.id,
      timestamp: record.timestamp,
      iso: new Date(record.timestamp * 1000).toISOString(),
      title: record.title
    };
  }

  async function buildReport({ startedAt, finishedAt, source, account, requests, comparison, outcome, reason = '' }) {
    const mismatchDetails = [];
    for (const pair of comparison.mismatched.slice(0, DETAIL_LIMIT)) {
      mismatchDetails.push({
        id: pair.api.id,
        timestamp: pair.api.timestamp,
        iso: new Date(pair.api.timestamp * 1000).toISOString(),
        title: pair.api.title,
        export_raw_sha256: await sha256Hex(pair.exported.canonical),
        api_raw_sha256: await sha256Hex(pair.api.canonical)
      });
    }
    return {
      report: 'torn-analytics-independent-log-reconciliation',
      report_version: 1,
      verifier_version: VERIFIER_VERSION,
      outcome,
      reason,
      method: {
        source: 'Fresh GET-only Torn API v2 user/profile and user/log requests',
        range_semantics: '(from, to]',
        coverage_strategy: 'Recursive timestamp bisection; raw pages split at 90 records or an older-page prev signal; exact-from echoes are quarantined and right-child midpoint records are promoted into the parent after exact-content checks; the root pre-coverage boundary remains excluded; next links are metadata, not collection continuations',
        mutation: 'None; results were held in memory only'
      },
      account: { id: account.id, name: account.name || source.accountName },
      source_export: {
        integrity_sha256: source.digest,
        collector_version: source.collectorVersion,
        exported_at: source.exportedAt,
        first_timestamp: source.first,
        last_timestamp: source.last,
        record_count: source.count
      },
      run: { started_at: startedAt, finished_at: finishedAt, api_requests: requests },
      comparison: {
        exact_matches: comparison.matched.length,
        api_only: comparison.apiOnly.length,
        export_only: comparison.exportOnly.length,
        same_id_payload_mismatches: comparison.mismatched.length,
        details_limit: DETAIL_LIMIT,
        details_truncated: [comparison.apiOnly, comparison.exportOnly, comparison.mismatched]
          .some(items => items.length > DETAIL_LIMIT),
        api_only_details: comparison.apiOnly.slice(0, DETAIL_LIMIT).map(safeDetail),
        export_only_details: comparison.exportOnly.slice(0, DETAIL_LIMIT).map(safeDetail),
        payload_mismatch_details: mismatchDetails
      }
    };
  }

  async function runReconciliation(exportPayload, apiKey, hooks = {}) {
    const startedAt = new Date().toISOString();
    const source = await validateExport(exportPayload);
    const transport = createTransport(apiKey, hooks);
    hooks.onTransport?.(transport);
    const account = await confirmAccount(transport, source.accountId);
    const fresh = await collectRange(source.first - 1, source.last, transport, hooks.onProgress);
    const comparison = compareRecords(source.records, fresh);
    const outcome = comparison.apiOnly.length || comparison.exportOnly.length || comparison.mismatched.length
      ? 'FAIL'
      : 'PASS';
    const report = await buildReport({
      startedAt,
      finishedAt: new Date().toISOString(),
      source,
      account,
      requests: transport.state.requests,
      comparison,
      outcome,
      reason: outcome === 'PASS'
        ? 'Fresh API records exactly matched every exported raw record in the declared coverage.'
        : 'One or more record identities or raw payloads differed.'
    });
    return { report, transport };
  }

  const testApi = {
    ReconciliationError,
    safeDiagnostic,
    stableJson,
    sha256Hex,
    validateExport,
    approvedApiUrl,
    buildLogUrl,
    normalizeApiPage,
    createTransport,
    collectRange,
    collectRangeDetailed,
    compareRecords,
    buildReport,
    runReconciliation,
    constants: { PAGE_LIMIT, SPLIT_THRESHOLD, REQUEST_LIMIT, RAW_FORMAT, EXPORT_FORMAT }
  };
  if (globalThis.__TA_RECONCILER_TEST_HOOK__) {
    globalThis.__TA_RECONCILER_TEST_EXPORTS__ = testApi;
    return;
  }

  const STYLE_ID = 'ta-independent-reconciler-style';
  const ROOT_ID = 'ta-independent-reconciler-root';
  let activeTransport = null;
  let preparedReport = null;
  let selectedPayload = null;

  function installStyle() {
    if (document.getElementById(STYLE_ID)) return;
    const style = document.createElement('style');
    style.id = STYLE_ID;
    style.textContent = `
      #${ROOT_ID}, #${ROOT_ID} * { box-sizing: border-box; }
      #${ROOT_ID} { position: fixed; inset: 0; z-index: 2147483647; background: rgba(0,0,0,.78); color: #eee; font: 15px/1.4 Arial,sans-serif; display: flex; align-items: center; justify-content: center; padding: 16px; }
      #${ROOT_ID} .ta-r-card { width: min(720px,100%); max-height: 92vh; overflow: auto; background: #191919; border: 1px solid #555; border-radius: 14px; padding: 18px; box-shadow: 0 20px 60px #000; }
      #${ROOT_ID} h2 { margin: 0 0 8px; font-size: 22px; color: #fff; }
      #${ROOT_ID} p { margin: 8px 0; }
      #${ROOT_ID} .ta-r-note { color: #c8c8c8; }
      #${ROOT_ID} .ta-r-safe { border-left: 4px solid #d5a84e; background: #211d16; padding: 10px 12px; border-radius: 6px; }
      #${ROOT_ID} label { display: block; margin-top: 14px; font-weight: 700; color: #fff; }
      #${ROOT_ID} input { width: 100%; margin-top: 6px; padding: 12px; border-radius: 8px; border: 1px solid #666; background: #101010; color: #fff; }
      #${ROOT_ID} .ta-r-actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 16px; }
      #${ROOT_ID} button { min-height: 44px; padding: 10px 16px; border-radius: 8px; border: 1px solid #777; background: #373737; color: #fff; font-weight: 700; }
      #${ROOT_ID} button.ta-r-primary { background: #a87924; border-color: #deb85e; color: #fff; }
      #${ROOT_ID} button:disabled { opacity: .45; }
      #${ROOT_ID} pre { white-space: pre-wrap; overflow-wrap: anywhere; background: #0c0c0c; border: 1px solid #444; border-radius: 8px; padding: 12px; max-height: 240px; overflow: auto; color: #ddd; }
      #${ROOT_ID} .ta-r-pass { color: #72db92; } #${ROOT_ID} .ta-r-fail { color: #ff8b82; } #${ROOT_ID} .ta-r-inconclusive { color: #f0c56e; }
      #${ROOT_ID} .ta-r-status { font-weight: 700; min-height: 24px; }
    `;
    document.head.appendChild(style);
  }

  function reportSummary(report) {
    const c = report.comparison;
    const lines = [
      `Outcome: ${report.outcome}`,
      report.reason,
      `Account: ${report.account.name || '(unknown)'} [${report.account.id}]`,
      `Coverage: ${new Date(report.source_export.first_timestamp * 1000).toISOString()} to ${new Date(report.source_export.last_timestamp * 1000).toISOString()}`,
      `Exported records: ${report.source_export.record_count}`,
      `Exact matches: ${c.exact_matches}`,
      `API-only: ${c.api_only}`,
      `Export-only: ${c.export_only}`,
      `Payload mismatches: ${c.same_id_payload_mismatches}`,
      `API requests: ${report.run.api_requests}`
    ];
    if (report.diagnostic?.range_from_iso && report.diagnostic?.range_to_iso) {
      lines.push(`Failing range: ${report.diagnostic.range_from_iso} to ${report.diagnostic.range_to_iso}`);
      lines.push(
        `Page state: ${report.diagnostic.page_record_count ?? 'unknown'} records · ` +
        `prev ${report.diagnostic.prev_present ? 'present' : 'absent'} · ` +
        `next ${report.diagnostic.next_present ? 'present' : 'absent'}`
      );
    }
    if (report.diagnostic?.offending_iso) {
      lines.push(
        `Out-of-range log: ${report.diagnostic.offending_log_id || '(unknown)'} · ` +
        `${report.diagnostic.offending_iso} · ${report.diagnostic.boundary_relation || 'unknown relation'}`
      );
    }
    return lines.join('\n');
  }

  function filenameFor(report) {
    const day = new Date().toISOString().slice(0, 10);
    return `TornAnalytics-${report.account.id}-reconciliation-${day}.json`;
  }

  async function saveReport(report) {
    const text = JSON.stringify(report, null, 2);
    const file = new File([text], filenameFor(report), { type: 'application/json' });
    if (navigator.share && navigator.canShare?.({ files: [file] })) {
      await navigator.share({ files: [file], title: 'Torn Analytics reconciliation report' });
      return;
    }
    const url = URL.createObjectURL(file);
    const link = document.createElement('a');
    link.href = url;
    link.download = file.name;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function mount() {
    if (document.getElementById(ROOT_ID)) return;
    installStyle();
    const root = document.createElement('div');
    root.id = ROOT_ID;
    root.innerHTML = `
      <section class="ta-r-card" role="dialog" aria-modal="true" aria-labelledby="ta-r-title">
        <h2 id="ta-r-title">Independent Log Reconciler v${VERIFIER_VERSION}</h2>
        <p class="ta-r-safe">Read-only: this tool makes GET requests only. It does not open, change, repair, or store Torn Analytics history.</p>
        <p class="ta-r-note">Choose the readable-history JSON exported from Torn Analytics v2.18.45. A complete scan can take time because dense periods are independently divided into smaller timestamp ranges.</p>
        <label>History export<input id="ta-r-file" type="file" accept="application/json,.json"></label>
        ${injectedKey ? '' : '<label>Session-only Torn API key<input id="ta-r-key" type="password" autocomplete="off" autocapitalize="off" spellcheck="false"></label>'}
        <div class="ta-r-actions">
          <button id="ta-r-run" class="ta-r-primary" disabled>Run read-only comparison</button>
          <button id="ta-r-cancel" disabled>Cancel</button>
          <button id="ta-r-save" disabled>Save report</button>
          <button id="ta-r-copy" disabled>Copy summary</button>
          <button id="ta-r-close">Close</button>
        </div>
        <p id="ta-r-status" class="ta-r-status">Waiting for an export file.</p>
        <pre id="ta-r-output" hidden></pre>
      </section>`;
    document.body.appendChild(root);

    const fileInput = root.querySelector('#ta-r-file');
    const keyInput = root.querySelector('#ta-r-key');
    const run = root.querySelector('#ta-r-run');
    const cancel = root.querySelector('#ta-r-cancel');
    const save = root.querySelector('#ta-r-save');
    const copy = root.querySelector('#ta-r-copy');
    const close = root.querySelector('#ta-r-close');
    const status = root.querySelector('#ta-r-status');
    const output = root.querySelector('#ta-r-output');

    fileInput.addEventListener('change', async () => {
      selectedPayload = null;
      preparedReport = null;
      save.disabled = true;
      copy.disabled = true;
      output.hidden = true;
      const file = fileInput.files?.[0];
      if (!file) {
        status.textContent = 'Waiting for an export file.';
        run.disabled = true;
        return;
      }
      status.textContent = 'Reading and validating the export…';
      try {
        selectedPayload = JSON.parse(await file.text());
        const checked = await validateExport(selectedPayload);
        status.textContent = `Validated ${checked.count.toLocaleString()} exported records for account ${checked.accountId}. Ready.`;
        run.disabled = false;
      } catch (error) {
        status.textContent = `FAIL: ${error.message}`;
        status.className = 'ta-r-status ta-r-fail';
        run.disabled = true;
      }
    });

    run.addEventListener('click', async () => {
      const key = String(injectedKey || keyInput?.value || '').trim();
      if (!selectedPayload || !key) {
        status.textContent = 'Select a valid export and provide the session-only API key.';
        return;
      }
      run.disabled = true;
      cancel.disabled = false;
      save.disabled = true;
      copy.disabled = true;
      preparedReport = null;
      status.className = 'ta-r-status';
      status.textContent = 'Confirming the API key account…';
      output.hidden = true;
      const startedAt = new Date().toISOString();
      let source = null;
      try {
        source = await validateExport(selectedPayload);
        const result = await runReconciliation(selectedPayload, key, {
          onTransport(transport) { activeTransport = transport; },
          onRequest(count) { status.textContent = `Read-only API request ${count.toLocaleString()}…`; },
          onProgress(info) {
            const start = new Date(info.from * 1000).toISOString();
            const end = new Date(info.to * 1000).toISOString();
            status.textContent = `Request ${activeTransport?.state.requests || 0}: ${info.mode} ${start} → ${end}`;
          }
        });
        preparedReport = result.report;
      } catch (error) {
        let fallbackSource = source;
        try { fallbackSource ||= await validateExport(selectedPayload); } catch {}
        const outcome = error?.outcome === 'FAIL' ? 'FAIL' : 'INCONCLUSIVE';
        preparedReport = {
          report: 'torn-analytics-independent-log-reconciliation',
          report_version: 1,
          verifier_version: VERIFIER_VERSION,
          outcome,
          reason: String(error?.message || error),
          diagnostic: safeDiagnostic(error),
          method: { source: 'Fresh GET-only Torn API requests', mutation: 'None; results were held in memory only' },
          account: { id: fallbackSource?.accountId || 0, name: fallbackSource?.accountName || '' },
          source_export: fallbackSource ? {
            integrity_sha256: fallbackSource.digest,
            collector_version: fallbackSource.collectorVersion,
            exported_at: fallbackSource.exportedAt,
            first_timestamp: fallbackSource.first,
            last_timestamp: fallbackSource.last,
            record_count: fallbackSource.count
          } : null,
          run: { started_at: startedAt, finished_at: new Date().toISOString(), api_requests: activeTransport?.state.requests || 0 },
          comparison: { exact_matches: 0, api_only: 0, export_only: 0, same_id_payload_mismatches: 0, details_limit: DETAIL_LIMIT, details_truncated: false, api_only_details: [], export_only_details: [], payload_mismatch_details: [] }
        };
      } finally {
        activeTransport = null;
        if (keyInput) keyInput.value = '';
        cancel.disabled = true;
        run.disabled = false;
      }
      const summary = reportSummary(preparedReport);
      status.textContent = summary.split('\n')[0];
      status.className = `ta-r-status ta-r-${preparedReport.outcome.toLowerCase()}`;
      output.textContent = summary;
      output.hidden = false;
      save.disabled = false;
      copy.disabled = false;
    });

    cancel.addEventListener('click', () => activeTransport?.cancel());
    save.addEventListener('click', async () => {
      if (!preparedReport) return;
      try { await saveReport(preparedReport); } catch (error) { status.textContent = `Could not save report: ${error.message}`; }
    });
    copy.addEventListener('click', async () => {
      if (!preparedReport) return;
      await navigator.clipboard.writeText(reportSummary(preparedReport));
      status.textContent = 'Summary copied.';
    });
    close.addEventListener('click', () => {
      activeTransport?.cancel();
      if (keyInput) keyInput.value = '';
      selectedPayload = null;
      preparedReport = null;
      root.remove();
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', mount, { once: true });
  } else {
    mount();
  }
})();
