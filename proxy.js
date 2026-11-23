// GsXFuscator: Cloudflare edge proxy. No Lua compiler or bearer credential in static assets.
const MAX_BODY = 32 * 1024 * 1024;
const MAX_SOURCE = 10 * 1024 * 1024;
const enc = new TextEncoder();
function failure(status, error) {
  return Response.json({error}, {status, headers: {
    'Cache-Control': 'no-store',
    'Content-Security-Policy': "default-src 'none'",
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer'
  }});
}

async function proxyBuild(request, env) {
  if (request.method !== 'POST') return failure(405, 'Use POST for builds.');
  const self = new URL(request.url).origin;
  const origin = request.headers.get('Origin');
  // Browser CSRF protection only. Origin/Fetch Metadata are not authentication.
  if (origin && origin !== self) return failure(403, 'Cross-origin builds are disabled.');
  const site = request.headers.get('Sec-Fetch-Site');
  if (site && !['same-origin', 'none'].includes(site)) {
    return failure(403, 'Cross-site builds are disabled.');
  }
  if (request.headers.get('Content-Type')?.split(';')[0].trim().toLowerCase() !== 'application/json') {
    return failure(415, 'Send application/json.');
  }
  const location = env.GSX_BUILD_ORIGIN;
  const token = env.GSX_BUILD_TOKEN;
  if (typeof location !== 'string' || typeof token !== 'string' || token.length < 32) {
    return failure(503, 'The private compiler is not configured.');
  }
  let remote;
  try {
    const url = new URL(location);
    if (url.protocol !== 'https:' || !url.hostname || url.username || url.password ||
        url.search || url.hash || (url.pathname !== '/' && url.pathname !== '')) {
      return failure(503, 'The private compiler endpoint must be a secure HTTPS origin.');
    }
    remote = new URL('/api/build', url);
  } catch (_) { return failure(503, 'Invalid compiler origin configuration.'); }
  if (!request.body) return failure(400, 'Missing build request.');
  const claimed = Number(request.headers.get('Content-Length'));
  if (Number.isFinite(claimed) && claimed > MAX_BODY) return failure(413, 'Request too large.');
  const reader = request.body.getReader();
  const parts = [];
  let length = 0;
  try {
    while (true) {
      const {done, value} = await reader.read();
      if (done) break;
      length += value.byteLength;
      if (length > MAX_BODY) {
        await reader.cancel();
        return failure(413, 'Request exceeds the 32 MiB JSON transport limit.');
      }
      parts.push(value);
    }
  } catch (_) { return failure(400, 'Unable to read request.'); }
  finally { reader.releaseLock(); }
  if (!length) return failure(400, 'Missing build request.');
  const bytes = new Uint8Array(length);
  let offset = 0;
  for (const part of parts) { bytes.set(part, offset); offset += part.byteLength; }
  let payload;
  try { payload = JSON.parse(new TextDecoder('utf-8', {fatal:true}).decode(bytes)); }
  catch (_) { return failure(400, 'Invalid JSON payload.'); }
  if (!payload || Array.isArray(payload) || typeof payload !== 'object' ||
      Object.keys(payload).some(key => !['source', 'delivery'].includes(key)) ||
      typeof payload.source !== 'string' || !payload.source.trim() ||
      !['sealed', 'direct-vm'].includes(payload.delivery)) {
    return failure(400, 'Invalid source or delivery mode.');
  }
  if (enc.encode(payload.source).byteLength > MAX_SOURCE) {
    return failure(413, 'Lua source exceeds 10 MiB.');
  }
  // Canonicalize to an allowlisted shape so callers cannot override server policy.
  const body = JSON.stringify({source:payload.source, delivery:payload.delivery});
  try {
    const upstream = await fetch(remote, {
      method: 'POST',
      redirect: 'manual',
      headers: {'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'},
      body
    });
    if ((upstream.status >= 300 && upstream.status < 400) || upstream.status >= 500 ||
        !upstream.headers.get('Content-Type')?.toLowerCase().includes('application/json')) {
      return failure(503, 'The private compiler is unavailable.');
    }
    if (upstream.status === 401 || upstream.status === 403) {
      return failure(503, 'Private compiler credentials were rejected.');
    }
    return new Response(upstream.body, {status:upstream.status, headers: {
      'Content-Type': 'application/json; charset=utf-8',
      'Cache-Control': 'no-store',
      'Content-Security-Policy': "default-src 'none'",
      'X-Content-Type-Options': 'nosniff',
      'Referrer-Policy': 'no-referrer'
    }});
  } catch (_) { return failure(503, 'The private compiler is unavailable.'); }
}
