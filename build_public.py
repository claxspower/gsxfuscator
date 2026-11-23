#!/usr/bin/env python3
"""Build a static GsXFuscator front-end with NO Lua engine, WASM, or modules.

Run from any directory: python tools/build_public.py
Only pages/public or worker/assets are safe to publish as static files.
"""
import base64
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'ui-src'

def encoded(path):
    return base64.b64encode(path.read_bytes()).decode('ascii')

FRONTEND_API = '''    // Sensitive Lua compiler modules are never sent to the browser.
    async function compileFile(build) {
      const abort = new AbortController();
      build.cancel = () => abort.abort();
      try {
        note('Sending source to the private compiler…', '');
        ringProgress(4, true);
        const response = await fetch('/api/build', {
          method: 'POST',
          credentials: 'same-origin',
          cache: 'no-store',
          signal: abort.signal,
          headers: {'Content-Type':'application/json', 'Accept':'application/json'},
          body: JSON.stringify({source: build.source, delivery: build.delivery})
        });
        let payload;
        try { payload = await response.json(); }
        catch (_) { throw new Error('The private compiler returned an invalid response.'); }
        if (!response.ok) {
          throw new Error(String(payload?.error || 'The private compiler rejected the request.'));
        }
        if (!payload || typeof payload !== 'object' || typeof payload.status !== 'string') {
          throw new Error('The private compiler returned an invalid build result.');
        }
        ringProgress(95, true);
        return payload;
      } catch (error) {
        if (error.name === 'AbortError') throw new Error('The selected file changed.');
        throw error;
      } finally {
        build.cancel = null;
      }
    }

'''

def main():
    html = (SRC / 'v3template.html').read_text(encoding='utf-8')
    for name in ['DASHBOARD_CSS','SETTINGS_CSS','SETTINGS_JS']:
        asset = {'DASHBOARD_CSS':'dashboard.css', 'SETTINGS_CSS':'settings.css', 'SETTINGS_JS':'settings.js'}[name]
        html = html.replace('/*__'+name+'__*/', (SRC / asset).read_text(encoding='utf-8'))
    html = html.replace('<!--__FULL_DEVELOPER_DOCS__-->',
        '<section class="doc-section" id="docs-library"><h3>Private developer references</h3>'
        '<p>Implementation, VM internals, complete API reference and build details are kept '
        'in the private source package and are not published with the website.</p></section>')
    for name, asset in [('DCART','dc-banner.jpg'),('GSXFUSCATOR_FAVICON','assets/gsxfuscator-favicon.png'),('GSXFUSCATOR_LOGO','assets/gsxfuscator-logo.webp')]:
        html = html.replace('__'+name+'__', encoded(SRC / asset))
    html, count = re.subn(r'\s*<script type="text/plain" id="engineSrc">.*?</script>', '', html, count=1, flags=re.S)
    if count != 1: raise RuntimeError('Browser engine script marker not found')
    begin = html.index('    const WORKER_B64 =')
    end = html.index('    // ------------------------------------------------------------------ build', begin)
    html = html[:begin] + FRONTEND_API + html[end:]
    html = html.replace('Choose a file to compile in your browser.', 'Choose a file to compile using the private service.')
    html = html.replace('choose a file to compile in your browser.', 'choose a file to compile using the private service.')
    html = html.replace("note('Compiling in your browser…', '');", "note('Compiling on the private server…', '');")
    html = html.replace('Full API reference, architecture, and end-to-end tutorials to build and test your own Lua obfuscator. Available offline.',
        'Quick start, security model and practical usage. Internal developer guides remain private.')
    for fragment, replacement in [
      ('docs-cli', '<h3>Private CLI reference</h3><p>The full CLI and source package are not distributed on the public site.</p>'),
      ('docs-api', '<h3>Private Lua API</h3><p>Source-level compiler APIs and examples are only available in the private backend package.</p>')
    ]:
      html, count = re.subn(r'<section class="doc-section" id="' + fragment + r'".*?</section>',
            '<section class="doc-section" id="' + fragment + '">' + replacement + '</section>',
            html, count=1, flags=re.S)
      if count != 1: raise RuntimeError('Could not strip source reference '+fragment)
    html = html.replace('Full developer library', 'Private developer references')
    for label in ('Build your own obfuscator','VM &amp; bytecode','Complete API','Test methodology'):
      html = re.sub(r'<a href="#dev-[^"]+">'+re.escape(label)+r'</a>', '', html)

    html = html.replace('The browser automatically enables strong protection', 'The private compiler enforces strong protection')
    html = html.replace('The browser compiles locally', 'The private server compiles')
    # Explicit privacy disclosure: requests now leave the browser.
    html = html.replace('Save your generated Lua directly; source and output are not stored in browser history.',
        'Compile on a private server, then download generated Lua; no build history is stored in the browser.')
    html = html.replace('Automatic Lua protection: Strong compact VM, Anti-Tamper, Anti-Debug and integrity checks.',
        'Private server-side Lua protection: Strong compact VM, Anti-Tamper, Anti-Debug and integrity checks.')
    # Do not request browser WASM or Workers: neither contains the protected engine.
    html = re.sub(r'<meta http-equiv="Content-Security-Policy" content="[^"]+">',
      '<meta http-equiv="Content-Security-Policy" content="default-src \'none\'; script-src \'self\' \'unsafe-inline\'; connect-src \'self\'; style-src \'self\' \'unsafe-inline\' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src \'self\' data:; worker-src \'none\'; object-src \'none\'; base-uri \'none\'; form-action \'none\'; frame-ancestors \'none\'">', html, count=1)
    if any(t in html for t in ['/*__','__WORKER_FINGERPRINT__','__GSXFUSCATOR_']):
        raise RuntimeError('Unreplaced template marker')
    # Assertions prevent accidentally publishing the entire private Lua/WASM compiler again.
    forbidden = ['const WORKER_B64', 'const WASM_B64', 'const DRIVER_B64', 'const MODULES =',
                 'id="engineSrc"', 'wasmoon.LuaFactory', 'package.searchers =']
    for item in forbidden:
        if item in html:
            raise RuntimeError('Sensitive compiler code leaked into the front-end: '+item)
    public = ROOT / 'pages' / 'public'
    public.mkdir(parents=True, exist_ok=True)
    (public / 'index.html').write_text(html, encoding='utf-8')
    (public / '_headers').write_text('''/*
  Content-Security-Policy: default-src 'none'; script-src 'self' 'unsafe-inline'; connect-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src 'self' data:; worker-src 'none'; object-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'
  X-Content-Type-Options: nosniff
  X-Frame-Options: DENY
  Referrer-Policy: no-referrer
  Cross-Origin-Resource-Policy: same-origin
  Permissions-Policy: camera=(), microphone=(), geolocation=()
''', encoding='utf-8')
    (public / '404.html').write_text('<!doctype html><meta charset="utf-8"><title>Not found</title><h1>404</h1>', encoding='utf-8')
    assets = ROOT / 'worker' / 'assets'
    assets.mkdir(parents=True, exist_ok=True)
    for f in ('index.html','_headers','404.html'):
        shutil.copy2(public/f, assets/f)
    proxy = (ROOT/'tools'/'proxy.js').read_text(encoding='utf-8')
    (ROOT/'pages'/'functions'/'api'/'build.js').write_text(proxy + '''\nexport async function onRequest({request, env}) { return proxyBuild(request, env); }\n''', encoding='utf-8')
    (ROOT/'worker'/'worker.js').write_text(proxy+'''\nexport default {
  async fetch(request, env) {
    if (new URL(request.url).pathname === '/api/build') return proxyBuild(request, env);
    // Only public static assets are ever returned. The Lua compiler is not bundled.
    const response = await env.ASSETS.fetch(request);
    const headers = new Headers(response.headers);
    headers.set('X-Content-Type-Options', 'nosniff');
    headers.set('Referrer-Policy', 'no-referrer');
    headers.set('X-Frame-Options', 'DENY');
    headers.set('Cross-Origin-Resource-Policy', 'same-origin');
    headers.set('Content-Security-Policy', "default-src 'none'; script-src 'self' 'unsafe-inline'; connect-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src 'self' data:; worker-src 'none'; object-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'");
    return new Response(response.body, {status: response.status, headers});
  }
};\n''', encoding='utf-8')
    print('Built secure web UI:', len(html.encode('utf-8')), 'bytes. No Lua engine/WASM in public output.')

if __name__ == '__main__': main()
