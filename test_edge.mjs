import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const here = path.dirname(fileURLToPath(import.meta.url));
const dir = path.resolve(here, '..');
const pages = await import(pathToFileURL(path.join(dir, 'pages/functions/api/build.js')).href);
const worker = (await import(pathToFileURL(path.join(dir, 'worker/worker.js')).href)).default;
const config = {GSX_BUILD_ORIGIN:'https://compiler.private.example/', GSX_BUILD_TOKEN:'s'.repeat(48)};
const seen = [];
const original = globalThis.fetch;
globalThis.fetch = async (url, options) => {
  seen.push({url:String(url), options});
  return Response.json({status:'OK', data:{ok:true}, code:'-- protected'});
};
function post(payload, headers = {}) {
  return new Request('https://website.pages.dev/api/build', {method:'POST', headers:{
    'Origin':'https://website.pages.dev', 'Content-Type':'application/json',
    'Sec-Fetch-Site':'same-origin', ...headers
  }, body: JSON.stringify(payload)});
}
try {
  const ctx = {request: post({source:'print(42)', delivery:'sealed'}), env:config};
  const ok = await pages.onRequest(ctx);
  assert.equal(ok.status, 200);
  assert.equal((await ok.json()).status, 'OK');
  assert.equal(seen.length,1);
  assert.equal(seen[0].url, 'https://compiler.private.example/api/build');
  assert.equal(seen[0].options.headers.Authorization, 'Bearer '+config.GSX_BUILD_TOKEN);
  assert.deepEqual(JSON.parse(seen[0].options.body),{source:'print(42)',delivery:'sealed'});
  const wrongOrigin = await pages.onRequest({request:post({source:'x',delivery:'sealed'},{Origin:'https://evil.example'}),env:config});
  assert.equal(wrongOrigin.status,403);
  const badArgs = await pages.onRequest({request:post({source:'x',delivery:'sealed',rules:{integrity:false}}),env:config});
  assert.equal(badArgs.status,400);
  const badMode = await pages.onRequest({request:post({source:'x',delivery:'off'}),env:config});
  assert.equal(badMode.status,400);
  const empty = await pages.onRequest({request:post({source:' ',delivery:'sealed'}),env:config});
  assert.equal(empty.status,400);
  const noSecret = await pages.onRequest({request:post({source:'x',delivery:'sealed'}),env:{}});
  assert.equal(noSecret.status,503);
  const workerReply = await worker.fetch(post({source:'print(1)',delivery:'direct-vm'}),config);
  assert.equal(workerReply.status,200);
  assert.equal(seen.length,2);
  assert.equal(JSON.parse(seen[1].options.body).delivery,'direct-vm');
  const staticReply = await worker.fetch(new Request('https://website.pages.dev/'),{
    ...config, ASSETS:{fetch:async()=>new Response('<html>UI</html>',{headers:{'Content-Type':'text/html'}})}
  });
  assert.equal(staticReply.status,200);
  assert.equal(staticReply.headers.get('X-Frame-Options'),'DENY');
  assert.match(await staticReply.text(), /UI/);
  assert.equal(seen.length,2);
  console.log('Edge proxy and static routing tests: PASS (9 checks)');
} finally {globalThis.fetch = original;}
