# Cloudflare Pages deployment

Pages project root: `pages/` (this folder). Build output directory: `public`.
The `functions/api/build.js` file must deploy as a Cloudflare Pages Function.
Add environment variable `GSX_BUILD_ORIGIN` (the HTTPS URL of the separate private
compiler backend, no path) and secret `GSX_BUILD_TOKEN` (a random 32+ character
string exactly matching the backend's `GSX_BUILD_TOKEN`).

Recommended Git deployment: set root directory `pages` and build output
`public`. Alternatively, from this folder use `npx wrangler pages deploy public`
with Pages Functions support in your Wrangler CLI. Do not deploy the
`private-backend/` directory as static assets.

Without a running configured private backend the UI can load, but Build returns
503. Nothing in the public static deployment can compile Lua on its own.
