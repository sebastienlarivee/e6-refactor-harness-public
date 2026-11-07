/** Host-only Pi SDK auth bridge. Stdout is a private subprocess pipe, never a log. */
import { readFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { pathToFileURL } from 'node:url';

const PUBLIC_BASE = 'https://api.openai.com/v1';
const DIRECT_SCOPE = 'chatgpt.tokens.use.direct';

// Ignore native/library console diagnostics: OAuth errors may contain tokens.
console.log = console.warn = console.error = () => {};
try {
  const [packageRoot, authPath, expectedVersion] = process.argv.slice(2);
  const manifest = JSON.parse(await readFile(join(packageRoot, 'package.json'), 'utf8'));
  if (manifest.name !== '@earendil-works/pi-coding-agent' || manifest.version !== expectedVersion)
    throw new Error('runtime');
  const require = createRequire(join(packageRoot, 'package.json'));
  // Pi AI is ESM-only; locate its installed package using native dependency
  // search paths without selecting CommonJS export conditions.
  const aiRoot = require.resolve.paths('@earendil-works/pi-ai')
    .map(root => join(root, '@earendil-works/pi-ai'))
    .find(root => existsSync(join(root, 'package.json')));
  if (!aiRoot) throw new Error('runtime');
  const aiManifest = JSON.parse(await readFile(join(aiRoot, 'package.json'), 'utf8'));
  if (aiManifest.version !== expectedVersion) throw new Error('runtime');
  const [{ AuthStorage }, { createModels }, { openaiProvider }, { getPiUserAgent }] = await Promise.all([
    import(pathToFileURL(join(packageRoot, 'dist/core/auth-storage.js'))),
    import(pathToFileURL(join(aiRoot, 'dist/models.js'))),
    import(pathToFileURL(join(aiRoot, 'dist/providers/openai.js'))),
    import(pathToFileURL(join(aiRoot, 'dist/utils/pi-user-agent.js'))),
  ]);
  const storage = AuthStorage.create(authPath);
  const signal = AbortSignal.timeout(30_000);
  // Refuse API-key fallback and older backend-api OAuth grants. Never start login.
  const before = await storage.read('openai', { signal });
  if (before?.type !== 'oauth' || !Array.isArray(before.scopes) || !before.scopes.includes(DIRECT_SCOPE) ||
      typeof before.clientId !== 'string' || !before.clientId)
    throw new Error('credential');
  const provider = openaiProvider();
  if (provider.baseUrl !== PUBLIC_BASE) throw new Error('endpoint');
  const models = createModels({ credentials: storage, authContext: {
    env: async () => undefined, fileExists: async () => false,
  } });
  models.setProvider(provider);
  // Native SDK resolves provider headers and refreshes/persists under its lock.
  const model = models.getModel('openai', 'gpt-6.1-sol');
  const resolved = await models.getAuth(model ?? 'openai', { minOAuthValidityMs: 300000, signal });
  const after = await storage.read('openai', { signal });
  if (after?.type !== 'oauth' || !Array.isArray(after.scopes) || !after.scopes.includes(DIRECT_SCOPE) ||
      !resolved?.auth || resolved.auth.apiKey !== after.access)
    throw new Error('credential');
  const baseUrl = resolved.auth.baseUrl ?? model?.baseUrl ?? provider.baseUrl;
  if (baseUrl !== PUBLIC_BASE) throw new Error('endpoint');
  const headers = { 'User-Agent': getPiUserAgent(), ...provider.headers, ...resolved.auth.headers };
  process.stdout.write(JSON.stringify({ kind: 'pi_oauth', auth: { ...resolved.auth, headers },
    base_url: baseUrl, expires_at: after.expires / 1000, scopes: after.scopes,
    source: 'pi-native-sdk', pi_version: manifest.version }));
} catch {
  // All diagnostics are fixed; native error causes and credential data stay private.
  process.stderr.write('Pi native OAuth resolution failed\n');
  process.exitCode = 1;
}
