/**
 * polly#197: read an environment variable without indexing `process.env`.
 *
 * A consumer may augment `NodeJS.ProcessEnv` with a closed key set (no index
 * signature), and then `process.env["X"]` and `process.env.NODE_ENV` do not
 * type-check in its program. The spread gives the copy an implicit index
 * signature. Browser bundles have no `process`, so they read undefined.
 */
export function readEnv(name: string): string | undefined {
  if (typeof process === "undefined" || !process.env) return undefined;
  const env: { [key: string]: string | undefined } = { ...process.env };
  return env[name];
}
