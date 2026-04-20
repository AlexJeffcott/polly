/**
 * Type guards for walking `unknown` values safely.
 *
 * Polly touches a lot of shapes it doesn't own: parsed JSON bodies
 * from the signalling server, IndexedDB records, `postMessage`
 * payloads, storage adapter returns. TypeScript sees every one of
 * those as `unknown`, and the ergonomic-but-unsafe fix — a bare `as`
 * cast — hides every shape mismatch until runtime. The helpers below
 * are the thinnest possible layer that turns a runtime shape check
 * into a compile-time narrowing, so the code that follows can read
 * the value without a cast.
 *
 * Each guard checks own-properties only (`Object.hasOwn`), not the
 * prototype chain. Walking into a prototype would make a simple
 * `hasKeyInObject(x, "toString")` pass for any object, which is
 * never what a caller looking for a specific data key intends.
 */

/** Narrow `input` to an object carrying its own `key`. Returns true
 * when the input is a non-null object with an own property under
 * the given key. The value under the key is left as `unknown`;
 * callers narrow further with `Array.isArray`, `typeof`, or another
 * guard. */
export function hasKeyInObject<K extends string>(
  input: unknown,
  key: K
): input is Record<K, unknown> {
  return typeof input === "object" && input !== null && Object.hasOwn(input, key);
}

/** Narrow `input` to a plain object (non-null, non-array). Useful as
 * a prelude to reads off a record whose shape is known at the
 * call site but typed as `unknown`. */
export function isRecord(input: unknown): input is Record<string, unknown> {
  return typeof input === "object" && input !== null && !Array.isArray(input);
}
