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

/*
 * Readers for values of unknown shape, such as fields of parsed JSON. Each
 * returns the value when it has the named type and `undefined` otherwise, so
 * `readString(pkg["name"]) ?? "unnamed"` replaces `pkg["name"] as string`,
 * which claims a type the data never promised.
 */

export function readString(input: unknown): string | undefined {
  return typeof input === "string" ? input : undefined;
}

export function readNumber(input: unknown): number | undefined {
  return typeof input === "number" ? input : undefined;
}

export function readBoolean(input: unknown): boolean | undefined {
  return typeof input === "boolean" ? input : undefined;
}

/** The array when every element is a string; `undefined` for anything else. */
export function readStringArray(input: unknown): string[] | undefined {
  return Array.isArray(input) && input.every((item): item is string => typeof item === "string")
    ? input
    : undefined;
}

export function readRecord(input: unknown): Record<string, unknown> | undefined {
  return isRecord(input) ? input : undefined;
}

/** The array, with every element that is not a plain object dropped; `undefined` for a non-array. */
export function readRecordArray(input: unknown): Record<string, unknown>[] | undefined {
  return Array.isArray(input) ? input.filter(isRecord) : undefined;
}

/**
 * Compile-time exhaustiveness check for discriminated unions.
 *
 * A string-literal union is decorative without one: add a third
 * variant and nothing flags the `switch` statements that only handled
 * the first two — the new case silently falls through whatever
 * `default` arm exists. Placing `assertNever` in that `default` arm
 * turns the gap into a type error, because `value` is only assignable
 * to `never` when every other case has already been handled. The
 * moment a variant is added and a switch forgets it, `value` is no
 * longer `never` and the call fails to type-check.
 *
 * ```ts
 * switch (event.kind) {
 *   case "a": return handleA(event);
 *   case "b": return handleB(event);
 *   default: return assertNever(event);
 * }
 * ```
 *
 * The `throw` is the runtime backstop for the case TypeScript cannot
 * see — a value arriving from outside the type system (a parsed JSON
 * body, a `postMessage` payload) that violates the declared union.
 */
export function assertNever(value: never): never {
  throw new Error(`assertNever: unexpected value ${JSON.stringify(value)}`);
}
