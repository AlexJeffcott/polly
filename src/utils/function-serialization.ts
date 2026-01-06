import serialize from "serialize-javascript";

/**
 * Check if we're in development mode
 */
const isDev = process.env.NODE_ENV !== "production";

/**
 * Serialize a function to send to client
 *
 * DEV ONLY: Used for hot reloading and debugging
 * PROD: No-op - client effects are baked into bundle at build time
 */
// biome-ignore lint/complexity/noBannedTypes: Generic function serialization requires Function type
export function serializeFunction(fn: Function): string {
  if (!isDev) {
    // In production, return empty string - this won't be used
    return "";
  }

  return serialize(fn, { space: 0 });
}

/**
 * Deserialize a function received from server
 *
 * DEV ONLY: Eval serialized function source
 * PROD: Should never be called - effects come from bundle
 */
// biome-ignore lint/complexity/noBannedTypes: Generic function deserialization requires Function type
export function deserializeFunction(serialized: string): Function {
  if (!isDev) {
    throw new Error(
      "[Polly] deserializeFunction should not be called in production. " +
        "Client effects should be imported from your bundle."
    );
  }

  if (!serialized) {
    throw new Error("[Polly] Cannot deserialize empty function");
  }

  // biome-ignore lint/security/noGlobalEval: Required for dev-mode function deserialization
  return eval(`(${serialized})`);
}
