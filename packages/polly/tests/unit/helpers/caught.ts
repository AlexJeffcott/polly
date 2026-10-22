/**
 * Narrow a caught value to the error class a test expects, failing the test
 * when it is anything else. Replaces `caught as unknown as MyError`.
 */
export function caughtAs<T>(ctor: new (...args: never[]) => T, caught: unknown): T {
  if (!(caught instanceof ctor)) {
    throw new Error(`expected a ${ctor.name}, caught ${String(caught)}`);
  }
  return caught;
}
