/**
 * Narrow a value to the class a test expects, failing the test when it is
 * anything else. Replaces `slot.channel as unknown as FakeDataChannel` when a
 * fake stands in for a DOM type the source declares.
 */
export function instanceOf<T>(ctor: new (...args: never[]) => T, value: unknown): T {
  if (!(value instanceof ctor)) {
    throw new Error(`expected a ${ctor.name}, got ${String(value)}`);
  }
  return value;
}
