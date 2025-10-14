import type { ExtensionMessage, RoutedMessage } from "@fairfox/web-ext/types";

/**
 * Test utilities for extension testing
 */

export function createMockRoutedMessage<T extends ExtensionMessage>(
  payload: T,
  overrides?: Partial<Omit<RoutedMessage<T>, "payload">>
): RoutedMessage<T> {
  return {
    id: overrides?.id || `msg-${Date.now()}-${Math.random()}`,
    source: overrides?.source || "background",
    targets: overrides?.targets || ["content"],
    tabId: overrides?.tabId,
    timestamp: overrides?.timestamp || Date.now(),
    payload,
  };
}

export function waitFor(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

export async function waitForCondition(
  condition: () => boolean,
  timeout = 1000,
  interval = 10
): Promise<void> {
  const startTime = Date.now();
  while (!condition()) {
    if (Date.now() - startTime > timeout) {
      throw new Error("Condition not met within timeout");
    }
    await waitFor(interval);
  }
}

export function expectType<T>(_value: T): void {
  // Type assertion helper for compile-time checks
}

/**
 * No-op function for mocks that don't need to do anything
 * Use this instead of empty arrow functions to satisfy linter
 */
// biome-ignore lint/suspicious/noEmptyBlockStatements: intentional no-op for mocks
export function noOp(): void {}

/**
 * Async no-op function for async mocks that don't need to do anything
 * Use this instead of empty async arrow functions to satisfy linter
 */
// biome-ignore lint/suspicious/noEmptyBlockStatements: intentional no-op for mocks
export async function noOpAsync(): Promise<void> {}
