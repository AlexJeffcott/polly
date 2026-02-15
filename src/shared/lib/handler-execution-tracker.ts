// Runtime handler execution tracking to prevent double-execution bugs
// Only active in development mode, zero runtime cost in production

export class HandlerExecutionTracker {
  private executions = new Map<string, Map<string, number>>(); // messageId → handlerType → count
  private readonly isDevelopment: boolean;

  constructor() {
    // Check if we're in development mode or test mode
    this.isDevelopment =
      typeof process !== "undefined" &&
      (process.env?.NODE_ENV === "development" || process.env?.NODE_ENV === "test");
  }

  /**
   * Track a handler execution. Throws error if handler executes multiple times
   * for the same message ID.
   *
   * @param messageId - Unique message identifier
   * @param handlerType - Handler type (e.g., 'TODO_ADD')
   * @throws Error if handler already executed for this message
   */
  track(messageId: string, handlerType: string): void {
    if (!this.isDevelopment) return;

    let handlerCounts = this.executions.get(messageId);
    if (!handlerCounts) {
      handlerCounts = new Map();
      this.executions.set(messageId, handlerCounts);
    }

    const count = (handlerCounts.get(handlerType) || 0) + 1;
    handlerCounts.set(handlerType, count);

    if (count > 1) {
      const error = new Error(
        `🔴 DOUBLE EXECUTION DETECTED\n\nHandler "${handlerType}" executed ${count} times for message ${messageId}.\n\nThis indicates multiple chrome.runtime.onMessage listeners are registered.\nCommon causes:\n  1. Both MessageBus and MessageRouter registered listeners\n  2. createBackground() called multiple times\n  3. Handler registered in multiple places\n\nFix: Ensure only ONE listener is registered. In background scripts,\nuse createBackground() instead of getMessageBus().\n`
      );

      console.error(error);

      // Also log the execution trace
      console.error("Execution trace for message:", messageId);
      console.error(Array.from(handlerCounts.entries()));

      throw error;
    }

    // Cleanup old messages after 5 seconds to prevent memory leak
    setTimeout(() => {
      this.executions.delete(messageId);
    }, 5000);
  }

  /**
   * Reset all tracked executions. Useful for testing.
   */
  reset(): void {
    this.executions.clear();
  }

  /**
   * Get execution count for a specific message and handler.
   * Useful for testing.
   */
  getExecutionCount(messageId: string, handlerType: string): number {
    return this.executions.get(messageId)?.get(handlerType) || 0;
  }
}

// Global singleton instance
export const globalExecutionTracker = new HandlerExecutionTracker();
