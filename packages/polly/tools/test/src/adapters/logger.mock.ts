// Mock logger adapter for testing
import type { LoggerAdapter } from "@/shared/adapters/logger.adapter";
import type { LogLevel } from "@/shared/types/messages";

export interface LogCall {
  level: LogLevel;
  message: string;
  context?: Record<string, unknown>;
  error?: Error;
  timestamp: number;
}

export interface MockLogger extends LoggerAdapter {
  _calls: LogCall[];
  _clear(): void;
}

export function createMockLogger(options?: { silent?: boolean }): MockLogger {
  const calls: LogCall[] = [];
  const silent = options?.silent ?? true;

  const logToConsole = (level: LogLevel, message: string, context?: Record<string, unknown>) => {
    if (!silent) {
      // biome-ignore lint/suspicious/noConsole: Mock logger intentionally uses console for testing
      const consoleMethod = level === "debug" ? console.log : console[level];
      consoleMethod(message, context);
    }
  };

  return {
    debug(message: string, context?: Record<string, unknown>): void {
      calls.push({
        level: "debug",
        message,
        ...(context && { context }),
        timestamp: Date.now(),
      });
      logToConsole("debug", message, context);
    },

    info(message: string, context?: Record<string, unknown>): void {
      calls.push({
        level: "info",
        message,
        ...(context && { context }),
        timestamp: Date.now(),
      });
      logToConsole("info", message, context);
    },

    warn(message: string, context?: Record<string, unknown>): void {
      calls.push({
        level: "warn",
        message,
        ...(context && { context }),
        timestamp: Date.now(),
      });
      logToConsole("warn", message, context);
    },

    error(message: string, error?: Error, context?: Record<string, unknown>): void {
      calls.push({
        level: "error",
        message,
        ...(error && { error }),
        ...(context && { context }),
        timestamp: Date.now(),
      });
      logToConsole("error", message, { ...context, error });
    },

    log(level: LogLevel, message: string, context?: Record<string, unknown>): void {
      calls.push({
        level,
        message,
        ...(context && { context }),
        timestamp: Date.now(),
      });
      logToConsole(level, message, context);
    },

    // Test-only internals
    _calls: calls,
    _clear() {
      calls.length = 0;
    },
  };
}
