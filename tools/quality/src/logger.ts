/**
 * Logger for the quality tool.
 *
 * One mutable singleton so every check writes through the same sink.
 * Tests replace the methods to capture output, then call `resetLogger()`
 * to restore defaults. No dependency injection chain through every
 * check signature — the singleton pattern matches how Polly's own
 * CLI output is consumed (stdout/stderr at process edge).
 *
 *   import { logger, resetLogger } from "./logger";
 *   logger.error("…");
 *
 *   // in tests
 *   const captured: string[] = [];
 *   logger.error = (m) => captured.push(m);
 *   // ... run check ...
 *   resetLogger();
 */

export type QualityLogger = {
  log: (message: string) => void;
  error: (message: string) => void;
  info: (message: string) => void;
  warn: (message: string) => void;
};

function defaultLog(message: string): void {
  console.log(message);
}
function defaultError(message: string): void {
  // biome-ignore lint/suspicious/noConsole: CLI output is the whole point of the default sink.
  console.error(message);
}
function defaultInfo(message: string): void {
  // biome-ignore lint/suspicious/noConsole: CLI output is the whole point of the default sink.
  console.info(message);
}
function defaultWarn(message: string): void {
  // biome-ignore lint/suspicious/noConsole: CLI output is the whole point of the default sink.
  console.warn(message);
}

export const logger: QualityLogger = {
  log: defaultLog,
  error: defaultError,
  info: defaultInfo,
  warn: defaultWarn,
};

export function resetLogger(): void {
  logger.log = defaultLog;
  logger.error = defaultError;
  logger.info = defaultInfo;
  logger.warn = defaultWarn;
}
