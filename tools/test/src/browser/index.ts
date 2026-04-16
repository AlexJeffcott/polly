/**
 * @fairfox/polly/test/browser — browser-side test harness for Polly
 * applications.
 *
 * Provides a lightweight describe/test/expect harness that runs inside a
 * Puppeteer-launched browser tab. Results are recorded on window.__testResults
 * and polled by the companion runner (run.ts). Applications import this
 * module in their *.browser.ts test files and call done() at the end.
 *
 * @example
 * ```typescript
 * import { describe, test, expect, done, waitFor } from "@fairfox/polly/test/browser";
 *
 * describe("my feature", () => {
 *   test("works in a real browser", async () => {
 *     expect(1 + 1).toBe(2);
 *   });
 * });
 *
 * done();
 * ```
 *
 * The runner is at tools/test/src/browser/run.ts and is invoked via:
 *
 *   bun tools/test/src/browser/run.ts [filter]
 *
 * It bundles each test file with Bun.build (using an internal plugin that
 * redirects Automerge to the base64 WASM variant), serves it on an
 * ephemeral port, launches Puppeteer, and collects results. A signalling
 * server for WebRTC tests starts automatically.
 */

export { cleanup, describe, done, expect, flush, test, waitFor } from "./harness";
