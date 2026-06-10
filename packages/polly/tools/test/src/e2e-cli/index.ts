/**
 * @fairfox/polly/test/e2e-cli — end-to-end test kit for the polly CLI.
 *
 * Drives `cli/polly.ts` from this checkout against throwaway temp projects:
 * scaffold with `polly init`, wire the scaffold's `@fairfox/polly`
 * dependency to the working tree, and build — proving the first thing a new
 * user does works cold, without a published release on the path.
 */

export { POLLY_PKG_DIR, type RunOptions, type RunResult, runBun, runCli } from "./run-cli";
export { type TempDir, withTempDir } from "./with-temp-dir";
