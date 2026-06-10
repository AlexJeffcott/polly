/**
 * @fairfox/polly/test/e2e-cli — a throwaway working directory.
 *
 * CLI scripts scaffold and build inside a fresh temp dir so each run starts
 * from cold disk — the filesystem analogue of the mesh kit's fresh-profile
 * guarantee — and leaves nothing behind.
 */

import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

export interface TempDir {
  /** Absolute path to the fresh directory. */
  dir: string;
  /** Remove the directory and everything under it. Idempotent. */
  cleanup: () => void;
}

/** Create a fresh empty temp directory. */
export function withTempDir(prefix = "polly-e2e-cli-"): TempDir {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  return {
    dir,
    cleanup: () => {
      try {
        rmSync(dir, { recursive: true, force: true });
      } catch {
        // best effort
      }
    },
  };
}
