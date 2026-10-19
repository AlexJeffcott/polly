/** A throwaway project on disk, for tests that must run the real `bun test`. */
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

export interface FixtureProject {
  dir: string;
  path(rel: string): string;
  remove(): void;
}

export function createFixtureProject(
  prefix: string,
  files: Record<string, string>
): FixtureProject {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(dir, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content);
  }
  return {
    dir,
    path: (rel) => join(dir, rel),
    remove: () => rmSync(dir, { recursive: true, force: true }),
  };
}
