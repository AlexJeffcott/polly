/**
 * `polly mutate init` — scaffold a `polly.mutate.ts` for a project: targets
 * from `src/` (or the whole tree), tests from `tests/` or `test/`. The import
 * specifier comes from `defineImportSpecifier`, so the file resolves in a
 * consumer project and in polly's own tree alike.
 */
import { existsSync } from "node:fs";
import { join } from "node:path";
import { MUTATION_CONFIG_FILE, type MutationConfig } from "./define.ts";
import { defineImportSpecifier, renderMutationConfig } from "./migrate.ts";

export interface InitResult {
  configPath: string;
  /** false when a config already existed and --force was not passed. */
  created: boolean;
  /** Where `defineMutation` is imported from. */
  specifier: string;
  mutate: string[];
  testGlob: string;
  warnings: string[];
}

function detectMutate(projectDir: string): string[] {
  if (existsSync(join(projectDir, "src"))) {
    return ["src/**/*.ts", "!src/**/*.test.ts", "!src/**/*.d.ts"];
  }
  return ["**/*.ts", "!**/*.test.ts", "!**/*.d.ts", "!dist/**", `!${MUTATION_CONFIG_FILE}`];
}

function detectTestGlob(projectDir: string): string {
  for (const d of ["tests", "test"]) {
    if (existsSync(join(projectDir, d))) return `${d}/**/*.test.ts`;
  }
  return "**/*.test.ts";
}

export async function initConfig(
  projectDir: string,
  opts: { force?: boolean } = {}
): Promise<InitResult> {
  const configPath = join(projectDir, MUTATION_CONFIG_FILE);
  const warnings: string[] = [];
  const specifier = defineImportSpecifier(projectDir);
  if (specifier === "@fairfox/polly/mutate") {
    try {
      Bun.resolveSync(specifier, projectDir);
    } catch {
      warnings.push("@fairfox/polly does not resolve here — install it, or the config cannot load");
    }
  }

  const mutate = detectMutate(projectDir);
  const testGlob = detectTestGlob(projectDir);
  if (!existsSync(join(projectDir, "src"))) {
    warnings.push("no src/ directory — adjust `targets` to point at your source");
  }
  if (!existsSync(join(projectDir, "tests")) && !existsSync(join(projectDir, "test"))) {
    warnings.push(`no tests/ directory — using "${testGlob}"; adjust tests.include if needed`);
  }

  if (existsSync(configPath) && !opts.force) {
    return { configPath, created: false, specifier, mutate, testGlob, warnings };
  }
  const config: MutationConfig = { targets: mutate, tests: { include: [testGlob] } };
  await Bun.write(configPath, renderMutationConfig(config, specifier));
  return { configPath, created: true, specifier, mutate, testGlob, warnings };
}
