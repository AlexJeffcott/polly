/**
 * `polly mutate init` — scaffold a `stryker.conf.json` for a project that
 * depends on @fairfox/polly, wired with the verify-primitive ignorer preset.
 *
 * The one fiddly bit is the plugin reference. Stryker's plugin loader resolves
 * specifiers from inside its OWN package, so the bare "@fairfox/polly/stryker"
 * only resolves on a flat node_modules layout. In a workspace (monorepo) or a
 * Bun-isolated install it must be referenced by path to the built file. We
 * resolve the actual plugin via Bun's resolver and pick the form that will load.
 */
import { existsSync } from "node:fs";
import { join, relative } from "node:path";

export interface InitResult {
  configPath: string;
  /** false when a config already existed and --force was not passed. */
  created: boolean;
  pluginRef: string;
  mutate: string[];
  testGlob: string;
  warnings: string[];
}

/**
 * The reference to write for the @fairfox/polly/stryker plugin: the bare
 * specifier when @fairfox/polly is hoisted into a flat node_modules (Stryker
 * resolves it), else a relative path to the built file (workspace / Bun-isolated).
 */
function resolvePluginRef(projectDir: string): string {
  const resolved = Bun.resolveSync("@fairfox/polly/stryker", projectDir);
  const hoisted = resolved.includes("/node_modules/") && !resolved.includes("/.bun/");
  return hoisted ? "@fairfox/polly/stryker" : relative(projectDir, resolved);
}

function detectMutate(projectDir: string): string[] {
  if (existsSync(join(projectDir, "src"))) {
    return ["src/**/*.ts", "!src/**/*.test.ts", "!src/**/*.d.ts"];
  }
  return ["**/*.ts", "!**/*.test.ts", "!**/*.d.ts", "!node_modules/**", "!dist/**"];
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
  const configPath = join(projectDir, "stryker.conf.json");
  const warnings: string[] = [];

  let pluginRef: string;
  try {
    pluginRef = resolvePluginRef(projectDir);
  } catch {
    throw new Error(
      "Cannot resolve @fairfox/polly from here. Run `polly mutate init` in a project that depends on @fairfox/polly."
    );
  }

  const mutate = detectMutate(projectDir);
  const testGlob = detectTestGlob(projectDir);
  if (!existsSync(join(projectDir, "src"))) {
    warnings.push("no src/ directory — adjust the `mutate` globs to point at your source");
  }
  if (!existsSync(join(projectDir, "tests")) && !existsSync(join(projectDir, "test"))) {
    warnings.push(`no tests/ directory — using "${testGlob}"; adjust bun.testFiles if needed`);
  }

  if (existsSync(configPath) && !opts.force) {
    return { configPath, created: false, pluginRef, mutate, testGlob, warnings };
  }

  // Note: redundancy/subsumption need the no-bail patched bun runner (disableBail
  // + coverageAnalysis "all"); without the patch the matrix is partial and
  // `polly mutate report` degrades to score + gaps + theatre.
  const config = {
    testRunner: "bun",
    bun: { testFiles: [testGlob], timeout: 30000 },
    plugins: ["stryker-mutator-bun-runner", pluginRef],
    ignorers: ["polly-verify"],
    coverageAnalysis: "all",
    disableBail: true,
    reporters: ["json", "clear-text"],
    mutate,
    thresholds: { high: 90, low: 70, break: null },
    ignorePatterns: [
      "**/node_modules/**",
      "**/dist/**",
      "**/.git/**",
      "**/.stryker-tmp/**",
      "**/reports/**",
    ],
    timeoutMS: 60000,
    concurrency: 4,
  };
  await Bun.write(configPath, `${JSON.stringify(config, null, 2)}\n`);
  return { configPath, created: true, pluginRef, mutate, testGlob, warnings };
}
