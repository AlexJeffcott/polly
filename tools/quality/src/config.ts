/**
 * Loader for the `quality` block of `polly.config.ts`.
 *
 * Consumers express their plugin set as
 *
 *   export default {
 *     quality: {
 *       plugins: [pollyCorePlugin, pollyUiPlugin, localPlugin],
 *       checks: { "polly:no-as-casting": { exclude: ["build"] } },
 *     },
 *   };
 *
 * If no config is found, the loader returns `pollyCorePlugin` only —
 * that's the minimum useful default and matches the surface every
 * polly consumer already gets.
 */

import { join } from "node:path";
import { pollyCorePlugin } from "./plugins/core";
import type { QualityRunConfig } from "./types";

const DEFAULT_PATHS = ["polly.config.ts", "polly.config.js", "polly.config.mjs"];

export async function loadQualityConfig(
  rootDir: string,
  explicitPath?: string
): Promise<QualityRunConfig> {
  const candidates = explicitPath ? [explicitPath] : DEFAULT_PATHS.map((p) => join(rootDir, p));

  for (const path of candidates) {
    if (!(await Bun.file(path).exists())) continue;
    const mod = (await import(path)) as unknown as { default?: { quality?: QualityRunConfig } };
    const config = mod.default?.quality;
    if (!config) continue;
    if (!Array.isArray(config.plugins) || config.plugins.length === 0) {
      throw new Error(`${path}: \`quality.plugins\` must be a non-empty array`);
    }
    return config;
  }

  return { plugins: [pollyCorePlugin] };
}
