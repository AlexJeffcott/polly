/**
 * Optional tool packages: the packages only polly's authoring tools load.
 *
 * `typescript-7`, `oxc-parser`, `weapon-regex`, `@cucumber/gherkin` and
 * `@cucumber/messages` are optional peer dependencies of @fairfox/polly, so a
 * consumer's production install does not carry them. Each place that loads
 * one goes through this module, which turns a module-not-found into a
 * message naming the polly command (or entry point), the missing packages and
 * the command that installs them.
 *
 *   - The `polly` CLI calls {@link missingToolPackages} before it spawns a
 *     tool, and prints {@link missingToolPackagesMessage} and exits 1.
 *   - Library modules (`@fairfox/polly/mutate`, `@fairfox/polly/bdd`) load the
 *     package with a top-level `await loadToolPackage(...)`, which throws a
 *     {@link MissingToolPackageError} carrying the same message.
 *
 * The versions here must match packages/polly/package.json (devDependencies
 * and peerDependencies); a unit test holds them together.
 */
import { isRecord, readString } from "../../../src/shared/lib/guards.ts";

/** Each optional tool package: the version polly develops against, and a specifier that resolves when it is installed. */
export const TOOL_PACKAGES = {
  "typescript-7": {
    install: "typescript-7@npm:typescript@7.1.0-beta",
    probe: "typescript-7/async",
  },
  "oxc-parser": { install: "oxc-parser@0.137.0", probe: "oxc-parser" },
  "weapon-regex": { install: "weapon-regex@1.3.6", probe: "weapon-regex" },
  "@cucumber/gherkin": { install: "@cucumber/gherkin@42.0.1", probe: "@cucumber/gherkin" },
  "@cucumber/messages": { install: "@cucumber/messages@34.2.1", probe: "@cucumber/messages" },
} as const;

export type ToolPackage = keyof typeof TOOL_PACKAGES;

const GHERKIN: readonly ToolPackage[] = ["@cucumber/gherkin", "@cucumber/messages"];

/**
 * The packages each `polly` command loads at start-up. `polly mutate` also
 * uses `typescript-7` for its type filter, but runs without it (the filter
 * switches off and says so), so it is not listed.
 */
export const COMMAND_TOOL_PACKAGES: Readonly<Record<string, readonly ToolPackage[]>> = {
  visualize: ["typescript-7"],
  verify: ["typescript-7", ...GHERKIN],
  mutate: ["oxc-parser", "weapon-regex"],
  bdd: GHERKIN,
};

/** `bun add -d <pkg>@<version> ...` for the given packages. */
export function installCommand(
  packages: readonly ToolPackage[],
  manager: "bun" | "npm" = "bun"
): string {
  const specs = packages.map((p) => TOOL_PACKAGES[p].install).join(" ");
  return manager === "bun" ? `bun add -d ${specs}` : `npm install -D ${specs}`;
}

/**
 * The message for a feature that cannot run because packages are missing.
 * `feature` names what the user ran: `polly visualize`, `@fairfox/polly/bdd`.
 */
export function missingToolPackagesMessage(
  feature: string,
  missing: readonly ToolPackage[]
): string {
  const names = [...missing];
  const last = names.pop() ?? "";
  const list = names.length === 0 ? last : `${names.join(", ")} and ${last}`;
  const verb = missing.length === 1 ? "is" : "are";
  return [
    `${feature} needs ${list}, which ${verb} not installed.`,
    "@fairfox/polly lists its tool packages as optional peer dependencies, so they are not installed with it.",
    "Add them as dev dependencies:",
    `  ${installCommand(missing, "bun")}`,
    `  (npm: ${installCommand(missing, "npm")})`,
  ].join("\n");
}

/** Thrown when an optional tool package cannot be found. `message` says what to install. */
export class MissingToolPackageError extends Error {
  readonly feature: string;
  readonly missing: readonly ToolPackage[];
  constructor(feature: string, missing: readonly ToolPackage[], cause?: unknown) {
    super(missingToolPackagesMessage(feature, missing), { cause });
    this.name = "MissingToolPackageError";
    this.feature = feature;
    this.missing = missing;
  }
}

/**
 * The packages in `packages` that do not resolve from `fromDir` (the
 * directory of the code that would import them, so the lookup walks the same
 * node_modules chain the import would). Bun's resolver, with the `import`
 * condition: `weapon-regex` exports nothing for `require`, so
 * `createRequire(...).resolve` would call it missing when it is installed.
 */
export function missingToolPackages(
  packages: readonly ToolPackage[],
  fromDir: string
): ToolPackage[] {
  return packages.filter((p) => {
    try {
      Bun.resolveSync(TOOL_PACKAGES[p].probe, fromDir);
      return false;
    } catch {
      return true;
    }
  });
}

/** True when `error` is a module-not-found for `pkg` (bun and node both use ERR_MODULE_NOT_FOUND). */
export function isMissingPackageError(error: unknown, pkg: ToolPackage): boolean {
  if (!isRecord(error)) return false;
  const code = readString(error["code"]);
  if (code !== "ERR_MODULE_NOT_FOUND" && code !== "MODULE_NOT_FOUND") return false;
  const text = `${readString(error["message"]) ?? ""} ${readString(error["specifier"]) ?? ""}`;
  return text.includes(pkg);
}

/** A library entry point and every tool package it loads. */
export interface ToolFeature {
  name: string;
  packages: readonly ToolPackage[];
}

export const BDD_FEATURE: ToolFeature = { name: "@fairfox/polly/bdd", packages: GHERKIN };
export const MUTATE_FEATURE: ToolFeature = {
  name: "@fairfox/polly/mutate",
  packages: COMMAND_TOOL_PACKAGES["mutate"] ?? [],
};

/**
 * The feature's packages that fail to import. Runs under node as well as
 * bun (a library import), so it imports rather than calling Bun's resolver;
 * the specifiers resolve from this module, inside the same node_modules
 * chain as the module that asked.
 */
async function missingByImport(packages: readonly ToolPackage[]): Promise<ToolPackage[]> {
  const missing: ToolPackage[] = [];
  for (const p of packages) {
    try {
      await import(TOOL_PACKAGES[p].probe);
    } catch (error) {
      if (isMissingPackageError(error, p)) missing.push(p);
    }
  }
  return missing;
}

/**
 * Load an optional tool package. `load` is the literal `() => import("...")`,
 * so the bundler keeps the specifier external and the result stays typed.
 * A missing package becomes a {@link MissingToolPackageError} that lists
 * every package of `feature` that is missing, not only the first to fail;
 * any other failure is rethrown as it is.
 */
export async function loadToolPackage<T>(
  pkg: ToolPackage,
  feature: ToolFeature,
  load: () => Promise<T>
): Promise<T> {
  try {
    return await load();
  } catch (error) {
    if (!isMissingPackageError(error, pkg)) throw error;
    const others = (await missingByImport(feature.packages)).filter((p) => p !== pkg);
    throw new MissingToolPackageError(feature.name, [pkg, ...others], error);
  }
}
