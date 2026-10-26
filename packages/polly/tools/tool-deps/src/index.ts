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
 * {@link RUNTIME_PEERS} lists optional runtime peers that a tool loads only
 * for one feature, through the same {@link loadToolPackage}.
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

/**
 * Optional runtime peers a tool loads only for one feature. These are not
 * tool packages: the mesh runtime imports them, so a mesh app has them
 * already. `polly visualize --snapshot` needs them to resolve a mesh key to
 * its document id; a plain `polly visualize` does not load them.
 */
export const RUNTIME_PEERS = {
  tweetnacl: { install: "tweetnacl@1.0.3", probe: "tweetnacl" },
  "@automerge/automerge-repo": {
    install: "@automerge/automerge-repo@2.5.6",
    probe: "@automerge/automerge-repo/slim",
  },
} as const;

export type RuntimePeer = keyof typeof RUNTIME_PEERS;

/** Any optional peer a tool can report missing. */
export type OptionalPeer = ToolPackage | RuntimePeer;

const OPTIONAL_PEERS: Record<OptionalPeer, { install: string; probe: string }> = {
  ...TOOL_PACKAGES,
  ...RUNTIME_PEERS,
};

function isRuntimePeer(p: OptionalPeer): p is RuntimePeer {
  return p in RUNTIME_PEERS;
}

const GHERKIN: readonly ToolPackage[] = ["@cucumber/gherkin", "@cucumber/messages"];

/**
 * The packages each `polly` command loads at start-up. `polly mutate` also
 * uses `typescript-7` for its type filter, but runs without it (the filter
 * switches off and says so), so it is not listed.
 */
export const COMMAND_TOOL_PACKAGES: Readonly<Record<string, readonly ToolPackage[]>> = {
  visualize: ["typescript-7"],
  verify: ["typescript-7"],
  mutate: ["oxc-parser", "weapon-regex"],
  bdd: GHERKIN,
};

/** Packages a flag adds to its command's start-up set: `polly verify --witness` parses features. */
export const FLAG_TOOL_PACKAGES: Readonly<
  Record<string, Readonly<Record<string, readonly ToolPackage[]>>>
> = {
  verify: { "--witness": GHERKIN },
};

/** The packages `polly <command> <args>` loads: the command's own, plus those of each flag given. */
export function commandToolPackages(command: string, args: readonly string[]): ToolPackage[] {
  const packages = new Set(COMMAND_TOOL_PACKAGES[command] ?? []);
  for (const [flag, extra] of Object.entries(FLAG_TOOL_PACKAGES[command] ?? {})) {
    if (args.includes(flag)) for (const p of extra) packages.add(p);
  }
  return [...packages];
}

/** `bun add -d <pkg>@<version> ...` for the given packages. */
export function installCommand(
  packages: readonly OptionalPeer[],
  manager: "bun" | "npm" = "bun"
): string {
  const specs = packages.map((p) => OPTIONAL_PEERS[p].install).join(" ");
  return manager === "bun" ? `bun add -d ${specs}` : `npm install -D ${specs}`;
}

/**
 * The message for a feature that cannot run because packages are missing.
 * `feature` names what the user ran: `polly visualize`, `@fairfox/polly/bdd`.
 */
export function missingToolPackagesMessage(
  feature: string,
  missing: readonly OptionalPeer[]
): string {
  const names = [...missing];
  const last = names.pop() ?? "";
  const list = names.length === 0 ? last : `${names.join(", ")} and ${last}`;
  const verb = missing.length === 1 ? "is" : "are";
  const why = missing.some(isRuntimePeer)
    ? `@fairfox/polly lists ${list} as optional peer dependencies (its mesh runtime loads them), so ${missing.length === 1 ? "it is" : "they are"} not installed with it.`
    : "@fairfox/polly lists its tool packages as optional peer dependencies, so they are not installed with it.";
  return [
    `${feature} needs ${list}, which ${verb} not installed.`,
    why,
    "Add them as dev dependencies:",
    `  ${installCommand(missing, "bun")}`,
    `  (npm: ${installCommand(missing, "npm")})`,
  ].join("\n");
}

/** Thrown when an optional tool package cannot be found. `message` says what to install. */
export class MissingToolPackageError extends Error {
  readonly feature: string;
  readonly missing: readonly OptionalPeer[];
  constructor(feature: string, missing: readonly OptionalPeer[], cause?: unknown) {
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

/**
 * Exit 1 with the install message when a package `polly <command> <args>`
 * loads is missing. Each tool's cli.ts calls this before it imports main.ts,
 * whose static imports would otherwise fail first with a bare "Cannot find
 * module". `fromDir` is the calling tool's directory.
 */
export function exitIfMissingToolPackages(
  command: string,
  args: readonly string[],
  fromDir: string
): void {
  const missing = missingToolPackages(commandToolPackages(command, args), fromDir);
  if (missing.length === 0) return;
  const flags = Object.keys(FLAG_TOOL_PACKAGES[command] ?? {}).filter((f) => args.includes(f));
  const feature = ["polly", command, ...flags].join(" ");
  process.stderr.write(`❌ ${missingToolPackagesMessage(feature, missing)}\n`);
  process.exit(1);
}

/** True when `error` is a module-not-found for `pkg` (bun and node both use ERR_MODULE_NOT_FOUND). */
export function isMissingPackageError(error: unknown, pkg: OptionalPeer): boolean {
  if (!isRecord(error)) return false;
  const code = readString(error["code"]);
  if (code !== "ERR_MODULE_NOT_FOUND" && code !== "MODULE_NOT_FOUND") return false;
  const text = `${readString(error["message"]) ?? ""} ${readString(error["specifier"]) ?? ""}`;
  return text.includes(pkg);
}

/** A library entry point (or tool feature) and every optional package it loads. */
export interface ToolFeature {
  name: string;
  packages: readonly OptionalPeer[];
}

export const BDD_FEATURE: ToolFeature = { name: "@fairfox/polly/bdd", packages: GHERKIN };
export const MUTATE_FEATURE: ToolFeature = {
  name: "@fairfox/polly/mutate",
  packages: COMMAND_TOOL_PACKAGES["mutate"] ?? [],
};
/** `polly visualize --snapshot`: the runtime peers that derive a mesh document id. */
export const VISUALIZE_SNAPSHOT_FEATURE: ToolFeature = {
  name: "polly visualize --snapshot",
  packages: ["tweetnacl", "@automerge/automerge-repo"],
};

/**
 * The feature's packages that fail to import. Runs under node as well as
 * bun (a library import), so it imports rather than calling Bun's resolver;
 * the specifiers resolve from this module, inside the same node_modules
 * chain as the module that asked.
 */
async function missingByImport(packages: readonly OptionalPeer[]): Promise<OptionalPeer[]> {
  const missing: OptionalPeer[] = [];
  for (const p of packages) {
    try {
      await import(OPTIONAL_PEERS[p].probe);
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
  pkg: OptionalPeer,
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
