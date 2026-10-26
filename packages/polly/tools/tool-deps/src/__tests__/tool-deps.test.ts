import { describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { isRecord, readRecord } from "../../../../src/shared/lib/guards.ts";
import {
  COMMAND_TOOL_PACKAGES,
  commandToolPackages,
  installCommand,
  isMissingPackageError,
  loadToolPackage,
  MissingToolPackageError,
  MUTATE_FEATURE,
  missingToolPackages,
  missingToolPackagesMessage,
  RUNTIME_PEERS,
  type RuntimePeer,
  TOOL_PACKAGES,
  type ToolPackage,
  VISUALIZE_SNAPSHOT_FEATURE,
} from "../index.ts";

const packageRoot = join(import.meta.dir, "../../../..");
const ALL = Object.keys(TOOL_PACKAGES).filter((k): k is ToolPackage => k in TOOL_PACKAGES);

async function manifest(): Promise<Record<string, unknown>> {
  const parsed: unknown = await Bun.file(join(packageRoot, "package.json")).json();
  if (!isRecord(parsed)) throw new Error("package.json is not an object");
  return parsed;
}

describe("package.json agrees with TOOL_PACKAGES", () => {
  test("no tool package is a runtime dependency", async () => {
    const deps = readRecord((await manifest())["dependencies"]) ?? {};
    for (const p of ALL) expect(deps[p]).toBeUndefined();
  });

  test("each is an optional peer and a devDependency at the install version", async () => {
    const m = await manifest();
    const dev = readRecord(m["devDependencies"]) ?? {};
    const peers = readRecord(m["peerDependencies"]) ?? {};
    const meta = readRecord(m["peerDependenciesMeta"]) ?? {};
    for (const p of ALL) {
      const install = TOOL_PACKAGES[p].install;
      expect(`${p}@${dev[p]}`).toBe(install);
      expect(peers[p]).toBeDefined();
      expect(readRecord(meta[p])?.["optional"]).toBe(true);
    }
  });

  test("each runtime peer is an optional peer and a devDependency at the install version", async () => {
    const m = await manifest();
    const dev = readRecord(m["devDependencies"]) ?? {};
    const peers = readRecord(m["peerDependencies"]) ?? {};
    const meta = readRecord(m["peerDependenciesMeta"]) ?? {};
    const runtime = Object.keys(RUNTIME_PEERS).filter((k): k is RuntimePeer => k in RUNTIME_PEERS);
    for (const p of runtime) {
      expect(`${p}@${dev[p]}`).toBe(RUNTIME_PEERS[p].install);
      expect(peers[p]).toBeDefined();
      expect(readRecord(meta[p])?.["optional"]).toBe(true);
    }
  });
});

describe("messages", () => {
  test("installCommand names exact versions for bun and npm", () => {
    expect(installCommand(["typescript-7"])).toBe(
      "bun add -d typescript-7@npm:typescript@7.1.0-beta"
    );
    expect(installCommand(["oxc-parser", "weapon-regex"], "npm")).toBe(
      "npm install -D oxc-parser@0.137.0 weapon-regex@1.3.6"
    );
  });

  test("the missing-package message names the feature, the packages and both commands", () => {
    const msg = missingToolPackagesMessage("polly bdd", [
      "@cucumber/gherkin",
      "@cucumber/messages",
    ]);
    expect(msg).toContain(
      "polly bdd needs @cucumber/gherkin and @cucumber/messages, which are not installed."
    );
    expect(msg).toContain("bun add -d @cucumber/gherkin@42.0.1 @cucumber/messages@34.2.1");
    expect(msg).toContain("npm install -D @cucumber/gherkin@42.0.1 @cucumber/messages@34.2.1");
    expect(missingToolPackagesMessage("polly visualize", ["typescript-7"])).toContain(
      "polly visualize needs typescript-7, which is not installed."
    );
  });

  test("a runtime-peer message says they are optional peers, not tool packages", () => {
    const msg = missingToolPackagesMessage(
      VISUALIZE_SNAPSHOT_FEATURE.name,
      VISUALIZE_SNAPSHOT_FEATURE.packages
    );
    expect(msg).toContain(
      "polly visualize --snapshot needs tweetnacl and @automerge/automerge-repo, which are not installed."
    );
    expect(msg).toContain(
      "@fairfox/polly lists tweetnacl and @automerge/automerge-repo as optional peer dependencies"
    );
    expect(msg).not.toContain("tool packages");
    expect(msg).toContain("bun add -d tweetnacl@1.0.3 @automerge/automerge-repo@2.5.6");
    expect(msg).toContain("npm install -D tweetnacl@1.0.3 @automerge/automerge-repo@2.5.6");
    expect(missingToolPackagesMessage("polly visualize --snapshot", ["tweetnacl"])).toContain(
      "so it is not installed with it."
    );
  });

  test("a flag adds its packages: verify needs gherkin only with --witness", () => {
    expect(commandToolPackages("verify", [])).toEqual(["typescript-7"]);
    expect(commandToolPackages("verify", ["--witness"])).toEqual([
      "typescript-7",
      "@cucumber/gherkin",
      "@cucumber/messages",
    ]);
    expect(commandToolPackages("bdd", ["--witness"])).toEqual([
      "@cucumber/gherkin",
      "@cucumber/messages",
    ]);
    expect(commandToolPackages("init", [])).toEqual([]);
  });

  test("every command lists only known packages", () => {
    for (const pkgs of Object.values(COMMAND_TOOL_PACKAGES)) {
      for (const p of pkgs) expect(TOOL_PACKAGES[p]).toBeDefined();
    }
  });
});

describe("missingToolPackages", () => {
  test("finds nothing missing from polly's own directory (devDependencies installed)", () => {
    expect(missingToolPackages(ALL, import.meta.dir)).toEqual([]);
  });

  test("reports every package missing from a directory with an empty node_modules", () => {
    const dir = mkdtempSync(join(tmpdir(), "polly-tool-deps-"));
    try {
      // A node_modules directory stops bun's auto-install from fetching the package.
      mkdirSync(join(dir, "node_modules"));
      expect(missingToolPackages(ALL, dir)).toEqual(ALL);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});

describe("loadToolPackage", () => {
  test("returns the module when the load succeeds", async () => {
    const mod = await loadToolPackage("weapon-regex", MUTATE_FEATURE, () => import("weapon-regex"));
    expect(typeof mod.mutate).toBe("function");
  });

  test("turns a module-not-found for that package into MissingToolPackageError", async () => {
    const notFound = Object.assign(new Error("Cannot find package 'oxc-parser' imported from x"), {
      code: "ERR_MODULE_NOT_FOUND",
    });
    const load = loadToolPackage("oxc-parser", MUTATE_FEATURE, () => Promise.reject(notFound));
    await expect(load).rejects.toBeInstanceOf(MissingToolPackageError);
    // weapon-regex, the feature's other package, is installed here, so only oxc-parser is named.
    await expect(load).rejects.toThrow(
      "@fairfox/polly/mutate needs oxc-parser, which is not installed."
    );
    await expect(load).rejects.toThrow("bun add -d oxc-parser@0.137.0\n");
  });

  test("rethrows any other failure unchanged", async () => {
    const other = new Error("boom");
    const load = loadToolPackage("oxc-parser", MUTATE_FEATURE, () => Promise.reject(other));
    await expect(load).rejects.toBe(other);
  });

  test("a real failed import of an absent package is recognised", async () => {
    const dir = mkdtempSync(join(tmpdir(), "polly-tool-deps-"));
    try {
      mkdirSync(join(dir, "node_modules"));
      const file = join(dir, "probe.mjs");
      await Bun.write(
        file,
        `try { await import("oxc-parser"); } catch (e) { console.log(JSON.stringify({ code: e.code, message: e.message })); }`
      );
      const out = Bun.spawnSync(["bun", file], { cwd: dir }).stdout.toString();
      const parsed: unknown = JSON.parse(out);
      expect(isMissingPackageError(parsed, "oxc-parser")).toBe(true);
      expect(isMissingPackageError(parsed, "weapon-regex")).toBe(false);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  test("isMissingPackageError rejects non-objects and other codes", () => {
    expect(isMissingPackageError("oxc-parser", "oxc-parser")).toBe(false);
    expect(isMissingPackageError({ code: "EACCES", message: "oxc-parser" }, "oxc-parser")).toBe(
      false
    );
    expect(
      isMissingPackageError(
        { code: "MODULE_NOT_FOUND", message: "Cannot find module 'oxc-parser'" },
        "oxc-parser"
      )
    ).toBe(true);
  });
});
