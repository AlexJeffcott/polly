import { describe, expect, test } from "bun:test";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  type CheckOutcome,
  computeInputsHash,
  getCachedOutcome,
  setCachedOutcome,
} from "@fairfox/polly/quality";

async function tmp(): Promise<string> {
  return mkdtemp(join(tmpdir(), "polly-cache-"));
}

describe("computeInputsHash", () => {
  test("identical inputs in different orders hash to the same value", async () => {
    const root = await tmp();
    await writeFile(join(root, "a.txt"), "alpha");
    await writeFile(join(root, "b.txt"), "beta");

    const h1 = await computeInputsHash(
      { files: [join(root, "a.txt"), join(root, "b.txt")], extras: { mode: "x", env: "y" } },
      root
    );
    const h2 = await computeInputsHash(
      { files: [join(root, "b.txt"), join(root, "a.txt")], extras: { env: "y", mode: "x" } },
      root
    );
    expect(h1).toBe(h2);
    await rm(root, { recursive: true });
  });

  test("changing file content changes the hash", async () => {
    const root = await tmp();
    await writeFile(join(root, "a.txt"), "alpha");
    const before = await computeInputsHash({ files: [join(root, "a.txt")] }, root);
    await writeFile(join(root, "a.txt"), "alpha-modified");
    const after = await computeInputsHash({ files: [join(root, "a.txt")] }, root);
    expect(before).not.toBe(after);
    await rm(root, { recursive: true });
  });

  test("a missing input is hashed deterministically as <absent>", async () => {
    const root = await tmp();
    const ghost = join(root, "does-not-exist.txt");
    const h1 = await computeInputsHash({ files: [ghost] }, root);
    const h2 = await computeInputsHash({ files: [ghost] }, root);
    expect(h1).toBe(h2);
    await rm(root, { recursive: true });
  });

  test("changing extras changes the hash", async () => {
    const root = await tmp();
    const h1 = await computeInputsHash({ files: [], extras: { tool: "1.0" } }, root);
    const h2 = await computeInputsHash({ files: [], extras: { tool: "1.1" } }, root);
    expect(h1).not.toBe(h2);
    await rm(root, { recursive: true });
  });
});

describe("get/setCachedOutcome", () => {
  const outcome: CheckOutcome = { ok: true, messages: ["all good"] };

  test("set then get returns the stored outcome on hash match", async () => {
    const root = await tmp();
    await setCachedOutcome(root, "polly:test", "abc123", outcome);
    const got = await getCachedOutcome(root, "polly:test", "abc123");
    expect(got).toEqual(outcome);
    await rm(root, { recursive: true });
  });

  test("hash mismatch returns null", async () => {
    const root = await tmp();
    await setCachedOutcome(root, "polly:test", "abc123", outcome);
    const got = await getCachedOutcome(root, "polly:test", "different");
    expect(got).toBeNull();
    await rm(root, { recursive: true });
  });

  test("missing entry returns null", async () => {
    const root = await tmp();
    const got = await getCachedOutcome(root, "polly:test", "abc123");
    expect(got).toBeNull();
    await rm(root, { recursive: true });
  });

  test("corrupt entry is treated as a miss", async () => {
    const root = await tmp();
    await setCachedOutcome(root, "polly:test", "abc123", outcome);
    const cachePath = join(root, ".cache", "polly-quality", "polly__test.json");
    await writeFile(cachePath, "{ this is not valid JSON");
    const got = await getCachedOutcome(root, "polly:test", "abc123");
    expect(got).toBeNull();
    await rm(root, { recursive: true });
  });

  test("namespaced ids are written to a filename without colons", async () => {
    const root = await tmp();
    await setCachedOutcome(root, "polly:no-as-casting", "h", outcome);
    const path = join(root, ".cache", "polly-quality", "polly__no-as-casting.json");
    const raw = await readFile(path, "utf8");
    expect(raw).toContain('"hash"');
    await rm(root, { recursive: true });
  });
});
