import { describe, expect, test } from "bun:test";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyCorePlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

async function runCheck(rootDir: string, id: string, config?: Record<string, unknown>) {
  const reg = registerPlugins([pollyCorePlugin]);
  const runConfig = config
    ? { plugins: [pollyCorePlugin], checks: { [id]: config } }
    : { plugins: [pollyCorePlugin] };
  return runChecks(reg, runConfig, [id], { rootDir, noCache: true });
}

describe("polly:no-banners", () => {
  test("passes on clean source", async () => {
    const root = await tmp("polly-cliche-banners-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "ok.ts"), `// section heading\nexport const x = 1;\n`);
    const report = await runCheck(root, "polly:no-banners");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("fails on a `// =====` divider", async () => {
    const root = await tmp("polly-cliche-banners-eq");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "bad.ts"),
      `// ============================================\n// HEADING\nexport const x = 1;\n`
    );
    const report = await runCheck(root, "polly:no-banners");
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("bad.ts:1"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("fails on a `// ─────` box-drawing divider", async () => {
    const root = await tmp("polly-cliche-banners-box");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "bad.ts"), `// ───────────────\nexport const x = 1;\n`);
    const report = await runCheck(root, "polly:no-banners");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("respects `// audit-allow: banner` line suppression", async () => {
    const root = await tmp("polly-cliche-banners-allow");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "ok.ts"),
      `// ───────── intentional divider ───────── // audit-allow: banner\nexport const x = 1;\n`
    );
    const report = await runCheck(root, "polly:no-banners");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-decorative-emoji", () => {
  test("fails on a 📦 in source", async () => {
    const root = await tmp("polly-cliche-emoji");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "bad.ts"), `console.log("📦 loaded");\n`);
    const report = await runCheck(root, "polly:no-decorative-emoji");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("passes on plain text", async () => {
    const root = await tmp("polly-cliche-emoji-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "ok.ts"), `console.log("loaded");\n`);
    const report = await runCheck(root, "polly:no-decorative-emoji");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-marketing", () => {
  test('fails on "comprehensive"', async () => {
    const root = await tmp("polly-cliche-marketing");
    await mkdir(join(root, "docs"), { recursive: true });
    await writeFile(join(root, "docs", "README.md"), `This is a comprehensive guide.\n`);
    const report = await runCheck(root, "polly:no-marketing");
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("README.md"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test('fails on "ensures that"', async () => {
    const root = await tmp("polly-cliche-marketing-ensures");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "bad.ts"),
      `/** This function ensures that the input is valid. */\nexport const f = (x: number) => x;\n`
    );
    const report = await runCheck(root, "polly:no-marketing");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("passes on neutral prose", async () => {
    const root = await tmp("polly-cliche-marketing-ok");
    await mkdir(join(root, "docs"), { recursive: true });
    await writeFile(join(root, "docs", "README.md"), `This guide covers the basics.\n`);
    const report = await runCheck(root, "polly:no-marketing");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-note-prefix", () => {
  test("fails on `// Note:`", async () => {
    const root = await tmp("polly-cliche-note");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "bad.ts"), `// Note: this is a thing\nexport const x = 1;\n`);
    const report = await runCheck(root, "polly:no-note-prefix");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("passes when the same content is written without the prefix", async () => {
    const root = await tmp("polly-cliche-note-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "ok.ts"), `// this is a thing\nexport const x = 1;\n`);
    const report = await runCheck(root, "polly:no-note-prefix");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-commented-code", () => {
  test("fails on a commented-out import", async () => {
    const root = await tmp("polly-cliche-commented");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "bad.ts"),
      `// import { x } from "./other";\nexport const y = 1;\n`
    );
    const report = await runCheck(root, "polly:no-commented-code");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("fails on a commented-out const", async () => {
    const root = await tmp("polly-cliche-commented-const");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "bad.ts"),
      `// const result = compute();\nexport const y = 1;\n`
    );
    const report = await runCheck(root, "polly:no-commented-code");
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });

  test("passes on prose comments", async () => {
    const root = await tmp("polly-cliche-commented-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "ok.ts"),
      `// describes what this file does\nexport const y = 1;\n`
    );
    const report = await runCheck(root, "polly:no-commented-code");
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});
