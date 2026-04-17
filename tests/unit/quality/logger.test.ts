import { afterEach, beforeEach, expect, test } from "bun:test";
import { mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkCssQuality, logger, resetLogger } from "@fairfox/polly/quality";

let root: string;
let captured: { level: string; message: string }[];

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-logger-"));
  captured = [];
  logger.log = (m) => captured.push({ level: "log", message: m });
  logger.error = (m) => captured.push({ level: "error", message: m });
  logger.info = (m) => captured.push({ level: "info", message: m });
  logger.warn = (m) => captured.push({ level: "warn", message: m });
});

afterEach(() => {
  resetLogger();
});

test("logger is mockable — check output is captured", async () => {
  await writeFile(join(root, "clean.module.css"), `.x { color: var(--polly-text); }`);
  const result = await checkCssQuality({ rootDir: root });
  result.print();
  expect(captured.length).toBeGreaterThan(0);
  expect(captured.every((c) => c.level === "log")).toBe(true);
  expect(captured[0]?.message).toContain("css-quality: no violations");
});

test("error output goes through logger.error, not console", async () => {
  await writeFile(join(root, "bad.module.css"), `.x { color: #fff; }`);
  const result = await checkCssQuality({ rootDir: root });
  result.print();
  const errors = captured.filter((c) => c.level === "error");
  expect(errors.length).toBeGreaterThan(0);
  expect(errors[0]?.message).toContain("❌");
});

test("resetLogger restores the default sinks", async () => {
  resetLogger();
  expect(typeof logger.log).toBe("function");
  expect(typeof logger.error).toBe("function");
  // After reset, logger.log should no longer be the captured one.
  const isCapturedFn = logger.log === ((m: string) => captured.push({ level: "log", message: m }));
  expect(isCapturedFn).toBe(false);
});
