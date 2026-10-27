// Adapter detection counts the project's code: not comments or strings (the
// heuristics matched regexes over the whole file, so `// bus.on("X")` counted
// as a call), and not declaration files (other packages' types).

import { afterAll, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { detectAdapter } from "../adapters/detection";

const TSCONFIG = JSON.stringify({ compilerOptions: { strict: true }, include: ["*.ts", "*.d.ts"] });

const PROSE_ONLY = `
// bus.on("A"), bus.on("B"), bus.emit("A")
/* chrome.runtime.sendMessage, chrome.tabs.query, MessageBus, getMessageBus */
/** new Worker("w.js"); new SharedWorker("s.js"); port.postMessage(1) */
export const notes = 'emitter.on("C"); emitter.emit("C"); self.postMessage(2)';
`;

// detect() keeps an alternative only above confidence 20, so each heuristic
// here scores over 20: event bus 4 x 5 + 3, extension 3 x 10 + 3 x 5, worker
// 20 + 5.
const CODE = `
declare const bus: { on(t: string, h: () => void): void; emit(t: string): void };
declare const port: { postMessage(m: unknown): void };
bus.on("A", () => {});
bus.on(\`B\`, () => {});
bus.on(\`C\${1}\`, () => {});
bus.on("D", () => {});
bus.on(name, () => {});
bus.emit("A");
port.postMessage(1);
new Worker("w.js");
declare const name: string;
`;

const CHROME = (n: number) => `
declare const chrome: { runtime: { id: string }; tabs: { id: number } };
declare class MessageBus {}
export const ids${n} = [chrome.runtime.id, chrome.tabs.id, MessageBus];
`;

const DECLARATIONS = `
declare class MessageBus {}
declare const chrome: { runtime: { id: string } };
export declare const id: string;
`;

function project(sources: string[], declarations: string[] = []): string {
  const dir = mkdtempSync(path.join(tmpdir(), "polly-detection-"));
  writeFileSync(path.join(dir, "tsconfig.json"), TSCONFIG);
  for (const [i, source] of sources.entries()) {
    writeFileSync(path.join(dir, `file${i}.ts`), source);
  }
  for (const [i, source] of declarations.entries()) {
    writeFileSync(path.join(dir, `types${i}.d.ts`), source);
  }
  return dir;
}

const dirs: string[] = [];
afterAll(() => {
  for (const dir of dirs) rmSync(dir, { recursive: true, force: true });
});

async function detectIn(dir: string) {
  dirs.push(dir);
  return detectAdapter(path.join(dir, "tsconfig.json"));
}

function detect(...sources: string[]) {
  return detectIn(project(sources));
}

function allEvidence(result: Awaited<ReturnType<typeof detectIn>>): string[] {
  return [result.evidence, ...(result.alternatives ?? []).map((a) => a.evidence)].flat();
}

describe("adapter detection reads code, not comments or strings", () => {
  test("patterns named only in comments and strings give no evidence", async () => {
    const result = await detect(PROSE_ONLY);
    expect(result.confidence).toBe(0);
    expect(allEvidence(result)).toEqual([]);
  });

  test("declaration files give no evidence", async () => {
    const declarations = [DECLARATIONS, DECLARATIONS, DECLARATIONS, DECLARATIONS];
    const result = await detectIn(project(["export const x = 1;"], declarations));
    expect(result.confidence).toBe(0);
    expect(allEvidence(result)).toEqual([]);
  });

  test("the same patterns as code are counted", async () => {
    const result = await detect(CODE, CHROME(1), CHROME(2), CHROME(3));
    const evidence = allEvidence(result);
    // bus.on(name, ...) has no string first argument.
    expect(evidence).toContain("Found 4 .on() call(s)");
    expect(evidence).toContain("Found 1 .emit() call(s)");
    expect(evidence).toContain("Found 1 .postMessage() call(s)");
    expect(evidence).toContain("Found 1 Worker instantiation(s)");
    expect(evidence).toContain("Found 3 file(s) using chrome.* APIs");
    expect(evidence).toContain("Found 3 file(s) using MessageBus");
  });
});
