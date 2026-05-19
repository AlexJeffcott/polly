import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

/**
 * polly#117: the verifier has no native support for the cross-peer
 * semantics of `$meshState` and `$peerState`. These tests confirm
 * that the extractor recognises calls to those factories so the CLI
 * can warn when a requires/ensures predicate references them.
 */
describe("HandlerExtractor — mesh/peer signal discovery (polly#117)", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-mesh-peer-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function createTsConfig(): string {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
          strict: true,
        },
        include: ["*.ts"],
      })
    );
    return tsConfigPath;
  }

  test("recognises $meshState calls and reports the signal", () => {
    const testFile = path.join(tempDir, "state.ts");
    fs.writeFileSync(
      testFile,
      `
function $meshState<T>(key: string, initial: T) {
  return { value: initial };
}

export const todos = $meshState<{ entries: string[] }>("todos-doc", { entries: [] });
`
    );

    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    expect(result.meshOrPeerSignals).toHaveLength(1);
    const sig = result.meshOrPeerSignals[0]!;
    expect(sig.kind).toBe("mesh");
    expect(sig.key).toBe("todos-doc");
    expect(sig.variableName).toBe("todos");
  });

  test("recognises $peerState calls and reports the signal", () => {
    const testFile = path.join(tempDir, "peer-state.ts");
    fs.writeFileSync(
      testFile,
      `
function $peerState<T>(key: string, initial: T) {
  return { value: initial };
}

export const presence = $peerState<{ online: boolean }>("presence-doc", { online: false });
`
    );

    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    expect(result.meshOrPeerSignals).toHaveLength(1);
    const sig = result.meshOrPeerSignals[0]!;
    expect(sig.kind).toBe("peer");
    expect(sig.key).toBe("presence-doc");
    expect(sig.variableName).toBe("presence");
  });

  test("recognises both factories in the same file", () => {
    const testFile = path.join(tempDir, "mixed.ts");
    fs.writeFileSync(
      testFile,
      `
function $meshState<T>(_key: string, initial: T) { return { value: initial }; }
function $peerState<T>(_key: string, initial: T) { return { value: initial }; }

export const docA = $meshState<{ entries: string[] }>("doc-a", { entries: [] });
export const docB = $peerState<{ ts: number }>("doc-b", { ts: 0 });
`
    );

    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    expect(result.meshOrPeerSignals).toHaveLength(2);
    const kinds = result.meshOrPeerSignals.map((s) => s.kind).sort();
    expect(kinds).toEqual(["mesh", "peer"]);
  });

  test("does not recognise $sharedState as mesh or peer", () => {
    const testFile = path.join(tempDir, "shared.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(_key: string, initial: T) { return { value: initial }; }

export const local = $sharedState<{ count: number }>("local", { count: 0 });
`
    );

    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    expect(result.meshOrPeerSignals).toHaveLength(0);
  });
});
