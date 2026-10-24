// The typescript-7 RelationshipExtractor against the ts-morph copy that
// handlers.ts still calls (relationships-morph.ts): every function and block
// of each corpus, extracted by both, must give the same relationships.
// Until handlers.ts moves to typescript-7 the parity harness only reaches
// the ts-morph copy, so this is the port's evidence. Delete this file with
// relationships-morph.ts.

import { afterAll, describe, expect, test } from "bun:test";
import * as path from "node:path";
import { type Node as MorphNode, Project } from "ts-morph";
import type { Node, SourceFile } from "typescript-7/ast";
import { AnalysisSession, forEachDescendant, kindName } from "../../program";
import { RelationshipExtractor } from "../relationships";
import { MorphRelationshipExtractor } from "../relationships-morph";

const POLLY_ROOT = path.resolve(import.meta.dir, "../../../../..");
const REPO_ROOT = path.resolve(POLLY_ROOT, "../..");

const CORPORA: [string, string][] = [
  [
    "architecture-corpus",
    path.join(POLLY_ROOT, "scripts/analysis-parity/fixtures/architecture-corpus/tsconfig.json"),
  ],
  ["pwa", path.join(POLLY_ROOT, "tools/verify/test-projects/pwa/tsconfig.json")],
  [
    "websocket-server",
    path.join(POLLY_ROOT, "tools/verify/test-projects/websocket-server/tsconfig.json"),
  ],
  ["full-featured", path.join(REPO_ROOT, "examples/full-featured/tsconfig.json")],
  ["todo-list", path.join(REPO_ROOT, "examples/todo-list/tsconfig.json")],
];

/** The node kinds handlers.ts hands the extractor: handler functions and if-branches. */
const HANDLER_KINDS = new Set([
  "ArrowFunction",
  "FunctionExpression",
  "FunctionDeclaration",
  "Block",
]);

const key = (file: string, pos: number, end: number, kind: string) =>
  `${file}:${pos}:${end}:${kind}`;

const session = new AnalysisSession();
afterAll(() => session.close());

type Twins = Map<string, { node: Node; file: SourceFile }>;

/** Every handler-kind typescript-7 node of the program, by file, span and kind. */
function ts7Nodes(files: readonly SourceFile[]): Twins {
  const nodes: Twins = new Map();
  for (const file of files) {
    forEachDescendant(file, (node) => {
      const kind = kindName(node);
      if (HANDLER_KINDS.has(kind))
        nodes.set(key(file.fileName, node.pos, node.end, kind), { node, file });
    });
  }
  return nodes;
}

interface Comparison {
  compared: number;
  nonEmpty: number;
  mismatches: string[];
}

/** Extract from every handler-kind ts-morph node and its typescript-7 twin; collect differences. */
function compareAll(
  morph: Project,
  twins: Twins,
  ts7: RelationshipExtractor,
  reference: MorphRelationshipExtractor
): Comparison {
  const result: Comparison = { compared: 0, nonEmpty: 0, mismatches: [] };
  const files = morph
    .getSourceFiles()
    .filter((file) => !file.getFilePath().includes("/node_modules/"));
  for (const morphFile of files) {
    morphFile.forEachDescendant((morphNode: MorphNode) => {
      const kind = morphNode.getKindName();
      if (!HANDLER_KINDS.has(kind)) return;
      const where = key(morphFile.getFilePath(), morphNode.getPos(), morphNode.getEnd(), kind);
      const twin = twins.get(where);
      if (!twin) {
        result.mismatches.push(`${where}: no typescript-7 node`);
        return;
      }
      const expected = reference.extractFromHandler(morphNode, morphFile, "corpus_handler");
      const actual = ts7.extractFromHandler(twin.node, twin.file, "corpus_handler");
      result.compared++;
      if (expected.length > 0) result.nonEmpty++;
      if (JSON.stringify(actual) !== JSON.stringify(expected)) {
        result.mismatches.push(
          `${where}: ${JSON.stringify(expected)} vs ${JSON.stringify(actual)}`
        );
      }
    });
  }
  return result;
}

describe("RelationshipExtractor (typescript-7) matches the ts-morph copy", () => {
  for (const [name, tsconfig] of CORPORA) {
    test(`${name}: every function and block`, async () => {
      const morph = new Project({ tsConfigFilePath: tsconfig });
      const program = await session.open(tsconfig);
      await program.prefetchImports();
      const { compared, nonEmpty, mismatches } = compareAll(
        morph,
        ts7Nodes(program.sourceFiles),
        new RelationshipExtractor(program),
        new MorphRelationshipExtractor()
      );

      expect(mismatches.slice(0, 10)).toEqual([]);
      expect(compared).toBeGreaterThan(5);
      if (name === "architecture-corpus") expect(nonEmpty).toBeGreaterThan(3);
    }, 120_000);
  }

  test("an unprefetched program is a caller error, not an empty answer", async () => {
    const tsconfig = CORPORA[0]?.[1] ?? "";
    const isolated = await session.openIsolated(tsconfig);
    const extractor = new RelationshipExtractor(isolated);
    const file = isolated.sourceFiles.find((f) => f.fileName.endsWith("background/index.ts"));
    expect(file).toBeDefined();
    if (!file) return;
    expect(() => extractor.extractFromHandler(file, file, "corpus_handler")).toThrow(
      /not prefetched/
    );
  });
});
