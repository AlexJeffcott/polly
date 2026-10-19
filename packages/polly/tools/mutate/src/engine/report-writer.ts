/**
 * Write the engine's results as a mutation-testing-report-schema document —
 * the same shape Stryker's json reporter writes — so `polly mutate report`,
 * `decisions`, `verify` and the mutation-testing-elements HTML viewer read it
 * unchanged.
 *
 * Fast mode (`--bail`) does not know which test killed a mutant, so
 * `killedBy` stays empty and `isMatrixComplete` correctly reports the matrix
 * as incomplete; the redundancy sections of the report then stay off. Matrix
 * mode fills `killedBy` and `testFiles[].tests[]` from the same ids (junit.ts).
 */
import { mkdirSync } from "node:fs";
import { dirname, relative } from "node:path";
import type { MutationReport } from "../ingest.ts";
import type { EngineResult } from "./types.ts";

export const ENGINE_NAME = "polly mutate (bun engine)";

export interface WrittenReport extends MutationReport {
  thresholds: { high: number; low: number };
  framework: { name: string };
  files: Record<
    string,
    {
      language: string;
      source: string;
      mutants: {
        id: string;
        mutatorName: string;
        replacement: string;
        status: string;
        statusReason?: string;
        location: {
          start: { line: number; column: number };
          end: { line: number; column: number };
        };
        killedBy: string[];
        coveredBy: string[];
      }[];
    }
  >;
}

export async function toMutationReport(result: EngineResult, cwd: string): Promise<WrittenReport> {
  const files: WrittenReport["files"] = {};
  const testFiles: NonNullable<MutationReport["testFiles"]> = {};
  for (const target of result.targets) {
    const rel = relative(cwd, target.file);
    files[rel] = {
      language:
        target.file.endsWith(".js") || target.file.endsWith(".jsx") ? "javascript" : "typescript",
      source: await Bun.file(target.file).text(),
      mutants: target.results.map((r) => ({
        id: r.mutant.id,
        mutatorName: r.mutant.mutatorName,
        replacement: r.mutant.replacement,
        status: r.status,
        ...(r.statusReason ? { statusReason: r.statusReason } : {}),
        location: r.mutant.location,
        killedBy: r.killedBy ?? [],
        coveredBy: [],
      })),
    };
    for (const t of target.coveringTests) testFiles[relative(cwd, t)] ??= { tests: [] };
    for (const t of target.tests) {
      const rel = relative(cwd, t.file);
      testFiles[rel] ??= { tests: [] };
      const entry = testFiles[rel];
      if (!entry.tests.some((x) => x.id === t.id)) {
        entry.tests.push({
          id: t.id,
          name: t.name,
          location: { start: { line: t.line, column: 1 } },
        });
      }
    }
  }
  return {
    schemaVersion: "1",
    thresholds: { high: 80, low: 60 },
    framework: { name: ENGINE_NAME },
    files,
    testFiles,
  };
}

export async function writeReport(report: WrittenReport, path: string): Promise<void> {
  mkdirSync(dirname(path), { recursive: true });
  await Bun.write(path, `${JSON.stringify(report, null, 2)}\n`);
}
