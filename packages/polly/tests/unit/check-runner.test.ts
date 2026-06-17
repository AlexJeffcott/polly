import { describe, expect, test } from "bun:test";
import {
  type BatchStep,
  formatDuration,
  runBatch,
  runStep,
  type StepResult,
  type StepRunner,
} from "../../tools/quality/src/check-runner";

const step = (name: string): BatchStep => ({ name, cmd: ["true"] });
const tick = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 5));

describe("formatDuration", () => {
  test("sub-second renders as ms", () => expect(formatDuration(250)).toBe("250ms"));
  test("at one second switches to seconds", () => expect(formatDuration(1000)).toBe("1.0s"));
  test("seconds carry one decimal", () => expect(formatDuration(2500)).toBe("2.5s"));
});

describe("runBatch — run-all (failFast off)", () => {
  test("runs every step and reports the full failure set", async () => {
    const calls: string[] = [];
    const run: StepRunner = async (s) => {
      calls.push(s.name);
      return { ok: s.name !== "b" && s.name !== "d", durationMs: 1 };
    };
    const steps = ["a", "b", "c", "d", "e"].map(step);
    const result = await runBatch({ steps, verbose: false, failFast: false, concurrency: 1 }, run);

    expect(calls).toEqual(["a", "b", "c", "d", "e"]);
    expect(result.ok).toBe(false);
    expect(result.failed).toEqual(["b", "d"]);
  });
});

describe("runBatch — serial soft fail-fast", () => {
  test("stops claiming steps after the first failure", async () => {
    const calls: string[] = [];
    const run: StepRunner = async (s) => {
      calls.push(s.name);
      return { ok: s.name !== "b", durationMs: 1 };
    };
    const steps = ["a", "b", "c", "d"].map(step);
    const result = await runBatch({ steps, verbose: false, failFast: true, concurrency: 1 }, run);

    expect(calls).toEqual(["a", "b"]); // c and d never claimed
    expect(result.failed).toEqual(["b"]);
    expect(result.ok).toBe(false);
  });
});

describe("runBatch — concurrent soft fail-fast", () => {
  test("a failure stops new claims while in-flight steps finish", async () => {
    const calls: string[] = [];
    const resolvers = new Map<string, (r: StepResult) => void>();
    const run: StepRunner = (s) => {
      calls.push(s.name);
      return new Promise<StepResult>((resolve) => {
        resolvers.set(s.name, resolve);
      });
    };
    const settle = (name: string, ok: boolean): void => {
      const resolve = resolvers.get(name);
      if (!resolve) throw new Error(`${name} was never claimed`);
      resolve({ ok, durationMs: 1 });
    };

    const steps = ["s0", "s1", "s2", "s3", "s4", "s5"].map(step);
    const batch = runBatch({ steps, verbose: false, failFast: true, concurrency: 2 }, run);

    await tick();
    expect(calls).toEqual(["s0", "s1"]); // pool of 2 claims the first two

    settle("s1", false); // trips the abort
    await tick();
    settle("s0", true); // finishing must not claim s2
    const result = await batch;

    expect(result.failed).toEqual(["s1"]);
    expect(result.ok).toBe(false);
    expect(calls).toEqual(["s0", "s1"]); // s2..s5 never claimed
  });
});

describe("runStep — real subprocess", () => {
  test("captures a passing step under the pool", async () => {
    const result = await runStep(
      { name: "pass", cmd: ["bun", "-e", "process.exit(0)"] },
      { verbose: false, concurrent: true }
    );
    expect(result.ok).toBe(true);
    expect(result.durationMs).toBeGreaterThanOrEqual(0);
  });

  test("reports and flushes a failing step", async () => {
    const result = await runStep(
      { name: "fail", cmd: ["bun", "-e", "console.log('boom'); process.exit(1)"] },
      { verbose: false, concurrent: true }
    );
    expect(result.ok).toBe(false);
  });

  test("serial (non-concurrent) capture path", async () => {
    const result = await runStep(
      { name: "serial", cmd: ["bun", "-e", "process.exit(0)"] },
      { verbose: false, concurrent: false }
    );
    expect(result.ok).toBe(true);
  });

  test("verbose streams live and still reports", async () => {
    const result = await runStep(
      { name: "verbose", cmd: ["bun", "-e", "process.exit(0)"] },
      { verbose: true }
    );
    expect(result.ok).toBe(true);
  });
});

describe("runBatch — default runner over real subprocesses", () => {
  test("a clean pool reports ok", async () => {
    const steps: BatchStep[] = [
      { name: "ok1", cmd: ["bun", "-e", "process.exit(0)"] },
      { name: "ok2", cmd: ["bun", "-e", "process.exit(0)"] },
    ];
    const result = await runBatch({ steps, verbose: false, concurrency: 2 });
    expect(result.ok).toBe(true);
    expect(result.failed).toEqual([]);
  });
});
