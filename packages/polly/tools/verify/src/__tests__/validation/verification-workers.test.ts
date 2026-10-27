import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { validateConfig } from "../../config/parser";

/**
 * `verification.workers` takes a count or `"auto"`, which is also the default.
 *
 * On examples/minimal (1,801,024 distinct states, 12 cores) TLC took 36 s with
 * one worker and 19 s with `-workers auto`, for the same state count.
 */

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-workers-"));

afterAll(() => {
  fs.rmSync(tmpDir, { recursive: true, force: true });
});

/** Write a minimal config declaring `verification`, and validate it. */
function validateWithVerification(verification: string, name: string) {
  const configPath = path.join(tmpDir, `${name}.js`);
  fs.writeFileSync(
    configPath,
    `module.exports.verificationConfig = {
      state: { ready: { type: "boolean" } },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
      verification: ${verification},
    };\n`
  );
  return validateConfig(configPath);
}

function workerIssues(result: ReturnType<typeof validateConfig>) {
  return result.issues.filter((i) => i.field === "verification.workers");
}

describe("verification.workers validation", () => {
  test('"auto" is accepted', () => {
    const result = validateWithVerification('{ workers: "auto" }', "auto");

    expect(workerIssues(result)).toHaveLength(0);
  });

  test("a positive integer is accepted", () => {
    const result = validateWithVerification("{ workers: 4 }", "four");

    expect(workerIssues(result)).toHaveLength(0);
  });

  test("zero is an error", () => {
    const result = validateWithVerification("{ workers: 0 }", "zero");
    const [issue] = workerIssues(result);

    expect(issue?.severity).toBe("error");
    expect(result.valid).toBe(false);
  });

  test("a fraction is an error, not passed to TLC", () => {
    const result = validateWithVerification("{ workers: 1.5 }", "fraction");
    const [issue] = workerIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.suggestion).toContain('"auto"');
  });
});
