import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { validateConfig } from "../../config/parser";
import { MIN_TLC_MEMORY } from "../../runner/memory";

/**
 * polly#181: `verification.memory` is validated where `verification.workers` is.
 *
 * A memory setting TLC cannot run in has to be rejected before the run starts,
 * because a run that dies for want of memory dies without a TLC message — the
 * whole reason the setting exists.
 */

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-181-"));

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

function memoryIssues(result: ReturnType<typeof validateConfig>) {
  return result.issues.filter((i) => i.field === "verification.memory");
}

describe("verification.memory validation", () => {
  test("a docker-style size is accepted", () => {
    const result = validateWithVerification('{ workers: 2, memory: "8g" }', "valid");

    expect(memoryIssues(result)).toHaveLength(0);
  });

  test("a size docker would reject is an error, not a warning", () => {
    const result = validateWithVerification('{ memory: "8gb" }', "bad-suffix");
    const [issue] = memoryIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("8gb");
    expect(result.valid).toBe(false);
  });

  test("below the minimum TLC can run in, the minimum is named", () => {
    const result = validateWithVerification('{ memory: "16m" }', "too-small");
    const [issue] = memoryIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain(MIN_TLC_MEMORY);
    expect(issue?.suggestion).toContain(MIN_TLC_MEMORY);
  });

  test("unset raises nothing — the runner's fixed default applies", () => {
    const result = validateWithVerification("{ workers: 2 }", "unset");

    expect(memoryIssues(result)).toHaveLength(0);
  });
});
