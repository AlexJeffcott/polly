import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { validateConfig } from "../../config/parser";

/**
 * `messages.maxTabs`: Tabs = 0..maxTabs, so 0 is one tab.
 *
 * The floor was 1, which is two tabs. No generated expression reads a
 * message's tab, so the second tab only doubled each send:
 * examples/mesh-recovery-pair did not finish at maxTabs 1 and finishes at 0.
 */

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-max-tabs-"));

afterAll(() => {
  fs.rmSync(tmpDir, { recursive: true, force: true });
});

function validateWithMaxTabs(maxTabs: string, name: string) {
  const configPath = path.join(tmpDir, `${name}.js`);
  fs.writeFileSync(
    configPath,
    `module.exports.verificationConfig = {
      state: { ready: { type: "boolean" } },
      messages: { maxInFlight: 1, maxTabs: ${maxTabs} },
      onBuild: "warn",
      onRelease: "error",
    };\n`
  );
  const result = validateConfig(configPath);
  return result.issues.filter((i) => i.field === "messages.maxTabs");
}

describe("messages.maxTabs validation", () => {
  test("0 (one tab) is accepted", () => {
    expect(validateWithMaxTabs("0", "zero")).toHaveLength(0);
  });

  test("a negative value is an error", () => {
    expect(validateWithMaxTabs("-1", "negative")[0]?.severity).toBe("error");
  });

  test("a fraction is an error", () => {
    expect(validateWithMaxTabs("0.5", "fraction")[0]?.severity).toBe("error");
  });
});
