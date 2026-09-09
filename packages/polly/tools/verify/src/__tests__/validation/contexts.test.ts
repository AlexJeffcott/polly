import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { validateConfig } from "../../config/parser";

/**
 * polly#185: `contexts` names become TLA+ model values in the generated `.cfg`.
 *
 * A name TLC cannot parse fails after the spec is written and the container is
 * up, with a SANY error pointing at a line the user never wrote. So the names
 * are checked here, where the config is read.
 */

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-185-"));

afterAll(() => {
  fs.rmSync(tmpDir, { recursive: true, force: true });
});

/** Write a minimal config with the given extra keys, and validate it. */
function validateWith(extra: string, name: string) {
  const configPath = path.join(tmpDir, `${name}.js`);
  fs.writeFileSync(
    configPath,
    `module.exports.verificationConfig = {
      state: { ready: { type: "boolean" } },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
      ${extra}
    };\n`
  );
  return validateConfig(configPath);
}

function contextIssues(result: ReturnType<typeof validateConfig>) {
  return result.issues.filter((i) => i.field === "contexts");
}

describe("contexts validation", () => {
  test("an omitted key raises nothing", () => {
    expect(contextIssues(validateWith("", "absent"))).toHaveLength(0);
  });

  test("plain identifiers are accepted", () => {
    const result = validateWith('contexts: ["server", "client", "worker_2"],', "valid");

    expect(contextIssues(result)).toHaveLength(0);
    expect(result.valid).toBe(true);
  });

  test("an empty array is an error naming the minimum of one", () => {
    const result = validateWith("contexts: [],", "empty");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("at least one context");
    expect(result.valid).toBe(false);
  });

  test("a non-array is an error", () => {
    const result = validateWith('contexts: "server",', "not-array");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("must be an array");
    expect(result.valid).toBe(false);
  });

  test("a name that is not a string is an error", () => {
    const result = validateWith("contexts: [3],", "not-string");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("is not a string");
    expect(result.valid).toBe(false);
  });

  test("a name that cannot sanitise into an identifier is an error", () => {
    const result = validateWith('contexts: ["1st"],', "leading-digit");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("not a TLA+ model value");
    expect(result.valid).toBe(false);
  });

  test("a name that sanitises is a warning naming the emitted value", () => {
    const result = validateWith('contexts: ["main-window"],', "sanitised");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("warning");
    expect(issue?.message).toContain('"main_window"');
    expect(result.valid).toBe(true);
  });

  test("a duplicate name is an error", () => {
    const result = validateWith('contexts: ["server", "server"],', "duplicate");
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("error");
    expect(issue?.message).toContain("declared twice");
    expect(result.valid).toBe(false);
  });

  test("two names that sanitise to the same model value collide", () => {
    const result = validateWith('contexts: ["main-window", "main:window"],', "sanitise-collision");
    const errors = contextIssues(result).filter((i) => i.severity === "error");

    expect(errors[0]?.message).toContain('both emit as "main_window"');
    expect(result.valid).toBe(false);
  });

  test.each([["Tabs"], ["NULL"], ["MaxMessages"], ["Contexts"], ["SUBSET"]])(
    "%s collides with a keyword or a constant the .cfg declares",
    (name) => {
      const result = validateWith(`contexts: ["${name}"],`, `reserved-${name}`);
      const [issue] = contextIssues(result);

      expect(issue?.severity).toBe("error");
      expect(issue?.message).toContain("collides");
      expect(result.valid).toBe(false);
    }
  );

  test("one context with a mesh block warns that PropagateMeshOp never fires", () => {
    const result = validateWith(
      'contexts: ["server"], mesh: { todos: { entries: { type: "enum", values: ["a", "b"] } } },',
      "mesh-single"
    );
    const [issue] = contextIssues(result);

    expect(issue?.severity).toBe("warning");
    expect(issue?.message).toContain("two distinct contexts");
    expect(result.valid).toBe(true);
  });

  test("two contexts with a mesh block raise nothing", () => {
    const result = validateWith(
      'contexts: ["peerA", "peerB"], mesh: { todos: { entries: { type: "enum", values: ["a", "b"] } } },',
      "mesh-pair"
    );

    expect(contextIssues(result)).toHaveLength(0);
  });
});

describe("the dead messages.maxContexts key", () => {
  test("declaring it warns and points at `contexts`", () => {
    const result = validateWith("", "no-max-contexts");
    expect(result.issues.filter((i) => i.field === "messages.maxContexts")).toHaveLength(0);

    const configPath = path.join(tmpDir, "max-contexts.js");
    fs.writeFileSync(
      configPath,
      `module.exports.verificationConfig = {
        state: { ready: { type: "boolean" } },
        messages: { maxInFlight: 1, maxTabs: 1, maxContexts: 3 },
        onBuild: "warn",
        onRelease: "error",
      };\n`
    );
    const withKey = validateConfig(configPath);
    const [issue] = withKey.issues.filter((i) => i.field === "messages.maxContexts");

    expect(issue?.severity).toBe("warning");
    expect(issue?.message).toContain("does not size the Contexts set");
    expect(issue?.suggestion).toContain("contexts:");
    expect(withKey.valid).toBe(true);
  });
});
