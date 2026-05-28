// Regression tests for polly#144 — the TLA+ generator used to silently drop
// every handler whose messageType wasn't a bare TLA+ identifier (HTTP routes
// like "POST /register/options", colon-namespaced WS messages like "chat:send"),
// emitting a "No message handlers found" stub and reporting a passing run with
// zero verified postconditions. These handlers are now kept: the messageType
// becomes a quoted TLA+ string literal and the action name is sanitized.

import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../../analysis/src/types";
import { RoundTripValidator } from "../../codegen/round-trip";
import { generateSubsystemTLA, TLAGenerator } from "../../codegen/tla";
import type { VerificationConfig } from "../../types";

const config: VerificationConfig = {
  state: { authPhase: { type: "enum", values: ["anonymous", "authenticated"] } },
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn",
  onRelease: "error",
};

function analysisWith(
  handlers: Array<{
    messageType: string;
    postconditions?: Array<{ expression: string; message?: string }>;
  }>
): CodebaseAnalysis {
  return {
    stateType: null,
    messageTypes: handlers.map((h) => h.messageType),
    fields: [],
    handlers: handlers.map((h) => ({
      messageType: h.messageType,
      node: "background" as const,
      assignments: [],
      preconditions: [],
      postconditions: h.postconditions ?? [],
      location: { file: "server.ts", line: 1 },
    })),
  };
}

describe("polly#144: non-identifier message handlers reach TLC", () => {
  test("HTTP routes and colon-namespaced messages survive codegen", async () => {
    const analysis = analysisWith([
      { messageType: "POST /register/options" },
      {
        messageType: "POST /login/verify",
        postconditions: [
          { expression: 'authMachine.value.phase === "authenticated"', message: "logged in" },
        ],
      },
      { messageType: "chat:send" },
      { messageType: "GET /me" },
    ]);

    const { spec } = await new TLAGenerator().generate(config, analysis);

    // No silent stub — the whole point of the bug.
    expect(spec).not.toContain("No message handlers found");
    expect(spec).not.toContain("No valid message handlers");

    // Message types appear as quoted TLA+ string literals (legal for any chars).
    expect(spec).toContain('"POST /register/options"');
    expect(spec).toContain('"chat:send"');
    expect(spec).toContain('"GET /me"');

    // Action names are sanitized into valid TLA+ identifiers.
    expect(spec).toContain("HandlePostRegisterOptions(ctx) ==");
    expect(spec).toContain("HandlePostLoginVerify(ctx) ==");
    expect(spec).toContain("HandleChatSend(ctx) ==");
    expect(spec).toContain("HandleGetMe(ctx) ==");

    // The dispatcher routes the quoted messageType to its sanitized action.
    expect(spec).toContain('IF msgType = "POST /register/options" THEN HandlePostRegisterOptions');

    // The route's ensures(...) becomes a real EnsuresAfter step-property.
    expect(spec).toContain("EnsuresAfter_HandlePostLoginVerify");
  });

  test("ensures count is non-zero for anchored route handlers", async () => {
    const analysis = analysisWith([
      {
        messageType: "POST /logout",
        postconditions: [{ expression: 'authMachine.value.phase === "anonymous"' }],
      },
    ]);

    const { spec } = await new TLAGenerator().generate(config, analysis);
    // Mirrors the cli.ts count of registered postcondition properties.
    const ensuresCount = (spec.match(/^EnsuresAfter_\w+ ==/gm) ?? []).length;
    expect(ensuresCount).toBeGreaterThan(0);
  });

  test("distinct messageTypes that sanitize alike get distinct action names", async () => {
    const analysis = analysisWith([
      { messageType: "task:tree-cloned" },
      { messageType: "task/tree/cloned" },
    ]);

    const { spec } = await new TLAGenerator().generate(config, analysis);
    const actions = (spec.match(/^Handle\w+\(ctx\) ==/gm) ?? []).map((l) =>
      l.replace("(ctx) ==", "")
    );
    // Both handlers keep a definition; the collision is broken with a suffix.
    expect(actions).toContain("HandleTaskTreeCloned");
    expect(actions).toContain("HandleTaskTreeCloned_2");
    expect(new Set(actions).size).toBe(actions.length); // all unique
  });

  test("validateInputs keeps representable types, rejects only artifacts", async () => {
    // Representable: must not throw.
    await new TLAGenerator().generate(config, analysisWith([{ messageType: "POST /x" }]));

    // Unrepresentable (no letter): must throw.
    await expect(
      new TLAGenerator().generate(config, analysisWith([{ messageType: "///" }]))
    ).rejects.toThrow(/[Uu]nrepresentable/);
  });

  test("subsystem path (the issue's repro) registers real ensures properties", async () => {
    // Reproduces the #144 report: a subsystem whose `handlers` list is made up
    // entirely of HTTP routes. It used to generate the no-handlers stub and
    // report 0 ensures next to a passing tick.
    const authSubsystem = {
      state: ["authPhase"],
      handlers: ["POST /login/verify", "POST /logout"],
    };
    const subsystemConfig: VerificationConfig = {
      ...config,
      messages: { maxInFlight: 2, maxTabs: 1 },
      subsystems: { auth: authSubsystem },
    };
    const analysis = analysisWith([
      {
        messageType: "POST /login/verify",
        postconditions: [{ expression: 'authMachine.value.phase === "authenticated"' }],
      },
      {
        messageType: "POST /logout",
        postconditions: [{ expression: 'authMachine.value.phase === "anonymous"' }],
      },
    ]);

    const { spec } = await generateSubsystemTLA("auth", authSubsystem, subsystemConfig, analysis);

    expect(spec).not.toContain("No message handlers found");
    expect(spec).toContain('UserMessageTypes == {"POST /login/verify", "POST /logout"}');
    const ensuresCount = (spec.match(/^EnsuresAfter_\w+ ==/gm) ?? []).length;
    expect(ensuresCount).toBe(2);
  });

  test("route message types round-trip back out of the generated spec", async () => {
    const analysis = analysisWith([
      { messageType: "POST /register/options" },
      { messageType: "chat:send" },
    ]);
    const { spec } = await new TLAGenerator().generate(config, analysis);

    const result = await new RoundTripValidator().validate(config, analysis, spec);
    expect(result.extracted.messageTypes).toContain("POST /register/options");
    expect(result.extracted.messageTypes).toContain("chat:send");
  });
});
