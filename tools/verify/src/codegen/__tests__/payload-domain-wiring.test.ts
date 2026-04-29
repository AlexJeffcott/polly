// Issue #72 — payload field types are pulled from the modeled state field's
// declared domain (FieldConfig) when a handler parameter writes into that field
// via a `param:X` assignment.

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

describe("PayloadType domain wiring (issue #72)", () => {
  let generator: TLAGenerator;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();
    baseAnalysis = {
      stateType: null,
      messageTypes: ["test"],
      fields: [],
      handlers: [],
      stateConstraints: [],
    };
  });

  test("enum state-field domain pulled into PayloadType", async () => {
    const config: VerificationConfig = {
      state: {
        theme: { type: "enum", values: ["light", "dark", "system"] },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "SET_THEME",
        assignments: [{ field: "theme", value: "param:theme" }],
        preconditions: [],
        postconditions: [],
        parameters: ["theme"],
      },
    ];

    const { spec } = await generator.generate(config, baseAnalysis);

    expect(spec).toMatch(/theme: \{"light", "dark", "system"\}/);
    expect(spec).toContain("payload.theme");
    expect(spec).not.toMatch(/theme: Value/);
  });

  test("bounded number domain pulled into PayloadType", async () => {
    const config: VerificationConfig = {
      state: {
        count: { type: "number", min: 0, max: 5 },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "SET_COUNT",
        assignments: [{ field: "count", value: "param:count" }],
        preconditions: [],
        postconditions: [],
        parameters: ["count"],
      },
    ];

    const { spec } = await generator.generate(config, baseAnalysis);

    expect(spec).toMatch(/count: 0\.\.5/);
    expect(spec).toContain("payload.count");
  });

  test("config-derived enum overrides param-name BOOLEAN heuristic", async () => {
    // Without the fix: parameter name `isOnline` triggers BOOL_PARAM_PATTERN,
    // so payload.isOnline would be typed BOOLEAN regardless of the destination
    // field's domain. With the fix: the modeled state field's enum wins because
    // it is strictly more precise.
    const config: VerificationConfig = {
      state: {
        connectionState: { type: "enum", values: ["online", "offline", "degraded"] },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "SET_ONLINE",
        assignments: [{ field: "connectionState", value: "param:isOnline" }],
        preconditions: [],
        postconditions: [],
        parameters: ["isOnline"],
      },
    ];

    const { spec } = await generator.generate(config, baseAnalysis);

    expect(spec).toMatch(/isOnline: \{"online", "offline", "degraded"\}/);
    expect(spec).not.toMatch(/isOnline: BOOLEAN/);
  });

  test("nested state field path resolves through flattened lookup", async () => {
    // Extractor at tools/analysis/src/extract/handlers.ts:1552 joins nested writes
    // with `_`, so `user.role` becomes `assignment.field = "user_role"`. The flat
    // map produced by flattenStateConfig must use the same join so the lookup hits.
    const config: VerificationConfig = {
      state: {
        "user.role": { type: "enum", values: ["guest", "user", "admin"] },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "USER_SET_ROLE",
        assignments: [{ field: "user_role", value: "param:role" }],
        preconditions: [],
        postconditions: [],
        parameters: ["role"],
      },
    ];

    const { spec } = await generator.generate(config, baseAnalysis);

    expect(spec).toMatch(/role: \{"guest", "user", "admin"\}/);
  });

  test("param without state-field link falls back to inferFieldType", async () => {
    // Regression guard: when a parameter doesn't write into any modeled state
    // field, the name-based heuristic still applies. `id` is a seeded default;
    // `extraFlag` matches no pattern and falls through to Value.
    const config: VerificationConfig = {
      state: {
        unrelated: { type: "boolean" },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "GENERIC",
        assignments: [],
        preconditions: [],
        postconditions: [],
        parameters: ["isReady", "extraFlag"],
      },
    ];

    const { spec } = await generator.generate(config, baseAnalysis);

    expect(spec).toContain("isReady: BOOLEAN");
    expect(spec).toContain("extraFlag: Value");
  });

  test("conflict: same param name, two different state-field domains, throws", async () => {
    // Auditor verified zero such conflicts in real examples; if it ever happens,
    // failing loudly is correct — silent fallback to Value would re-introduce
    // the very bug this method exists to fix.
    const config: VerificationConfig = {
      state: {
        status: { type: "enum", values: ["on", "off"] },
        volume: { type: "number", min: 0, max: 11 },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis.handlers = [
      {
        messageType: "SET_STATUS",
        assignments: [{ field: "status", value: "param:value" }],
        preconditions: [],
        postconditions: [],
        parameters: ["value"],
      },
      {
        messageType: "SET_VOLUME",
        assignments: [{ field: "volume", value: "param:value" }],
        preconditions: [],
        postconditions: [],
        parameters: ["value"],
      },
    ];

    expect(generator.generate(config, baseAnalysis)).rejects.toThrow(
      /PayloadType conflict.*"value".*SET_STATUS.*SET_VOLUME/s
    );
  });
});
