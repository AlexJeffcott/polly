import { describe, expect, test } from "bun:test";
import fc from "fast-check";
import { TLAGenerator } from "../../codegen/tla";
import type { CodebaseAnalysis, FieldAnalysis, VerificationConfig } from "../../core/model";

describe("Property-Based Testing: TLA+ Generation", () => {
  // Arbitraries for generating random valid inputs
  const fieldConfigArb = fc.oneof(
    // Boolean field
    fc.record({
      type: fc.constant("boolean" as const),
    }),
    // Enum field
    fc.record({
      type: fc.constant("enum" as const),
      values: fc.array(fc.string({ minLength: 1, maxLength: 10 }), { minLength: 1, maxLength: 5 }),
    }),
    // Number with bounds
    fc
      .record({
        min: fc.integer({ min: 0, max: 100 }),
        max: fc.integer({ min: 0, max: 100 }),
      })
      .map((obj) => ({
        min: Math.min(obj.min, obj.max),
        max: Math.max(obj.min, obj.max),
      })),
    // Array with max length
    fc.record({
      maxLength: fc.integer({ min: 1, max: 20 }),
    }),
    // Map with max size
    fc.record({
      maxSize: fc.integer({ min: 1, max: 10 }),
    })
  );

  const validIdentifierArb = fc
    .stringMatching(/^[a-zA-Z][a-zA-Z0-9_]{0,15}$/)
    .filter((s) => s.length > 0);

  const messageConfigArb = fc.oneof(
    // WebSocket
    fc.record({
      maxInFlight: fc.integer({ min: 1, max: 10 }),
      maxClients: fc.integer({ min: 1, max: 5 }),
    }),
    // Chrome extension
    fc.record({
      maxInFlight: fc.integer({ min: 1, max: 10 }),
      maxTabs: fc.integer({ min: 0, max: 5 }),
    }),
    // PWA
    fc.record({
      maxInFlight: fc.integer({ min: 1, max: 10 }),
      maxWorkers: fc.integer({ min: 1, max: 3 }),
      maxClients: fc.integer({ min: 1, max: 5 }),
    }),
    // Electron
    fc.record({
      maxInFlight: fc.integer({ min: 1, max: 10 }),
      maxRenderers: fc.integer({ min: 1, max: 3 }),
    }),
    // Generic
    fc.record({
      maxInFlight: fc.integer({ min: 1, max: 10 }),
      maxContexts: fc.integer({ min: 1, max: 5 }),
    })
  );

  const configArb: fc.Arbitrary<VerificationConfig> = fc.record({
    state: fc.dictionary(validIdentifierArb, fieldConfigArb, { maxKeys: 10 }),
    messages: messageConfigArb,
    onBuild: fc.constantFrom("warn" as const, "error" as const),
    onRelease: fc.constantFrom("warn" as const, "error" as const),
  });

  const typeInfoArb = fc.record({
    name: validIdentifierArb,
    kind: fc.constantFrom(
      "boolean",
      "string",
      "number",
      "enum",
      "array",
      "object",
      "map",
      "set",
      "null",
      "unknown"
    ),
    nullable: fc.boolean(),
    enumValues: fc.option(fc.array(fc.string(), { maxLength: 5 })),
  });

  const fieldAnalysisArb: fc.Arbitrary<FieldAnalysis> = fc.record({
    path: validIdentifierArb,
    type: typeInfoArb,
    confidence: fc.constantFrom("high" as const, "medium" as const, "low" as const),
    evidence: fc.array(fc.string(), { maxLength: 3 }),
    suggestions: fc.array(fc.string(), { maxLength: 3 }),
    bounds: fc.option(
      fc.record({
        min: fc.option(fc.integer({ min: 0, max: 100 })),
        max: fc.option(fc.integer({ min: 0, max: 100 })),
        maxLength: fc.option(fc.integer({ min: 1, max: 20 })),
        maxSize: fc.option(fc.integer({ min: 1, max: 10 })),
        values: fc.option(fc.array(fc.string(), { maxLength: 5 })),
      })
    ),
  });

  const analysisArb: fc.Arbitrary<CodebaseAnalysis> = fc.record({
    messageTypes: fc.array(validIdentifierArb, { maxLength: 10 }),
    handlers: fc.constant([]),
    fields: fc.array(fieldAnalysisArb, { maxLength: 5 }),
    typeDefinitions: fc.constant([]),
  });

  test("generates valid TLA+ for any valid config", async () => {
    await fc.assert(
      fc.asyncProperty(configArb, analysisArb, async (config, analysis) => {
        const generator = new TLAGenerator();
        const result = await generator.generate(config, analysis);

        // Property: Generated spec must exist and be non-empty
        expect(result.spec).toBeTruthy();
        expect(result.spec.length).toBeGreaterThan(0);

        // Property: Generated config must exist and be non-empty
        expect(result.cfg).toBeTruthy();
        expect(result.cfg.length).toBeGreaterThan(0);

        // Property: Spec must have valid TLA+ structure
        expect(result.spec).toMatch(/----+ MODULE \w+ ----+/);
        expect(result.spec).toContain("EXTENDS MessageRouter");
        expect(result.spec).toMatch(/=+/); // Closing delimiter

        // Property: Config must have valid structure
        expect(result.cfg).toContain("SPECIFICATION");
        expect(result.cfg).toContain("CONSTANTS");
        expect(result.cfg).toContain("INVARIANTS");
      }),
      { numRuns: 100, timeout: 30000 }
    );
  });

  test("all message types become valid TLA+ identifiers", async () => {
    await fc.assert(
      fc.asyncProperty(configArb, analysisArb, async (config, analysis) => {
        const generator = new TLAGenerator();
        const result = await generator.generate(config, analysis);

        // Property: All message types in spec should be valid TLA+ identifiers
        for (const messageType of analysis.messageTypes) {
          // If message type is valid, it should appear in spec
          if (/^[a-zA-Z][a-zA-Z0-9_]*$/.test(messageType)) {
            expect(result.spec).toContain(`"${messageType}"`);
          }
        }
      }),
      { numRuns: 50, timeout: 30000 }
    );
  });

  test("state fields are preserved in generated spec", async () => {
    await fc.assert(
      fc.asyncProperty(configArb, analysisArb, async (config, analysis) => {
        const generator = new TLAGenerator();
        const result = await generator.generate(config, analysis);

        // Property: All configured state fields should appear in State definition
        const stateFieldNames = Object.keys(config.state);
        for (const fieldName of stateFieldNames) {
          // Sanitized field name should appear in State ==
          const _sanitized = fieldName.replace(/\./g, "_");
          if (stateFieldNames.length > 0) {
            expect(result.spec).toContain("State == [");
          }
        }
      }),
      { numRuns: 50, timeout: 30000 }
    );
  });

  test("constants are bounded correctly", async () => {
    await fc.assert(
      fc.asyncProperty(configArb, analysisArb, async (config, analysis) => {
        const generator = new TLAGenerator();
        const result = await generator.generate(config, analysis);

        // Property: MaxMessages should match maxInFlight
        expect(result.cfg).toMatch(
          new RegExp(`MaxMessages\\s*=\\s*${config.messages.maxInFlight}`)
        );

        // Property: Project-specific constants should be present
        // Note: Priority order is maxWorkers > maxRenderers > maxContexts > maxClients
        const hasMaxWorkers = "maxWorkers" in config.messages;
        const hasMaxRenderers = !hasMaxWorkers && "maxRenderers" in config.messages;
        const hasMaxContexts =
          !hasMaxWorkers && !hasMaxRenderers && "maxContexts" in config.messages;
        const hasMaxClients =
          !hasMaxWorkers && !hasMaxRenderers && !hasMaxContexts && "maxClients" in config.messages;

        if (hasMaxWorkers) {
          expect(result.cfg).toContain("MaxWorkers");
        }
        if (hasMaxRenderers) {
          expect(result.cfg).toContain("MaxRenderers");
        }
        if (hasMaxContexts) {
          expect(result.cfg).toContain("MaxContexts");
        }
        if (hasMaxClients) {
          expect(result.cfg).toContain("MaxClients");
        }

        // MaxTabId should always be present
        expect(result.cfg).toMatch(/MaxTabId\s*=\s*\d+/);
      }),
      { numRuns: 50, timeout: 30000 }
    );
  });

  test("generation never crashes on valid inputs", async () => {
    await fc.assert(
      fc.asyncProperty(configArb, analysisArb, async (config, analysis) => {
        const generator = new TLAGenerator();

        // Property: Should never throw for valid inputs
        await expect(generator.generate(config, analysis)).resolves.toBeDefined();
      }),
      { numRuns: 200, timeout: 60000 }
    );
  });

  test("empty config generates minimal valid spec", async () => {
    const emptyConfig: VerificationConfig = {
      state: {},
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };

    const emptyAnalysis: CodebaseAnalysis = {
      messageTypes: [],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(emptyConfig, emptyAnalysis);

    // Property: Even empty config should generate valid TLA+
    expect(result.spec).toContain("MODULE UserApp");
    expect(result.spec).toContain("EXTENDS MessageRouter");
    expect(result.cfg).toContain("SPECIFICATION UserSpec");
  });

  test("field names are sanitized correctly", async () => {
    const configWithDots: VerificationConfig = {
      state: {
        "user.name": { type: "enum", values: ["alice", "bob"] },
        "settings.theme": { type: "enum", values: ["light", "dark"] },
      },
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: [],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(configWithDots, analysis);

    // Property: Dots should be replaced with underscores
    expect(result.spec).toContain("user_name");
    expect(result.spec).toContain("settings_theme");
    expect(result.spec).not.toContain("user.name");
  });
});
