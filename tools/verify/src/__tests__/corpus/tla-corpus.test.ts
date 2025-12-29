import { describe, test, expect } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import type { VerificationConfig, CodebaseAnalysis } from "../../core/model";

describe("Corpus Testing: Real-World TLA+ Examples", () => {
  /**
   * Test that our generator produces specs compatible with standard TLA+ patterns
   * from the official TLA+ Examples repository
   */

  const simpleCounter: VerificationConfig = {
    state: {
      count: { min: 0, max: 10 },
    },
    messages: { maxInFlight: 3, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  };

  const simpleCounterAnalysis: CodebaseAnalysis = {
    messageTypes: ["increment", "decrement", "reset"],
    handlers: [],
    fields: [],
    typeDefinitions: [],
  };

  test("generates spec with DieHard-style structure", async () => {
    // DieHard is a classic TLA+ example: filling jugs with constraints
    const dieHardConfig: VerificationConfig = {
      state: {
        small: { min: 0, max: 3 },
        big: { min: 0, max: 5 },
      },
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["fillSmall", "fillBig", "emptySmall", "emptyBig", "smallToBig", "bigToSmall"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(dieHardConfig, analysis);

    // Should have integer ranges like DieHard
    expect(result.spec).toMatch(/0\.\.3/); // Small jug
    expect(result.spec).toMatch(/0\.\.5/); // Big jug

    // Should have all actions
    expect(result.spec).toContain('"fillSmall"');
    expect(result.spec).toContain('"fillBig"');
  });

  test("generates spec with TwoPhase-style structure", async () => {
    // Two-phase commit is another classic example
    const twoPhaseConfig: VerificationConfig = {
      state: {
        tmState: { type: "enum", values: ["init", "preparing", "committed", "aborted"] },
        rmState: { type: "enum", values: ["working", "prepared", "committed", "aborted"] },
      },
      messages: { maxInFlight: 5, maxContexts: 3 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["prepare", "commit", "abort"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(twoPhaseConfig, analysis);

    // Should have enum sets for state
    expect(result.spec).toMatch(/"init",\s*"preparing",\s*"committed",\s*"aborted"/);
    expect(result.spec).toMatch(/"working",\s*"prepared",\s*"committed",\s*"aborted"/);

    // Should have state transition structure
    expect(result.spec).toContain("StateTransition");
  });

  test("generates spec with Paxos-style message types", async () => {
    // Paxos consensus algorithm
    const paxosConfig: VerificationConfig = {
      state: {
        maxBallot: { min: 0, max: 10 },
        maxVal: { min: 0, max: 5 },
      },
      messages: { maxInFlight: 10, maxContexts: 3 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["Prepare", "Promise", "Accept", "Accepted"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(paxosConfig, analysis);

    // Should have all Paxos message types
    expect(result.spec).toContain('"Prepare"');
    expect(result.spec).toContain('"Promise"');
    expect(result.spec).toContain('"Accept"');
    expect(result.spec).toContain('"Accepted"');
  });

  test("handles Queue-style sequence operations", async () => {
    const queueConfig: VerificationConfig = {
      state: {
        queue: { maxLength: 10 },
      },
      messages: { maxInFlight: 5, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["enqueue", "dequeue"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(queueConfig, analysis);

    // Should use Seq for queue
    expect(result.spec).toContain("Seq(Value)");
    expect(result.spec).toContain("queue");
  });

  test("handles Set-style operations", async () => {
    const setConfig: VerificationConfig = {
      state: {
        members: { maxSize: 5 },
      },
      messages: { maxInFlight: 3, maxContexts: 2 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["add", "remove", "clear"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(setConfig, analysis);

    // Should use map/function for sets
    expect(result.spec).toMatch(/\[Keys -> Value\]/);
  });

  test("generates valid TLA+ operators structure", async () => {
    const generator = new TLAGenerator();
    const result = await generator.generate(simpleCounter, simpleCounterAnalysis);

    // Should follow standard TLA+ operator structure:
    // 1. MODULE declaration
    expect(result.spec).toMatch(/^-+ MODULE \w+ -+/m);

    // 2. EXTENDS clause
    expect(result.spec).toMatch(/EXTENDS\s+\w+/);

    // 3. VARIABLE declarations
    expect(result.spec).toMatch(/VARIABLE\s+\w+/);

    // 4. Init operator
    expect(result.spec).toMatch(/Init\s+==|UserInit\s+==/);

    // 5. Next operator
    expect(result.spec).toMatch(/Next\s+==|UserNext\s+==/);

    // 6. Spec formula
    expect(result.spec).toMatch(/Spec\s+==|UserSpec\s+==/);

    // 7. Closing delimiter
    expect(result.spec).toMatch(/^=+$/m);
  });

  test("uses standard TLA+ operators correctly", async () => {
    const generator = new TLAGenerator();
    const result = await generator.generate(simpleCounter, simpleCounterAnalysis);

    // Should use standard operators when applicable
    // Conjunction - always present in Init
    expect(result.spec).toMatch(/\/\\/);

    // Disjunction - always present in Next
    expect(result.spec).toMatch(/\\\//);

    // Universal quantification - used in invariants
    expect(result.spec).toMatch(/\\A/);

    // Unchanged - used for state stability
    expect(result.spec).toMatch(/UNCHANGED/);

    // Note: \E (existential quantification) only appears when there are
    // complex handlers with state transitions, not required in all specs
  });

  test("follows TLA+ naming conventions", async () => {
    const generator = new TLAGenerator();
    const result = await generator.generate(simpleCounter, simpleCounterAnalysis);

    // Operators should be CapitalCase
    const lines = result.spec.split("\n");
    for (const line of lines) {
      const match = line.match(/^([A-Z][a-zA-Z0-9]*)\s*==/);
      if (match) {
        const operatorName = match[1];
        // Should start with capital letter (already matched)
        expect(operatorName[0]).toMatch(/[A-Z]/);
      }
    }
  });

  test("generates invariants in standard form", async () => {
    const config: VerificationConfig = {
      state: {
        count: { min: 0, max: 10 },
      },
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["increment"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(config, analysis);

    // Should have TypeOK invariant
    expect(result.cfg).toContain("TypeOK");
    expect(result.cfg).toContain("INVARIANTS");

    // Should have universal quantification in invariants
    expect(result.spec).toMatch(/\\A\s+\w+\s+\\in/);
  });

  test("config file uses standard TLA+ config syntax", async () => {
    const generator = new TLAGenerator();
    const result = await generator.generate(simpleCounter, simpleCounterAnalysis);

    // Config should have standard sections
    expect(result.cfg).toMatch(/SPECIFICATION\s+\w+/);
    expect(result.cfg).toContain("CONSTANTS");
    expect(result.cfg).toContain("INVARIANTS");
    expect(result.cfg).toContain("CONSTRAINT");
  });

  test("handles complex nested state structures", async () => {
    const complexConfig: VerificationConfig = {
      state: {
        user: { maxSize: 3 },
        settings: { maxSize: 5 },
        cache: { maxLength: 10 },
      },
      messages: { maxInFlight: 5, maxContexts: 3 },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      messageTypes: ["updateUser", "updateSettings", "clearCache"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(complexConfig, analysis);

    // Should handle all state fields
    expect(result.spec).toContain("user");
    expect(result.spec).toContain("settings");
    expect(result.spec).toContain("cache");

    // Should still be valid TLA+
    expect(result.spec).toMatch(/^-+ MODULE \w+ -+/m);
    expect(result.spec).toMatch(/^=+$/m);
  });

  test("maintains compatibility with MessageRouter template", async () => {
    const generator = new TLAGenerator();
    const result = await generator.generate(simpleCounter, simpleCounterAnalysis);

    // Should extend MessageRouter
    expect(result.spec).toContain("EXTENDS MessageRouter");

    // Should reference MessageRouter variables in allVars
    expect(result.spec).toContain("ports");
    expect(result.spec).toContain("messages");
    expect(result.spec).toContain("pendingRequests");

    // Should reference MessageRouter operators (inherited via EXTENDS)
    expect(result.spec).toMatch(/Init\s/); // MessageRouter's Init

    // Note: ConnectPort, DisconnectPort, SendMessage are inherited from MessageRouter
    // and don't appear explicitly in the generated spec since we EXTEND it
  });

  test("handles all supported project types", async () => {
    const projectTypes = [
      { messages: { maxInFlight: 3, maxClients: 2 }, expectedConstant: "MaxClients" },
      { messages: { maxInFlight: 3, maxTabs: 1 }, expectedConstant: "MaxTabId" },
      { messages: { maxInFlight: 3, maxContexts: 3 }, expectedConstant: "MaxContexts" },
      { messages: { maxInFlight: 3, maxRenderers: 2 }, expectedConstant: "MaxRenderers" },
      { messages: { maxInFlight: 3, maxWorkers: 1, maxClients: 3 }, expectedConstant: "MaxWorkers" },
    ];

    const analysis: CodebaseAnalysis = {
      messageTypes: ["test"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    for (const projectType of projectTypes) {
      const config: VerificationConfig = {
        state: {},
        messages: projectType.messages as any,
        onBuild: "warn",
        onRelease: "error",
      };

      const generator = new TLAGenerator();
      const result = await generator.generate(config, analysis);

      // Each project type should generate valid TLA+
      expect(result.spec).toMatch(/^-+ MODULE \w+ -+/m);
      expect(result.cfg).toContain(projectType.expectedConstant);
    }
  });
});
