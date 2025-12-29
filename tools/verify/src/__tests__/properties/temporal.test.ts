// Tests for temporal property generation

import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../../analysis/src/extract/types";
import {
  TemporalPatterns,
  type TemporalProperty,
  TemporalPropertyGenerator,
  TemporalTLAGenerator,
} from "../../codegen/temporal";

describe("Temporal Property Generation", () => {
  const createAnalysis = (messageTypes: string[], handlers: any[] = []): CodebaseAnalysis => ({
    messageTypes,
    handlers,
    fields: [],
    typeDefinitions: [],
  });

  // ============================================================================
  // Basic Property Generation (10 tests)
  // ============================================================================

  test("generates init-first property when init exists", () => {
    const analysis = createAnalysis(["init", "update", "delete"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const initProp = properties.find((p) => p.name === "InitMessageFirst");
    expect(initProp).toBeDefined();
    expect(initProp?.type).toBe("order");
    expect(initProp?.target).toBe("init");
  });

  test("does not generate init-first when no init message", () => {
    const analysis = createAnalysis(["update", "delete"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const initProp = properties.find((p) => p.name === "InitMessageFirst");
    expect(initProp).toBeUndefined();
  });

  test("detects request-response pattern", () => {
    const analysis = createAnalysis(["request", "response"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const reqResProp = properties.find((p) => p.name.includes("RequestEventuallyGets"));
    expect(reqResProp).toBeDefined();
    expect(reqResProp?.type).toBe("implies-eventually");
  });

  test("detects query-result pattern", () => {
    const analysis = createAnalysis(["query", "result"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const queryProp = properties.find((p) => p.name.includes("QueryEventuallyGets"));
    expect(queryProp).toBeDefined();
  });

  test("detects command-ack pattern", () => {
    const analysis = createAnalysis(["command", "ack"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const cmdProp = properties.find((p) => p.name.includes("CommandEventuallyGets"));
    expect(cmdProp).toBeDefined();
  });

  test("detects send-receive pattern", () => {
    const analysis = createAnalysis(["send", "receive"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const sendProp = properties.find((p) => p.name.includes("SendEventuallyGets"));
    expect(sendProp).toBeDefined();
  });

  test("detects start-complete pattern", () => {
    const analysis = createAnalysis(["start", "complete"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const startProp = properties.find((p) => p.name.includes("EventuallyCompletes"));
    expect(startProp).toBeDefined();
    expect(startProp?.type).toBe("implies-eventually");
  });

  test("detects start-finish pattern", () => {
    const analysis = createAnalysis(["start", "finish"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const startProp = properties.find((p) => p.name.includes("EventuallyCompletes"));
    expect(startProp).toBeDefined();
  });

  test("handles multiple request-response patterns", () => {
    const analysis = createAnalysis(["request", "response", "query", "result"]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const patterns = properties.filter((p) => p.name.includes("EventuallyGets"));
    expect(patterns.length).toBeGreaterThanOrEqual(2);
  });

  test("generates properties for empty analysis", () => {
    const analysis = createAnalysis([]);

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    expect(properties).toHaveLength(0);
  });

  // ============================================================================
  // Handler-Based Property Generation (5 tests)
  // ============================================================================

  test("detects ordering from handler preconditions", () => {
    const analysis = createAnalysis(
      ["login", "updateProfile"],
      [
        {
          messageType: "updateProfile",
          preconditions: [
            {
              expression: "state.authenticated === true",
              location: { line: 1, column: 1 },
            },
          ],
          location: { file: "test.ts", line: 1, column: 1 },
          mutations: [],
          postconditions: [],
        },
      ]
    );

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const authProp = properties.find((p) => p.name.includes("RequiresLogin"));
    expect(authProp).toBeDefined();
    expect(authProp?.type).toBe("implies-eventually");
  });

  test("includes location info from handlers", () => {
    const analysis = createAnalysis(
      ["login", "updateProfile"],
      [
        {
          messageType: "updateProfile",
          preconditions: [
            {
              expression: "state.authenticated === true",
              location: { line: 42, column: 10 },
            },
          ],
          location: { file: "handlers.ts", line: 42, column: 10 },
          mutations: [],
          postconditions: [],
        },
      ]
    );

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const authProp = properties.find((p) => p.name.includes("RequiresLogin"));
    expect(authProp?.location).toBeDefined();
    expect(authProp?.location?.file).toBe("handlers.ts");
    expect(authProp?.location?.line).toBe(42);
  });

  test("ignores handlers without authentication preconditions", () => {
    const analysis = createAnalysis(
      ["login", "increment"],
      [
        {
          messageType: "increment",
          preconditions: [
            {
              expression: "state.count < 100",
              location: { line: 1, column: 1 },
            },
          ],
          location: { file: "test.ts", line: 1, column: 1 },
          mutations: [],
          postconditions: [],
        },
      ]
    );

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const authProp = properties.find((p) => p.name.includes("RequiresLogin"));
    expect(authProp).toBeUndefined();
  });

  test("handles handlers with multiple preconditions", () => {
    const analysis = createAnalysis(
      ["login", "adminAction"],
      [
        {
          messageType: "adminAction",
          preconditions: [
            {
              expression: "state.authenticated === true",
              location: { line: 1, column: 1 },
            },
            {
              expression: "state.role === 'admin'",
              location: { line: 2, column: 1 },
            },
          ],
          location: { file: "test.ts", line: 1, column: 1 },
          mutations: [],
          postconditions: [],
        },
      ]
    );

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const authProp = properties.find((p) => p.name.includes("RequiresLogin"));
    expect(authProp).toBeDefined();
  });

  test("skips login requirement when no login message exists", () => {
    const analysis = createAnalysis(
      ["updateProfile"],
      [
        {
          messageType: "updateProfile",
          preconditions: [
            {
              expression: "state.authenticated === true",
              location: { line: 1, column: 1 },
            },
          ],
          location: { file: "test.ts", line: 1, column: 1 },
          mutations: [],
          postconditions: [],
        },
      ]
    );

    const generator = new TemporalPropertyGenerator();
    const properties = generator.generateProperties(analysis);

    const authProp = properties.find((p) => p.name.includes("RequiresLogin"));
    expect(authProp).toBeUndefined();
  });

  // ============================================================================
  // Custom Ordering Rules (5 tests)
  // ============================================================================

  test("creates custom ordering rule", () => {
    const generator = new TemporalPropertyGenerator();

    const property = generator.createOrderingRule({
      first: "connect",
      second: "send",
      description: "Must connect before sending",
    });

    expect(property.name).toBe("connectBeforesend");
    expect(property.type).toBe("order");
    expect(property.description).toBe("Must connect before sending");
  });

  test("ordering rule has correct trigger and target", () => {
    const generator = new TemporalPropertyGenerator();

    const property = generator.createOrderingRule({
      first: "login",
      second: "logout",
      description: "Must login before logout",
    });

    expect(property.trigger).toBe('delivered["logout"]');
    expect(property.target).toBe('delivered["login"]');
  });

  test("ordering rule handles message names with special chars", () => {
    const generator = new TemporalPropertyGenerator();

    const property = generator.createOrderingRule({
      first: "user-login",
      second: "user-logout",
      description: "Login before logout",
    });

    expect(property.trigger).toContain("user-logout");
    expect(property.target).toContain("user-login");
  });

  test("ordering rule description is preserved", () => {
    const generator = new TemporalPropertyGenerator();

    const property = generator.createOrderingRule({
      first: "A",
      second: "B",
      description: "Very specific ordering constraint for business logic",
    });

    expect(property.description).toBe("Very specific ordering constraint for business logic");
  });

  test("multiple ordering rules can be created", () => {
    const generator = new TemporalPropertyGenerator();

    const rules = [
      { first: "A", second: "B", description: "A before B" },
      { first: "B", second: "C", description: "B before C" },
      { first: "A", second: "C", description: "A before C" },
    ];

    const properties = rules.map((rule) => generator.createOrderingRule(rule));

    expect(properties).toHaveLength(3);
    expect(properties[0]?.name).toBe("ABeforeB");
    expect(properties[1]?.name).toBe("BBeforeC");
    expect(properties[2]?.name).toBe("ABeforeC");
  });
});

describe("Temporal TLA+ Generation", () => {
  // ============================================================================
  // Eventually Properties (3 tests)
  // ============================================================================

  test("generates eventually property", () => {
    const property: TemporalProperty = {
      name: "EventuallyComplete",
      description: "System eventually completes",
      type: "eventually",
      target: "state.done = TRUE",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla).toHaveLength(1);
    expect(tla[0]).toContain("EventuallyComplete == <>(state.done = TRUE)");
  });

  test("includes description as comment", () => {
    const property: TemporalProperty = {
      name: "EventuallyComplete",
      description: "System eventually completes processing",
      type: "eventually",
      target: "done",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("\\* System eventually completes processing");
  });

  test("handles empty description", () => {
    const property: TemporalProperty = {
      name: "Prop",
      description: "",
      type: "eventually",
      target: "done",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).not.toContain("\\*");
    expect(tla[0]).toContain("Prop == <>(done)");
  });

  // ============================================================================
  // Always Properties (2 tests)
  // ============================================================================

  test("generates always property", () => {
    const property: TemporalProperty = {
      name: "AlwaysPositive",
      description: "Count always positive",
      type: "always",
      target: "state.count > 0",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("AlwaysPositive == [](state.count > 0)");
  });

  test("always property uses [] operator", () => {
    const property: TemporalProperty = {
      name: "SafetyProperty",
      description: "",
      type: "always",
      target: "safe",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("[]");
    expect(tla[0]).not.toContain("<>");
  });

  // ============================================================================
  // Implies-Eventually Properties (3 tests)
  // ============================================================================

  test("generates implies-eventually property", () => {
    const property: TemporalProperty = {
      name: "RequestGetsResponse",
      description: "Every request gets response",
      type: "implies-eventually",
      trigger: 'delivered["request"]',
      target: 'delivered["response"]',
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("RequestGetsResponse == ");
    expect(tla[0]).toContain('delivered["request"] => <>');
    expect(tla[0]).toContain('delivered["response"]');
  });

  test("implies-eventually uses []( => <>) pattern", () => {
    const property: TemporalProperty = {
      name: "Pattern",
      description: "",
      type: "implies-eventually",
      trigger: "A",
      target: "B",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("[](");
    expect(tla[0]).toContain(" => <>(");
  });

  test("handles complex trigger expressions", () => {
    const property: TemporalProperty = {
      name: "ComplexTrigger",
      description: "",
      type: "implies-eventually",
      trigger: "state.count > 0 /\\ state.active",
      target: "state.done",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("state.count > 0 /\\ state.active");
  });

  // ============================================================================
  // Ordering Properties (3 tests)
  // ============================================================================

  test("generates ordering property", () => {
    const property: TemporalProperty = {
      name: "LoginBeforeUpdate",
      description: "Login before update",
      type: "order",
      trigger: 'delivered["update"]',
      target: 'delivered["login"]',
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("LoginBeforeUpdate == ");
    expect(tla[0]).toContain('[](delivered["update"] => delivered["login"])');
  });

  test("generates init-first ordering (special case)", () => {
    const property: TemporalProperty = {
      name: "InitMessageFirst",
      description: "Init first",
      type: "order",
      target: "init",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("InitMessageFirst == ");
    expect(tla[0]).toContain('delivered["init"]');
    expect(tla[0]).toContain("MessageTypes");
  });

  test("ordering uses always implication", () => {
    const property: TemporalProperty = {
      name: "OrderProp",
      description: "",
      type: "order",
      trigger: "second",
      target: "first",
    };

    const generator = new TemporalTLAGenerator();
    const tla = generator.generateTLAProperties([property]);

    expect(tla[0]).toContain("[](");
    expect(tla[0]).toContain(" => ");
    expect(tla[0]).not.toContain("<>");
  });

  // ============================================================================
  // Config Generation (1 test)
  // ============================================================================

  test("generates config file property declarations", () => {
    const properties: TemporalProperty[] = [
      {
        name: "Prop1",
        description: "",
        type: "eventually",
        target: "done",
      },
      {
        name: "Prop2",
        description: "",
        type: "always",
        target: "safe",
      },
    ];

    const generator = new TemporalTLAGenerator();
    const config = generator.generateConfigProperties(properties);

    expect(config).toHaveLength(2);
    expect(config[0]).toBe("PROPERTY Prop1");
    expect(config[1]).toBe("PROPERTY Prop2");
  });

  // ============================================================================
  // Delivered Variables (1 test)
  // ============================================================================

  test("generates delivered tracking variables", () => {
    const generator = new TemporalTLAGenerator();
    const vars = generator.generateDeliveredVariables();

    expect(vars).toContain("VARIABLE delivered");
    expect(vars).toContain("InitDelivered");
    expect(vars).toContain("MarkDelivered");
    expect(vars).toContain("[msg \\in MessageTypes |-> FALSE]");
  });
});

describe("Temporal Patterns", () => {
  test("creates eventually pattern", () => {
    const prop = TemporalPatterns.eventually("Done", "Eventually done", "state.done");

    expect(prop.name).toBe("Done");
    expect(prop.type).toBe("eventually");
    expect(prop.target).toBe("state.done");
  });

  test("creates always pattern", () => {
    const prop = TemporalPatterns.always("Safe", "Always safe", "state.safe");

    expect(prop.name).toBe("Safe");
    expect(prop.type).toBe("always");
    expect(prop.target).toBe("state.safe");
  });

  test("creates implies-eventually pattern", () => {
    const prop = TemporalPatterns.impliesEventually("ReqResp", "Request response", "req", "resp");

    expect(prop.name).toBe("ReqResp");
    expect(prop.type).toBe("implies-eventually");
    expect(prop.trigger).toBe("req");
    expect(prop.target).toBe("resp");
  });

  test("creates ordering pattern", () => {
    const prop = TemporalPatterns.ordering("A", "B", "A before B");

    expect(prop.name).toBe("ABeforeB");
    expect(prop.type).toBe("order");
    expect(prop.trigger).toContain("B");
    expect(prop.target).toContain("A");
  });

  test("creates request-response pattern", () => {
    const prop = TemporalPatterns.requestResponse("request", "response");

    expect(prop.name).toBe("requestEventuallyGetsresponse");
    expect(prop.type).toBe("implies-eventually");
    expect(prop.trigger).toContain("request");
    expect(prop.target).toContain("response");
  });
});
