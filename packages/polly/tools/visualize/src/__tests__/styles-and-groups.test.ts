import { describe, expect, test } from "bun:test";
import type { ArchitectureAnalysis, ContextInfo } from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL, type StructurizrDSLOptions } from "../codegen/structurizr";

// generateElementStyle, generateRelationshipStyle, getContextTechnology,
// generateComponentDefinition and the automatic-grouping helpers are private,
// so these tests read them through the DSL that generateStructurizrDSL emits.

function handler(messageType: string): MessageHandler {
  return {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: "/test/background.ts", line: 7 },
    messageType,
  };
}

function context(type: string, handlers: MessageHandler[] = []): ContextInfo {
  return {
    type: type as ContextInfo["type"],
    entryPoint: `${type}.ts`,
    handlers,
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
  };
}

function analysisWith(
  handlers: MessageHandler[],
  extraContexts: Record<string, ContextInfo> = {}
): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test Extension", version: "1.0.0", description: "Test" },
    contexts: { background: context("background", handlers), ...extraContexts },
    messageFlows: [],
    integrations: [],
  };
}

function dslFor(types: string[], options?: StructurizrDSLOptions): string {
  return generateStructurizrDSL(analysisWith(types.map(handler)), options);
}

/** The body of the background container, up to its closing brace. */
function backgroundBody(dsl: string): string {
  const lines = dsl.split("\n");
  const start = lines.findIndex((l) => l.startsWith("      background = container "));
  const end = lines.findIndex((l, i) => i > start && l === "      }");
  return lines
    .slice(start + 1, end)
    .join("\n")
    .trimEnd();
}

/**
 * Groups and component ids in the background container, with their
 * indentation kept: a grouped component sits two spaces deeper than its
 * group header, an ungrouped one at the group-header depth.
 */
function layout(dsl: string): string[] {
  const out: string[] = [];
  for (const line of backgroundBody(dsl).split("\n")) {
    const group = line.match(/^( *)group "(.*)" \{$/);
    if (group) {
      out.push(`${group[1]}group ${group[2]}`);
      continue;
    }
    const comp = line.match(/^( *)(\w+) = component /);
    if (comp) out.push(`${comp[1]}${comp[2]}`);
  }
  return out;
}

const G = "        "; // group header / ungrouped component indent
const C = "          "; // grouped component indent

/** One `element "tag" { ... }` or `relationship "tag" { ... }` block. */
function styleBlock(dsl: string, kind: "element" | "relationship", tag: string): string {
  const header = `      ${kind} "${tag}" {`;
  const start = dsl.indexOf(header);
  if (start < 0) return "";
  const end = dsl.indexOf("\n      }", start);
  return dsl.slice(start, end + "\n      }".length);
}

describe("element styles", () => {
  test("every field is emitted in a fixed order", () => {
    const dsl = dslFor([], {
      styles: {
        elements: {
          Full: {
            shape: "Box",
            icon: "https://example.com/i.png",
            width: 450,
            height: 300,
            background: "#111111",
            color: "#222222",
            fontSize: 20,
            border: "Dashed",
            opacity: 40,
            metadata: true,
            description: true,
          },
        },
      },
    });
    expect(styleBlock(dsl, "element", "Full")).toBe(
      [
        '      element "Full" {',
        "        shape Box",
        "        icon https://example.com/i.png",
        "        width 450",
        "        height 300",
        "        background #111111",
        "        color #222222",
        "        fontSize 20",
        "        border Dashed",
        "        opacity 40",
        "        metadata true",
        "        description true",
        "      }",
      ].join("\n")
    );
  });

  test("opacity 0, metadata false and description false are still emitted", () => {
    const dsl = dslFor([], {
      styles: { elements: { Falsy: { opacity: 0, metadata: false, description: false } } },
    });
    expect(styleBlock(dsl, "element", "Falsy")).toBe(
      [
        '      element "Falsy" {',
        "        opacity 0",
        "        metadata false",
        "        description false",
        "      }",
      ].join("\n")
    );
  });

  test("an empty style emits only the braces", () => {
    const dsl = dslFor([], { styles: { elements: { Empty: {} } } });
    expect(styleBlock(dsl, "element", "Empty")).toBe('      element "Empty" {\n      }');
  });

  for (const [field, value] of [
    ["shape", "Circle"],
    ["icon", "x.png"],
    ["width", 10],
    ["height", 11],
    ["background", "#abcdef"],
    ["color", "#fedcba"],
    ["fontSize", 9],
    ["border", "Dotted"],
  ] as const) {
    test(`a style with only ${field} emits only ${field}`, () => {
      const dsl = dslFor([], { styles: { elements: { One: { [field]: value } } } });
      expect(styleBlock(dsl, "element", "One")).toBe(
        `      element "One" {\n        ${field} ${value}\n      }`
      );
    });
  }

  test("default element styles are emitted", () => {
    const dsl = dslFor([]);
    expect(styleBlock(dsl, "element", "Message Handler")).toBe(
      [
        '      element "Message Handler" {',
        "        shape Hexagon",
        "        background #1168bd",
        "        color #ffffff",
        "        fontSize 14",
        "      }",
      ].join("\n")
    );
  });
});

describe("relationship styles", () => {
  test("every field is emitted in a fixed order", () => {
    const dsl = dslFor([], {
      styles: {
        relationships: {
          Full: {
            thickness: 4,
            color: "#333333",
            style: "Dotted",
            routing: "Curved",
            fontSize: 18,
            width: 200,
            position: 60,
            opacity: 70,
          },
        },
      },
    });
    expect(styleBlock(dsl, "relationship", "Full")).toBe(
      [
        '      relationship "Full" {',
        "        thickness 4",
        "        color #333333",
        "        style Dotted",
        "        routing Curved",
        "        fontSize 18",
        "        width 200",
        "        position 60",
        "        opacity 70",
        "      }",
      ].join("\n")
    );
  });

  test("opacity 0 is still emitted", () => {
    const dsl = dslFor([], { styles: { relationships: { Zero: { opacity: 0 } } } });
    expect(styleBlock(dsl, "relationship", "Zero")).toBe(
      '      relationship "Zero" {\n        opacity 0\n      }'
    );
  });

  test("an empty style emits only the braces", () => {
    const dsl = dslFor([], { styles: { relationships: { Empty: {} } } });
    expect(styleBlock(dsl, "relationship", "Empty")).toBe('      relationship "Empty" {\n      }');
  });

  for (const [field, value] of [
    ["thickness", 5],
    ["color", "#010203"],
    ["style", "Solid"],
    ["routing", "Direct"],
    ["fontSize", 8],
    ["width", 120],
    ["position", 30],
  ] as const) {
    test(`a style with only ${field} emits only ${field}`, () => {
      const dsl = dslFor([], { styles: { relationships: { One: { [field]: value } } } });
      expect(styleBlock(dsl, "relationship", "One")).toBe(
        `      relationship "One" {\n        ${field} ${value}\n      }`
      );
    });
  }
});

describe("styles section", () => {
  test("holds only style blocks: headers, one-line fields and closers", () => {
    const dsl = dslFor([], {
      styles: {
        elements: { Extra: { shape: "Box" } },
        relationships: { Extra: { thickness: 1 } },
      },
    });
    const start = dsl.indexOf("    styles {\n");
    const end = dsl.indexOf("\n    }", start);
    const lines = dsl.slice(start + "    styles {\n".length, end).split("\n");
    const stray = lines.filter(
      (l) => !/^ {6}(element|relationship) "[^"]+" \{$|^ {8}\w+ \S+$|^ {6}\}$/.test(l)
    );
    expect(stray).toEqual([]);
    expect(lines.filter((l) => l.startsWith('      relationship "'))).toEqual([
      '      relationship "Relationship" {',
      '      relationship "Sync" {',
      '      relationship "Async" {',
      '      relationship "Database" {',
      '      relationship "Extra" {',
    ]);
  });
});

describe("container technology labels", () => {
  const cases: Array<[string, string]> = [
    ["background", "Service Worker / Background Script"],
    ["content", "Content Script"],
    ["popup", "Browser Action Popup"],
    ["devtools", "DevTools Panel"],
    ["options", "Options Page"],
    ["offscreen", "Offscreen Document"],
    ["server", "Server Application"],
    ["client", "Client Application"],
    ["shared", "Shared Library"],
    ["worker", "Application Context"],
  ];

  test("each context type gets its technology label", () => {
    const extra: Record<string, ContextInfo> = {};
    for (const [type] of cases) {
      if (type !== "background") extra[type] = context(type);
    }
    const dsl = generateStructurizrDSL(analysisWith([], extra));
    for (const [type, technology] of cases) {
      const cap = type.charAt(0).toUpperCase() + type.slice(1);
      expect(dsl).toContain(
        `\n      ${type} = container "${cap}" "${cap} context" "${technology}" {\n`
      );
    }
  });
});

describe("component definitions", () => {
  test("tags, properties and perspectives are emitted and escaped", () => {
    const dsl = dslFor(["LOGIN", "PING"], {
      perspectives: {
        login_handler: [
          { name: 'Sec"urity', description: 'Holds "tokens"' },
          { name: "Perf", description: "Fast" },
        ],
      },
      properties: { PING: { Source: "", Owner: 'team "a"' } },
    });
    expect(backgroundBody(dsl)).toBe(
      [
        '        group "Authentication" {',
        '          login_handler = component "Login Handler" "Authenticates users and establishes sessions" {',
        '            tags "Message Handler" "Authentication"',
        "            properties {",
        '              "Source" "background.ts:7"',
        '              "Technology" "TypeScript"',
        '              "Message Type" "Authentication"',
        '              "Pattern" "Authentication Handler"',
        "            }",
        "            perspectives {",
        '              "Sec\\"urity" "Holds \\"tokens\\""',
        '              "Perf" "Fast"',
        "            }",
        "          }",
        "        }",
        "",
        '        ping_handler = component "Ping Handler" "Processes PING messages and coordinates business logic" {',
        '          tags "Message Handler"',
        "          properties {",
        '            "Technology" "TypeScript"',
        '            "Pattern" "Message Handler"',
        '            "Owner" "team \\"a\\""',
        "          }",
        "        }",
      ].join("\n")
    );
  });

  test("the description is escaped", () => {
    const body = backgroundBody(dslFor(['say"hi']));
    expect(body).toContain('"Processes say\\"hi messages and coordinates business logic" {');
  });
});

describe("explicit groups", () => {
  test("named groups wrap their components; first group wins; empty groups are skipped", () => {
    const dsl = dslFor(["ALPHA", "BETA", "GAMMA"], {
      groups: [
        { name: 'Core "x"', components: ["beta_handler", "alpha_handler"] },
        { name: "Nothing", components: ["missing_handler"] },
        { name: "Again", components: ["alpha_handler"] },
      ],
    });
    const body = backgroundBody(dsl);
    expect(body.split("\n").filter((l) => /group |^ {8}\}$|^$/.test(l))).toEqual([
      '        group "Core \\"x\\"" {',
      "        }",
      "",
      "        }",
    ]);
    expect(layout(dsl)).toEqual([
      `${G}group Core \\"x\\"`,
      `${C}alpha_handler`,
      `${C}beta_handler`,
      `${G}gamma_handler`,
    ]);
  });
});

describe("automatic groups", () => {
  test("every auth keyword joins Authentication, case-insensitively", () => {
    const dsl = dslFor(["DO_LOGIN", "DO_LOGOUT", "X_AUTH", "VERIFY_X", "REGISTER", "SIGNUP"]);
    expect(layout(dsl)).toEqual([
      `${G}group Authentication`,
      `${C}do_login_handler`,
      `${C}do_logout_handler`,
      `${C}x_auth_handler`,
      `${C}verify_x_handler`,
      `${C}register_handler`,
      `${C}signup_handler`,
    ]);
  });

  test("subscribe types join Subscriptions; a lone group of half the components is kept", () => {
    expect(layout(dslFor(["SUBSCRIBE_FEED", "Z1"]))).toEqual([
      `${G}group Subscriptions`,
      `${C}subscribe_feed_handler`,
      `${G}z1_handler`,
    ]);
    expect(layout(dslFor(["UNSUBSCRIBE_FEED", "SUBSCRIBE_X"]))).toEqual([
      `${G}group Subscriptions`,
      `${C}unsubscribe_feed_handler`,
      `${C}subscribe_x_handler`,
    ]);
  });

  test("a component matching auth and subscribe is declared once, under Authentication", () => {
    expect(layout(dslFor(["AUTH_SUBSCRIBE", "SUBSCRIBE_X"]))).toEqual([
      `${G}group Authentication`,
      `${C}auth_subscribe_handler`,
      `${G}group Subscriptions`,
      `${C}subscribe_x_handler`,
    ]);
    expect(layout(dslFor(["AUTH_SUBSCRIBE"]))).toEqual([
      `${G}group Authentication`,
      `${C}auth_subscribe_handler`,
    ]);
  });

  test("a lone Subscriptions group under half the components is dropped", () => {
    // No auth handler means no Authentication group, so Subscriptions is the
    // only group and one of three is under half.
    expect(layout(dslFor(["SUBSCRIBE", "Z1", "Z2"]))).toEqual([
      `${G}subscribe_handler`,
      `${G}z1_handler`,
      `${G}z2_handler`,
    ]);
  });

  test("one group under half the components is dropped", () => {
    expect(layout(dslFor(["LOGIN", "Z1", "Z2"]))).toEqual([
      `${G}login_handler`,
      `${G}z1_handler`,
      `${G}z2_handler`,
    ]);
  });

  test("two groups are kept even under half the components", () => {
    expect(layout(dslFor(["LOGIN", "SUBSCRIBE", "Z1", "Z2", "Z3"]))).toEqual([
      `${G}group Authentication`,
      `${C}login_handler`,
      `${G}group Subscriptions`,
      `${C}subscribe_handler`,
      `${G}z1_handler`,
      `${G}z2_handler`,
      `${G}z3_handler`,
    ]);
  });

  test("entity_action types group by entity", () => {
    expect(layout(dslFor(["USER_ADD", "USER_REMOVE", "Z1"]))).toEqual([
      `${G}group User Management`,
      `${C}user_add_handler`,
      `${C}user_remove_handler`,
      `${G}z1_handler`,
    ]);
  });

  test("actionEntity types group by entity", () => {
    expect(layout(dslFor(["addUser", "removeUser"]))).toEqual([
      `${G}group User Management`,
      `${C}adduser_handler`,
      `${C}removeuser_handler`,
    ]);
  });

  test("a plain entity name groups with entity_action types", () => {
    expect(layout(dslFor(["TODO", "TODO_LOAD"]))).toEqual([
      `${G}group Todo Management`,
      `${C}todo_handler`,
      `${C}todo_load_handler`,
    ]);
  });

  test("entity_action must start the type", () => {
    // "x9_user_add" has no leading entity, so it is not in User Management;
    // both fall through to Command Handlers.
    expect(layout(dslFor(["X9_USER_ADD", "USER_REMOVE"]))).toEqual([
      `${G}group Command Handlers`,
      `${C}x9_user_add_handler`,
      `${C}user_remove_handler`,
    ]);
  });

  test("entity actions cover every verb", () => {
    for (const verb of ["create", "update", "delete", "get", "fetch", "list", "query"]) {
      expect(layout(dslFor([`ITEM_${verb.toUpperCase()}`, "ITEM_ADD"]))).toEqual([
        `${G}group Item Management`,
        `${C}item_${verb}_handler`,
        `${C}item_add_handler`,
      ]);
      expect(layout(dslFor([`${verb}Item`, "addItem"]))).toEqual([
        `${G}group Item Management`,
        `${C}${verb}item_handler`,
        `${C}additem_handler`,
      ]);
    }
  });

  test("WebSocket lifecycle types are never entities", () => {
    for (const word of ["CONNECTION", "MESSAGE", "CLOSE", "ERROR"]) {
      const lower = word.toLowerCase();
      expect(layout(dslFor([word, `${word}_FETCH`]))).toEqual([
        `${G}${lower}_handler`,
        `${G}${lower}_fetch_handler`,
      ]);
    }
  });

  test("components already in Authentication do not count towards an entity", () => {
    expect(layout(dslFor(["USER_ADD_LOGIN", "USER_REMOVE"]))).toEqual([
      `${G}group Authentication`,
      `${C}user_add_login_handler`,
      `${G}user_remove_handler`,
    ]);
  });

  test("every query keyword joins Query Handlers", () => {
    expect(
      layout(dslFor(["QA_QUERY", "QB_GET", "QC_FETCH", "QD_LOAD", "QE_LIST", "QF_READ"]))
    ).toEqual([
      `${G}group Query Handlers`,
      `${C}qa_query_handler`,
      `${C}qb_get_handler`,
      `${C}qc_fetch_handler`,
      `${C}qd_load_handler`,
      `${C}qe_list_handler`,
      `${C}qf_read_handler`,
    ]);
  });

  test("every command keyword joins Command Handlers", () => {
    expect(
      layout(
        dslFor([
          "CA_COMMAND",
          "CB_ADD",
          "CC_CREATE",
          "CD_UPDATE",
          "CE_DELETE",
          "CF_REMOVE",
          "CG_SET",
          "CH_CLEAR",
        ])
      )
    ).toEqual([
      `${G}group Command Handlers`,
      `${C}ca_command_handler`,
      `${C}cb_add_handler`,
      `${C}cc_create_handler`,
      `${C}cd_update_handler`,
      `${C}ce_delete_handler`,
      `${C}cf_remove_handler`,
      `${C}cg_set_handler`,
      `${C}ch_clear_handler`,
    ]);
  });

  test("two query handlers alone are half the components and form a group", () => {
    expect(layout(dslFor(["QA_GET", "QB_LIST", "Z1", "Z2"]))).toEqual([
      `${G}group Query Handlers`,
      `${C}qa_get_handler`,
      `${C}qb_list_handler`,
      `${G}z1_handler`,
      `${G}z2_handler`,
    ]);
  });

  test("two command handlers alone are half the components and form a group", () => {
    expect(layout(dslFor(["CA_ADD", "CB_CLEAR", "Z1", "Z2"]))).toEqual([
      `${G}group Command Handlers`,
      `${C}ca_add_handler`,
      `${C}cb_clear_handler`,
      `${G}z1_handler`,
      `${G}z2_handler`,
    ]);
  });

  test("a single query or command handler forms no group", () => {
    expect(layout(dslFor(["QA_GET", "CA_ADD"]))).toEqual([
      `${G}qa_get_handler`,
      `${G}ca_add_handler`,
    ]);
  });

  test("a type matching query and command is a query only", () => {
    expect(layout(dslFor(["GET_SETTINGS", "CA_ADD", "CB_CLEAR"]))).toEqual([
      `${G}group Command Handlers`,
      `${C}ca_add_handler`,
      `${C}cb_clear_handler`,
      `${G}get_settings_handler`,
    ]);
  });

  test("components in an entity group do not count towards Query Handlers", () => {
    expect(layout(dslFor(["TODO_GET", "TODO_LIST", "CONFIG_LOAD"]))).toEqual([
      `${G}group Todo Management`,
      `${C}todo_get_handler`,
      `${C}todo_list_handler`,
      `${G}config_load_handler`,
    ]);
  });

  test("components in an entity group do not count towards Command Handlers", () => {
    expect(layout(dslFor(["TODO_ADD", "TODO_REMOVE", "CONFIG_SET"]))).toEqual([
      `${G}group Todo Management`,
      `${C}todo_add_handler`,
      `${C}todo_remove_handler`,
      `${G}config_set_handler`,
    ]);
  });

  test("query and command groups both form, in that order", () => {
    expect(layout(dslFor(["QA_GET", "QB_READ", "CA_ADD", "CB_SET"]))).toEqual([
      `${G}group Query Handlers`,
      `${C}qa_get_handler`,
      `${C}qb_read_handler`,
      `${G}group Command Handlers`,
      `${C}ca_add_handler`,
      `${C}cb_set_handler`,
    ]);
  });
});
