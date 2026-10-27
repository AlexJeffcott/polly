import { describe, expect, test } from "bun:test";
import { unknownMessageNames } from "../../analysis/unknown-message-names";

const TYPES = ["GET_SETTINGS", "SETTINGS_UPDATE", "LOGIN", "LOGOUT"];

describe("unknownMessageNames", () => {
  test("reports an include name that matches no message type", () => {
    const config = { messages: { include: ["SETTINGS_GET", "SETTINGS_UPDATE"] } };
    expect(unknownMessageNames(config, TYPES)).toEqual([
      { where: "messages.include", name: "SETTINGS_GET" },
    ]);
  });

  test("reports nothing when every name matches", () => {
    const config = {
      messages: {
        include: ["GET_SETTINGS", "LOGIN"],
        perMessageBounds: { LOGIN: 1 },
        symmetry: [["LOGIN", "LOGOUT"]],
      },
      subsystems: { auth: { handlers: ["LOGIN", "LOGOUT"] } },
      tier2: { temporalConstraints: [{ before: "LOGIN", after: "LOGOUT" }] },
    };
    expect(unknownMessageNames(config, TYPES)).toEqual([]);
  });

  test("checks every key that names a message type", () => {
    const config = {
      messages: {
        exclude: ["EXCLUDED"],
        symmetry: [["LOGIN", "SYMMETRIC"]],
        perMessageBounds: { BOUNDED: 1 },
      },
      subsystems: {
        auth: { handlers: ["LOGIN", "HANDLED"], bounds: { perMessageBounds: { SUB_BOUNDED: 1 } } },
      },
      tier2: {
        temporalConstraints: [{ before: "BEFORE", after: "LOGIN" }],
        boundedExploration: { criticalPaths: [["LOGIN", "CRITICAL"]] },
      },
    };
    expect(unknownMessageNames(config, TYPES)).toEqual([
      { where: "messages.exclude", name: "EXCLUDED" },
      { where: "messages.symmetry", name: "SYMMETRIC" },
      { where: "messages.perMessageBounds", name: "BOUNDED" },
      { where: "subsystems.auth.handlers", name: "HANDLED" },
      { where: "subsystems.auth.bounds.perMessageBounds", name: "SUB_BOUNDED" },
      { where: "tier2.temporalConstraints", name: "BEFORE" },
      { where: "tier2.boundedExploration.criticalPaths", name: "CRITICAL" },
    ]);
  });

  test("reports a repeated name once per config path", () => {
    const config = {
      tier2: {
        temporalConstraints: [
          { before: "MISSING", after: "LOGIN" },
          { before: "LOGOUT", after: "MISSING" },
        ],
      },
    };
    expect(unknownMessageNames(config, TYPES)).toEqual([
      { where: "tier2.temporalConstraints", name: "MISSING" },
    ]);
  });
});
