// The public `defineVerification` types `state` and `mesh` with the same
// StateConfig / MeshConfig the codegen reads (state-config.ts). They were
// `Record<string, unknown>`, so a consumer config the CLI could not use still
// type-checked. Each `Accepted<...> = false` below fails `bun check` if the
// public type goes back to accepting anything.

import { describe, expect, test } from "bun:test";
import { defineVerification } from "../config";

type PublicConfig = Parameters<typeof defineVerification>[0];
type Accepted<T> = [T] extends [PublicConfig] ? true : false;

type Messages = { messages: { maxInFlight: number } };
const messages = { maxInFlight: 1 };

describe("defineVerification state types", () => {
  test("accepts the shapes the codegen reads", () => {
    const config = defineVerification({
      state: {
        flag: [false, true],
        count: { type: "number", min: 0, max: 3 },
        user: { role: { type: "enum", values: ["admin", "guest"] } },
      },
      mesh: { todos: { entries: { type: "enum", values: ["empty", "many"] } } },
      messages,
    });
    expect(config.state.flag).toEqual([false, true]);
  });

  test("rejects a state value that is not a field or an object of fields", () => {
    const bareNumber: Accepted<{ state: { n: number } } & Messages> = false;
    const bareString: Accepted<{ state: { s: string } } & Messages> = false;
    const numberPair: Accepted<{ state: { b: [number, number] } } & Messages> = false;
    expect([bareNumber, bareString, numberPair]).toEqual([false, false, false]);
  });

  test("rejects a mesh field that is not a FieldConfig", () => {
    const meshNumber: Accepted<{ state: {}; mesh: { doc: { f: number } } } & Messages> = false;
    expect(meshNumber).toBe(false);
  });
});
