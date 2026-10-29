/**
 * The packed visited set (checker/state-store.ts): states go in as value IDs
 * and come out the same, membership stays exact across field relayouts, and
 * a state takes the words its variables' dictionaries need, not one per
 * variable.
 */

import { describe, expect, test } from "bun:test";
import { PackedStateStore, StateCodec } from "../../checker/state-store";

function state(...ids: number[]): Int32Array {
  return Int32Array.from(ids);
}

describe("packed state store", () => {
  test("a state comes back with the value IDs it went in with", () => {
    const codec = new StateCodec(3);
    const store = new PackedStateStore(codec);
    expect(store.add(codec.encode(state(4100, 7, 123456)), -1)).toBe(true);
    expect(store.add(codec.encode(state(4100, 8, 123456)), 0)).toBe(true);
    expect(Array.from(store.get(0, new Int32Array(3)))).toEqual([4100, 7, 123456]);
    expect(Array.from(store.get(1, new Int32Array(3)))).toEqual([4100, 8, 123456]);
    expect(store.parent(1)).toBe(0);
  });

  test("a state already in the set is not added again", () => {
    const codec = new StateCodec(2);
    const store = new PackedStateStore(codec);
    expect(store.add(codec.encode(state(5000, 1)), -1)).toBe(true);
    expect(store.has(codec.encode(state(5000, 1)))).toBe(true);
    expect(store.add(codec.encode(state(5000, 1)), 0)).toBe(false);
    expect(store.has(codec.encode(state(5000, 2)))).toBe(false);
    expect(store.count).toBe(1);
  });

  test("membership and values survive every relayout, in both stores of a codec", () => {
    const codec = new StateCodec(4);
    const inModel = new PackedStateStore(codec);
    const outside = new PackedStateStore(codec);
    // Variable 1 takes 3,000 values, so its field is widened many times;
    // the others take 1, 2 and 50 values.
    const all: Int32Array[] = [];
    for (let i = 0; i < 3000; i++) all.push(state(9000, 20_000 + i * 7, i % 2, 4096 + (i % 50)));
    all.forEach((s, i) => {
      const target = i % 3 === 0 ? outside : inModel;
      expect(target.add(codec.encode(s), i - 1)).toBe(true);
    });
    expect(codec.relayouts).toBeGreaterThan(3);
    expect(inModel.count + outside.count).toBe(3000);
    all.forEach((s, i) => {
      const target = i % 3 === 0 ? outside : inModel;
      const other = i % 3 === 0 ? inModel : outside;
      expect(target.has(codec.encode(s))).toBe(true);
      expect(other.has(codec.encode(s))).toBe(false);
    });
    const out = new Int32Array(4);
    for (let k = 0; k < inModel.count; k++) {
      const back = Array.from(inModel.get(k, out));
      expect(all.some((s) => Array.from(s).join() === back.join())).toBe(true);
    }
  });

  test("a state is as wide as its dictionaries, not one word per variable", () => {
    const codec = new StateCodec(8);
    const store = new PackedStateStore(codec);
    // minimal's shape: one variable with many values, seven with few.
    for (let i = 0; i < 100_000; i++) {
      store.add(
        codec.encode(state(4200 + (i % 8), 10_000 + i, 4300, 4, 2, i % 5, 4400 + (i % 7), 4112)),
        -1
      );
    }
    expect(store.count).toBe(100_000);
    // Fields, with room for twice the values seen: 4 + 18 + 0 + 0 + 0 + 4 +
    // 4 + 0 = 30 bits, one word against eight.
    expect(codec.width).toBe(1);
  });
});
