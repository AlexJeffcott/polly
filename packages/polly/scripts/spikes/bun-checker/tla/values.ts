// TLA+ values. Every value has a canonical key: two values are equal when
// their keys are equal, as TLC's fingerprints treat them. Records, tuples and
// sequences are all functions, as in TLA+: <<a, b>> = [i \in 1..2 |-> ...].

export class EvalError extends Error {}

export class ModelValue {
  constructor(readonly name: string) {}
}

export class TFun {
  private _key?: string;
  private _map?: Map<string, number>;
  constructor(
    readonly dom: Value[],
    readonly val: Value[]
  ) {}
  get map(): Map<string, number> {
    if (!this._map) {
      this._map = new Map();
      for (let i = 0; i < this.dom.length; i++) this._map.set(key(this.dom[i] as Value), i);
    }
    return this._map;
  }
  get key(): string {
    if (this._key === undefined) {
      const parts = this.dom.map((d, i) => `${key(d)}:${key(this.val[i] as Value)}`);
      parts.sort();
      this._key = `[${parts.join(",")}]`;
    }
    return this._key;
  }
}

export class TSet {
  private _key?: string;
  private _keys?: Set<string>;
  // elems are distinct; their order is the sort order of their keys.
  constructor(readonly elems: Value[]) {}
  get keys(): Set<string> {
    if (!this._keys) this._keys = new Set(this.elems.map(key));
    return this._keys;
  }
  get key(): string {
    if (this._key === undefined) this._key = `{${[...this.keys].join(",")}}`;
    return this._key;
  }
  has(v: Value): boolean {
    return this.keys.has(key(v));
  }
}

// Sets that are never enumerated whole or that are built on demand.
export type LazySet =
  | { lazy: "Nat" }
  | { lazy: "Int" }
  | { lazy: "STRING" }
  | { lazy: "Seq"; of: SetValue }
  | { lazy: "recSet"; fields: Array<[string, SetValue]> }
  | { lazy: "funSet"; dom: SetValue; range: SetValue }
  | { lazy: "subset"; of: SetValue };

export class Lazy {
  constructor(readonly s: LazySet) {}
}

export type SetValue = TSet | Lazy;
export type Value = boolean | number | string | ModelValue | TFun | TSet | Lazy;

export function key(v: Value): string {
  switch (typeof v) {
    case "boolean":
      return v ? "T" : "F";
    case "number":
      return `${v}`;
    case "string":
      return JSON.stringify(v);
  }
  if (v instanceof TFun || v instanceof TSet) return v.key;
  if (v instanceof ModelValue) return `@${v.name}`;
  throw new EvalError(`a ${describe(v)} has no fingerprint`);
}

export function equal(a: Value, b: Value): boolean {
  if (a === b) return true;
  if (typeof a !== "object" || typeof b !== "object") return false;
  return key(a) === key(b);
}

export function describe(v: Value): string {
  if (v instanceof Lazy) return `set ${v.s.lazy}`;
  if (v instanceof TSet) return "set";
  if (v instanceof TFun) return "function";
  if (v instanceof ModelValue) return `model value ${v.name}`;
  return typeof v;
}

export function mkSet(items: Value[]): TSet {
  const seen = new Map<string, Value>();
  for (const v of items) {
    const k = key(v);
    if (!seen.has(k)) seen.set(k, v);
  }
  const ks = [...seen.keys()].sort();
  return new TSet(ks.map((k) => seen.get(k) as Value));
}

export function mkSeq(items: Value[]): TFun {
  return new TFun(
    items.map((_, i) => i + 1),
    items
  );
}

export function mkRecord(fields: Array<[string, Value]>): TFun {
  return new TFun(
    fields.map(([n]) => n),
    fields.map(([, v]) => v)
  );
}

export function apply(f: Value, arg: Value): Value {
  if (f instanceof TFun) {
    const i = f.map.get(key(arg));
    if (i === undefined) throw new EvalError(`${show(arg)} is not in the domain of ${show(f)}`);
    return f.val[i] as Value;
  }
  if (typeof f === "string" && typeof arg === "number") {
    const c = f[arg - 1];
    if (c === undefined) throw new EvalError(`index ${arg} out of string range`);
    return c;
  }
  throw new EvalError(`cannot apply a ${describe(f)}`);
}

// A sequence is a function with domain 1..n. Strings are sequences too.
export function seqItems(s: Value): Value[] {
  if (typeof s === "string") return [...s];
  if (!(s instanceof TFun)) throw new EvalError(`expected a sequence, got a ${describe(s)}`);
  const out: Value[] = new Array(s.dom.length);
  for (let i = 0; i < s.dom.length; i++) {
    const d = s.dom[i];
    if (typeof d !== "number" || d < 1 || d > s.dom.length) throw new EvalError(`expected a sequence, got ${show(s)}`);
    out[d - 1] = s.val[i] as Value;
  }
  return out;
}

export function isFinite(s: SetValue): boolean {
  if (s instanceof TSet) return true;
  switch (s.s.lazy) {
    case "Nat":
    case "Int":
    case "STRING":
    case "Seq":
      return false;
    case "recSet":
      return s.s.fields.every(([, f]) => isFinite(f));
    case "funSet":
      return isFinite(s.s.dom) && isFinite(s.s.range);
    case "subset":
      return isFinite(s.s.of);
  }
}

export function member(v: Value, s: Value): boolean {
  if (s instanceof TSet) return s.has(v);
  if (!(s instanceof Lazy)) throw new EvalError(`\\in needs a set, got a ${describe(s)}`);
  const l = s.s;
  switch (l.lazy) {
    case "Nat":
      return typeof v === "number" && v >= 0;
    case "Int":
      return typeof v === "number";
    case "STRING":
      return typeof v === "string";
    case "Seq": {
      if (typeof v === "string") return [...v].every((c) => member(c, l.of));
      if (!(v instanceof TFun)) return false;
      const n = v.dom.length;
      for (let i = 0; i < n; i++) {
        const d = v.dom[i];
        if (typeof d !== "number" || d < 1 || d > n) return false;
        if (!member(v.val[i] as Value, l.of)) return false;
      }
      return true;
    }
    case "recSet": {
      if (!(v instanceof TFun) || v.dom.length !== l.fields.length) return false;
      for (const [name, set] of l.fields) {
        const i = v.map.get(key(name));
        if (i === undefined || !member(v.val[i] as Value, set)) return false;
      }
      return true;
    }
    case "funSet": {
      if (!(v instanceof TFun)) return false;
      const dom = mkSet(v.dom);
      if (!(l.dom instanceof TSet)) throw new EvalError("[S -> T] needs a finite S");
      if (dom.key !== l.dom.key) return false;
      return v.val.every((x) => member(x, l.range));
    }
    case "subset":
      if (!(v instanceof TSet)) return false;
      return v.elems.every((x) => member(x, l.of));
  }
}

// Enumerate a set. Only finite sets can be enumerated.
export function elements(s: Value): Value[] {
  if (s instanceof TSet) return s.elems;
  if (!(s instanceof Lazy)) throw new EvalError(`expected a set, got a ${describe(s)}`);
  const l = s.s;
  switch (l.lazy) {
    case "recSet": {
      let acc: Array<Array<[string, Value]>> = [[]];
      for (const [name, set] of l.fields) {
        const next: Array<Array<[string, Value]>> = [];
        for (const partial of acc) for (const v of elements(set)) next.push([...partial, [name, v]]);
        acc = next;
      }
      return mkSet(acc.map(mkRecord)).elems;
    }
    case "funSet": {
      const dom = elements(l.dom);
      const range = elements(l.range);
      let acc: Value[][] = [[]];
      for (let i = 0; i < dom.length; i++) {
        const next: Value[][] = [];
        for (const partial of acc) for (const v of range) next.push([...partial, v]);
        acc = next;
      }
      return mkSet(acc.map((vals) => new TFun(dom, vals))).elems;
    }
    case "subset": {
      const base = elements(l.of);
      if (base.length > 20) throw new EvalError(`SUBSET of ${base.length} elements is too large`);
      const out: Value[] = [];
      for (let m = 0; m < 1 << base.length; m++) out.push(mkSet(base.filter((_, i) => (m >>> i) & 1)));
      return mkSet(out).elems;
    }
    default:
      throw new EvalError(`cannot enumerate the infinite set ${l.lazy}`);
  }
}

export function show(v: Value): string {
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "boolean") return v ? "TRUE" : "FALSE";
  if (typeof v === "number") return `${v}`;
  if (v instanceof ModelValue) return v.name;
  if (v instanceof TSet) return `{${v.elems.map(show).join(", ")}}`;
  if (v instanceof Lazy) return `<${v.s.lazy}>`;
  const isSeq = v.dom.every((d, i) => d === i + 1);
  if (isSeq) return `<<${v.val.map(show).join(", ")}>>`;
  if (v.dom.every((d) => typeof d === "string")) return `[${v.dom.map((d, i) => `${d} |-> ${show(v.val[i] as Value)}`).join(", ")}]`;
  return `(${v.dom.map((d, i) => `${show(d)} :> ${show(v.val[i] as Value)}`).join(" @@ ")})`;
}
