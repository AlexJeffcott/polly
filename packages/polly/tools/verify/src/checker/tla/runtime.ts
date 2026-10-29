// Interned TLA+ values for compiled checking. Each distinct value has one
// integer ID, so two values are equal exactly when their IDs are equal.
//
//   kind  INT    a = the integer
//   kind  STR    a = index into `names`        (strings)
//   kind  MODEL  a = index into `names`        (model values)
//   kind  SET    pool[a .. a+n)   element IDs, ascending
//   kind  FUN    pool[a .. a+n)   pairs (domain ID, value ID), domain ascending
//
// Records, tuples and sequences are FUN, as in TLA+. Integers 0..SMALL-1 are
// interned first, so their IDs ascend with their values.
//
// Array reads in this file are `(arr[i] ?? 0)`, inline. The indices come from
// the tables themselves, so a read out of range is a defect in this file, and
// it gives ID 0 (FALSE) rather than undefined. A checked helper call here cost
// 26 % on full-featured (1.54 s against 1.22 s); the parity script
// (scripts/e2e-verify-bun-parity.ts) is the check for this class of defect.

import { Lazy, ModelValue, TFun, TlaEvalError, TSet, type Value } from "./values";

export const K_BOOL = 0;
export const K_INT = 1;
export const K_STR = 2;
export const K_MODEL = 3;
export const K_SET = 4;
export const K_FUN = 5;

const SMALL = 4096;

// Sets that are never enumerated: membership only.
export type LazyRT =
  | { k: "Nat" }
  | { k: "Int" }
  | { k: "STRING" }
  | { k: "Seq"; of: SetRT }
  | { k: "recSet"; fields: Array<[number, SetRT]> }
  | { k: "funSet"; dom: number; range: SetRT }
  | { k: "subset"; of: SetRT };
export type SetRT = number | LazyRT;

function grownInt32(x: Int32Array<ArrayBuffer>): Int32Array<ArrayBuffer> {
  const y = new Int32Array(x.length * 2);
  y.set(x);
  return y;
}

function hashInts(kind: number, buf: Int32Array, off: number, len: number): number {
  let h = 0x9747b28c ^ (kind * 0x27d4eb2f) ^ len;
  for (let i = 0; i < len; i++) {
    let k = Math.imul(buf[off + i] ?? 0, 0xcc9e2d51);
    k = (k << 15) | (k >>> 17);
    h ^= Math.imul(k, 0x1b873593);
    h = (h << 13) | (h >>> 19);
    h = (Math.imul(h, 5) + 0xe6546b64) | 0;
  }
  h ^= h >>> 16;
  h = Math.imul(h, 0x85ebca6b);
  h ^= h >>> 13;
  h = Math.imul(h, 0xc2b2ae35);
  return h ^ (h >>> 16);
}

export class Runtime {
  kind = new Uint8Array(1 << 16);
  a = new Int32Array(1 << 16);
  n = new Int32Array(1 << 16);
  hash = new Int32Array(1 << 16);
  count = 0;
  pool = new Int32Array(1 << 20);
  plen = 0;
  private table = new Int32Array(1 << 16).fill(-1);
  private mask = (1 << 16) - 1;
  private composites = 0;
  private strIds = new Map<string, number>();
  private modelIds = new Map<string, number>();
  private bigInts = new Map<number, number>();
  names: string[] = [];
  // Scratch space for building a segment before it is interned.
  private scr = new Int32Array(1 << 12);

  readonly FALSE: number;
  readonly TRUE: number;
  private readonly INT0: number;
  readonly EMPTY_SET: number;
  readonly EMPTY_FUN: number;

  constructor() {
    this.FALSE = this.alloc(K_BOOL, 0, 0);
    this.TRUE = this.alloc(K_BOOL, 1, 0);
    this.INT0 = this.count;
    for (let i = 0; i < SMALL; i++) this.alloc(K_INT, i, 0);
    this.EMPTY_SET = this.intern(K_SET, this.scr, 0, 0);
    this.EMPTY_FUN = this.intern(K_FUN, this.scr, 0, 0);
  }

  private alloc(kind: number, a: number, n: number): number {
    if (this.count === this.kind.length) {
      const kind = new Uint8Array(this.kind.length * 2);
      kind.set(this.kind);
      this.kind = kind;
      this.a = grownInt32(this.a);
      this.n = grownInt32(this.n);
      this.hash = grownInt32(this.hash);
    }
    const id = this.count++;
    this.kind[id] = kind;
    this.a[id] = a;
    this.n[id] = n;
    return id;
  }

  private ensureScr(len: number): Int32Array {
    if (this.scr.length < len) this.scr = new Int32Array(Math.max(len, this.scr.length * 2));
    return this.scr;
  }

  // Interns the segment buf[off .. off+len) of the given kind.
  intern(kind: number, buf: Int32Array, off: number, len: number): number {
    const h = hashInts(kind, buf, off, len);
    let i = h & this.mask;
    for (;;) {
      const id = this.table[i] ?? 0;
      if (id < 0) break;
      if (this.hash[id] === h && this.kind[id] === kind && this.n[id] === len) {
        const s = this.a[id] ?? 0;
        let same = true;
        for (let j = 0; j < len; j++) {
          if (this.pool[s + j] !== buf[off + j]) {
            same = false;
            break;
          }
        }
        if (same) return id;
      }
      i = (i + 1) & this.mask;
    }
    if (this.plen + len > this.pool.length) {
      // Old views into the pool stay valid: segments never change.
      const p = new Int32Array(Math.max(this.pool.length * 2, this.plen + len));
      p.set(this.pool.subarray(0, this.plen));
      this.pool = p;
    }
    const pool = this.pool;
    const base = this.plen;
    for (let j = 0; j < len; j++) pool[base + j] = buf[off + j] ?? 0;
    const id = this.alloc(kind, this.plen, len);
    this.hash[id] = h;
    this.plen += len;
    this.table[i] = id;
    if (++this.composites * 2 > this.mask) this.rehash();
    return id;
  }

  private rehash() {
    this.table = new Int32Array(this.table.length * 2).fill(-1);
    this.mask = this.table.length - 1;
    for (let id = 0; id < this.count; id++) {
      const k = this.kind[id] ?? 0;
      if (k !== K_SET && k !== K_FUN) continue;
      let i = (this.hash[id] ?? 0) & this.mask;
      while ((this.table[i] ?? 0) >= 0) i = (i + 1) & this.mask;
      this.table[i] = id;
    }
  }

  // ------------------------------------------------------------ scalars
  int(v: number): number {
    if (v >= 0 && v < SMALL && Number.isInteger(v)) return this.INT0 + v;
    if (!Number.isSafeInteger(v) || v > 0x7fffffff || v < -0x80000000)
      throw new TlaEvalError(`integer ${v} is out of range`);
    let id = this.bigInts.get(v);
    if (id === undefined) {
      id = this.alloc(K_INT, v, 0);
      this.bigInts.set(v, id);
    }
    return id;
  }
  iv(id: number): number {
    if (this.kind[id] !== K_INT)
      throw new TlaEvalError(`expected an integer, got ${this.show(id)}`);
    return this.a[id] ?? 0;
  }
  // The text of a string or model value.
  name(id: number): string {
    const s = this.names[this.a[id] ?? 0];
    if (s === undefined) throw new Error(`internal: value ${id} has no name`);
    return s;
  }
  bool(b: boolean): number {
    return b ? this.TRUE : this.FALSE;
  }
  str(s: string): number {
    let id = this.strIds.get(s);
    if (id === undefined) {
      this.names.push(s);
      id = this.alloc(K_STR, this.names.length - 1, 0);
      this.strIds.set(s, id);
    }
    return id;
  }
  model(name: string): number {
    let id = this.modelIds.get(name);
    if (id === undefined) {
      this.names.push(name);
      id = this.alloc(K_MODEL, this.names.length - 1, 0);
      this.modelIds.set(name, id);
    }
    return id;
  }

  // ------------------------------------------------------------ sets
  private checkSet(s: number): void {
    if (this.kind[s] !== K_SET) throw new TlaEvalError(`expected a set, got ${this.show(s)}`);
  }
  // A set from IDs in any order, with repeats.
  setOf(ids: ArrayLike<number>): number {
    const len = ids.length;
    const b = this.ensureScr(len);
    for (let i = 0; i < len; i++) b[i] = ids[i] ?? 0;
    // Insertion sort: sets here have few elements.
    for (let i = 1; i < len; i++) {
      const x = b[i] ?? 0;
      let j = i - 1;
      while (j >= 0 && (b[j] ?? 0) > x) {
        b[j + 1] = b[j] ?? 0;
        j--;
      }
      b[j + 1] = x;
    }
    let m = 0;
    for (let i = 0; i < len; i++) if (i === 0 || b[i] !== b[m - 1]) b[m++] = b[i] ?? 0;
    return this.intern(K_SET, b, 0, m);
  }
  setLen(s: number): number {
    this.checkSet(s);
    return this.n[s] ?? 0;
  }
  // The elements of s. The view stays valid when the pool grows.
  elems(s: number): Int32Array {
    this.checkSet(s);
    const a = this.a[s] ?? 0;
    return this.pool.subarray(a, a + (this.n[s] ?? 0));
  }
  setHas(s: number, x: number): boolean {
    this.checkSet(s);
    let lo = this.a[s] ?? 0;
    let hi = lo + (this.n[s] ?? 0) - 1;
    const p = this.pool;
    while (lo <= hi) {
      const mid = (lo + hi) >>> 1;
      const v = p[mid] ?? 0;
      if (v === x) return true;
      if (v < x) lo = mid + 1;
      else hi = mid - 1;
    }
    return false;
  }
  union(s: number, t: number): number {
    this.checkSet(s);
    this.checkSet(t);
    const ns = this.n[s] ?? 0;
    const nt = this.n[t] ?? 0;
    const b = this.ensureScr(ns + nt);
    const p = this.pool;
    let i = this.a[s] ?? 0;
    let j = this.a[t] ?? 0;
    const ie = i + ns;
    const je = j + nt;
    let m = 0;
    while (i < ie && j < je) {
      const x = p[i] ?? 0;
      const y = p[j] ?? 0;
      if (x === y) {
        b[m++] = x;
        i++;
        j++;
      } else if (x < y) {
        b[m++] = x;
        i++;
      } else {
        b[m++] = y;
        j++;
      }
    }
    while (i < ie) b[m++] = p[i++] ?? 0;
    while (j < je) b[m++] = p[j++] ?? 0;
    return this.intern(K_SET, b, 0, m);
  }
  // s \ t (keep = false) or s \cap t (keep = true); t may be lazy.
  filterBy(s: number, t: SetRT, keep: boolean): number {
    this.checkSet(s);
    const ns = this.n[s] ?? 0;
    const b = this.ensureScr(ns);
    const a = this.a[s] ?? 0;
    let m = 0;
    for (let i = 0; i < ns; i++) {
      const x = this.pool[a + i] ?? 0;
      if (this.member(x, t) === keep) b[m++] = x;
    }
    return m === ns ? s : this.intern(K_SET, b, 0, m);
  }
  range(lo: number, hi: number): number {
    if (hi < lo) return this.EMPTY_SET;
    const ids: number[] = [];
    for (let v = lo; v <= hi; v++) ids.push(this.int(v));
    return this.setOf(ids);
  }
  inRange(x: number, lo: number, hi: number): boolean {
    if (this.kind[x] !== K_INT) return false;
    const v = this.a[x] ?? 0;
    return v >= lo && v <= hi;
  }
  subseteq(s: number, t: SetRT): boolean {
    this.checkSet(s);
    const a = this.a[s] ?? 0;
    const n = this.n[s] ?? 0;
    for (let i = 0; i < n; i++) if (!this.member(this.pool[a + i] ?? 0, t)) return false;
    return true;
  }
  member(x: number, s: SetRT): boolean {
    if (typeof s === "number") return this.setHas(s, x);
    const kx = this.kind[x];
    switch (s.k) {
      case "Nat":
        return kx === K_INT && (this.a[x] ?? 0) >= 0;
      case "Int":
        return kx === K_INT;
      case "STRING":
        return kx === K_STR;
      case "Seq": {
        if (kx !== K_FUN) return false;
        const a = this.a[x] ?? 0;
        const n = (this.n[x] ?? 0) >> 1;
        for (let i = 0; i < n; i++) {
          if (this.pool[a + 2 * i] !== this.int(i + 1)) return false;
          if (!this.member(this.pool[a + 2 * i + 1] ?? 0, s.of)) return false;
        }
        return true;
      }
      case "recSet": {
        if (kx !== K_FUN || this.n[x] !== 2 * s.fields.length) return false;
        const a = this.a[x] ?? 0;
        for (const [i, [f, set]] of s.fields.entries()) {
          if (this.pool[a + 2 * i] !== f) return false;
          if (!this.member(this.pool[a + 2 * i + 1] ?? 0, set)) return false;
        }
        return true;
      }
      case "funSet": {
        if (kx !== K_FUN) return false;
        const a = this.a[x] ?? 0;
        const n = (this.n[x] ?? 0) >> 1;
        const dom = this.elems(s.dom);
        if (dom.length !== n) return false;
        for (let i = 0; i < n; i++) {
          if (this.pool[a + 2 * i] !== dom[i]) return false;
          if (!this.member(this.pool[a + 2 * i + 1] ?? 0, s.range)) return false;
        }
        return true;
      }
      case "subset": {
        if (kx !== K_SET) return false;
        return this.subseteq(x, s.of);
      }
    }
  }

  // ------------------------------------------------------------ functions
  private checkFun(f: number): void {
    if (this.kind[f] !== K_FUN) throw new TlaEvalError(`expected a function, got ${this.show(f)}`);
  }
  // Index in the pool of the pair whose domain element is x, or -1.
  private find(f: number, x: number): number {
    const a = this.a[f] ?? 0;
    const n = (this.n[f] ?? 0) >> 1;
    const p = this.pool;
    // Sequences: domain i sits at pair i-1.
    const k = x - this.INT0;
    if (k >= 1 && k <= n && p[a + 2 * (k - 1)] === x) return a + 2 * (k - 1);
    if (n <= 8) {
      for (let i = 0; i < n; i++) if (p[a + 2 * i] === x) return a + 2 * i;
      return -1;
    }
    let lo = 0;
    let hi = n - 1;
    while (lo <= hi) {
      const mid = (lo + hi) >>> 1;
      const v = p[a + 2 * mid] ?? 0;
      if (v === x) return a + 2 * mid;
      if (v < x) lo = mid + 1;
      else hi = mid - 1;
    }
    return -1;
  }
  // Pool index of the pair for x in f, or -1: for an update that finds its
  // key once (putIdx).
  findIdx(f: number, x: number): number {
    this.checkFun(f);
    return this.find(f, x);
  }
  // f with the value of the pair at pool index i (from findIdx(f, ...)) set to v.
  putIdx(f: number, i: number, v: number): number {
    if (this.pool[i + 1] === v) return f;
    const a = this.a[f] ?? 0;
    const len = this.n[f] ?? 0;
    const b = this.ensureScr(len);
    for (let j = 0; j < len; j++) b[j] = this.pool[a + j] ?? 0;
    b[i - a + 1] = v;
    return this.intern(K_FUN, b, 0, len);
  }
  // [x \in DOMAIN f \ t |-> f[x]]: f without the keys in t.
  restrict(f: number, t: SetRT): number {
    this.checkFun(f);
    const a = this.a[f] ?? 0;
    const len = this.n[f] ?? 0;
    const b = this.ensureScr(len);
    let m = 0;
    for (let i = 0; i < len; i += 2) {
      const d = this.pool[a + i] ?? 0;
      if (this.member(d, t)) continue;
      b[m++] = d;
      b[m++] = this.pool[a + i + 1] ?? 0;
    }
    return m === len ? f : this.intern(K_FUN, b, 0, m);
  }
  apply(f: number, x: number): number {
    this.checkFun(f);
    const i = this.find(f, x);
    if (i < 0) throw new TlaEvalError(`${this.show(x)} is not in the domain of ${this.show(f)}`);
    return this.pool[i + 1] ?? 0;
  }
  inDomain(f: number, x: number): boolean {
    this.checkFun(f);
    return this.find(f, x) >= 0;
  }
  // [f EXCEPT ![x] = v]; f when x is not in the domain.
  put(f: number, x: number, v: number): number {
    this.checkFun(f);
    const i = this.find(f, x);
    if (i < 0) return f;
    if (this.pool[i + 1] === v) return f;
    const a = this.a[f] ?? 0;
    const len = this.n[f] ?? 0;
    const b = this.ensureScr(len);
    for (let j = 0; j < len; j++) b[j] = this.pool[a + j] ?? 0;
    b[i - a + 1] = v;
    return this.intern(K_FUN, b, 0, len);
  }
  // A function from pairs in scratch-independent arrays.
  funOf(dom: ArrayLike<number>, val: ArrayLike<number>): number {
    const n = dom.length;
    const order = Array.from({ length: n }, (_, i) => i);
    let sorted = true;
    for (let i = 1; i < n; i++) if ((dom[i] ?? 0) <= (dom[i - 1] ?? 0)) sorted = false;
    if (!sorted) order.sort((x, y) => (dom[x] ?? 0) - (dom[y] ?? 0));
    const b = this.ensureScr(2 * n);
    let m = 0;
    for (let i = 0; i < n; i++) {
      const j = order[i] ?? 0;
      if (m > 0 && b[m - 2] === dom[j])
        throw new TlaEvalError("a function with a repeated domain element");
      b[m++] = dom[j] ?? 0;
      b[m++] = val[j] ?? 0;
    }
    return this.intern(K_FUN, b, 0, m);
  }
  // [x \in s |-> fn(x)]
  funOver(s: number, fn: (x: number) => number): number {
    const xs = this.elems(s);
    const vals = new Array<number>(xs.length);
    for (let i = 0; i < xs.length; i++) vals[i] = fn(xs[i] ?? 0);
    return this.funOf(xs, vals);
  }
  seq(vals: number[]): number {
    const dom = vals.map((_, i) => this.int(i + 1));
    return this.funOf(dom, vals);
  }
  seqVals(s: number): number[] {
    this.checkFun(s);
    const a = this.a[s] ?? 0;
    const n = (this.n[s] ?? 0) >> 1;
    const out = new Array<number>(n);
    for (let i = 0; i < n; i++) {
      if (this.pool[a + 2 * i] !== this.int(i + 1))
        throw new TlaEvalError(`expected a sequence, got ${this.show(s)}`);
      out[i] = this.pool[a + 2 * i + 1] ?? 0;
    }
    return out;
  }
  len(s: number): number {
    if (this.kind[s] === K_STR) return this.name(s).length;
    this.checkFun(s);
    return (this.n[s] ?? 0) >> 1;
  }
  append(s: number, v: number): number {
    const vals = this.seqVals(s);
    vals.push(v);
    return this.seq(vals);
  }
  subSeq(s: number, m: number, n: number): number {
    if (this.kind[s] === K_STR)
      throw new TlaEvalError("SubSeq on a string is not supported by the compiled engine");
    const vals = this.seqVals(s);
    if (m > n) return this.EMPTY_FUN;
    if (m < 1 || n > vals.length)
      throw new TlaEvalError(`SubSeq out of range: ${m}..${n} of ${vals.length}`);
    return this.seq(vals.slice(m - 1, n));
  }
  head(s: number): number {
    const vals = this.seqVals(s);
    if (vals.length === 0) throw new TlaEvalError("Head of an empty sequence");
    return vals[0] ?? 0;
  }
  tail(s: number): number {
    const vals = this.seqVals(s);
    if (vals.length === 0) throw new TlaEvalError("Tail of an empty sequence");
    return this.seq(vals.slice(1));
  }
  domain(f: number): number {
    this.checkFun(f);
    const a = this.a[f] ?? 0;
    const n = (this.n[f] ?? 0) >> 1;
    const b = this.ensureScr(n);
    for (let i = 0; i < n; i++) b[i] = this.pool[a + 2 * i] ?? 0;
    return this.intern(K_SET, b, 0, n);
  }
  // Pool offset and pair count of f, for loops over its domain.
  funStart(f: number): number {
    this.checkFun(f);
    return this.a[f] ?? 0;
  }
  funSize(f: number): number {
    this.checkFun(f);
    return (this.n[f] ?? 0) >> 1;
  }
  // f @@ g
  merge(f: number, g: number): number {
    this.checkFun(f);
    this.checkFun(g);
    const dom: number[] = [];
    const val: number[] = [];
    const fa = this.a[f] ?? 0;
    for (let i = 0; i < (this.n[f] ?? 0) >> 1; i++) {
      dom.push(this.pool[fa + 2 * i] ?? 0);
      val.push(this.pool[fa + 2 * i + 1] ?? 0);
    }
    const ga = this.a[g] ?? 0;
    for (let i = 0; i < (this.n[g] ?? 0) >> 1; i++) {
      const d = this.pool[ga + 2 * i] ?? 0;
      if (this.find(f, d) >= 0) continue;
      dom.push(d);
      val.push(this.pool[ga + 2 * i + 1] ?? 0);
    }
    return this.funOf(dom, val);
  }
  // A record whose field-name IDs are already ascending.
  rec(fields: number[], vals: number[]): number {
    const n = fields.length;
    const b = this.ensureScr(2 * n);
    for (let i = 0; i < n; i++) {
      b[2 * i] = fields[i] ?? 0;
      b[2 * i + 1] = vals[i] ?? 0;
    }
    return this.intern(K_FUN, b, 0, 2 * n);
  }

  // ------------------------------------------------------------ conversion
  // An interpreter value as an ID; a lazy set stays lazy unless it is finite
  // and small enough to list.
  fromValue(v: Value): SetRT {
    if (typeof v === "boolean") return this.bool(v);
    if (typeof v === "number") return this.int(v);
    if (typeof v === "string") return this.str(v);
    if (v instanceof ModelValue) return this.model(v.name);
    if (v instanceof TSet) return this.setOf(v.elems.map((x) => this.idOf(x)));
    if (v instanceof TFun)
      return this.funOf(
        v.dom.map((x) => this.idOf(x)),
        v.val.map((x) => this.idOf(x))
      );
    if (v instanceof Lazy) {
      const s = v.s;
      switch (s.lazy) {
        case "Nat":
        case "Int":
        case "STRING":
          return { k: s.lazy };
        case "Seq":
          return { k: "Seq", of: this.fromValue(s.of) };
        case "recSet": {
          const fields = s.fields.map(([name, set]): [number, SetRT] => [
            this.str(name),
            this.fromValue(set),
          ]);
          fields.sort((x, y) => x[0] - y[0]);
          return { k: "recSet", fields };
        }
        case "funSet":
          return { k: "funSet", dom: this.idOf(s.dom), range: this.fromValue(s.range) };
        case "subset":
          return { k: "subset", of: this.fromValue(s.of) };
      }
    }
    throw new TlaEvalError("value cannot be converted");
  }
  idOf(v: Value): number {
    const r = this.fromValue(v);
    if (typeof r !== "number")
      throw new TlaEvalError(`an infinite set where a value is needed (${r.k})`);
    return r;
  }

  show(id: number): string {
    switch (this.kind[id]) {
      case K_BOOL:
        return id === this.TRUE ? "TRUE" : "FALSE";
      case K_INT:
        return `${this.a[id]}`;
      case K_STR:
        return JSON.stringify(this.names[this.a[id] ?? 0]);
      case K_MODEL:
        return this.name(id);
      case K_SET:
        return `{${[...this.elems(id)].map((x) => this.show(x)).join(", ")}}`;
    }
    const a = this.a[id] ?? 0;
    const n = (this.n[id] ?? 0) >> 1;
    const parts: string[] = [];
    let isSeq = true;
    let isRec = true;
    for (let i = 0; i < n; i++) {
      const d = this.pool[a + 2 * i] ?? 0;
      if (d !== this.int(i + 1)) isSeq = false;
      if (this.kind[d] !== K_STR) isRec = false;
    }
    for (let i = 0; i < n; i++) {
      const d = this.pool[a + 2 * i] ?? 0;
      const v = this.show(this.pool[a + 2 * i + 1] ?? 0);
      parts.push(
        isSeq ? v : isRec ? `${this.names[this.a[d] ?? 0]} |-> ${v}` : `${this.show(d)} :> ${v}`
      );
    }
    if (isSeq) return `<<${parts.join(", ")}>>`;
    if (isRec) return `[${parts.join(", ")}]`;
    return `(${parts.join(" @@ ")})`;
  }
}
