/**
 * The checker's visited set, packed.
 *
 * A state is one interned value ID per variable (tla/runtime.ts). IDs are
 * global, and every composite value has an ID of 4096 or more, but each
 * variable takes few distinct values: on examples/minimal, `messages` takes
 * 97,009 and the other seven variables 1 to 505 each. So each variable gets
 * its own dense numbering (a "local" index), and a stored state is those
 * local indices packed into 32-bit words, each field as wide as its
 * variable's dictionary needs: 39 bits (2 words) on minimal against 8 words
 * of IDs.
 *
 * Field widths grow while the search runs. When a variable's dictionary
 * outgrows its field, the codec lays the fields out again and every store
 * that uses it re-encodes its rows (`relayout`). A field never spans two
 * words, so packing is one shift and one OR per variable.
 *
 * The set is exact: a probe compares the packed words, so two states are the
 * same only when every local index, and so every value ID, is the same.
 */

/** Bits for local indices 0..count-1 (0 bits when there is one value). */
function bitsFor(count: number): number {
  return count <= 1 ? 0 : 32 - Math.clz32(count - 1);
}

function grown(x: Int32Array, min: number): Int32Array<ArrayBuffer> {
  let len = Math.max(16, x.length);
  while (len < min) len *= 2;
  const y = new Int32Array(len);
  y.set(x);
  return y;
}

type Layout = { width: number; word: Int32Array; shift: Int32Array; mask: Int32Array };

export class StateCodec {
  /** 32-bit words in one packed state. */
  width = 0;
  /** Field layouts done since the start; one per dictionary that outgrew its field. */
  relayouts = 0;
  /** The packed form of the last `encode`; `width` words long. */
  key = new Int32Array(1);
  private bits: Int32Array;
  private layout: Layout;
  // Per variable: global ID -> local index + 1 (0: not seen), and back.
  private localOf: Int32Array[];
  private globalOf: Int32Array[];
  private counts: Int32Array;
  private readonly stores: PackedStateStore[] = [];

  constructor(readonly vars: number) {
    this.bits = new Int32Array(vars);
    this.counts = new Int32Array(vars);
    this.localOf = Array.from({ length: vars }, () => new Int32Array(16));
    this.globalOf = Array.from({ length: vars }, () => new Int32Array(16));
    this.layout = this.place(this.bits);
    this.width = this.layout.width;
  }

  /** First fit, in variable order: a field that does not fit starts a new word. */
  private place(bits: Int32Array): Layout {
    const n = this.vars;
    const word = new Int32Array(n);
    const shift = new Int32Array(n);
    const mask = new Int32Array(n);
    let w = 0;
    let used = 0;
    for (let v = 0; v < n; v++) {
      const b = bits[v] ?? 0;
      if (used + b > 32) {
        w++;
        used = 0;
      }
      word[v] = w;
      shift[v] = used;
      mask[v] = b === 32 ? -1 : (1 << b) - 1;
      used += b;
    }
    return { width: Math.max(1, w + 1), word, shift, mask };
  }

  register(store: PackedStateStore): void {
    this.stores.push(store);
  }

  /** The local index of `id` for variable v, given out on first sight. */
  private local(v: number, id: number): number {
    let map = this.localOf[v] ?? new Int32Array(0);
    const known = id < map.length ? (map[id] ?? 0) : 0;
    if (known > 0) return known - 1;
    if (id >= map.length) {
      map = grown(map, id + 1);
      this.localOf[v] = map;
    }
    const loc = this.counts[v] ?? 0;
    this.counts[v] = loc + 1;
    map[id] = loc + 1;
    let back = this.globalOf[v] ?? new Int32Array(0);
    if (loc >= back.length) {
      back = grown(back, loc + 1);
      this.globalOf[v] = back;
    }
    back[loc] = id;
    if (bitsFor(loc + 1) > (this.bits[v] ?? 0)) this.widen(v, loc + 1);
    return loc;
  }

  /**
   * Gives variable v room for twice `count` values, so a dictionary that
   * keeps growing is laid out again once per doubling of its size, not once
   * per bit.
   */
  private widen(v: number, count: number): void {
    const before = this.layout;
    const bits = this.bits.slice();
    bits[v] = Math.min(31, bitsFor(count * 2));
    const after = this.place(bits);
    this.bits = bits;
    this.layout = after;
    this.width = after.width;
    this.relayouts++;
    for (const store of this.stores) store.relayout(before, after);
  }

  /** Packs value IDs `s` into `key`. */
  encode(s: Int32Array): Int32Array {
    const n = this.vars;
    for (;;) {
      const { word, shift } = this.layout;
      const relayouts = this.relayouts;
      if (this.key.length < this.width) this.key = new Int32Array(this.width);
      const key = this.key;
      key.fill(0, 0, this.width);
      let v = 0;
      for (; v < n; v++) {
        const id = s[v] ?? 0;
        let loc = (this.localOf[v]?.[id] ?? 0) - 1;
        if (loc < 0) {
          loc = this.local(v, id);
          // A new field layout: pack again from the first variable.
          if (this.relayouts !== relayouts) break;
        }
        const at = word[v] ?? 0;
        key[at] = (key[at] ?? 0) | (loc << (shift[v] ?? 0));
      }
      if (v === n) return key;
    }
  }

  /** Unpacks the row at `rows[off ..]` into value IDs in `out`. */
  decode(rows: Int32Array, off: number, out: Int32Array): void {
    const { word, shift, mask } = this.layout;
    for (let v = 0; v < this.vars; v++) {
      const w = rows[off + (word[v] ?? 0)] ?? 0;
      const loc = (w >>> (shift[v] ?? 0)) & (mask[v] ?? 0);
      out[v] = this.globalOf[v]?.[loc] ?? 0;
    }
  }

  pack(locals: Int32Array, layout: Layout, rows: Int32Array, off: number): void {
    rows.fill(0, off, off + layout.width);
    for (let v = 0; v < this.vars; v++) {
      const at = off + (layout.word[v] ?? 0);
      rows[at] = (rows[at] ?? 0) | ((locals[v] ?? 0) << (layout.shift[v] ?? 0));
    }
  }

  unpack(rows: Int32Array, off: number, layout: Layout, locals: Int32Array): void {
    for (let v = 0; v < this.vars; v++) {
      const w = rows[off + (layout.word[v] ?? 0)] ?? 0;
      locals[v] = (w >>> (layout.shift[v] ?? 0)) & (layout.mask[v] ?? 0);
    }
  }
}

/**
 * Exact set of packed states, kept in the order they were added, so states
 * [a, b) are one BFS level. Each state keeps the index of the state it was
 * reached from (-1 for an init state).
 */
export class PackedStateStore {
  count = 0;
  private rows: Int32Array;
  private parents = new Int32Array(1 << 16);
  private table = new Int32Array(1 << 16).fill(-1);
  private mask = (1 << 16) - 1;
  private width: number;

  constructor(private readonly codec: StateCodec) {
    this.width = codec.width;
    this.rows = new Int32Array(this.width << 16);
    codec.register(this);
  }

  private hash(buf: Int32Array, off: number): number {
    let h = 0x9747b28c;
    for (let i = 0; i < this.width; i++) {
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

  /** The slot holding `key`, or the empty slot where it would go (as -slot - 1). */
  private slot(key: Int32Array): number {
    const w = this.width;
    let i = this.hash(key, 0) & this.mask;
    for (;;) {
      const k = this.table[i] ?? -1;
      if (k < 0) return -i - 1;
      let same = true;
      for (let j = 0; j < w; j++) {
        if (this.rows[k * w + j] !== key[j]) {
          same = false;
          break;
        }
      }
      if (same) return i;
      i = (i + 1) & this.mask;
    }
  }

  /** Whether `key` (from `codec.encode`) is in the set. */
  has(key: Int32Array): boolean {
    return this.slot(key) >= 0;
  }

  /** Adds `key` (from `codec.encode`), reached from `parent`; false when present. */
  add(key: Int32Array, parent: number): boolean {
    const found = this.slot(key);
    if (found >= 0) return false;
    const w = this.width;
    if ((this.count + 1) * w > this.rows.length) {
      this.rows = grown(this.rows, (this.count + 1) * w);
    }
    if (this.count + 1 > this.parents.length) {
      this.parents = grown(this.parents, this.count + 1);
    }
    const off = this.count * w;
    for (let j = 0; j < w; j++) this.rows[off + j] = key[j] ?? 0;
    this.parents[this.count] = parent;
    this.table[-found - 1] = this.count++;
    if (this.count * 2 > this.mask) this.rehash(this.table.length * 2);
    return true;
  }

  private rehash(size: number): void {
    this.table = new Int32Array(size).fill(-1);
    this.mask = size - 1;
    for (let k = 0; k < this.count; k++) {
      let i = this.hash(this.rows, k * this.width) & this.mask;
      while ((this.table[i] ?? -1) >= 0) i = (i + 1) & this.mask;
      this.table[i] = k;
    }
  }

  /** Re-encodes every row from layout `before` to `after` (local indices do not change). */
  relayout(before: Layout, after: Layout): void {
    const locals = new Int32Array(this.codec.vars);
    const rows = new Int32Array(Math.max(after.width << 4, this.count * after.width * 2));
    for (let k = 0; k < this.count; k++) {
      this.codec.unpack(this.rows, k * before.width, before, locals);
      this.codec.pack(locals, after, rows, k * after.width);
    }
    this.rows = rows;
    this.width = after.width;
    this.rehash(this.table.length);
  }

  /** Writes the value IDs of state k into `out`. */
  get(k: number, out: Int32Array): Int32Array {
    this.codec.decode(this.rows, k * this.width, out);
    return out;
  }

  parent(k: number): number {
    return this.parents[k] ?? -1;
  }

  /** Bytes held by rows, parents and table. */
  bytes(): number {
    return this.rows.byteLength + this.parents.byteLength + this.table.byteLength;
  }
}
