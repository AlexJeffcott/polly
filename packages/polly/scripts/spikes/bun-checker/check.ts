// Explicit-state BFS checker for examples/minimal's generated UserApp.tla (+ MessageRouter.tla),
// safety only, one thread. Spike 2.
//
// Differences from spike 1 (tlc-spike/check.ts):
//  * Actions cover the delivery branch: ENABLED StateTransition per handler, the
//    `\E p \in PayloadType : payload' = p` choice, and HandleActivate's contextStates write.
//  * Bounds come from the spec, not from hand: Contexts, MaxMessages, Tabs, TimeoutLimit are read
//    from UserApp.cfg; UserMessageTypes, Value and PayloadType's field count from UserApp.tla.
//  * Encoding is a general variable-length bit string (see `encode`): enum fields get
//    ceil(log2 |domain|) bits from those parsed sizes; Nat fields with no declared bound
//    (time, routingDepth, timestamps) use a self-delimiting 4-bit-chunk varint, so no bound is needed;
//    only the messages and pendingRequests entries that exist are written. A state is any number of
//    32-bit words. The visited set is a hash table keyed by a 64-bit fingerprint (two 32-bit lanes)
//    over those words; by default a fingerprint hit is confirmed by comparing the stored words, so the
//    set is exact. `--fp-only` skips the comparison and behaves like TLC (fingerprint equality = same
//    state; collision assumption stated in the report).
//
// Usage: bun check2.ts --spec DIR [--bug loops|probe] [--fp-only] [--dump FILE]
//   --bug loops : NoRoutingLoops replaced by routingDepth < 2 (a violation to find)
//   --bug probe : extra invariant ProbeNoPingDelivered (no message of type PING is ever delivered)

const args = process.argv.slice(2);
function opt(name: string, dflt?: string): string | undefined {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : dflt;
}
const SPEC = opt("--spec", ".")!;
const BUG = opt("--bug", "")!;
const FP_ONLY = args.includes("--fp-only");
const DUMP = opt("--dump");

// ---------------------------------------------------------------- spec parameters
const cfg = await Bun.file(`${SPEC}/UserApp.cfg`).text();
const tla = await Bun.file(`${SPEC}/UserApp.tla`).text();
function setConst(name: string): string[] {
  const m = new RegExp(`^\\s*${name}\\s*=\\s*\\{([^}]*)\\}`, "m").exec(cfg);
  if (!m) throw new Error(`cfg: ${name} not found`);
  return m[1].split(",").map((s) => s.trim()).filter(Boolean);
}
function numConst(name: string): number {
  const m = new RegExp(`^\\s*${name}\\s*=\\s*(\\d+)`, "m").exec(cfg);
  if (!m) throw new Error(`cfg: ${name} not found`);
  return Number(m[1]);
}
function tlaSet(name: string): string[] {
  const m = new RegExp(`^${name}\\s*==\\s*\\{([^}]*)\\}`, "m").exec(tla);
  if (!m) throw new Error(`tla: ${name} not found`);
  return m[1].split(",").map((s) => s.trim().replace(/"/g, "")).filter(Boolean);
}
const CTX = setConst("Contexts");
const TABS = setConst("Tabs");
const MaxMessages = numConst("MaxMessages");
const TimeoutLimit = numConst("TimeoutLimit");
const MSG_TYPES = tlaSet("UserMessageTypes");
const VALUES = tlaSet("Value");
// PayloadType is either the record set, or (since 922db6b, when no expression
// reads payload) one record: `{CHOOSE p \in [...] : TRUE}`.
const ptm = /^PayloadType\s*==\s*(\{CHOOSE p \\in )?\[([^\]]*)\]/m.exec(tla);
if (!ptm) throw new Error("tla: PayloadType not found");
const PAYLOAD_FIELDS = ptm[2].split(",").length;
const NPAYLOAD = ptm[1] ? 1 : VALUES.length ** PAYLOAD_FIELDS;
const constraintM = /StateConstraint\s*==\s*\n\s*Len\(messages\)\s*<=\s*(\w+)/.exec(tla);
if (!constraintM) throw new Error("tla: StateConstraint shape not recognised");
const ConstraintLen = constraintM[1] === "MaxMessages" ? MaxMessages : Number(constraintM[1]);

// INVARIANTS block of the cfg decides which invariants are checked
const invBlock = /^INVARIANTS[ \t]*\n((?:[ \t]+\w+[ \t]*(?:\n|$))+)/m.exec(cfg);
const INVS = new Set(invBlock ? invBlock[1].split(/\s+/).filter(Boolean) : []);
const KNOWN_INVS = ["TypeOK", "NoRoutingLoops", "UserStateTypeInvariant", "ProbeNoPingDelivered"];
for (const i of INVS) if (!KNOWN_INVS.includes(i)) throw new Error(`no hand-compiled invariant ${i}`);
if (BUG === "probe") INVS.add("ProbeNoPingDelivered");
const CHK_TYPEOK = INVS.has("TypeOK"), CHK_LOOPS = INVS.has("NoRoutingLoops"), CHK_PROBE = INVS.has("ProbeNoPingDelivered");

const NC = CTX.length;
const NT = TABS.length;
const NM = MSG_TYPES.length;

// Hand-compiled handler actions (the only spec part that varies by app).
// guard: ENABLED StateTransition(ctx, type) given user_active of ctx; next: user_active' of ctx.
const HANDLERS: Record<string, { guard: (active: number) => boolean; next: (active: number) => number }> = {
  ACTIVATE: { guard: (a) => a === 0, next: () => 1 }, // HandleActivate: active = FALSE; active' = TRUE
  PING: { guard: (a) => a === 1, next: (a) => a }, //     HandlePing: active = TRUE; UNCHANGED
};
for (const t of MSG_TYPES) if (!HANDLERS[t]) throw new Error(`no hand-compiled handler for ${t}`);
const H_GUARD = MSG_TYPES.map((t) => HANDLERS[t].guard);
const H_NEXT = MSG_TYPES.map((t) => HANDLERS[t].next);
const PING = MSG_TYPES.indexOf("PING");

const PENDING = 0, DELIVERED = 2, FAILED = 3, TIMEOUT = 4; // MessageStatus order: pending routing delivered failed timeout
const STATUS_NAMES = ["pending", "routing", "delivered", "failed", "timeout"];

// ---------------------------------------------------------------- decoded state layout (Int32Array)
const F_PORTS = 0, F_NMSG = 1, F_PEND = 2, F_DELIV = 3, F_DEPTH = 4, F_TIME = 5, F_PAYLOAD = 6, F_ACTIVE = 7;
const M0 = 8, MW = 7; // per message: src tgt tab type status ts dt(0 = NoTarget, c+1)
const P0 = M0 + MaxMessages * MW, PW = 3; // per pending id: sender targets timestamp
const SLEN = P0 + MaxMessages * PW;
const CUR = new Int32Array(SLEN);
const NXT = new Int32Array(SLEN);

// ---------------------------------------------------------------- general bit encoding
function bitsFor(n: number) { return n <= 1 ? 0 : 32 - Math.clz32(n - 1); }
const W_NMSG = bitsFor(MaxMessages + 1);
const W_CTX = bitsFor(NC);
const W_TAB = bitsFor(NT);
const W_TYPE = bitsFor(NM);
const W_STATUS = bitsFor(STATUS_NAMES.length);
const W_DT = bitsFor(NC + 1);
const W_PAYLOAD = bitsFor(NPAYLOAD);

const BUF = new Uint32Array(64);
let bitpos = 0;
function put(v: number, w: number) {
  if (w === 0) return;
  const word = bitpos >>> 5, off = bitpos & 31;
  BUF[word] |= v << off;
  if (off + w > 32) BUF[word + 1] |= v >>> (32 - off);
  bitpos += w;
}
function putNat(v: number) { // 3 data bits + continuation bit per chunk; no upper bound
  if (v < 0) throw new Error("negative Nat");
  do {
    const c = v & 7; v >>>= 3;
    put(c | (v ? 8 : 0), 4);
  } while (v);
}
let nwords = 0;
function encode(S: Int32Array) {
  for (let i = 0; i <= nwords; i++) BUF[i] = 0; // clear only what the previous encode touched
  bitpos = 0;
  const n = S[F_NMSG];
  if (n > MaxMessages) throw new Error("nmsg exceeds MaxMessages");
  put(n, W_NMSG);
  put(S[F_PORTS], NC);
  for (let i = 0; i < n; i++) {
    const b = M0 + i * MW;
    put(S[b], W_CTX); put(S[b + 1], NC); put(S[b + 2], W_TAB); put(S[b + 3], W_TYPE);
    put(S[b + 4], W_STATUS); putNat(S[b + 5]); put(S[b + 6], W_DT);
  }
  const pend = S[F_PEND];
  put(pend, MaxMessages);
  for (let i = 0; i < MaxMessages; i++) {
    if (!((pend >>> i) & 1)) continue;
    const b = P0 + i * PW;
    put(S[b], W_CTX); put(S[b + 1], NC); putNat(S[b + 2]);
  }
  put(S[F_DELIV], MaxMessages);
  putNat(S[F_DEPTH]);
  putNat(S[F_TIME]);
  put(S[F_PAYLOAD], W_PAYLOAD);
  put(S[F_ACTIVE], NC);
  nwords = (bitpos + 31) >>> 5;
  if (bitpos > maxBits) maxBits = bitpos;
  if (bitpos > 64) wide++;
}
let rp = 0, rbit = 0;
function get(w: number): number {
  if (w === 0) return 0;
  const word = rp + (rbit >>> 5), off = rbit & 31;
  let v = POOL[word] >>> off;
  if (off + w > 32) v |= POOL[word + 1] << (32 - off);
  rbit += w;
  return w === 32 ? v >>> 0 : v & ((1 << w) - 1);
}
function getNat(): number {
  let v = 0, sh = 0, c: number;
  do { c = get(4); v |= (c & 7) << sh; sh += 3; } while (c & 8);
  return v;
}
function decode(k: number, S: Int32Array) {
  rp = OFF[k]; rbit = 0;
  S.fill(0);
  const n = get(W_NMSG);
  S[F_NMSG] = n;
  S[F_PORTS] = get(NC);
  for (let i = 0; i < n; i++) {
    const b = M0 + i * MW;
    S[b] = get(W_CTX); S[b + 1] = get(NC); S[b + 2] = get(W_TAB); S[b + 3] = get(W_TYPE);
    S[b + 4] = get(W_STATUS); S[b + 5] = getNat(); S[b + 6] = get(W_DT);
  }
  const pend = get(MaxMessages);
  S[F_PEND] = pend;
  for (let i = 0; i < MaxMessages; i++) {
    if (!((pend >>> i) & 1)) continue;
    const b = P0 + i * PW;
    S[b] = get(W_CTX); S[b + 1] = get(NC); S[b + 2] = getNat();
  }
  S[F_DELIV] = get(MaxMessages);
  S[F_DEPTH] = getNat();
  S[F_TIME] = getNat();
  S[F_PAYLOAD] = get(W_PAYLOAD);
  S[F_ACTIVE] = get(NC);
}

// ---------------------------------------------------------------- state pool + visited set
let poolCap = 1 << 24;
let POOL = new Uint32Array(poolCap);
let poolLen = 0;
let cap = 1 << 22;
let OFF = new Int32Array(cap + 1);
let HA = new Uint32Array(cap), HB = new Uint32Array(cap);
let PARENT = new Int32Array(cap);
let count = 0;
let tbits = 23;
let table = new Int32Array(1 << tbits).fill(-1);
let tfp = new Uint32Array(1 << tbits); // lane-b fingerprint beside the slot: one cache line per probe
let tmask = (1 << tbits) - 1;
let fpCollisions = 0, maxBits = 0, wide = 0, wideStored = 0;

let ha = 0, hb = 0;
function hashBuf() {
  let a = 0x9747b28c ^ nwords, b = 0x5bd1e995 ^ Math.imul(nwords, 0x27d4eb2f);
  for (let i = 0; i < nwords; i++) {
    const w = BUF[i];
    let k = Math.imul(w, 0xcc9e2d51); k = (k << 15) | (k >>> 17); k = Math.imul(k, 0x1b873593);
    a ^= k; a = (a << 13) | (a >>> 19); a = (Math.imul(a, 5) + 0xe6546b64) | 0;
    let j = Math.imul(w ^ 0x7f4a7c15, 0x85ebca6b); j = (j << 17) | (j >>> 15); j = Math.imul(j, 0xc2b2ae35);
    b ^= j; b = (b << 11) | (b >>> 21); b = (Math.imul(b, 9) + 0x2f8b9c1d) | 0;
  }
  a ^= a >>> 16; a = Math.imul(a, 0x85ebca6b); a ^= a >>> 13; a = Math.imul(a, 0xc2b2ae35); a ^= a >>> 16;
  b ^= b >>> 15; b = Math.imul(b, 0x2c1b3c6d); b ^= b >>> 12; b = Math.imul(b, 0x297a2d39); b ^= b >>> 15;
  ha = a >>> 0; hb = b >>> 0;
}
function sameWords(k: number): boolean {
  const s = OFF[k];
  if (OFF[k + 1] - s !== nwords) return false;
  for (let i = 0; i < nwords; i++) if (POOL[s + i] !== BUF[i]) return false;
  return true;
}
function growStates() {
  cap *= 2;
  const o = new Int32Array(cap + 1); o.set(OFF); OFF = o;
  const a = new Uint32Array(cap); a.set(HA); HA = a;
  const b = new Uint32Array(cap); b.set(HB); HB = b;
  const p = new Int32Array(cap); p.set(PARENT); PARENT = p;
}
function store(parent: number) {
  if (count === cap) growStates();
  if (poolLen + nwords > poolCap) {
    poolCap *= 2;
    const np = new Uint32Array(poolCap); np.set(POOL); POOL = np;
  }
  for (let i = 0; i < nwords; i++) POOL[poolLen + i] = BUF[i];
  OFF[count] = poolLen;
  poolLen += nwords;
  OFF[count + 1] = poolLen;
  HA[count] = ha; HB[count] = hb; PARENT[count] = parent;
  if (bitpos > 64) wideStored++;
  return count++;
}
function rehash() {
  tbits++;
  table = new Int32Array(1 << tbits).fill(-1);
  tfp = new Uint32Array(1 << tbits);
  tmask = (1 << tbits) - 1;
  for (let k = 0; k < count; k++) {
    let j = HA[k] & tmask;
    while (table[j] !== -1) j = (j + 1) & tmask;
    table[j] = k; tfp[j] = HB[k];
  }
}
// insert the state in BUF; returns its new index, or -1 if already visited
function insert(parent: number): number {
  hashBuf();
  let j = ha & tmask;
  for (;;) {
    const k = table[j];
    if (k === -1) break;
    if (tfp[j] === hb && HA[k] === ha) {
      if (FP_ONLY) return -1;
      if (sameWords(k)) return -1;
      fpCollisions++;
    }
    j = (j + 1) & tmask;
  }
  const idx = store(parent);
  table[j] = idx; tfp[j] = hb;
  if (count * 2 > tmask) rehash();
  return idx;
}

// ---------------------------------------------------------------- invariants
function violated(S: Int32Array): string | null {
  const n = S[F_NMSG];
  if (CHK_PROBE) {
    for (let i = 0; i < n; i++) {
      const b = M0 + i * MW;
      if (S[b + 3] === PING && S[b + 4] === DELIVERED) return "ProbeNoPingDelivered";
    }
  }
  // TypeOK
  if (CHK_TYPEOK) for (let i = 0; i < n; i++) {
    const b = M0 + i * MW;
    if (S[b] >= NC || S[b + 1] === 0 || (S[b + 1] & ~((1 << NC) - 1)) !== 0 || S[b + 4] >= STATUS_NAMES.length) return "TypeOK";
  }
  if (CHK_TYPEOK && (S[F_DEPTH] < 0 || S[F_TIME] < 0)) return "TypeOK";
  // NoRoutingLoops
  // routingDepth <= Len(messages) since 22fa537 (was routingDepth < 3).
  if (CHK_LOOPS && !(BUG === "loops" ? S[F_DEPTH] < 2 : S[F_DEPTH] <= S[F_NMSG])) return "NoRoutingLoops";
  // UserStateTypeInvariant: contextStates[ctx] \in [user_active: BOOLEAN] -- one bit per ctx, holds by construction
  return null;
}

function show(S: Int32Array): string {
  const msgs: string[] = [];
  for (let i = 0; i < S[F_NMSG]; i++) {
    const b = M0 + i * MW;
    const tg = CTX.filter((_, c) => S[b + 1] & (1 << c));
    msgs.push(`[id ${i + 1} ${MSG_TYPES[S[b + 3]]} src ${CTX[S[b]]} tgt {${tg}} tab ${TABS[S[b + 2]]} ${STATUS_NAMES[S[b + 4]]} ts ${S[b + 5]} dt ${S[b + 6] ? CTX[S[b + 6] - 1] : "NoTarget"}]`);
  }
  const p = CTX.map((c, k) => `${c}=${S[F_PORTS] & (1 << k) ? "C" : "D"}`).join(",");
  const pend = [];
  for (let i = 0; i < MaxMessages; i++) if ((S[F_PEND] >>> i) & 1) { const b = P0 + i * PW; pend.push(`${i + 1}:${CTX[S[b]]}/${S[b + 1]}/${S[b + 2]}`); }
  const act = CTX.filter((_, c) => S[F_ACTIVE] & (1 << c));
  return `ports{${p}} msgs<<${msgs.join(" ")}>> pend{${pend}} deliv{${[...Array(MaxMessages).keys()].filter((x) => (S[F_DELIV] >>> x) & 1).map((x) => x + 1)}} depth ${S[F_DEPTH]} time ${S[F_TIME]} payload ${S[F_PAYLOAD]} active{${act}}`;
}

// ---------------------------------------------------------------- successor emission
let generated = 0, outOfModel = 0;
let violation: { inv: string; idx: number; S?: Int32Array } | null = null;
let curIdx = -1;
const VCHK = new Int32Array(SLEN);

function emit(S: Int32Array) {
  generated++;
  if (!(S[F_NMSG] <= ConstraintLen)) {
    // TLC: out-of-constraint successor is generated and invariant-checked, never stored or expanded
    outOfModel++;
    if (violation === null) { const inv = violated(S); if (inv) violation = { inv, idx: curIdx, S: S.slice() }; }
    return;
  }
  encode(S);
  const idx = insert(curIdx);
  if (idx >= 0 && violation === null) {
    const inv = violated(S);
    if (inv) violation = { inv, idx };
  }
}

function removePending(S: Int32Array, i: number) { S[F_PEND] &= ~(1 << i); const b = P0 + i * PW; S[b] = 0; S[b + 1] = 0; S[b + 2] = 0; }

function successors() {
  const C = CUR, N = NXT;
  const ports = C[F_PORTS], n = C[F_NMSG], depth = C[F_DEPTH], time = C[F_TIME];
  // ConnectPort(c)
  for (let c = 0; c < NC; c++) {
    if ((ports >>> c) & 1) continue;
    N.set(C); N[F_PORTS] = ports | (1 << c); emit(N);
  }
  // DisconnectPort(c): drop pending requests whose recorded targets contain c
  for (let c = 0; c < NC; c++) {
    if (!((ports >>> c) & 1)) continue;
    N.set(C); N[F_PORTS] = ports & ~(1 << c);
    for (let i = 0; i < MaxMessages; i++) if ((C[F_PEND] >>> i) & 1 && (C[P0 + i * PW + 1] >>> c) & 1) removePending(N, i);
    emit(N);
  }
  // SendMessage(src, targetSet, tab, msgType)
  if (n < MaxMessages && depth === 0) {
    for (let src = 0; src < NC; src++) {
      if (!((ports >>> src) & 1)) continue;
      for (let ts = 1; ts < 1 << NC; ts++) for (let tab = 0; tab < NT; tab++) for (let ty = 0; ty < NM; ty++) {
        N.set(C);
        const b = M0 + n * MW;
        N[b] = src; N[b + 1] = ts; N[b + 2] = tab; N[b + 3] = ty; N[b + 4] = PENDING; N[b + 5] = time; N[b + 6] = 0;
        N[F_NMSG] = n + 1;
        // pendingRequests @@ (newId :> [sender, targets, timestamp]); newId = n+1 is never already in the domain
        N[F_PEND] = C[F_PEND] | (1 << n);
        const p = P0 + n * PW; N[p] = src; N[p + 1] = ts; N[p + 2] = time;
        N[F_TIME] = time + 1;
        emit(N);
      }
    }
  }
  // UserRouteMessage(i)
  if (depth < 5) {
    for (let i = 0; i < n; i++) {
      const b = M0 + i * MW;
      if (C[b + 4] !== PENDING) continue;
      const tgts = C[b + 1], ty = C[b + 3];
      for (let t = 0; t < NC; t++) {
        if (!((tgts >>> t) & 1)) continue;
        const act = (C[F_ACTIVE] >>> t) & 1;
        if ((ports >>> t) & 1 && H_GUARD[ty](act)) {
          const a2 = H_NEXT[ty](act);
          for (let pl = 0; pl < NPAYLOAD; pl++) {
            N.set(C);
            N[b + 4] = DELIVERED; N[b + 6] = t + 1;
            N[F_DELIV] = C[F_DELIV] | (1 << i);
            removePending(N, i);
            N[F_TIME] = time + 1; N[F_DEPTH] = depth + 1;
            N[F_PAYLOAD] = pl;
            N[F_ACTIVE] = (C[F_ACTIVE] & ~(1 << t)) | (a2 << t);
            emit(N);
          }
        } else {
          N.set(C);
          N[b + 4] = FAILED;
          removePending(N, i);
          N[F_TIME] = time + 1; N[F_DEPTH] = depth + 1;
          emit(N);
        }
      }
    }
  }
  // CompleteRouting
  if (depth > 0) { N.set(C); N[F_DEPTH] = 0; emit(N); }
  // TimeoutMessage(i)
  for (let i = 0; i < n; i++) {
    const b = M0 + i * MW;
    if (C[b + 4] !== PENDING) continue;
    if (!(time - C[b + 5] > TimeoutLimit)) continue;
    N.set(C); N[b + 4] = TIMEOUT; removePending(N, i); N[F_TIME] = time + 1; emit(N);
  }
}

// ---------------------------------------------------------------- BFS
const t0 = performance.now();
for (let pl = 0; pl < NPAYLOAD; pl++) {
  NXT.fill(0); NXT[F_PAYLOAD] = pl; // Init: all disconnected, <<>>, empty requests, {} , 0, 0, user_active FALSE
  emit(NXT);
}
let levelEnd = count, depthLevels = 1, head = 0;
while (head < count && violation === null) {
  if (head === levelEnd) { levelEnd = count; depthLevels++; }
  curIdx = head;
  decode(head, CUR);
  head++;
  successors();
}
const ms = performance.now() - t0;

if (violation) {
  console.log(`Error: Invariant ${violation.inv} is violated.`);
  const trace: number[] = [];
  for (let k = violation.idx; k !== -1; k = PARENT[k]) trace.push(k);
  trace.reverse();
  trace.forEach((k, i) => { decode(k, VCHK); console.log(`State ${i + 1}: ${show(VCHK)}`); });
  if (violation.S) console.log(`State ${trace.length + 1} (out of constraint): ${show(violation.S)}`);
}
console.log(`${generated} states generated, ${count} distinct states found, depth ${depthLevels}, out-of-model successors ${outOfModel}`);
console.log(`encoding: max ${maxBits} bits/state; successors wider than 64 bits ${wide}; distinct states wider than 64 bits ${wideStored}; pool ${(poolLen * 4 / 2 ** 20).toFixed(1)} MiB; 64-bit fingerprint collisions ${FP_ONLY ? "n/a (--fp-only)" : fpCollisions}`);
console.log(`invariants: {${[...INVS]}}`);
console.log(`params: Contexts ${NC} Tabs ${NT} MaxMessages ${MaxMessages} msgTypes {${MSG_TYPES}} payload ${NPAYLOAD}`);
console.log(`wall ${(ms / 1000).toFixed(3)} s (BFS only)`);

if (DUMP) {
  const lines: string[] = [];
  for (let k = 0; k < count; k++) { decode(k, VCHK); lines.push(show(VCHK)); }
  await Bun.write(DUMP, `${lines.sort().join("\n")}\n`);
}
