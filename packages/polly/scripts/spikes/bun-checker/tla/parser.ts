// Parser for the TLA+ subset that polly's codegen writes. A Pratt parser with
// SANY's operator precedences, plus the column rule for /\ and \/ bullet lists:
// a bullet list at column c ends at the first later token at column <= c.

import { lex, TlaSyntaxError, type Token } from "./lexer";

export type Bound = { vars: string[]; set: Expr };
export type ExceptClause = { path: Array<{ index: Expr[] } | { field: string }>; value: Expr };
export type Def = { name: string; params: string[]; body: Expr };

export type Expr =
  | { k: "num"; v: number }
  | { k: "str"; v: string }
  | { k: "bool"; v: boolean }
  | { k: "id"; name: string }
  | { k: "call"; name: string; args: Expr[] }
  | { k: "op"; op: string; args: Expr[] }
  | { k: "and"; items: Expr[] }
  | { k: "or"; items: Expr[] }
  | { k: "prime"; e: Expr }
  | { k: "index"; f: Expr; args: Expr[] }
  | { k: "dot"; r: Expr; field: string }
  | { k: "setEnum"; items: Expr[] }
  | { k: "setFilter"; v: string; set: Expr; pred: Expr }
  | { k: "setMap"; e: Expr; bounds: Bound[] }
  | { k: "tuple"; items: Expr[] }
  | { k: "fun"; bounds: Bound[]; e: Expr }
  | { k: "rec"; fields: Array<[string, Expr]> }
  | { k: "recSet"; fields: Array<[string, Expr]> }
  | { k: "funSet"; dom: Expr; range: Expr }
  | { k: "except"; f: Expr; clauses: ExceptClause[] }
  | { k: "at" }
  | { k: "if"; c: Expr; t: Expr; e: Expr }
  | { k: "let"; defs: Def[]; body: Expr }
  | { k: "choose"; v: string; set: Expr; pred: Expr }
  | { k: "quant"; q: "E" | "A"; bounds: Bound[]; body: Expr }
  | { k: "actBox"; a: Expr; sub: Expr }
  | { k: "temporal"; op: string; args: Expr[] };

export type Module = {
  name: string;
  extends: string[];
  constants: string[];
  variables: string[];
  defs: Def[];
};

// Binary operators: [precedence, associativity]. SANY's table.
const INFIX: Record<string, number> = {
  "=>": 1, "<=>": 2, "~>": 2, "-+->": 2, "/\\": 3, "\\/": 3,
  "=": 5, "#": 5, "<": 5, ">": 5, "<=": 5, ">=": 5, "\\in": 5, "\\notin": 5, "\\subseteq": 5, "\\subset": 5,
  "@@": 6, ":>": 7, "\\union": 8, "\\intersect": 8, "\\": 8, "..": 9, "+": 10, "-": 10, "%": 11,
  "*": 13, "\\o": 13, "\\div": 13, "\\X": 10, "^": 14,
};

export function parseModule(src: string, file: string): Module {
  return new Parser(lex(src, file), file).module();
}

class Parser {
  private pos = 0;
  // Column limits of the open bullet lists, innermost last.
  private limits: number[] = [];

  constructor(
    private readonly toks: Token[],
    private readonly file: string
  ) {}

  private err(msg: string, tok = this.raw()): TlaSyntaxError {
    return new TlaSyntaxError(`${this.file}:${tok.line}:${tok.col}: ${msg} (at ${JSON.stringify(tok.v || tok.t)})`);
  }
  private raw(o = 0): Token {
    return this.toks[Math.min(this.pos + o, this.toks.length - 1)] as Token;
  }
  // The next token, or an end-of-input token when it sits at or left of the
  // innermost bullet column.
  private peek(): Token {
    const tok = this.raw();
    const limit = this.limits[this.limits.length - 1];
    if (limit !== undefined && tok.col <= limit && tok.t !== "eof") return { t: "eof", v: "", line: tok.line, col: tok.col };
    return tok;
  }
  private next(): Token {
    return this.toks[this.pos++] as Token;
  }
  private isOp(v: string, tok = this.peek()): boolean {
    return tok.t === "op" && tok.v === v;
  }
  private isKw(v: string, tok = this.peek()): boolean {
    return tok.t === "kw" && tok.v === v;
  }
  private expectOp(v: string): Token {
    const tok = this.raw();
    if (tok.t !== "op" || tok.v !== v) throw this.err(`expected ${v}`);
    return this.next();
  }
  private expectKw(v: string): Token {
    const tok = this.raw();
    if (tok.t !== "kw" || tok.v !== v) throw this.err(`expected ${v}`);
    return this.next();
  }
  private ident(): string {
    const tok = this.raw();
    if (tok.t !== "id") throw this.err("expected an identifier");
    this.next();
    return tok.v;
  }
  // Run fn with no bullet limit: brackets reset the column rule.
  private unlimited<T>(fn: () => T): T {
    const saved = this.limits;
    this.limits = [];
    try {
      return fn();
    } finally {
      this.limits = saved;
    }
  }

  module(): Module {
    while (this.raw().t === "sep") this.next();
    this.expectKw("MODULE");
    const name = this.ident();
    while (this.raw().t === "sep") this.next();
    const mod: Module = { name, extends: [], constants: [], variables: [], defs: [] };
    for (;;) {
      const tok = this.raw();
      if (tok.t === "end" || tok.t === "eof") break;
      if (tok.t === "sep") {
        this.next();
        continue;
      }
      if (this.isKw("EXTENDS", tok)) {
        this.next();
        mod.extends.push(...this.nameList());
      } else if (this.isKw("CONSTANT", tok) || this.isKw("CONSTANTS", tok)) {
        this.next();
        mod.constants.push(...this.nameList());
      } else if (this.isKw("VARIABLE", tok) || this.isKw("VARIABLES", tok)) {
        this.next();
        mod.variables.push(...this.nameList());
      } else if (tok.t === "id") {
        mod.defs.push(this.def());
      } else throw this.err("expected a definition");
    }
    return mod;
  }

  // a, b, c, also with the comma first on a line: `NULL\n ,Max`.
  private nameList(): string[] {
    const names = [this.ident()];
    while (this.isOp(",", this.raw())) {
      this.next();
      names.push(this.ident());
    }
    return names;
  }

  private def(): Def {
    const name = this.ident();
    const params: string[] = [];
    if (this.isOp("(", this.raw())) {
      this.next();
      params.push(this.ident());
      while (this.isOp(",", this.raw())) {
        this.next();
        params.push(this.ident());
      }
      this.expectOp(")");
    }
    this.expectOp("==");
    return { name, params, body: this.expr(0) };
  }

  expr(minPrec: number): Expr {
    let left = this.prefix();
    for (;;) {
      const tok = this.peek();
      if (tok.t !== "op") break;
      if (tok.v === "'") {
        this.next();
        left = { k: "prime", e: left };
        continue;
      }
      if (tok.v === "[") {
        this.next();
        const args = this.unlimited(() => this.exprList("]"));
        this.expectOp("]");
        left = { k: "index", f: left, args };
        continue;
      }
      if (tok.v === ".") {
        this.next();
        left = { k: "dot", r: left, field: this.ident() };
        continue;
      }
      const prec = INFIX[tok.v];
      if (prec === undefined || prec < minPrec) break;
      this.next();
      const right = this.expr(prec + 1);
      if (tok.v === "/\\" || tok.v === "\\/") {
        const k = tok.v === "/\\" ? "and" : "or";
        const items = left.k === k ? [...left.items, right] : [left, right];
        left = { k, items } as Expr;
      } else if (tok.v === "~>" || tok.v === "-+->") {
        left = { k: "temporal", op: tok.v, args: [left, right] };
      } else left = { k: "op", op: tok.v, args: [left, right] };
    }
    return left;
  }

  private exprList(close: string): Expr[] {
    const items = [this.expr(0)];
    while (this.isOp(",")) {
      this.next();
      items.push(this.expr(0));
    }
    if (!this.isOp(close, this.raw())) throw this.err(`expected ${close}`);
    return items;
  }

  private bullets(kind: "/\\" | "\\/"): Expr {
    const col = this.raw().col;
    const items: Expr[] = [];
    while (this.isOp(kind, this.raw()) && this.raw().col === col) {
      this.next();
      this.limits.push(col);
      try {
        items.push(this.expr(0));
      } finally {
        this.limits.pop();
      }
    }
    if (items.length === 1) return items[0] as Expr;
    return { k: kind === "/\\" ? "and" : "or", items } as Expr;
  }

  private bounds(): Bound[] {
    const out: Bound[] = [];
    do {
      if (out.length > 0) this.next(); // the comma
      const vars = [this.ident()];
      while (this.isOp(",")) {
        this.next();
        vars.push(this.ident());
      }
      this.expectOp("\\in");
      out.push({ vars, set: this.expr(0) });
    } while (this.isOp(","));
    return out;
  }

  private prefix(): Expr {
    const tok = this.peek();
    if (tok.t === "eof") throw this.err("unexpected end of expression");
    if (tok.t === "num") {
      this.next();
      return { k: "num", v: Number(tok.v) };
    }
    if (tok.t === "str") {
      this.next();
      return { k: "str", v: tok.v };
    }
    if (tok.t === "id") {
      this.next();
      if (this.isOp("(", this.raw())) {
        this.next();
        const args = this.unlimited(() => this.exprList(")"));
        this.expectOp(")");
        return { k: "call", name: tok.v, args };
      }
      return { k: "id", name: tok.v };
    }
    if (tok.t === "kw") {
      switch (tok.v) {
        case "TRUE":
        case "FALSE":
          this.next();
          return { k: "bool", v: tok.v === "TRUE" };
        case "IF": {
          this.next();
          const c = this.expr(0);
          this.expectKw("THEN");
          const t = this.expr(0);
          this.expectKw("ELSE");
          return { k: "if", c, t, e: this.expr(0) };
        }
        case "LET": {
          this.next();
          const defs: Def[] = [];
          while (!this.isKw("IN", this.raw())) defs.push(this.def());
          this.next();
          return { k: "let", defs, body: this.expr(0) };
        }
        case "CHOOSE": {
          this.next();
          const v = this.ident();
          this.expectOp("\\in");
          const set = this.expr(0);
          this.expectOp(":");
          return { k: "choose", v, set, pred: this.expr(0) };
        }
        case "DOMAIN":
          this.next();
          return { k: "op", op: "DOMAIN", args: [this.expr(10)] };
        case "SUBSET":
        case "UNION":
          this.next();
          return { k: "op", op: tok.v, args: [this.expr(9)] };
        case "UNCHANGED":
        case "ENABLED":
          this.next();
          return { k: "op", op: tok.v, args: [this.expr(5)] };
        default:
          throw this.err(`${tok.v} is not supported`);
      }
    }
    // Operators in prefix position.
    switch (tok.v) {
      case "/\\":
      case "\\/":
        return this.bullets(tok.v);
      case "~":
        this.next();
        return { k: "op", op: "~", args: [this.expr(5)] };
      case "-":
        this.next();
        return { k: "op", op: "neg", args: [this.expr(13)] };
      case "[]":
      case "<>":
        this.next();
        return { k: "temporal", op: tok.v, args: [this.expr(5)] };
      case "\\E":
      case "\\A": {
        this.next();
        const bounds = this.bounds();
        this.expectOp(":");
        return { k: "quant", q: tok.v === "\\E" ? "E" : "A", bounds, body: this.expr(0) };
      }
      case "@":
        this.next();
        return { k: "at" };
      case "(": {
        this.next();
        const e = this.unlimited(() => this.expr(0));
        this.expectOp(")");
        return e;
      }
      case "<<": {
        this.next();
        if (this.isOp(">>", this.raw())) {
          this.next();
          return { k: "tuple", items: [] };
        }
        const items = this.unlimited(() => this.exprList(">>"));
        this.expectOp(">>");
        return { k: "tuple", items };
      }
      case "{":
        this.next();
        return this.unlimited(() => this.braces());
      case "[":
        this.next();
        return this.unlimited(() => this.brackets());
    }
    throw this.err("unexpected token");
  }

  // After `{`.
  private braces(): Expr {
    if (this.isOp("}")) {
      this.next();
      return { k: "setEnum", items: [] };
    }
    // {x \in S : P}
    if (this.raw().t === "id" && this.isOp("\\in", this.raw(1))) {
      const save = this.pos;
      const v = this.ident();
      this.next();
      const set = this.expr(0);
      if (this.isOp(":")) {
        this.next();
        const pred = this.expr(0);
        this.expectOp("}");
        return { k: "setFilter", v, set, pred };
      }
      this.pos = save;
    }
    const first = this.expr(0);
    // {e : x \in S}
    if (this.isOp(":")) {
      this.next();
      const bounds = this.bounds();
      this.expectOp("}");
      return { k: "setMap", e: first, bounds };
    }
    const items = [first];
    while (this.isOp(",")) {
      this.next();
      items.push(this.expr(0));
    }
    this.expectOp("}");
    return { k: "setEnum", items };
  }

  // After `[`.
  private brackets(): Expr {
    // [a |-> e, ...] and [a : S, ...]
    if (this.raw().t === "id" && (this.isOp("|->", this.raw(1)) || this.isOp(":", this.raw(1)))) {
      const isRec = this.isOp("|->", this.raw(1));
      const fields: Array<[string, Expr]> = [];
      do {
        if (fields.length > 0) this.next();
        const name = this.ident();
        this.expectOp(isRec ? "|->" : ":");
        fields.push([name, this.expr(0)]);
      } while (this.isOp(","));
      this.expectOp("]");
      return isRec ? { k: "rec", fields } : { k: "recSet", fields };
    }
    // [x \in S |-> e]
    if (this.raw().t === "id" && this.isOp("\\in", this.raw(1))) {
      const save = this.pos;
      const bounds = this.bounds();
      if (this.isOp("|->")) {
        this.next();
        const e = this.expr(0);
        this.expectOp("]");
        return { k: "fun", bounds, e };
      }
      this.pos = save;
    }
    const first = this.expr(0);
    if (this.isKw("EXCEPT")) {
      this.next();
      const clauses: ExceptClause[] = [];
      do {
        if (clauses.length > 0) this.next();
        this.expectOp("!");
        const path: ExceptClause["path"] = [];
        for (;;) {
          if (this.isOp("[")) {
            this.next();
            const index = this.exprList("]");
            this.expectOp("]");
            path.push({ index });
          } else if (this.isOp(".")) {
            this.next();
            path.push({ field: this.ident() });
          } else break;
        }
        this.expectOp("=");
        clauses.push({ path, value: this.expr(0) });
      } while (this.isOp(","));
      this.expectOp("]");
      return { k: "except", f: first, clauses };
    }
    if (this.isOp("->")) {
      this.next();
      const range = this.expr(0);
      this.expectOp("]");
      return { k: "funSet", dom: first, range };
    }
    if (this.isOp("]_")) {
      this.next();
      return { k: "actBox", a: first, sub: this.prefix() };
    }
    throw this.err("unsupported [ ] form");
  }
}
