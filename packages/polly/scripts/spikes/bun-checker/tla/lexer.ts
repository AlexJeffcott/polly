// Lexer for the TLA+ subset that polly's codegen writes. Each token keeps its
// line and column: the parser needs the column for /\ and \/ bullet lists.

export type TokenType = "id" | "num" | "str" | "op" | "kw" | "sep" | "end" | "eof";
export type Token = { t: TokenType; v: string; line: number; col: number };

const KEYWORDS = new Set([
  "MODULE", "EXTENDS", "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES", "ASSUME", "LOCAL",
  "INSTANCE", "RECURSIVE", "LAMBDA", "LET", "IN", "IF", "THEN", "ELSE", "CASE", "OTHER", "CHOOSE",
  "EXCEPT", "DOMAIN", "SUBSET", "UNION", "UNCHANGED", "ENABLED", "TRUE", "FALSE",
]);

// Operators made of symbols, longest first.
const SYMBOLS = [
  "-+->", "<=>", "|->", "=>", "~>", "[]", "<>", "<<", ">>", "->", ":>", "@@", "..", "==", "/=",
  "<=", ">=", "=<", "]_", "::", "/\\", "\\/", "'", "!", "@", "<", ">", "=", "+", "-", "*", "%",
  "~", "#", "(", ")", "[", "]", "{", "}", ",", ":", ".", "^", "|", "&",
];

// Operators spelt as a backslash and a word.
const BACKSLASH_WORDS = new Set([
  "in", "notin", "subseteq", "subset", "union", "cup", "intersect", "cap", "E", "A", "X", "o",
  "div", "times", "land", "lor", "lnot", "neg", "equiv", "leq", "geq",
]);
const ALIASES: Record<string, string> = {
  "\\cup": "\\union", "\\cap": "\\intersect", "\\land": "/\\", "\\lor": "\\/", "\\lnot": "~",
  "\\neg": "~", "\\leq": "<=", "\\geq": ">=", "=<": "<=", "/=": "#", "\\equiv": "<=>",
};

export class TlaSyntaxError extends Error {}

export function lex(src: string, file: string): Token[] {
  const out: Token[] = [];
  let i = 0;
  let line = 1;
  let lineStart = 0;
  const err = (msg: string) => new TlaSyntaxError(`${file}:${line}:${i - lineStart + 1}: ${msg}`);
  const push = (t: TokenType, v: string, start: number) => out.push({ t, v, line, col: start - lineStart + 1 });

  while (i < src.length) {
    const ch = src[i] as string;
    if (ch === "\n") {
      line++;
      i++;
      lineStart = i;
      continue;
    }
    if (ch === " " || ch === "\t" || ch === "\r") {
      i++;
      continue;
    }
    // \* line comment
    if (src.startsWith("\\*", i)) {
      while (i < src.length && src[i] !== "\n") i++;
      continue;
    }
    // (* block comment *), nested
    if (src.startsWith("(*", i)) {
      let depth = 0;
      while (i < src.length) {
        if (src.startsWith("(*", i)) {
          depth++;
          i += 2;
        } else if (src.startsWith("*)", i)) {
          depth--;
          i += 2;
          if (depth === 0) break;
        } else {
          if (src[i] === "\n") {
            line++;
            lineStart = i + 1;
          }
          i++;
        }
      }
      if (depth !== 0) throw err("unclosed comment");
      continue;
    }
    // ---- separators and ==== module end
    if (src.startsWith("----", i)) {
      const s = i;
      while (src[i] === "-") i++;
      push("sep", "----", s);
      continue;
    }
    if (src.startsWith("====", i)) {
      const s = i;
      while (src[i] === "=") i++;
      push("end", "====", s);
      continue;
    }
    if (/[0-9]/.test(ch)) {
      const s = i;
      while (/[0-9]/.test(src[i] ?? "")) i++;
      if (/[A-Za-z_]/.test(src[i] ?? "")) throw err("identifiers that start with a digit are not supported");
      push("num", src.slice(s, i), s);
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      const s = i;
      while (/[A-Za-z0-9_]/.test(src[i] ?? "")) i++;
      const word = src.slice(s, i);
      push(KEYWORDS.has(word) ? "kw" : "id", word, s);
      continue;
    }
    if (ch === '"') {
      const s = i;
      i++;
      let v = "";
      while (i < src.length && src[i] !== '"') {
        if (src[i] === "\\") {
          const e = src[i + 1];
          v += e === "n" ? "\n" : e === "t" ? "\t" : (e ?? "");
          i += 2;
        } else v += src[i++];
      }
      if (src[i] !== '"') throw err("unclosed string");
      i++;
      push("str", v, s);
      continue;
    }
    if (ch === "\\") {
      const m = /^\\([A-Za-z]+)/.exec(src.slice(i, i + 16));
      if (m && BACKSLASH_WORDS.has(m[1] as string)) {
        const op = `\\${m[1]}`;
        push("op", ALIASES[op] ?? op, i);
        i += op.length;
        continue;
      }
      if (src.startsWith("\\/", i)) {
        push("op", "\\/", i);
        i += 2;
        continue;
      }
      push("op", "\\", i);
      i++;
      continue;
    }
    const sym = SYMBOLS.find((s) => src.startsWith(s, i));
    if (!sym) throw err(`unexpected character ${JSON.stringify(ch)}`);
    push("op", ALIASES[sym] ?? sym, i);
    i += sym.length;
  }
  out.push({ t: "eof", v: "", line: line + 1, col: 0 });
  return out;
}
