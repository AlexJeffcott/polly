#!/usr/bin/env bun
// inventory.ts : count the TLA+ operators and keywords in the specs that
// `polly verify` generates, per spec set. The count decides how much TLA+ a
// checker that compiles the generated `.tla` must accept.
//
// Usage: bun inventory.ts DIR...   (each DIR holds one generated spec set)
//        bun inventory.ts          (every examples/**/specs/tla/generated set)

import { readdirSync, readFileSync, statSync } from "node:fs";
import { basename, join, relative, resolve } from "node:path";

const ROOT = resolve(import.meta.dir, "../../../../..");

// Longest first, so `\subseteq` is not read as `\sub` and `=>` not as `=`.
const OPERATORS = [
  "\\subseteq", "\\union", "\\cup", "\\intersect", "\\cap", "\\in", "\\notin",
  "\\E", "\\A", "\\/", "/\\", "\\X", "\\o", "\\div", "\\",
  "<=>", "=>", "~>", "[]", "<>", "|->", "->", ":>", "@@", "..", "==", "#", "/=",
  "<=", ">=", "<<", ">>", "'", "!", "@", "<", ">", "=", "+", "-", "*", "%", "~",
];
const KEYWORDS = [
  "EXTENDS", "CONSTANTS", "CONSTANT", "VARIABLES", "VARIABLE", "ASSUME", "INSTANCE",
  "LET", "IN", "IF", "THEN", "ELSE", "CASE", "OTHER", "CHOOSE", "EXCEPT", "DOMAIN",
  "SUBSET", "UNION", "UNCHANGED", "ENABLED", "LAMBDA", "RECURSIVE",
  "BOOLEAN", "STRING", "Nat", "Int", "TRUE", "FALSE",
  "Len", "Append", "Head", "Tail", "SubSeq", "Seq", "Cardinality", "IsFiniteSet",
  "Print", "Assert", "ToString", "Permutations", "SortSeq", "WF_", "SF_",
];

function stripComments(text: string): string {
  let out = text.replace(/\(\*[\s\S]*?\*\)/g, " ");
  out = out.replace(/\\\*.*$/gm, "");
  // Strings carry message names and literals, not syntax.
  return out.replace(/"[^"\n]*"/g, '""');
}

function count(text: string): Map<string, number> {
  const counts = new Map<string, number>();
  const add = (k: string) => counts.set(k, (counts.get(k) ?? 0) + 1);
  const body = stripComments(text);
  for (const word of body.match(/\b[A-Za-z_][A-Za-z0-9_]*\b/g) ?? []) {
    if (KEYWORDS.includes(word)) add(word);
    else if (word.startsWith("WF_")) add("WF_");
    else if (word.startsWith("SF_")) add("SF_");
  }
  let i = 0;
  while (i < body.length) {
    const op = OPERATORS.find((o) => body.startsWith(o, i));
    if (op && !(op === "\\" && /[A-Za-z]/.test(body[i + 1] ?? ""))) {
      add(op);
      i += op.length;
    } else i += 1;
  }
  return counts;
}

function specSets(): string[] {
  const out: string[] = [];
  const walk = (dir: string) => {
    for (const entry of readdirSync(dir)) {
      if (entry === "node_modules" || entry.startsWith(".")) continue;
      const path = join(dir, entry);
      if (!statSync(path).isDirectory()) continue;
      if (readdirSync(path).some((f) => f.endsWith(".cfg"))) out.push(path);
      walk(path);
    }
  };
  walk(join(ROOT, "examples"));
  return out.filter((d) => d.includes(join("specs", "tla", "generated")));
}

const dirs = process.argv.length > 2 ? process.argv.slice(2).map((d) => resolve(d)) : specSets();
const total = new Map<string, Set<string>>();
for (const dir of dirs) {
  // Witness_*.tla files are written only by `--witness` and are checked apart.
  const files = readdirSync(dir).filter((f) => f.endsWith(".tla") && !f.startsWith("Witness_"));
  const counts = new Map<string, number>();
  for (const file of files) {
    for (const [k, n] of count(readFileSync(join(dir, file), "utf-8"))) counts.set(k, (counts.get(k) ?? 0) + n);
  }
  const name = relative(ROOT, dir);
  for (const k of counts.keys()) total.set(k, (total.get(k) ?? new Set()).add(name));
  console.log(`\n## ${name} (${files.map((f) => basename(f)).join(", ")})`);
  console.log([...counts].sort((a, b) => b[1] - a[1]).map(([k, n]) => `${k}:${n}`).join("  "));
}
console.log(`\n## All ${dirs.length} sets: construct -> number of sets that use it`);
for (const [k, sets] of [...total].sort((a, b) => b[1].size - a[1].size || a[0].localeCompare(b[0]))) {
  console.log(`${k.padEnd(12)} ${sets.size}`);
}
