/**
 * The verify cross-link, half two: hold every scenario trace against the
 * verification config — the always-on, static, cheap gate (`polly bdd check`).
 * The deeper TLC reachability *witness* rides `polly verify --witness`
 * (tools/verify); this file never runs a model checker.
 *
 * Three checks, each the BDD analogue of a verify guarantee:
 *   1. every `When` message type is one the config actually models (and so has
 *      a handler the model knows about) — a scenario that drives a phantom
 *      message is a scenario about nothing;
 *   2. every `Given`/`Then` state expression names a field the config tracks —
 *      an assertion on an unmodeled field can't be cross-checked or verified;
 *   3. every feature that filters/selects/validates carries a negative
 *      complement (a scenario tagged `@negative` or `@formal`) — the mechanical
 *      enforcer of the Tester's "prove the system also says no" rule, which is
 *      exactly what mutation testing then makes teeth on.
 */
import { resolve } from "node:path";
import { extractTraces } from "./extract.ts";
import type { ScenarioTrace } from "./types.ts";

export interface Finding {
  kind: "error" | "warn";
  scenario: string;
  message: string;
}

export interface CrossCheckResult {
  ok: boolean;
  checked: number;
  findings: Finding[];
}

interface VerifyConfigShape {
  state?: Record<string, unknown>;
  messages?: { include?: string[]; perMessageBounds?: Record<string, number> };
  subsystems?: Record<string, { state?: string[]; handlers?: string[] }>;
}

function isRecord(input: unknown): input is Record<string, unknown> {
  return typeof input === "object" && input !== null && !Array.isArray(input);
}

function isStringArray(input: unknown): input is string[] {
  return Array.isArray(input) && input.every((item) => typeof item === "string");
}

function isMessagesShape(input: unknown): input is VerifyConfigShape["messages"] {
  if (!isRecord(input)) return false;
  if (input["include"] !== undefined && !isStringArray(input["include"])) return false;
  if (input["perMessageBounds"] !== undefined && !isRecord(input["perMessageBounds"])) {
    return false;
  }
  return true;
}

function isSubsystemsShape(input: unknown): input is VerifyConfigShape["subsystems"] {
  if (!isRecord(input)) return false;
  for (const sub of Object.values(input)) {
    if (!isRecord(sub)) return false;
    if (sub["state"] !== undefined && !isStringArray(sub["state"])) return false;
    if (sub["handlers"] !== undefined && !isStringArray(sub["handlers"])) return false;
  }
  return true;
}

/**
 * Narrow a dynamically imported export to the slice of the verification config
 * this file reads. A bare cast would accept a config whose `messages.include`
 * or `subsystems[x].handlers` is not an array of strings, and every check below
 * would then read an empty set and report a clean bill on nothing. Keys this
 * file does not read are left alone.
 */
function isVerifyConfigShape(input: unknown): input is VerifyConfigShape {
  if (!isRecord(input)) return false;
  if (input["state"] !== undefined && !isRecord(input["state"])) return false;
  if (input["messages"] !== undefined && !isMessagesShape(input["messages"])) return false;
  if (input["subsystems"] !== undefined && !isSubsystemsShape(input["subsystems"])) return false;
  return true;
}

async function loadVerifyConfig(configPath: string): Promise<VerifyConfigShape> {
  const mod = await import(`file://${resolve(configPath)}?t=${Bun.nanoseconds()}`);
  const config: unknown = mod.verificationConfig ?? mod.default;
  if (!config) throw new Error(`no verificationConfig/default export in ${configPath}`);
  if (!isVerifyConfigShape(config)) {
    throw new Error(
      `verificationConfig in ${configPath} does not match the shape this check reads ` +
        "(state must be an object; messages.include and subsystems[*].state/handlers must be string arrays)"
    );
  }
  return config;
}

/** Union of every message type the config models. */
function messageSet(config: VerifyConfigShape): Set<string> {
  const set = new Set<string>();
  for (const t of config.messages?.include ?? []) set.add(t);
  for (const t of Object.keys(config.messages?.perMessageBounds ?? {})) set.add(t);
  for (const sub of Object.values(config.subsystems ?? {})) {
    for (const h of sub.handlers ?? []) set.add(h);
  }
  return set;
}

/** Every state field key the config tracks. */
function stateKeys(config: VerifyConfigShape): string[] {
  const keys = new Set(Object.keys(config.state ?? {}));
  for (const sub of Object.values(config.subsystems ?? {})) {
    for (const f of sub.state ?? []) keys.add(f);
  }
  return [...keys];
}

/** Dotted identifier paths in an expression, minus string literals and keywords. */
function fieldsIn(expr: string): string[] {
  const noStrings = expr.replace(/"[^"]*"|'[^']*'/g, "");
  const ids = noStrings.match(/[a-zA-Z_$][\w$]*(?:\.[a-zA-Z_$][\w$]*)*/g) ?? [];
  const ignore = new Set(["true", "false", "null", "undefined", "length", "value"]);
  return ids.filter((id) => !ignore.has(id) && Number.isNaN(Number(id)));
}

/** A field matches a config key if either is a dotted prefix of the other. */
function fieldKnown(field: string, keys: string[]): boolean {
  return keys.some((k) => k === field || field.startsWith(`${k}.`) || k.startsWith(`${field}.`));
}

const NEGATIVE_TAGS = new Set(["negative", "formal", "forbidden"]);

function checkTrace(
  trace: ScenarioTrace,
  messages: Set<string>,
  keys: string[],
  findings: Finding[]
): void {
  const id = `${trace.feature} › ${trace.scenario}`;

  for (const step of [...trace.given, ...trace.when, ...trace.then]) {
    if (step.unbound) {
      findings.push({ kind: "warn", scenario: id, message: `step has no binding: "${step.text}"` });
    }
  }

  for (const step of trace.when) {
    if (step.message && !messages.has(step.message)) {
      findings.push({
        kind: "error",
        scenario: id,
        message: `When sends "${step.message}", which the verification config does not model`,
      });
    }
  }

  for (const step of [...trace.given, ...trace.then]) {
    if (!step.stateExpr) continue;
    for (const field of fieldsIn(step.stateExpr)) {
      if (!fieldKnown(field, keys)) {
        findings.push({
          kind: "error",
          scenario: id,
          message: `${step.keyword} asserts on "${field}", absent from the config's state map`,
        });
      }
    }
  }
}

/** A feature filters/selects/validates if any Then mentions an exclusion/limit notion. */
function featureNeedsNegative(traces: ScenarioTrace[]): boolean {
  return traces.some((t) =>
    t.then.some((s) => /\bnot\b|exclud|reject|empty|invalid|limit|forbidden/i.test(s.text))
  );
}

function checkNegativeComplement(traces: ScenarioTrace[], findings: Finding[]): void {
  const byFeature = new Map<string, ScenarioTrace[]>();
  for (const t of traces) {
    const arr = byFeature.get(t.feature) ?? [];
    arr.push(t);
    byFeature.set(t.feature, arr);
  }
  for (const [feature, group] of byFeature) {
    const hasNegative = group.some((t) => t.tags.some((tag) => NEGATIVE_TAGS.has(tag)));
    if (!hasNegative && featureNeedsNegative(group)) {
      findings.push({
        kind: "warn",
        scenario: feature,
        message:
          "feature filters/selects/validates but has no negative complement (a @negative or @formal scenario) — an over-permissive build would still pass",
      });
    }
  }
}

export async function checkAgainstVerify(opts: {
  featureFiles: string[];
  stepFiles: string[];
  configPath: string;
}): Promise<CrossCheckResult> {
  const config = await loadVerifyConfig(opts.configPath);
  const messages = messageSet(config);
  const keys = stateKeys(config);

  const traces = await extractTraces(opts.featureFiles, opts.stepFiles);
  const findings: Finding[] = [];

  for (const trace of traces) checkTrace(trace, messages, keys, findings);
  checkNegativeComplement(traces, findings);

  return {
    ok: findings.every((f) => f.kind !== "error"),
    checked: traces.length,
    findings,
  };
}
