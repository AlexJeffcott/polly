/**
 * `polly bdd new <feature>` — scaffold a `.feature` stub seeded from the
 * project's verification config, so a three-amigos session starts from polly's
 * real ubiquitous language (the message types and state fields the model
 * already tracks) instead of inventing terms. The session's job is to turn
 * those into declarative scenarios; this just lays the table.
 */
import { existsSync } from "node:fs";
import { resolve } from "node:path";

interface ConfigShape {
  state?: Record<string, unknown>;
  messages?: { include?: string[]; perMessageBounds?: Record<string, number> };
  subsystems?: Record<string, { handlers?: string[] }>;
}

async function loadVocabulary(
  configPath: string
): Promise<{ messages: string[]; fields: string[] }> {
  if (!existsSync(configPath)) return { messages: [], fields: [] };
  const mod = await import(`file://${resolve(configPath)}?t=${Bun.nanoseconds()}`);
  const config: ConfigShape = mod.verificationConfig ?? mod.default ?? {};
  const messages = new Set<string>();
  for (const t of config.messages?.include ?? []) messages.add(t);
  for (const t of Object.keys(config.messages?.perMessageBounds ?? {})) messages.add(t);
  for (const sub of Object.values(config.subsystems ?? {})) {
    for (const h of sub.handlers ?? []) messages.add(h);
  }
  return { messages: [...messages].sort(), fields: Object.keys(config.state ?? {}).sort() };
}

function slug(name: string): string {
  return name
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-|-$/g, "");
}

export interface ScaffoldResult {
  created: boolean;
  featurePath: string;
  messages: string[];
  fields: string[];
}

export async function scaffoldFeature(
  cwd: string,
  name: string,
  configPath: string
): Promise<ScaffoldResult> {
  const { messages, fields } = await loadVocabulary(configPath);
  const featurePath = resolve(cwd, "features", `${slug(name)}.feature`);

  if (existsSync(featurePath)) {
    return { created: false, featurePath, messages, fields };
  }

  const body = `Feature: ${name}
  # Three-amigos: state the user story, then converge on declarative scenarios.
  # As a <role> I want <capability> so that <benefit>.
  #
  # Bind each step in features/steps.ts. The dual-use binding carries formal
  # metadata so 'polly bdd check' can cross-check it against the verify config:
  #   When-steps declare \`message\` (a modeled message type)
  #   Given/Then-steps declare \`stateExpr\` (a tracked state field)
  #
  # Message types this project models:
${messages.map((m) => `  #   - ${m}`).join("\n") || "  #   (none found — is specs/verification.config.ts present?)"}
  # State fields this project tracks:
${fields.map((f) => `  #   - ${f}`).join("\n") || "  #   (none found)"}

  Scenario: <name the behaviour by its outcome>
    Given <context that is already true>
    When <a single action>
    Then <an observable outcome>

  @negative
  Scenario: <the negative complement — what is excluded / rejected / empty>
    Given <context>
    When <a single action>
    Then <the system observably says no>
`;

  await Bun.write(featurePath, body);
  return { created: true, featurePath, messages, fields };
}
