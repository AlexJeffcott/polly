/**
 * Parse `.feature` files into the runner's normalized AST.
 *
 * Thin wrapper over `@cucumber/gherkin` (parser only — no cucumber runtime):
 * we keep our own {@link ParsedFeature} shape so the rest of the tool never
 * touches the gherkin message types, and swapping the parser stays a one-file
 * change. Responsibilities beyond raw parsing:
 *   - normalize And/But to the preceding concrete keyword (Given/When/Then);
 *   - fold Background steps into a feature-level list;
 *   - expand each Scenario Outline into one concrete scenario per Examples row.
 */
import { AstBuilder, GherkinClassicTokenMatcher, Parser } from "@cucumber/gherkin";
import type { GherkinDocument, Scenario } from "@cucumber/messages";
import { IdGenerator } from "@cucumber/messages";
import type { ParsedFeature, ParsedScenario, ParsedStep, StepKeyword } from "./types.ts";

function newParser() {
  return new Parser(new AstBuilder(IdGenerator.uuid()), new GherkinClassicTokenMatcher());
}

/** And/But inherit the previous concrete keyword; a leading And/But defaults to Given. */
function normalizeKeyword(raw: string, prev: StepKeyword | null): StepKeyword {
  const k = raw.trim().toLowerCase();
  if (k === "given") return "given";
  if (k === "when") return "when";
  if (k === "then") return "then";
  return prev ?? "given";
}

interface RawStep {
  keyword: string;
  text: string;
  location?: { line?: number };
}

function normalizeSteps(rawSteps: readonly RawStep[]): ParsedStep[] {
  const out: ParsedStep[] = [];
  let prev: StepKeyword | null = null;
  for (const s of rawSteps) {
    const keyword = normalizeKeyword(s.keyword, prev);
    prev = keyword;
    out.push({
      keyword,
      rawKeyword: s.keyword.trim(),
      text: s.text.trim(),
      line: s.location?.line ?? 0,
    });
  }
  return out;
}

function tagNames(tags: ReadonlyArray<{ name: string }> | undefined): string[] {
  return (tags ?? []).map((t) => t.name.replace(/^@/, ""));
}

/** Substitute `<placeholder>` cells from an Examples row into step text. */
function fillOutline(text: string, headers: string[], cells: string[]): string {
  let filled = text;
  headers.forEach((h, i) => {
    filled = filled.split(`<${h}>`).join(cells[i] ?? "");
  });
  return filled;
}

/** A plain scenario, or one concrete scenario per Scenario Outline Examples row. */
function buildScenarios(sc: Scenario): ParsedScenario[] {
  const baseSteps = sc.steps ?? [];
  const tags = tagNames(sc.tags);
  const examples = sc.examples ?? [];

  if (examples.length === 0) {
    return [
      { name: sc.name, tags, steps: normalizeSteps(baseSteps), line: sc.location?.line ?? 0 },
    ];
  }

  const out: ParsedScenario[] = [];
  for (const ex of examples) {
    const headers = (ex.tableHeader?.cells ?? []).map((c) => c.value);
    for (const row of ex.tableBody ?? []) {
      const cells = (row.cells ?? []).map((c) => c.value);
      const rowSteps = baseSteps.map((s) => ({
        keyword: s.keyword,
        text: fillOutline(s.text, headers, cells),
        location: s.location,
      }));
      const label = headers.map((h, i) => `${h}=${cells[i] ?? ""}`).join(", ");
      out.push({
        name: `${sc.name} [${label}]`,
        tags: [...tags, ...tagNames(ex.tags)],
        steps: normalizeSteps(rowSteps),
        line: row.location?.line ?? sc.location?.line ?? 0,
        fromOutline: true,
      });
    }
  }
  return out;
}

export function parseFeatureText(text: string, file: string): ParsedFeature {
  const doc: GherkinDocument = newParser().parse(text);
  const feature = doc.feature;
  if (!feature) {
    return { name: "", description: "", tags: [], background: [], scenarios: [], file };
  }

  let background: ParsedStep[] = [];
  const scenarios: ParsedScenario[] = [];

  for (const child of feature.children ?? []) {
    if (child.background) {
      background = normalizeSteps(child.background.steps ?? []);
    } else if (child.scenario) {
      scenarios.push(...buildScenarios(child.scenario));
    }
  }

  return {
    name: feature.name,
    description: (feature.description ?? "").trim(),
    tags: tagNames(feature.tags),
    background,
    scenarios,
    file,
  };
}

export async function parseFeatureFile(path: string): Promise<ParsedFeature> {
  const text = await Bun.file(path).text();
  return parseFeatureText(text, path);
}
