#!/usr/bin/env bun
/**
 * Generate `src/polly-ui/registry.generated.ts` from the canonical
 * polly-ui sources.
 *
 * Tokens come from `src/polly-ui/theme.css`: every `--polly-*: <value>;`
 * inside the `:root` block becomes a registry entry. The token's
 * category is inferred from its name prefix so consumers and checks
 * can group them without re-parsing the CSS at runtime.
 *
 * Components come from `src/polly-ui/index.ts`: every `export { Name }`
 * line whose first identifier matches a known UI primitive becomes a
 * registry entry. Native-element replacements are pulled from
 * `tools/quality/src/check-shared-components.ts` so the registry stays
 * in lockstep with the conformance check.
 *
 * Run as part of `build:lib`. The output file lives next to
 * `src/polly-ui/registry.ts` (the hand-written re-export that pins
 * the public API surface).
 */

import { writeFile } from "node:fs/promises";
import { join } from "node:path";

const ROOT = process.cwd();
const THEME_PATH = join(ROOT, "src", "polly-ui", "theme.css");
const INDEX_PATH = join(ROOT, "src", "polly-ui", "index.ts");
const SHARED_COMPONENTS_PATH = join(
  ROOT,
  "tools",
  "quality",
  "src",
  "check-shared-components.ts"
);
const OUTPUT_PATH = join(ROOT, "src", "polly-ui", "registry.generated.ts");

type TokenCategory =
  | "color"
  | "spacing"
  | "radius"
  | "typography"
  | "motion"
  | "sizing"
  | "shadow"
  | "z-index"
  | "other";

type TokenEntry = {
  name: string;
  category: TokenCategory;
  default: string;
};

type ComponentEntry = {
  name: string;
  replaces: string[];
  importPath: string;
};

const CATEGORY_RULES: Array<{ match: RegExp; category: TokenCategory }> = [
  { match: /^space-/, category: "spacing" },
  { match: /^radius/, category: "radius" },
  { match: /^font|typography|line-height|letter-spacing/, category: "typography" },
  { match: /^transition|duration|easing|motion/, category: "motion" },
  { match: /^control-height|measure|size|min-/, category: "sizing" },
  { match: /^shadow|elevation/, category: "shadow" },
  { match: /^z-/, category: "z-index" },
  {
    match: /^surface|border|text|accent|danger|success|warning|focus|status|background|fg|bg/,
    category: "color",
  },
];

function inferCategory(tokenName: string): TokenCategory {
  // Strip the `polly-` prefix that every variable carries.
  const stripped = tokenName.replace(/^polly-/, "");
  for (const rule of CATEGORY_RULES) {
    if (rule.match.test(stripped)) return rule.category;
  }
  return "other";
}

function parseTokens(themeCss: string): TokenEntry[] {
  // Match `--polly-name: value;` declarations. Capture name and value
  // separately. Restrict to declarations inside the first :root block to
  // avoid double-counting dark-mode overrides.
  const rootMatch = themeCss.match(/:root\s*\{([\s\S]*?)\n\s*\}/);
  if (!rootMatch?.[1]) return [];
  const block = rootMatch[1];
  const out: TokenEntry[] = [];
  const seen = new Set<string>();
  const declRe = /--([a-z][a-z0-9-]*)\s*:\s*([^;]+);/gi;
  let m: RegExpExecArray | null = declRe.exec(block);
  while (m !== null) {
    const name = m[1];
    const value = (m[2] ?? "").trim();
    if (name && !seen.has(name)) {
      seen.add(name);
      out.push({ name, category: inferCategory(name), default: value });
    }
    m = declRe.exec(block);
  }
  return out.sort((a, b) => a.name.localeCompare(b.name));
}

function parseComponentNames(indexTs: string): string[] {
  // Match `export { Name } from "./Name.tsx";` or `export { Name, type … }`.
  // We extract the first identifier in the export brace block.
  const out = new Set<string>();
  const re = /export\s+\{\s*(\w+)/g;
  let m: RegExpExecArray | null = re.exec(indexTs);
  while (m !== null) {
    const name = m[1];
    if (name && /^[A-Z]/.test(name)) out.add(name);
    m = re.exec(indexTs);
  }
  return [...out].sort();
}

function parseSharedComponentReplacements(
  source: string
): Map<string, string[]> {
  // The `DEFAULT_SHARED_COMPONENT_RULES` array carries `element` and
  // `replacement` strings. We invert it to a `replacement → [element]`
  // map so the registry can answer "which native elements does
  // <Button> replace?". One replacement may map to several elements
  // (e.g. <ActionInput> covers both <input> and <textarea>).
  const out = new Map<string, string[]>();
  // Match objects of the form { pattern: …, element: "<x>", replacement: "<Y>" }.
  const re = /element:\s*"<([^>]+)>"\s*,\s*replacement:\s*"([^"]+)"/g;
  let m: RegExpExecArray | null = re.exec(source);
  while (m !== null) {
    const element = m[1];
    const replacement = m[2];
    if (!element || !replacement) {
      m = re.exec(source);
      continue;
    }
    // Replacement may contain multiple component refs separated by `or`.
    const componentRefs = replacement.match(/<([A-Z]\w*)/g) ?? [];
    for (const ref of componentRefs) {
      const compName = ref.replace(/^</, "");
      const list = out.get(compName) ?? [];
      list.push(element);
      out.set(compName, list);
    }
    m = re.exec(source);
  }
  return out;
}

function buildComponents(
  names: string[],
  replacements: Map<string, string[]>
): ComponentEntry[] {
  return names.map((name) => ({
    name,
    replaces: replacements.get(name) ?? [],
    importPath: "@fairfox/polly/ui",
  }));
}

function emitOutput(tokens: TokenEntry[], components: ComponentEntry[]): string {
  const header = `/**
 * Generated by scripts/build-polly-ui-registry.ts.
 *
 * Do not edit by hand. Edit src/polly-ui/theme.css, src/polly-ui/index.ts,
 * or tools/quality/src/check-shared-components.ts and re-run the
 * generator to refresh this file.
 */

`;
  const tokensLit = JSON.stringify(tokens, null, 2);
  const componentsLit = JSON.stringify(components, null, 2);
  return `${header}export type PollyUiTokenCategory =
  | "color"
  | "spacing"
  | "radius"
  | "typography"
  | "motion"
  | "sizing"
  | "shadow"
  | "z-index"
  | "other";

export type PollyUiToken = {
  name: string;
  category: PollyUiTokenCategory;
  default: string;
};

export type PollyUiComponent = {
  name: string;
  replaces: string[];
  importPath: string;
};

export const pollyUiTokens: readonly PollyUiToken[] = ${tokensLit} as const;

export const pollyUiComponents: readonly PollyUiComponent[] = ${componentsLit} as const;
`;
}

async function main(): Promise<void> {
  const themeCss = await Bun.file(THEME_PATH).text();
  const indexTs = await Bun.file(INDEX_PATH).text();
  const sharedSrc = await Bun.file(SHARED_COMPONENTS_PATH).text();

  const tokens = parseTokens(themeCss);
  const componentNames = parseComponentNames(indexTs);
  const replacements = parseSharedComponentReplacements(sharedSrc);
  const components = buildComponents(componentNames, replacements);

  const output = emitOutput(tokens, components);
  await writeFile(OUTPUT_PATH, output, "utf8");

  process.stdout.write(
    `polly-ui registry: ${tokens.length} token(s), ${components.length} component(s) → ${OUTPUT_PATH}\n`
  );
}

await main();
