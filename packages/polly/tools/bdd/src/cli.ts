#!/usr/bin/env bun
/**
 * `polly bdd` — author and run executable Gherkin against polly's own model.
 *
 * BDD is polly's third verification stratum. verify (TLA+) proves invariants
 * over the handler state machine; mutate (Stryker) proves the tests have teeth;
 * BDD pins down what a feature should do *from the user's perspective*, as
 * concrete examples that run across the real factory boundary. A Gherkin
 * scenario decomposes onto the same vocabulary the other two already speak:
 * Given = state signals, When = a message type, Then = an observable outcome.
 *
 * Thin verb dispatcher over the reusable functions in this directory.
 */
import { resolve } from "node:path";
import { parseBddArgs } from "./args.ts";
import { checkAgainstVerify } from "./check-verify.ts";
import { resolveBddConfig } from "./config.ts";
import { formatRun, toJson } from "./report.ts";
import { runFeatures } from "./run.ts";
import { scaffoldFeature } from "./scaffold.ts";

const HELP = `polly bdd — executable Gherkin against polly's handlers + state

Three-amigos sessions produce acceptance examples from the user's perspective;
this runs them across the real factory boundary and cross-checks them against
the verification config — so the example layer, the formal layer, and the
mutation layer all describe the same handlers and state.

Usage:
  polly bdd [run] [path]      Run .feature files (default: features/**/*.feature)
  polly bdd check             Cross-check scenarios against specs/verification.config.ts
  polly bdd new <name>        Scaffold a feature stub seeded from the verify vocabulary
  polly bdd help              Show this help

Flags:
  --features <glob>   feature files (default: features/**/*.feature)
  --steps <glob>      step modules to load (default: features/**/*.steps.ts + features/steps.ts)
  --tags <tag>        only run scenarios with this tag (~tag negates)
  --json              machine-readable output
  -h, --help

Scenarios tagged @formal cover precondition-only behaviour (requires() is a
runtime no-op) — the runner defers them; 'polly verify' checks them, since the
requires() guard is extracted into the TLA+ model.`;

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: a flat verb dispatcher — the branches are the command surface.
async function main(): Promise<number> {
  const args = parseBddArgs(process.argv.slice(2));
  if (args.help || args.verb === "help") {
    console.log(HELP);
    return 0;
  }

  const cwd = process.cwd();

  switch (args.verb) {
    case "run": {
      const cfg = await resolveBddConfig(cwd, args);
      if (cfg.featureFiles.length === 0) {
        console.log("No .feature files found (looked for features/**/*.feature).");
        return 1;
      }
      if (cfg.stepFiles.length === 0) {
        console.log(
          "No step modules found (looked for features/**/*.steps.ts and features/steps.ts)."
        );
        return 1;
      }
      const result = await runFeatures({
        featureFiles: cfg.featureFiles,
        stepFiles: cfg.stepFiles,
        tagFilter: args.tags,
      });
      console.log(args.json ? toJson(result) : formatRun(result, cwd));
      return result.ok ? 0 : 1;
    }

    case "check": {
      const cfg = await resolveBddConfig(cwd, args);
      const configPath = resolve(cwd, "specs", "verification.config.ts");
      const result = await checkAgainstVerify({
        featureFiles: cfg.featureFiles,
        stepFiles: cfg.stepFiles,
        configPath,
      });
      if (args.json) {
        console.log(JSON.stringify(result, null, 2));
        return result.ok ? 0 : 1;
      }
      console.log(`\nCross-checked ${result.checked} scenario(s) against the verification config:`);
      if (result.findings.length === 0) {
        console.log("  ✓ every When models a real message; every Given/Then names a tracked field");
      }
      for (const f of result.findings) {
        console.log(`  ${f.kind === "error" ? "✗" : "⚠"} ${f.scenario}\n      ${f.message}`);
      }
      console.log(result.ok ? "\n✓ BDD ↔ verify cross-check holds." : "\n✗ Cross-check failed.");
      return result.ok ? 0 : 1;
    }

    case "new": {
      const name = args.rest.join(" ").trim();
      if (!name) {
        console.log("usage: polly bdd new <feature name>");
        return 1;
      }
      const configPath = resolve(cwd, "specs", "verification.config.ts");
      const res = await scaffoldFeature(cwd, name, configPath);
      if (!res.created) {
        console.log(`${res.featurePath} already exists.`);
        return 1;
      }
      console.log(`✓ wrote ${res.featurePath}`);
      console.log(
        `  seeded from ${res.messages.length} message type(s), ${res.fields.length} state field(s)`
      );
      console.log("\nNext: bind the steps in features/steps.ts, then 'polly bdd run'.");
      return 0;
    }

    default:
      console.log(`Unknown subcommand: ${args.verb}\n`);
      console.log(HELP);
      return 1;
  }
}

main()
  .then((code) => process.exit(code))
  .catch((err) => {
    console.log(`\n❌ ${err instanceof Error ? err.message : String(err)}`);
    process.exit(1);
  });
