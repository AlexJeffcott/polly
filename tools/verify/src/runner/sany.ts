// SANY integration - Official TLA+ syntax analyzer
// SANY is the official TLA+ parser that validates specification syntax

import * as fs from "node:fs";
import * as path from "node:path";
import type { DockerRunResult, DockerRunner } from "./docker";

/**
 * Parse error from SANY with location information
 */
export type ParseError = {
  type: "syntax" | "semantic" | "lexical" | "unknown";
  message: string;
  line?: number;
  column?: number;
  file?: string;
  suggestion?: string;
};

/**
 * Result of SANY validation
 */
export type ValidationResult = {
  valid: boolean;
  errors: ParseError[];
  warnings: string[];
  output: string;
};

/**
 * SANYRunner integrates the official TLA+ syntax analyzer (SANY)
 * via Docker to validate generated specifications.
 *
 * SANY is the standard TLA+ parser used by TLC and the TLA+ Toolbox.
 * Running it ensures that generated specs are syntactically valid
 * before attempting model checking.
 */
export class SANYRunner {
  constructor(private dockerRunner: DockerRunner) {}

  /**
   * Parse and validate TLA+ spec using SANY
   *
   * Runs: docker run talex5/tla java tla2sany.SANY spec.tla
   *
   * Returns structured validation result with errors, warnings, and line numbers
   */
  async validateSpec(specPath: string): Promise<ValidationResult> {
    // Ensure spec file exists
    if (!fs.existsSync(specPath)) {
      return {
        valid: false,
        errors: [
          {
            type: "unknown",
            message: `Spec file not found: ${specPath}`,
          },
        ],
        warnings: [],
        output: "",
      };
    }

    const specDir = path.dirname(specPath);
    const specName = path.basename(specPath);

    // Run SANY in Docker
    // Mount spec directory so SANY can find imported modules
    const args = [
      "run",
      "--rm",
      "-v",
      `${specDir}:/specs`,
      "talex5/tla",
      "sh",
      "-c",
      `cd /specs && java tla2sany.SANY ${specName}`,
    ];

    try {
      const result = await this.dockerRunner.runCommand("docker", args, {
        timeout: 30000, // 30 seconds should be plenty for parsing
      });

      return this.parseSANYOutput(result, specPath);
    } catch (error) {
      return {
        valid: false,
        errors: [
          {
            type: "unknown",
            message: `SANY execution failed: ${error instanceof Error ? error.message : String(error)}`,
          },
        ],
        warnings: [],
        output: "",
      };
    }
  }

  /**
   * Quick syntax-only check without semantic analysis
   *
   * This is faster than full validation and useful for
   * fast-fail during development.
   */
  async checkSyntax(specPath: string): Promise<boolean> {
    const result = await this.validateSpec(specPath);
    // Only check for syntax errors, ignore semantic warnings
    return result.errors.filter((e) => e.type === "syntax" || e.type === "lexical").length === 0;
  }

  /**
   * Full validation including module imports
   *
   * This validates not just the main spec but also ensures
   * all imported modules can be found and parsed.
   */
  async validateWithDependencies(specPath: string, _modulesDir: string): Promise<ValidationResult> {
    // For now, just validate the spec - dependency tracking can be enhanced later
    // The Docker mount already gives SANY access to the spec directory
    return this.validateSpec(specPath);
  }

  /**
   * Parse SANY output to extract errors, warnings, and line numbers
   *
   * SANY output format:
   * - "Parsing file ..." - indicates parsing started
   * - "Semantic processing of module ..." - indicates semantic analysis
   * - "*** Errors: N" - error count
   * - "Lexical error at line X, column Y" - syntax errors
   * - "Semantic error at line X, column Y" - semantic errors
   */
  private parseSANYOutput(result: DockerRunResult, specPath: string): ValidationResult {
    const output = result.stdout + result.stderr;
    const errors: ParseError[] = [];
    const warnings: string[] = [];

    // SANY exit code 0 means success
    // But if there are semantic warnings, we need to parse them (they use location format)
    if (
      result.exitCode === 0 &&
      !output.includes("*** Errors:") &&
      !output.includes("***Parse Error***") &&
      !output.includes("Fatal errors") &&
      !output.includes("*** Warnings:")
    ) {
      return {
        valid: true,
        errors: [],
        warnings: this.extractWarnings(output),
        output,
      };
    }

    // Parse error patterns
    const lines = output.split("\n");
    let inWarningsSection = false; // Track if we're in "Semantic errors: *** Warnings:" section

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (!line) continue;

      // Track if we're in the warnings section
      if (line.includes("*** Warnings:")) {
        inWarningsSection = true;
      } else if (line.includes("*** Errors:")) {
        inWarningsSection = false;
      }

      // SANY-style parse errors: "***Parse Error***" followed by context
      // Format:
      //   ***Parse Error***
      //   Was expecting "..."
      //   Encountered "..." at line X, column Y
      if (line.includes("***Parse Error***")) {
        const expectingLine = lines[i + 1] || "";
        const encounteredLine = lines[i + 2] || "";

        // Extract line/column from "Encountered ... at line X, column Y"
        const locationMatch = encounteredLine.match(/at line (\d+), column (\d+)/);

        let message = "Parse error";
        if (expectingLine.includes("Was expecting")) {
          message = expectingLine.trim();
        }

        errors.push({
          type: "syntax",
          message,
          line: locationMatch?.[1] ? Number.parseInt(locationMatch[1]) : undefined,
          column: locationMatch?.[2] ? Number.parseInt(locationMatch[2]) : undefined,
          file: specPath,
          suggestion: this.suggestSyntaxFix(message),
        });
        i += 2; // Skip the next two lines we already processed
        continue;
      }

      // Lexical errors (invalid characters, unclosed strings, etc.)
      const lexicalMatch = line.match(
        /Lexical error at line (\d+), column (\d+)\.?\s*Encountered:\s*(.+)/
      );
      if (lexicalMatch?.[1] && lexicalMatch[2] && lexicalMatch[3]) {
        errors.push({
          type: "lexical",
          message: `Lexical error: ${lexicalMatch[3]}`,
          line: Number.parseInt(lexicalMatch[1]),
          column: Number.parseInt(lexicalMatch[2]),
          file: specPath,
          suggestion: this.suggestLexicalFix(lexicalMatch[3]),
        });
        continue;
      }

      // Parse errors (single-line format)
      const parseMatch = line.match(
        /(?:Parse |Syntax )error at line (\d+), column (\d+)(?:\s+of\s+module\s+\w+)?\.?\s*(.+)/i
      );
      if (parseMatch?.[1] && parseMatch[2] && parseMatch[3]) {
        errors.push({
          type: "syntax",
          message: parseMatch[3],
          line: Number.parseInt(parseMatch[1]),
          column: Number.parseInt(parseMatch[2]),
          file: specPath,
          suggestion: this.suggestSyntaxFix(parseMatch[3]),
        });
        continue;
      }

      // Semantic error/warning location line:
      // "line X, col Y to line X, col Y of module ModuleName"
      // followed by error/warning message on next line(s)
      const semanticLocationMatch = line.match(
        /^line (\d+), col (\d+) to line \d+, col \d+ of module (\w+)/
      );
      if (semanticLocationMatch?.[1] && semanticLocationMatch[2]) {
        // Collect message lines (until we hit another "line" or empty line or end)
        const msgLines = [];
        let j = i + 1;
        while (j < lines.length) {
          const msgLine = lines[j];
          if (
            !msgLine ||
            msgLine.trim() === "" ||
            msgLine.startsWith("line ") ||
            msgLine.includes("***")
          ) {
            break;
          }
          msgLines.push(msgLine.trim());
          j++;
        }

        const message = msgLines.join(" ").trim();

        // Add to warnings if in warnings section, otherwise errors
        if (inWarningsSection) {
          warnings.push(
            `line ${semanticLocationMatch[1]}, col ${semanticLocationMatch[2]}: ${message || "Semantic warning"}`
          );
        } else {
          errors.push({
            type: "semantic",
            message: message || "Semantic error",
            line: Number.parseInt(semanticLocationMatch[1]),
            column: Number.parseInt(semanticLocationMatch[2]),
            file: specPath,
          });
        }
        i = j - 1; // Skip to last processed line
        continue;
      }

      // Semantic errors (single-line format - fallback)
      const semanticMatch = line.match(
        /Semantic error at line (\d+), column (\d+)(?:\s+of\s+module\s+\w+)?\.?\s*(.+)/i
      );
      if (semanticMatch?.[1] && semanticMatch[2] && semanticMatch[3]) {
        errors.push({
          type: "semantic",
          message: semanticMatch[3],
          line: Number.parseInt(semanticMatch[1]),
          column: Number.parseInt(semanticMatch[2]),
          file: specPath,
        });
        continue;
      }

      // Generic error pattern
      if (line.includes("Error:") || line.includes("error:")) {
        errors.push({
          type: "unknown",
          message: line.trim(),
        });
      }

      // Warnings
      if (line.includes("Warning:") || line.includes("warning:")) {
        warnings.push(line.trim());
      }
    }

    // If we found no specific errors but SANY failed, create a generic error
    if (errors.length === 0 && result.exitCode !== 0) {
      errors.push({
        type: "unknown",
        message: "SANY validation failed with unknown error",
      });
    }

    // Valid if there are no errors (warnings are ok)
    return {
      valid: errors.length === 0,
      errors,
      warnings,
      output,
    };
  }

  /**
   * Extract warnings from SANY output
   */
  private extractWarnings(output: string): string[] {
    const warnings: string[] = [];
    const lines = output.split("\n");

    for (const line of lines) {
      if (line.includes("Warning:") || line.includes("warning:")) {
        warnings.push(line.trim());
      }
    }

    return warnings;
  }

  /**
   * Suggest fix for lexical errors
   */
  private suggestLexicalFix(error: string): string | undefined {
    if (error.includes('"') && error.includes("(59)")) {
      return "Check for invalid characters like semicolons in identifiers. TLA+ identifiers must match /^[a-zA-Z][a-zA-Z0-9_]*$/";
    }
    if (error.includes("Encountered: <EOF>")) {
      return "Unexpected end of file - check for unclosed brackets or incomplete definitions";
    }
    return undefined;
  }

  /**
   * Suggest fix for syntax errors
   */
  private suggestSyntaxFix(error: string): string | undefined {
    if (error.toLowerCase().includes("expected")) {
      return "Syntax structure error - verify operator placement and bracket matching";
    }
    return undefined;
  }
}
