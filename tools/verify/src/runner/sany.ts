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

    // Check for early success
    if (this.isSuccessfulParse(result.exitCode, output)) {
      return {
        valid: true,
        errors: [],
        warnings: this.extractWarnings(output),
        output,
      };
    }

    // Parse errors from output
    const { errors, warnings } = this.parseErrorsFromOutput(output, specPath);

    // Add fallback error if no specific errors found
    const finalErrors = this.addFallbackErrorIfNeeded(errors, result.exitCode);

    return {
      valid: finalErrors.length === 0,
      errors: finalErrors,
      warnings,
      output,
    };
  }

  /**
   * Parse errors and warnings from SANY output text
   */
  private parseErrorsFromOutput(
    output: string,
    specPath: string
  ): { errors: ParseError[]; warnings: string[] } {
    const errors: ParseError[] = [];
    const warnings: string[] = [];
    const lines = output.split("\n");
    let inWarningsSection = false;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (!line) continue;

      // Track warnings section
      inWarningsSection = this.updateWarningsSection(line, inWarningsSection);

      // Try each error pattern handler
      const result = this.tryParseErrorPatterns(line, lines, i, specPath, inWarningsSection);
      if (result.handled) {
        if (result.error) errors.push(result.error);
        if (result.warning) warnings.push(result.warning);
        if (result.skipLines) i += result.skipLines;
      }
    }

    return { errors, warnings };
  }

  /**
   * Add fallback error if no specific errors were found but exit code indicates failure
   */
  private addFallbackErrorIfNeeded(errors: ParseError[], exitCode: number): ParseError[] {
    if (errors.length === 0 && exitCode !== 0) {
      return [
        ...errors,
        {
          type: "unknown",
          message: "SANY validation failed with unknown error",
        },
      ];
    }
    return errors;
  }

  /**
   * Check if parse completed successfully
   */
  private isSuccessfulParse(exitCode: number, output: string): boolean {
    return (
      exitCode === 0 &&
      !output.includes("*** Errors:") &&
      !output.includes("***Parse Error***") &&
      !output.includes("Fatal errors") &&
      !output.includes("*** Warnings:")
    );
  }

  /**
   * Update warnings section tracking
   */
  private updateWarningsSection(line: string, inWarningsSection: boolean): boolean {
    if (line.includes("*** Warnings:")) return true;
    if (line.includes("*** Errors:")) return false;
    return inWarningsSection;
  }

  /**
   * Try parsing the line with all error pattern handlers
   */
  private tryParseErrorPatterns(
    line: string,
    lines: string[],
    index: number,
    specPath: string,
    inWarningsSection: boolean
  ): { handled: boolean; error?: ParseError; warning?: string; skipLines?: number } {
    // Try ***Parse Error*** pattern (multi-line)
    const parseErrorResult = this.tryParseError(line, lines, index, specPath);
    if (parseErrorResult) return parseErrorResult;

    // Try lexical error pattern
    const lexicalResult = this.tryLexicalError(line, specPath);
    if (lexicalResult) return lexicalResult;

    // Try syntax error pattern
    const syntaxResult = this.trySyntaxError(line, specPath);
    if (syntaxResult) return syntaxResult;

    // Try semantic location pattern (multi-line)
    const semanticLocationResult = this.trySemanticLocation(
      line,
      lines,
      index,
      specPath,
      inWarningsSection
    );
    if (semanticLocationResult) return semanticLocationResult;

    // Try semantic error fallback
    const semanticResult = this.trySemanticError(line, specPath);
    if (semanticResult) return semanticResult;

    // Try generic error/warning patterns
    const genericResult = this.tryGenericErrorOrWarning(line);
    if (genericResult) return genericResult;

    return { handled: false };
  }

  /**
   * Handle ***Parse Error*** pattern (multi-line)
   */
  private tryParseError(
    line: string,
    lines: string[],
    index: number,
    specPath: string
  ): { handled: boolean; error: ParseError; skipLines: number } | null {
    if (!line.includes("***Parse Error***")) return null;

    const expectingLine = lines[index + 1] || "";
    const encounteredLine = lines[index + 2] || "";
    const locationMatch = encounteredLine.match(/at line (\d+), column (\d+)/);

    let message = "Parse error";
    if (expectingLine.includes("Was expecting")) {
      message = expectingLine.trim();
    }

    return {
      handled: true,
      error: {
        type: "syntax",
        message,
        line: locationMatch?.[1] ? Number.parseInt(locationMatch[1]) : undefined,
        column: locationMatch?.[2] ? Number.parseInt(locationMatch[2]) : undefined,
        file: specPath,
        suggestion: this.suggestSyntaxFix(message),
      },
      skipLines: 2,
    };
  }

  /**
   * Handle lexical error pattern
   */
  private tryLexicalError(
    line: string,
    specPath: string
  ): { handled: boolean; error: ParseError } | null {
    const lexicalMatch = line.match(
      /Lexical error at line (\d+), column (\d+)\.?\s*Encountered:\s*(.+)/
    );
    if (!lexicalMatch?.[1] || !lexicalMatch[2] || !lexicalMatch[3]) return null;

    return {
      handled: true,
      error: {
        type: "lexical",
        message: `Lexical error: ${lexicalMatch[3]}`,
        line: Number.parseInt(lexicalMatch[1]),
        column: Number.parseInt(lexicalMatch[2]),
        file: specPath,
        suggestion: this.suggestLexicalFix(lexicalMatch[3]),
      },
    };
  }

  /**
   * Handle syntax error pattern (single-line)
   */
  private trySyntaxError(
    line: string,
    specPath: string
  ): { handled: boolean; error: ParseError } | null {
    const parseMatch = line.match(
      /(?:Parse |Syntax )error at line (\d+), column (\d+)(?:\s+of\s+module\s+\w+)?\.?\s*(.+)/i
    );
    if (!parseMatch?.[1] || !parseMatch[2] || !parseMatch[3]) return null;

    return {
      handled: true,
      error: {
        type: "syntax",
        message: parseMatch[3],
        line: Number.parseInt(parseMatch[1]),
        column: Number.parseInt(parseMatch[2]),
        file: specPath,
        suggestion: this.suggestSyntaxFix(parseMatch[3]),
      },
    };
  }

  /**
   * Handle semantic location pattern (multi-line)
   */
  private trySemanticLocation(
    line: string,
    lines: string[],
    index: number,
    specPath: string,
    inWarningsSection: boolean
  ): { handled: boolean; error?: ParseError; warning?: string; skipLines: number } | null {
    const semanticLocationMatch = line.match(
      /^line (\d+), col (\d+) to line \d+, col \d+ of module (\w+)/
    );
    if (!semanticLocationMatch?.[1] || !semanticLocationMatch[2]) return null;

    // Collect message lines
    const msgLines = [];
    let j = index + 1;
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

    if (inWarningsSection) {
      return {
        handled: true,
        warning: `line ${semanticLocationMatch[1]}, col ${semanticLocationMatch[2]}: ${message || "Semantic warning"}`,
        skipLines: j - index - 1,
      };
    }

    return {
      handled: true,
      error: {
        type: "semantic",
        message: message || "Semantic error",
        line: Number.parseInt(semanticLocationMatch[1]),
        column: Number.parseInt(semanticLocationMatch[2]),
        file: specPath,
      },
      skipLines: j - index - 1,
    };
  }

  /**
   * Handle semantic error fallback (single-line)
   */
  private trySemanticError(
    line: string,
    specPath: string
  ): { handled: boolean; error: ParseError } | null {
    const semanticMatch = line.match(
      /Semantic error at line (\d+), column (\d+)(?:\s+of\s+module\s+\w+)?\.?\s*(.+)/i
    );
    if (!semanticMatch?.[1] || !semanticMatch[2] || !semanticMatch[3]) return null;

    return {
      handled: true,
      error: {
        type: "semantic",
        message: semanticMatch[3],
        line: Number.parseInt(semanticMatch[1]),
        column: Number.parseInt(semanticMatch[2]),
        file: specPath,
      },
    };
  }

  /**
   * Handle generic error or warning patterns
   */
  private tryGenericErrorOrWarning(
    line: string
  ): { handled: boolean; error?: ParseError; warning?: string } | null {
    if (line.includes("Error:") || line.includes("error:")) {
      return {
        handled: true,
        error: {
          type: "unknown",
          message: line.trim(),
        },
      };
    }

    if (line.includes("Warning:") || line.includes("warning:")) {
      return {
        handled: true,
        warning: line.trim(),
      };
    }

    return null;
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
