// Invariant extraction from JSDoc comments
// Extract domain-specific invariants from code annotations

import { Node, Project, type SourceFile } from "ts-morph";
import type { CodebaseAnalysis } from "../../../analysis/src/extract/types";

/**
 * Extracted invariant from JSDoc annotation
 */
export type Invariant = {
  /** Name for the invariant (auto-generated if not provided) */
  name: string;
  /** Description from JSDoc comment */
  description: string;
  /** JavaScript expression that should always be true */
  expression: string;
  /** Source location */
  location: {
    file: string;
    line: number;
  };
};

/**
 * Result of invariant extraction
 */
export type InvariantExtractionResult = {
  invariants: Invariant[];
  warnings: string[];
};

/**
 * InvariantExtractor extracts application-specific invariants from:
 * - @invariant JSDoc tags
 * - @ensures JSDoc tags (treated as post-condition invariants)
 * - @requires JSDoc tags (treated as pre-condition invariants)
 *
 * These are translated to TLA+ invariants that TLC can check.
 */
export class InvariantExtractor {
  private warnings: string[] = [];

  /**
   * Extract invariants from TypeScript project
   */
  extractInvariants(projectPath: string): InvariantExtractionResult {
    const project = new Project({
      tsConfigFilePath: `${projectPath}/tsconfig.json`,
      skipAddingFilesFromTsConfig: false,
    });

    const invariants: Invariant[] = [];

    for (const sourceFile of project.getSourceFiles()) {
      // Skip node_modules and test files
      if (
        sourceFile.getFilePath().includes("node_modules") ||
        sourceFile.getFilePath().includes(".test.") ||
        sourceFile.getFilePath().includes(".spec.")
      ) {
        continue;
      }

      invariants.push(...this.extractFromSourceFile(sourceFile));
    }

    return {
      invariants,
      warnings: this.warnings,
    };
  }

  /**
   * Extract invariants from codebase analysis result
   * (Alternative entry point when analysis is already done)
   */
  extractFromAnalysis(_analysis: CodebaseAnalysis): InvariantExtractionResult {
    // For now, return empty - could be enhanced to extract from handlers
    return {
      invariants: [],
      warnings: [],
    };
  }

  /**
   * Extract invariants from a single source file
   */
  private extractFromSourceFile(sourceFile: SourceFile): Invariant[] {
    const invariants: Invariant[] = [];

    // Traverse all nodes looking for JSDoc comments
    sourceFile.forEachDescendant((node) => {
      const jsDocs = this.getJsDocComments(node);

      for (const jsDoc of jsDocs) {
        // Extract @invariant tags
        for (const tag of jsDoc.getTags()) {
          if (tag.getTagName() === "invariant") {
            const text = tag.getComment();
            if (typeof text === "string" && text.trim()) {
              invariants.push(this.createInvariant(text.trim(), "invariant", sourceFile, node));
            }
          }

          if (tag.getTagName() === "ensures") {
            const text = tag.getComment();
            if (typeof text === "string" && text.trim()) {
              invariants.push(
                this.createInvariant(text.trim(), "post-condition", sourceFile, node)
              );
            }
          }

          if (tag.getTagName() === "requires") {
            const text = tag.getComment();
            if (typeof text === "string" && text.trim()) {
              invariants.push(this.createInvariant(text.trim(), "pre-condition", sourceFile, node));
            }
          }
        }
      }
    });

    return invariants;
  }

  /**
   * Get JSDoc comments for a node
   */
  private getJsDocComments(node: Node): any[] {
    if (Node.isJSDocable(node)) {
      return node.getJsDocs();
    }
    return [];
  }

  /**
   * Create invariant from JSDoc annotation
   */
  private createInvariant(
    expression: string,
    type: "invariant" | "pre-condition" | "post-condition",
    sourceFile: SourceFile,
    node: Node
  ): Invariant {
    // Extract description from preceding comment text
    const description = this.extractDescription(node, expression);

    // Generate name from expression
    const name = this.generateInvariantName(expression, type);

    return {
      name,
      description,
      expression,
      location: {
        file: sourceFile.getFilePath(),
        line: node.getStartLineNumber(),
      },
    };
  }

  /**
   * Extract human-readable description from JSDoc
   */
  private extractDescription(node: Node, expression: string): string {
    if (Node.isJSDocable(node)) {
      const jsDocs = node.getJsDocs();
      for (const jsDoc of jsDocs) {
        const desc = jsDoc.getDescription();
        if (desc?.trim()) {
          return desc.trim();
        }
      }
    }

    // Fallback: use expression as description
    return `Invariant: ${expression}`;
  }

  /**
   * Generate invariant name from expression
   *
   * Examples:
   * - "state.count >= 0" -> "CountNonNegative"
   * - "state.items.length <= 100" -> "ItemsMaxLength"
   */
  private generateInvariantName(
    expression: string,
    type: "invariant" | "pre-condition" | "post-condition"
  ): string {
    // Extract field names from expression
    const fieldMatches = expression.match(/state\.(\w+)/g);
    if (!fieldMatches || fieldMatches.length === 0) {
      // No state references, use generic name
      const prefix = type === "pre-condition" ? "Pre" : type === "post-condition" ? "Post" : "";
      return `${prefix}Invariant${Math.random().toString(36).substring(2, 7)}`;
    }

    // Use first field name as base
    const fieldName = fieldMatches[0]?.replace("state.", "");

    // Determine constraint type
    let constraintSuffix = "";
    if (expression.includes("<=")) {
      constraintSuffix = "MaxValue";
    } else if (expression.includes(">=")) {
      constraintSuffix = "MinValue";
    } else if (expression.includes("===") || expression.includes("==")) {
      constraintSuffix = "Equals";
    } else if (expression.includes("!==") || expression.includes("!=")) {
      constraintSuffix = "NotEquals";
    } else if (expression.includes("<")) {
      constraintSuffix = "LessThan";
    } else if (expression.includes(">")) {
      constraintSuffix = "GreaterThan";
    } else {
      constraintSuffix = "Check";
    }

    // Capitalize field name
    const capitalizedField = fieldName.charAt(0).toUpperCase() + fieldName.slice(1);

    const prefix = type === "pre-condition" ? "Pre" : type === "post-condition" ? "Post" : "";

    return `${prefix}${capitalizedField}${constraintSuffix}`;
  }

  /**
   * Validate that expression is safe to translate to TLA+
   */
  validateExpression(expression: string): { valid: boolean; error?: string } {
    // Check for dangerous patterns
    if (expression.includes("eval(")) {
      return { valid: false, error: "eval() not allowed in invariants" };
    }

    // Check for basic syntax issues
    const openParens = (expression.match(/\(/g) || []).length;
    const closeParens = (expression.match(/\)/g) || []).length;
    if (openParens !== closeParens) {
      return { valid: false, error: "Unbalanced parentheses" };
    }

    const openBrackets = (expression.match(/\[/g) || []).length;
    const closeBrackets = (expression.match(/\]/g) || []).length;
    if (openBrackets !== closeBrackets) {
      return { valid: false, error: "Unbalanced brackets" };
    }

    return { valid: true };
  }
}

/**
 * InvariantGenerator converts extracted invariants to TLA+ format
 */
export class InvariantGenerator {
  /**
   * Generate TLA+ invariant definitions from extracted invariants
   */
  generateTLAInvariants(
    invariants: Invariant[],
    tsExpressionToTLA: (expr: string) => string
  ): string[] {
    const tlaInvariants: string[] = [];

    for (const invariant of invariants) {
      tlaInvariants.push(this.generateSingleInvariant(invariant, tsExpressionToTLA));
    }

    return tlaInvariants;
  }

  /**
   * Generate single TLA+ invariant
   */
  private generateSingleInvariant(
    invariant: Invariant,
    tsExpressionToTLA: (expr: string) => string
  ): string {
    const lines: string[] = [];

    // Add description as comment
    if (invariant.description) {
      lines.push(`\\* ${invariant.description}`);
    }

    // Translate expression to TLA+
    const tlaExpr = tsExpressionToTLA(invariant.expression);

    // Wrap in universal quantifier over all contexts
    lines.push(`${invariant.name} ==`);
    lines.push(`  \\A ctx \\in Contexts : ${tlaExpr}`);

    return lines.join("\n");
  }

  /**
   * Generate INVARIANT declarations for TLA+ config file
   */
  generateConfigInvariants(invariants: Invariant[]): string[] {
    return invariants.map((inv) => `INVARIANT ${inv.name}`);
  }
}
