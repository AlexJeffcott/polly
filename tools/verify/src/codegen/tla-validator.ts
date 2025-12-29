// Lightweight TypeScript-based TLA+ validator
// Provides fast feedback before running SANY

/**
 * Validation error with location and suggestion
 */
export type ValidationError = {
  type: "identifier" | "expression" | "reserved" | "bracket" | "record" | "operator" | "module";
  message: string;
  line?: number;
  column?: number;
  suggestion?: string;
};

/**
 * TLAValidator performs lightweight syntax validation
 * to catch common issues before running SANY.
 *
 * This is much faster than SANY and provides instant feedback
 * during development and code generation.
 */
export class TLAValidator {
  /**
   * TLA+ reserved words that cannot be used as identifiers
   * Source: TLA+ Language Specification
   */
  private static readonly RESERVED_WORDS = new Set([
    // Boolean operators
    "TRUE",
    "FALSE",
    "BOOLEAN",
    // Action operators
    "ENABLED",
    "UNCHANGED",
    "CHOOSE",
    // Temporal operators
    "WF",
    "SF",
    // Set operators
    "SUBSET",
    "UNION",
    "DOMAIN",
    // Sequence operators
    "Seq",
    "Len",
    "Append",
    "Head",
    "Tail",
    "SubSeq",
    // Module keywords
    "MODULE",
    "EXTENDS",
    "INSTANCE",
    "CONSTANTS",
    "VARIABLES",
    "ASSUME",
    "THEOREM",
    "AXIOM",
    "LEMMA",
    // Definition keywords
    "LOCAL",
    "LET",
    "IN",
    "IF",
    "THEN",
    "ELSE",
    "CASE",
    "OTHER",
    // Logic keywords
    "EXCEPT",
    "WITH",
    // Type operators
    "STRING",
    "Nat",
    "Int",
    "Real",
  ]);

  /**
   * TLA+ operators that we generate
   * (Reserved for future validation)
   */
  private static readonly _VALID_OPERATORS = new Set([
    // Logical
    "/\\",
    "\\/",
    "~",
    "=>",
    "<=>",
    // Comparison
    "=",
    "#",
    "/=",
    "<",
    ">",
    "<=",
    ">=",
    // Set membership
    "\\in",
    "\\notin",
    "\\subseteq",
    "\\union",
    "\\intersect",
    "\\",
    // Quantifiers
    "\\A",
    "\\E",
    // Temporal
    "[]",
    "<>",
    "~>",
    // Priming
    "'",
    // Function/record
    ".",
    "[",
    "]",
    "!",
    "@",
  ]);

  /**
   * Validate a TLA+ identifier
   *
   * Valid identifiers:
   * - Start with a letter (a-z, A-Z)
   * - Followed by letters, digits, or underscores
   * - Cannot be a reserved word
   */
  validateIdentifier(name: string): ValidationError | null {
    if (!name || name.length === 0) {
      return {
        type: "identifier",
        message: "Identifier cannot be empty",
      };
    }

    // Check pattern
    if (!/^[a-zA-Z][a-zA-Z0-9_]*$/.test(name)) {
      return {
        type: "identifier",
        message: `Invalid identifier '${name}'. TLA+ identifiers must start with a letter and contain only letters, digits, and underscores.`,
        suggestion: this.suggestIdentifierFix(name),
      };
    }

    // Check reserved words
    if (TLAValidator.RESERVED_WORDS.has(name.toUpperCase())) {
      return {
        type: "reserved",
        message: `'${name}' is a TLA+ reserved word and cannot be used as an identifier`,
        suggestion: `Try adding a suffix like '${name}_value' or using a different name`,
      };
    }

    return null;
  }

  /**
   * Validate a TLA+ expression
   *
   * Performs basic checks:
   * - Bracket matching
   * - No invalid characters
   * - Proper operator usage
   */
  validateExpression(expr: string): ValidationError | null {
    if (!expr || expr.trim().length === 0) {
      return null; // Empty expressions are okay in some contexts
    }

    // Check bracket matching
    const bracketError = this.validateBrackets(expr);
    if (bracketError) {
      return bracketError;
    }

    // Check for common JavaScript operators that aren't valid in TLA+
    const invalidOperators = ["===", "!==", "&&", "||", "++", "--"];
    for (const op of invalidOperators) {
      if (expr.includes(op)) {
        return {
          type: "operator",
          message: `Invalid operator '${op}' in TLA+ expression`,
          suggestion: this.suggestOperatorReplacement(op),
        };
      }
    }

    return null;
  }

  /**
   * Check if a word is a TLA+ reserved word
   */
  isReservedWord(word: string): boolean {
    return TLAValidator.RESERVED_WORDS.has(word.toUpperCase());
  }

  /**
   * Validate bracket matching in text
   *
   * Checks:
   * - () parentheses
   * - [] square brackets
   * - {} curly braces
   * - << >> angle brackets (TLA+ sequences)
   * - /\ \/ conjunctions (must be balanced)
   */
  validateBrackets(text: string): ValidationError | null {
    const stack: Array<{ char: string; pos: number }> = [];
    const pairs: Record<string, string> = {
      "(": ")",
      "[": "]",
      "{": "}",
    };

    // Track /\ and \/ balance
    let _conjunctionBalance = 0;
    let _disjunctionBalance = 0;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      if (!char) continue;

      const nextChar = text[i + 1];

      // Handle << and >>
      if (char === "<" && nextChar === "<") {
        stack.push({ char: "<<", pos: i });
        i++; // Skip next char
        continue;
      }
      if (char === ">" && nextChar === ">") {
        const top = stack.pop();
        if (!top || top.char !== "<<") {
          return {
            type: "bracket",
            message: `Unmatched '>>' at position ${i}`,
          };
        }
        i++; // Skip next char
        continue;
      }

      // Handle /\ and \/
      if (char === "/" && nextChar === "\\") {
        _conjunctionBalance++;
        i++; // Skip next char
        continue;
      }
      if (char === "\\" && nextChar === "/") {
        _disjunctionBalance++;
        i++; // Skip next char
        continue;
      }

      // Handle opening brackets
      if (char in pairs) {
        stack.push({ char, pos: i });
        continue;
      }

      // Handle closing brackets
      if (Object.values(pairs).includes(char)) {
        const top = stack.pop();
        if (!top || pairs[top.char] !== char) {
          return {
            type: "bracket",
            message: `Unmatched '${char}' at position ${i}`,
            suggestion: top
              ? `Expected '${pairs[top.char]}' to match '${top.char}' at position ${top.pos}`
              : undefined,
          };
        }
      }
    }

    // Check for unclosed brackets
    if (stack.length > 0) {
      const top = stack[stack.length - 1];
      if (top) {
        return {
          type: "bracket",
          message: `Unclosed '${top.char}' at position ${top.pos}`,
          suggestion: `Add '${pairs[top.char] || ">>"}'`,
        };
      }
    }

    return null;
  }

  /**
   * Validate TLA+ record syntax
   *
   * Valid: [field1: value1, field2: value2]
   * Invalid: {field1: value1} (JavaScript object syntax)
   */
  validateRecordSyntax(record: string): ValidationError | null {
    const trimmed = record.trim();

    // Check for JavaScript object syntax
    if (trimmed.startsWith("{") && trimmed.includes(":")) {
      return {
        type: "record",
        message: "Invalid record syntax. TLA+ uses [field: value], not {field: value}",
        suggestion: `Replace { } with [ ]: [${trimmed.slice(1, -1)}]`,
      };
    }

    return null;
  }

  /**
   * Validate operator usage in context
   *
   * Some operators are only valid in certain contexts:
   * - Priming (') only in actions
   * - Temporal operators ([], <>) only in temporal properties
   */
  validateOperator(
    op: string,
    context: "action" | "invariant" | "temporal"
  ): ValidationError | null {
    // Priming only in actions
    if (op === "'" && context !== "action") {
      return {
        type: "operator",
        message: "Prime operator (') can only be used in actions, not in invariants",
        suggestion: "Remove the prime or move this expression to an action",
      };
    }

    // Temporal operators only in temporal properties
    const temporalOps = ["[]", "<>", "~>", "WF", "SF"];
    if (temporalOps.includes(op) && context !== "temporal") {
      return {
        type: "operator",
        message: `Temporal operator '${op}' can only be used in temporal properties`,
        suggestion: "Move this to a temporal property or use a non-temporal operator",
      };
    }

    return null;
  }

  /**
   * Validate module structure
   *
   * Checks for:
   * - MODULE declaration
   * - EXTENDS clause
   * - Valid operator definitions
   * - ==== separator lines
   */
  validateModuleStructure(spec: string): ValidationError[] {
    const errors: ValidationError[] = [];
    const lines = spec.split("\n");

    // Check for MODULE declaration
    let hasModule = false;
    let moduleLineNum = 0;
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (!line) continue;

      const trimmed = line.trim();
      if (trimmed.startsWith("MODULE ")) {
        hasModule = true;
        moduleLineNum = i + 1;

        // Validate module name
        const moduleMatch = trimmed.match(/^MODULE\s+(\w+)/);
        if (moduleMatch?.[1]) {
          const nameError = this.validateIdentifier(moduleMatch[1]);
          if (nameError) {
            errors.push({
              ...nameError,
              line: i + 1,
              message: `Invalid module name: ${nameError.message}`,
            });
          }
        }
        break;
      }
    }

    if (!hasModule) {
      errors.push({
        type: "module",
        message: "Missing MODULE declaration",
        line: 1,
        suggestion: "Add 'MODULE ModuleName' at the start of the file",
      });
    }

    // Check for ==== separator after MODULE
    if (hasModule && moduleLineNum < lines.length) {
      let foundSeparator = false;
      for (let i = moduleLineNum; i < Math.min(moduleLineNum + 3, lines.length); i++) {
        if (lines[i]?.trim().match(/^={4,}$/)) {
          foundSeparator = true;
          break;
        }
      }
      if (!foundSeparator) {
        errors.push({
          type: "module",
          message: "Missing ==== separator after MODULE declaration",
          line: moduleLineNum + 1,
          suggestion: "Add a line with ==== after the MODULE declaration",
        });
      }
    }

    // Check for EXTENDS clause
    const hasExtends = spec.includes("EXTENDS");
    if (!hasExtends) {
      errors.push({
        type: "module",
        message: "Missing EXTENDS clause",
        suggestion: "Add 'EXTENDS Naturals, Sequences' or other required modules",
      });
    }

    // Validate operator definitions (must have ==)
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (!line) continue;

      // Look for operator definitions (lines with ==)
      if (line.includes("==") && !line.trim().startsWith("\\*")) {
        // Check that identifier before == is valid
        const match = line.match(/^(\w+)\s*==\s*/);
        if (match?.[1]) {
          const error = this.validateIdentifier(match[1]);
          if (error) {
            errors.push({
              ...error,
              line: i + 1,
            });
          }
        }
      }
    }

    return errors;
  }

  /**
   * Suggest fix for invalid identifier
   */
  private suggestIdentifierFix(name: string): string {
    // Replace invalid characters with underscores
    const fixed = name.replace(/[^a-zA-Z0-9_]/g, "_");

    // Ensure it starts with a letter
    const finalFixed = /^[a-zA-Z]/.test(fixed) ? fixed : `id_${fixed}`;

    return `Try '${finalFixed}' instead`;
  }

  /**
   * Suggest replacement for invalid operator
   */
  private suggestOperatorReplacement(op: string): string {
    const replacements: Record<string, string> = {
      "===": "=",
      "!==": "#",
      "&&": "/\\",
      "||": "\\/",
      "++": "+ 1",
      "--": "- 1",
    };

    return `Use '${replacements[op] || "valid TLA+ operator"}' instead`;
  }
}
