// Round-trip validation - ensures generated TLA+ preserves all information
// from the original configuration and analysis

import type { CodebaseAnalysis, VerificationConfig } from "../types";

/**
 * Comparison error found during round-trip validation
 */
export type ComparisonError = {
  type: "missing" | "extra" | "mismatch";
  component: "message-type" | "state-field" | "handler" | "invariant" | "init" | "next";
  message: string;
  expected?: string;
  actual?: string;
};

/**
 * Result of round-trip validation
 */
export type RoundTripResult = {
  valid: boolean;
  errors: ComparisonError[];
  extracted: {
    messageTypes: string[];
    stateFields: string[];
    handlers: string[];
    hasInit: boolean;
    hasNext: boolean;
  };
};

/**
 * RoundTripValidator ensures that generated TLA+ specifications
 * preserve all information from the original analysis.
 *
 * This prevents silent data loss during code generation.
 *
 * Validation pipeline:
 * 1. Parse generated TLA+
 * 2. Extract components (message types, state fields, handlers)
 * 3. Compare with original analysis
 * 4. Report any discrepancies
 */
export class RoundTripValidator {
  /**
   * Validate that generated TLA+ preserves all information
   */
  async validate(
    config: VerificationConfig,
    analysis: CodebaseAnalysis,
    generatedSpec: string
  ): Promise<RoundTripResult> {
    const errors: ComparisonError[] = [];

    // Extract components from generated spec
    const extracted = {
      messageTypes: this.extractMessageTypes(generatedSpec),
      stateFields: this.extractStateFields(generatedSpec),
      handlers: this.extractHandlers(generatedSpec),
      hasInit: this.hasInitialState(generatedSpec),
      hasNext: this.hasNextState(generatedSpec),
    };

    // Validate message types
    this.validateMessageTypes(analysis.messageTypes, extracted.messageTypes, errors);

    // Validate state fields
    const configFields = Object.keys(config.state);
    this.validateStateFields(configFields, extracted.stateFields, errors);

    // Validate handlers
    this.validateHandlers(analysis.handlers, extracted.handlers, errors);

    // Validate init/next structure
    if (!extracted.hasInit) {
      errors.push({
        type: "missing",
        component: "init",
        message: "Generated spec is missing InitialState operator",
      });
    }

    if (!extracted.hasNext) {
      errors.push({
        type: "missing",
        component: "next",
        message: "Generated spec is missing StateTransition/Next operator",
      });
    }

    return {
      valid: errors.length === 0,
      errors,
      extracted,
    };
  }

  /**
   * Extract message types from UserMessageTypes set
   *
   * Pattern: UserMessageTypes == {"type1", "type2", ...}
   */
  private extractMessageTypes(spec: string): string[] {
    const match = spec.match(/UserMessageTypes\s*==\s*\{([^}]+)\}/);
    if (!match || !match[1]) {
      return [];
    }

    const content = match[1];
    // Extract quoted strings
    const typeMatches = content.match(/"([^"]+)"/g);
    if (!typeMatches) {
      return [];
    }

    return typeMatches.map((t) => t.slice(1, -1)); // Remove quotes
  }

  /**
   * Extract state fields from State record
   *
   * Pattern: State == [field1: Type1, field2: Type2, ...]
   * Or: [contextStates: [ctx |-> [field1: ..., field2: ...]]]
   */
  private extractStateFields(spec: string): string[] {
    const fields: string[] = [];

    // Look for state field definitions
    // Pattern 1: Direct field definitions in State record
    const stateRecordMatch = spec.match(/State\s*==\s*\[([^\]]+)\]/s);
    if (stateRecordMatch?.[1]) {
      const content = stateRecordMatch[1];
      // Extract field names (before colons)
      const fieldMatches = content.matchAll(/(\w+)\s*:/g);
      for (const match of fieldMatches) {
        if (match[1] && match[1] !== "ctx") {
          fields.push(match[1]);
        }
      }
    }

    // Pattern 2: contextStates with embedded record
    const contextStatesMatch = spec.match(/contextStates\s*:\s*\[\s*ctx\s*\|->\s*\[([^\]]+)\]/s);
    if (contextStatesMatch?.[1]) {
      const content = contextStatesMatch[1];
      const fieldMatches = content.matchAll(/(\w+)\s*:/g);
      for (const match of fieldMatches) {
        if (match[1]) {
          fields.push(match[1]);
        }
      }
    }

    return [...new Set(fields)]; // Remove duplicates
  }

  /**
   * Extract handler operators from spec
   *
   * Pattern: Handle<MessageType>(ctx) ==
   */
  private extractHandlers(spec: string): string[] {
    const handlers: string[] = [];
    const lines = spec.split("\n");

    for (const line of lines) {
      const match = line.match(/^Handle(\w+)\s*\(\s*ctx\s*\)\s*==/);
      if (match?.[1]) {
        handlers.push(match[1]);
      }
    }

    return handlers;
  }

  /**
   * Check if spec has InitialState operator
   */
  private hasInitialState(spec: string): boolean {
    return /InitialState\s*==/.test(spec) || /Init\s*==/.test(spec);
  }

  /**
   * Check if spec has StateTransition/Next operator
   */
  private hasNextState(spec: string): boolean {
    return /StateTransition\s*==/.test(spec) || /Next\s*==/.test(spec);
  }

  /**
   * Validate message types are preserved
   */
  private validateMessageTypes(
    expected: string[],
    actual: string[],
    errors: ComparisonError[]
  ): void {
    const expectedSet = new Set(expected);
    const actualSet = new Set(actual);

    // Check for missing types
    for (const type of expected) {
      if (!actualSet.has(type)) {
        errors.push({
          type: "missing",
          component: "message-type",
          message: `Message type '${type}' from analysis is missing in generated spec`,
          expected: type,
        });
      }
    }

    // Check for extra types (suspicious but not necessarily wrong)
    for (const type of actual) {
      if (!expectedSet.has(type)) {
        errors.push({
          type: "extra",
          component: "message-type",
          message: `Message type '${type}' appears in spec but not in analysis`,
          actual: type,
        });
      }
    }
  }

  /**
   * Validate state fields are preserved
   */
  private validateStateFields(
    expected: string[],
    actual: string[],
    errors: ComparisonError[]
  ): void {
    const actualSet = new Set(actual);

    // Check for missing fields
    for (const field of expected) {
      if (!actualSet.has(field)) {
        errors.push({
          type: "missing",
          component: "state-field",
          message: `State field '${field}' from config is missing in generated spec`,
          expected: field,
        });
      }
    }

    // Extra fields are okay (e.g., metadata fields)
  }

  /**
   * Validate handlers are present
   */
  private validateHandlers(
    expectedHandlers: Array<{ messageType: string }>,
    actualHandlers: string[],
    errors: ComparisonError[]
  ): void {
    // Convert expected handlers to message types
    const expectedTypes = expectedHandlers.map((h) => h.messageType);
    const actualSet = new Set(actualHandlers);

    // Each handler should have a corresponding Handle*() operator
    // The handler name is PascalCase version of messageType
    for (const messageType of expectedTypes) {
      const handlerName = this.messageTypeToPascalCase(messageType);

      if (!actualSet.has(handlerName)) {
        errors.push({
          type: "missing",
          component: "handler",
          message: `Handler for message type '${messageType}' is missing (expected Handle${handlerName})`,
          expected: `Handle${handlerName}`,
        });
      }
    }
  }

  /**
   * Convert message type to PascalCase for handler name
   *
   * Examples:
   * - "query" -> "Query"
   * - "user_login" -> "UserLogin"
   * - "API_REQUEST" -> "ApiRequest"
   */
  private messageTypeToPascalCase(messageType: string): string {
    return messageType
      .split(/[_-]/)
      .map((word) => {
        if (word.length === 0) return "";
        // Handle all-caps words
        if (word === word.toUpperCase()) {
          return word.charAt(0).toUpperCase() + word.slice(1).toLowerCase();
        }
        return word.charAt(0).toUpperCase() + word.slice(1);
      })
      .join("");
  }
}
