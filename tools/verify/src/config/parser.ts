// Configuration validator - detects incomplete configuration

import * as fs from "node:fs";
import * as path from "node:path";
import type { ConfigIssue, ValidationResult, VerificationConfig } from "../types";

export class ConfigValidator {
  private issues: ConfigIssue[] = [];

  validate(configPath: string): ValidationResult {
    this.issues = [];

    if (!fs.existsSync(configPath)) {
      this.issues.push({
        type: "incomplete",
        severity: "error",
        message: "Configuration file does not exist",
        suggestion: "Run 'bun verify --setup' to generate configuration",
      });

      return {
        valid: false,
        issues: this.issues,
      };
    }

    // Read the source file
    const configSource = fs.readFileSync(configPath, "utf-8");

    // Check for CONFIGURE markers
    this.checkConfigureMarkers(configSource);

    // Check for REVIEW markers (warnings only)
    this.checkReviewMarkers(configSource);

    // Load and validate the actual config
    try {
      const config = this.loadConfig(configPath);
      this.validateConfig(config);
    } catch (error) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        message: `Failed to load configuration: ${error instanceof Error ? error.message : String(error)}`,
        suggestion: "Check for syntax errors in the configuration file",
      });
    }

    const hasErrors = this.issues.some((i) => i.severity === "error");

    return {
      valid: !hasErrors,
      issues: this.issues,
    };
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Config validation requires complex pattern matching
  private checkConfigureMarkers(source: string): void {
    const configureRegex = /\/\*\s*CONFIGURE\s*\*\//g;
    const matches = [...source.matchAll(configureRegex)];

    if (matches.length > 0) {
      // Find line numbers for each match
      const lines = source.split("\n");
      const locations: Array<{ line: number; column: number; context: string }> = [];

      for (const match of matches) {
        const position = match.index ?? 0;
        const lineNumber = source.substring(0, position).split("\n").length;
        const line = lines[lineNumber - 1];

        // Skip if this is in a single-line comment
        if (line?.trim().startsWith("//")) {
          continue;
        }

        // Extract field name from context
        const fieldMatch = line?.match(/"([^"]+)":\s*{/);
        const fieldName = fieldMatch ? fieldMatch[1] : "unknown";

        locations.push({
          line: lineNumber,
          column: (match.index ?? 0) - source.lastIndexOf("\n", position),
          context: fieldName ?? "unknown",
        });
      }

      // Only add issues if there are actual incomplete markers (not in comments)
      if (locations.length > 0) {
        this.issues.push({
          type: "incomplete",
          severity: "error",
          message: `Found ${locations.length} incomplete configuration marker(s)`,
          suggestion: "Replace all /* CONFIGURE */ markers with actual values",
        });

        // Add individual issues for each marker
        for (const loc of locations) {
          this.issues.push({
            type: "incomplete",
            severity: "error",
            field: loc.context,
            location: { line: loc.line, column: loc.column },
            message: `Incomplete configuration at line ${loc.line}`,
            suggestion: `Fill in value for "${loc.context}"`,
          });
        }
      }
    }
  }

  private checkReviewMarkers(source: string): void {
    const reviewRegex = /\/\*\s*REVIEW\s*\*\//g;
    const matches = [...source.matchAll(reviewRegex)];

    if (matches.length > 0) {
      // Filter out matches in single-line comments
      const lines = source.split("\n");
      const validMatches = [...matches].filter((match) => {
        const position = match.index ?? 0;
        const lineNumber = source.substring(0, position).split("\n").length;
        const line = lines[lineNumber - 1];
        return !line?.trim().startsWith("//");
      });

      if (validMatches.length > 0) {
        this.issues.push({
          type: "incomplete",
          severity: "warning",
          message: `Found ${validMatches.length} value(s) that should be reviewed`,
          suggestion: "Review auto-generated values marked with /* REVIEW */",
        });
      }
    }
  }

  private loadConfig(configPath: string): VerificationConfig {
    // Dynamic import of the config file
    // Note: In production, this would use proper module loading
    delete require.cache[require.resolve(path.resolve(configPath))];
    const module = require(path.resolve(configPath));
    return module.verificationConfig || module.default || module;
  }

  private validateConfig(config: VerificationConfig): void {
    // Check for null values
    this.findNullPlaceholders(config.state, "state");
    this.findNullPlaceholders(config.messages, "messages");

    // Validate bounds
    this.validateBounds(config);

    // Validate Tier 1 optimizations
    this.validateTier1Optimizations(config.messages);

    // Validate verification options
    if (config.verification) {
      this.validateVerificationOptions(config.verification);
    }

    // Validate Tier 2 optimizations
    if (config.tier2) {
      this.validateTier2Optimizations(config.tier2);
    }

    // Validate subsystems
    if (config.subsystems) {
      this.validateSubsystems(config.subsystems, config.state);
    }
  }

  private findNullPlaceholders(obj: unknown, path: string): void {
    if (obj === null || obj === undefined) {
      this.issues.push({
        type: "null_placeholder",
        severity: "error",
        field: path,
        message: `Configuration incomplete: ${path}`,
        suggestion: "Replace null with a concrete value",
      });
      return;
    }

    if (typeof obj !== "object") {
      return;
    }

    for (const [key, value] of Object.entries(obj)) {
      const fullPath = `${path}.${key}`;

      if (value === null) {
        this.issues.push({
          type: "null_placeholder",
          severity: "error",
          field: fullPath,
          message: `Configuration incomplete: ${fullPath}`,
          suggestion: "Replace null with a concrete value",
        });
      } else if (typeof value === "object" && value !== null && !Array.isArray(value)) {
        this.findNullPlaceholders(value, fullPath);
      }
    }
  }

  private validateBounds(config: VerificationConfig): void {
    // Check messages config
    this.validateMessageBounds(config.messages);

    // Check state field bounds
    for (const [fieldName, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) {
        continue;
      }

      this.validateFieldBounds(fieldName, fieldConfig);
    }
  }

  private validateMessageBounds(messages: {
    maxInFlight: number | null;
    maxTabs?: number | null;
  }): void {
    if (messages.maxInFlight !== null) {
      if (messages.maxInFlight < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "messages.maxInFlight",
          message: "maxInFlight must be at least 1",
          suggestion: "Use a value between 4-10 for most cases",
        });
      }

      if (messages.maxInFlight > 20) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "messages.maxInFlight",
          message: "Very high maxInFlight (>20) will slow verification significantly",
          suggestion: "Use 4-10 for development, up to 20 for thorough verification",
        });
      }
    }

    if (messages.maxTabs !== null && messages.maxTabs !== undefined) {
      if (messages.maxTabs < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "messages.maxTabs",
          message: "maxTabs must be at least 1",
          suggestion: "Use 2-3 for most cases",
        });
      }

      if (messages.maxTabs > 10) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "messages.maxTabs",
          message: "Very high maxTabs (>10) will slow verification significantly",
          suggestion: "Use 2-3 for most cases",
        });
      }
    }
  }

  private validateFieldBounds(fieldName: string, fieldConfig: Record<string, unknown>): void {
    // Array bounds
    if ("maxLength" in fieldConfig) {
      this.validateArrayBounds(fieldName, fieldConfig);
    }

    // Number bounds
    if ("min" in fieldConfig && "max" in fieldConfig) {
      this.validateNumberBounds(fieldName, fieldConfig);
    }

    // Map/Set bounds
    if ("maxSize" in fieldConfig) {
      this.validateMapSetBounds(fieldName, fieldConfig);
    }
  }

  private validateArrayBounds(fieldName: string, fieldConfig: Record<string, unknown>): void {
    const maxLength = (fieldConfig as { maxLength?: number | null }).maxLength;
    if (maxLength === null) return;

    if (maxLength < 0) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: `state.${fieldName}.maxLength`,
        message: "maxLength cannot be negative",
        suggestion: "Use a positive number",
      });
    }

    if (maxLength > 50) {
      this.issues.push({
        type: "unrealistic_bound",
        severity: "warning",
        field: `state.${fieldName}.maxLength`,
        message: `Very large maxLength (${maxLength}) will slow verification`,
        suggestion: "Use 10-20 for most cases",
      });
    }
  }

  private validateNumberBounds(fieldName: string, fieldConfig: Record<string, unknown>): void {
    const min = (fieldConfig as { min?: number | null }).min;
    const max = (fieldConfig as { max?: number | null }).max;

    if (min !== null && max !== null && min > max) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: `state.${fieldName}`,
        message: `Invalid range: min (${min}) > max (${max})`,
        suggestion: "Ensure min is less than or equal to max",
      });
    }

    if (min !== null && max !== null && max - min > 1000) {
      this.issues.push({
        type: "unrealistic_bound",
        severity: "warning",
        field: `state.${fieldName}`,
        message: `Very large number range (${max - min}) will slow verification`,
        suggestion: "Use smaller ranges when possible",
      });
    }
  }

  private validateMapSetBounds(fieldName: string, fieldConfig: Record<string, unknown>): void {
    const maxSize = (fieldConfig as { maxSize?: number | null }).maxSize;
    if (maxSize === null) return;

    if (maxSize < 0) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: `state.${fieldName}.maxSize`,
        message: "maxSize cannot be negative",
        suggestion: "Use a positive number",
      });
    }

    if (maxSize > 20) {
      this.issues.push({
        type: "unrealistic_bound",
        severity: "warning",
        field: `state.${fieldName}.maxSize`,
        message: `Very large maxSize (${maxSize}) will slow verification`,
        suggestion: "Use 3-5 for most cases",
      });
    }
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Validation requires checking multiple conditions
  private validateTier1Optimizations(messages: VerificationConfig["messages"]): void {
    // Validate include/exclude are mutually exclusive
    if (messages.include && messages.exclude) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: "messages",
        message: "Cannot use both 'include' and 'exclude' filters",
        suggestion: "Use either 'include' OR 'exclude', not both",
      });
    }

    // Validate symmetry groups have at least 2 members
    if (messages.symmetry) {
      for (let i = 0; i < messages.symmetry.length; i++) {
        const group = messages.symmetry[i];
        if (group.length < 2) {
          this.issues.push({
            type: "invalid_value",
            severity: "warning",
            field: `messages.symmetry[${i}]`,
            message: "Symmetry group must have at least 2 message types",
            suggestion: "Remove single-element symmetry groups",
          });
        }
      }
    }

    // Validate perMessageBounds values are realistic
    if (messages.perMessageBounds) {
      for (const [msgType, bound] of Object.entries(messages.perMessageBounds)) {
        if (bound < 1) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: `messages.perMessageBounds.${msgType}`,
            message: `Per-message bound must be at least 1`,
            suggestion: "Use a positive number",
          });
        }
        if (bound > 20) {
          this.issues.push({
            type: "unrealistic_bound",
            severity: "warning",
            field: `messages.perMessageBounds.${msgType}`,
            message: `Per-message bound ${bound} is outside recommended range (1-20)`,
            suggestion: "Consider adjusting bound to a more realistic value",
          });
        }
      }
    }

    // Validate tabSymmetry
    if (messages.tabSymmetry !== undefined) {
      if (typeof messages.tabSymmetry !== "boolean") {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "messages.tabSymmetry",
          message: "tabSymmetry must be a boolean",
          suggestion: "Use true or false",
        });
      }

      if (messages.tabSymmetry && (messages.maxTabs === undefined || messages.maxTabs === null)) {
        this.issues.push({
          type: "invalid_value",
          severity: "warning",
          field: "messages.tabSymmetry",
          message: "tabSymmetry enabled but maxTabs not set",
          suggestion: "Set maxTabs to define the number of tabs for symmetry reduction",
        });
      }
    }
  }

  private validateVerificationOptions(
    verification: NonNullable<VerificationConfig["verification"]>
  ): void {
    if (verification.timeout !== undefined) {
      if (verification.timeout < 0) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "verification.timeout",
          message: "Timeout cannot be negative",
          suggestion: "Use 0 for no timeout, or positive number for timeout in seconds",
        });
      }
      if (verification.timeout > 3600) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "verification.timeout",
          message: "Timeout over 1 hour (3600s) is very long",
          suggestion: "Consider reducing timeout or using 0 for no limit",
        });
      }
    }

    if (verification.workers !== undefined) {
      if (verification.workers < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "verification.workers",
          message: "Workers must be at least 1",
          suggestion: "Use 1 or more workers",
        });
      }
      if (verification.workers > 16) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "verification.workers",
          message: "More than 16 workers may not improve performance",
          suggestion: "Typical range is 1-8 workers",
        });
      }
    }
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Validation requires checking multiple conditions
  private validateTier2Optimizations(tier2: NonNullable<VerificationConfig["tier2"]>): void {
    // Validate temporal constraints
    if (tier2.temporalConstraints) {
      for (let i = 0; i < tier2.temporalConstraints.length; i++) {
        const constraint = tier2.temporalConstraints[i];
        if (!constraint.before || !constraint.after) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: `tier2.temporalConstraints[${i}]`,
            message: "Temporal constraint must have 'before' and 'after' fields",
            suggestion: "Specify both message types for ordering constraint",
          });
        }
        if (constraint.before === constraint.after) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: `tier2.temporalConstraints[${i}]`,
            message: "Temporal constraint cannot have same message type for 'before' and 'after'",
            suggestion: "Use different message types",
          });
        }
      }
    }

    // Validate bounded exploration
    if (tier2.boundedExploration) {
      if (tier2.boundedExploration.maxDepth !== undefined) {
        if (tier2.boundedExploration.maxDepth < 1) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: "tier2.boundedExploration.maxDepth",
            message: "maxDepth must be at least 1",
            suggestion: "Use positive integer for depth limit",
          });
        }
        if (tier2.boundedExploration.maxDepth > 100) {
          this.issues.push({
            type: "unrealistic_bound",
            severity: "warning",
            field: "tier2.boundedExploration.maxDepth",
            message: "maxDepth > 100 may not be useful",
            suggestion: "Typical range is 10-50",
          });
        }
      }
    }
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Subsystem validation requires checking multiple cross-references
  private validateSubsystems(
    subsystems: Record<string, { state: string[]; handlers: string[] }>,
    stateConfig: Record<string, unknown>
  ): void {
    const stateFieldNames = Object.keys(stateConfig);
    const allAssignedHandlers = new Map<string, string>(); // handler → subsystem name
    const allAssignedFields = new Map<string, string>(); // field → subsystem name

    for (const [subsystemName, subsystem] of Object.entries(subsystems)) {
      // Validate state field references
      for (const field of subsystem.state) {
        if (!stateFieldNames.includes(field)) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: `subsystems.${subsystemName}.state`,
            message: `State field "${field}" does not exist in top-level state config`,
            suggestion: `Available fields: ${stateFieldNames.join(", ")}`,
          });
        }

        // Check for duplicate field assignments across subsystems
        const existingOwner = allAssignedFields.get(field);
        if (existingOwner) {
          this.issues.push({
            type: "invalid_value",
            severity: "warning",
            field: `subsystems.${subsystemName}.state`,
            message: `State field "${field}" is assigned to both "${existingOwner}" and "${subsystemName}"`,
            suggestion: "State fields should be partitioned across subsystems for non-interference",
          });
        } else {
          allAssignedFields.set(field, subsystemName);
        }
      }

      // Validate handler references (no empty arrays)
      if (subsystem.handlers.length === 0) {
        this.issues.push({
          type: "invalid_value",
          severity: "warning",
          field: `subsystems.${subsystemName}.handlers`,
          message: `Subsystem "${subsystemName}" has no handlers`,
          suggestion: "Add at least one handler to the subsystem",
        });
      }

      // Check for duplicate handler assignments across subsystems
      for (const handler of subsystem.handlers) {
        const existingOwner = allAssignedHandlers.get(handler);
        if (existingOwner) {
          this.issues.push({
            type: "invalid_value",
            severity: "error",
            field: `subsystems.${subsystemName}.handlers`,
            message: `Handler "${handler}" is assigned to both "${existingOwner}" and "${subsystemName}"`,
            suggestion: "Each handler must belong to exactly one subsystem",
          });
        } else {
          allAssignedHandlers.set(handler, subsystemName);
        }
      }

      // Validate state array is non-empty
      if (subsystem.state.length === 0) {
        this.issues.push({
          type: "invalid_value",
          severity: "warning",
          field: `subsystems.${subsystemName}.state`,
          message: `Subsystem "${subsystemName}" has no state fields`,
          suggestion: "Add at least one state field to the subsystem",
        });
      }
    }
  }
}

export function validateConfig(configPath: string): ValidationResult {
  const validator = new ConfigValidator();
  return validator.validate(configPath);
}
