// Configuration validator - detects incomplete configuration

import type { ValidationResult, ConfigIssue, VerificationConfig } from "../types";
import * as fs from "node:fs";
import * as path from "node:path";

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

  private checkConfigureMarkers(source: string): void {
    const configureRegex = /\/\*\s*CONFIGURE\s*\*\//g;
    const matches = [...source.matchAll(configureRegex)];

    if (matches.length > 0) {
      // Find line numbers for each match
      const lines = source.split("\n");
      const locations: Array<{ line: number; column: number; context: string }> = [];

      for (const match of matches) {
        const position = match.index!;
        const lineNumber = source.substring(0, position).split("\n").length;
        const line = lines[lineNumber - 1];

        // Extract field name from context
        const fieldMatch = line?.match(/"([^"]+)":\s*{/);
        const fieldName = fieldMatch ? fieldMatch[1] : "unknown";

        locations.push({
          line: lineNumber,
          column: match.index! - source.lastIndexOf("\n", position),
          context: fieldName ?? "unknown",
        });
      }

      this.issues.push({
        type: "incomplete",
        severity: "error",
        message: `Found ${matches.length} incomplete configuration marker(s)`,
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

  private checkReviewMarkers(source: string): void {
    const reviewRegex = /\/\*\s*REVIEW\s*\*\//g;
    const matches = [...source.matchAll(reviewRegex)];

    if (matches.length > 0) {
      this.issues.push({
        type: "incomplete",
        severity: "warning",
        message: `Found ${matches.length} value(s) that should be reviewed`,
        suggestion: "Review auto-generated values marked with /* REVIEW */",
      });
    }
  }

  private loadConfig(configPath: string): VerificationConfig {
    // Dynamic import of the config file
    // Note: In production, this would use proper module loading
    delete require.cache[require.resolve(path.resolve(configPath))];
    const module = require(path.resolve(configPath));
    return module.default || module;
  }

  private validateConfig(config: VerificationConfig): void {
    // Check for null values
    this.findNullPlaceholders(config.state, "state");
    this.findNullPlaceholders(config.messages, "messages");

    // Validate bounds
    this.validateBounds(config);
  }

  private findNullPlaceholders(obj: any, path: string): void {
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
    if (config.messages.maxInFlight !== null) {
      if (config.messages.maxInFlight < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "messages.maxInFlight",
          message: "maxInFlight must be at least 1",
          suggestion: "Use a value between 4-10 for most cases",
        });
      }

      if (config.messages.maxInFlight > 20) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "messages.maxInFlight",
          message: "Very high maxInFlight (>20) will slow verification significantly",
          suggestion: "Use 4-10 for development, up to 20 for thorough verification",
        });
      }
    }

    if (config.messages.maxTabs !== null && config.messages.maxTabs !== undefined) {
      if (config.messages.maxTabs < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "messages.maxTabs",
          message: "maxTabs must be at least 1",
          suggestion: "Use 2-3 for most cases",
        });
      }

      if (config.messages.maxTabs > 10) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "messages.maxTabs",
          message: "Very high maxTabs (>10) will slow verification significantly",
          suggestion: "Use 2-3 for most cases",
        });
      }
    }

    // Check state field bounds
    for (const [fieldName, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) {
        continue;
      }

      // Array bounds
      if ("maxLength" in fieldConfig) {
        const maxLength = (fieldConfig as any).maxLength;
        if (maxLength !== null) {
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
      }

      // Number bounds
      if ("min" in fieldConfig && "max" in fieldConfig) {
        const min = (fieldConfig as any).min;
        const max = (fieldConfig as any).max;

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

      // Map/Set bounds
      if ("maxSize" in fieldConfig) {
        const maxSize = (fieldConfig as any).maxSize;
        if (maxSize !== null) {
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
      }
    }
  }
}

export function validateConfig(configPath: string): ValidationResult {
  const validator = new ConfigValidator();
  return validator.validate(configPath);
}
