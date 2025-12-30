// TLA+ specification generator

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import type { MessageHandler } from "../core/model";
import type { SANYRunner, ValidationResult as SANYValidationResult } from "../runner/sany";
import type { CodebaseAnalysis, VerificationConfig } from "../types";
import { type Invariant, InvariantExtractor, InvariantGenerator } from "./invariants";
import type { RoundTripResult, RoundTripValidator } from "./round-trip";
import { type TemporalProperty, TemporalPropertyGenerator, TemporalTLAGenerator } from "./temporal";
import type { TLAValidator, ValidationError } from "./tla-validator";

/**
 * Validation report from all validators
 */
export type ValidationReport = {
  syntaxValidation: {
    passed: boolean;
    errors: ValidationError[];
  };
  sanyValidation: {
    passed: boolean;
    result: SANYValidationResult | null;
  };
  roundTripValidation: {
    passed: boolean;
    result: RoundTripResult | null;
  };
};

/**
 * Validation error thrown when generation produces invalid TLA+
 */
export class TLAValidationError extends Error {
  constructor(
    message: string,
    public readonly report: ValidationReport
  ) {
    super(message);
    this.name = "TLAValidationError";
  }
}

export class TLAGenerator {
  private lines: string[] = [];
  private indent = 0;
  private extractedInvariants: Invariant[] = [];
  private temporalProperties: TemporalProperty[] = [];
  private symmetrySets: string[] = [];
  private filteredMessageTypes: string[] = [];

  /**
   * Create TLA+ generator with optional validators and property generators
   *
   * If validators are provided, generate() will automatically validate
   * the generated spec and throw TLAValidationError if invalid.
   *
   * If enableInvariants or enableTemporalProperties is true, the generator
   * will extract and include these properties in the spec.
   */
  constructor(
    private options?: {
      validator?: TLAValidator;
      sanyRunner?: SANYRunner;
      roundTripValidator?: RoundTripValidator;
      enableInvariants?: boolean;
      enableTemporalProperties?: boolean;
      projectPath?: string; // Required if enableInvariants is true
    }
  ) {}

  /**
   * Check if a string is a valid TLA+ identifier
   * TLA+ identifiers must:
   * - Start with a letter (a-zA-Z)
   * - Contain only letters, digits, and underscores
   * - Not be empty
   */
  private isValidTLAIdentifier(s: string): boolean {
    if (!s || s.length === 0) {
      return false;
    }
    // TLA+ identifiers: start with letter, contain only alphanumeric + underscore
    return /^[a-zA-Z][a-zA-Z0-9_]*$/.test(s);
  }

  /**
   * Generate TLA+ specification with optional validation
   *
   * If validators were provided in constructor, this method will:
   * 1. Pre-validate inputs
   * 2. Generate spec
   * 3. Fast syntax validation
   * 4. SANY validation (comprehensive)
   * 5. Round-trip validation
   *
   * Throws TLAValidationError if validation fails.
   */
  async generate(
    config: VerificationConfig,
    analysis: CodebaseAnalysis
  ): Promise<{
    spec: string;
    cfg: string;
    validation?: ValidationReport;
  }> {
    // Pre-validate inputs
    this.validateInputs(config, analysis);

    // Extract invariants and temporal properties if enabled
    this.extractInvariantsIfEnabled();
    this.generateTemporalPropertiesIfEnabled(analysis);

    // Generate spec and config
    this.lines = [];
    this.indent = 0;
    const spec = this.generateSpec(config, analysis);
    const cfg = this.generateConfig(config);

    // If no validators provided, return immediately (backward compatibility)
    if (!this.hasValidators()) {
      return { spec, cfg };
    }

    // Perform all validations
    const validation = await this.performAllValidations(spec, config, analysis);

    return { spec, cfg, validation };
  }

  /**
   * Check if any validators are configured
   */
  private hasValidators(): boolean {
    return !!(
      this.options?.validator ||
      this.options?.sanyRunner ||
      this.options?.roundTripValidator
    );
  }

  /**
   * Extract invariants from project if enabled
   */
  private extractInvariantsIfEnabled(): void {
    if (this.options?.enableInvariants && this.options.projectPath) {
      const extractor = new InvariantExtractor();
      const result = extractor.extractInvariants(this.options.projectPath);
      this.extractedInvariants = result.invariants;

      if (result.warnings.length > 0 && process.env["POLLY_DEBUG"]) {
        console.log("[DEBUG] Invariant extraction warnings:");
        for (const warning of result.warnings) {
          console.log(`  - ${warning}`);
        }
      }
    }
  }

  /**
   * Generate temporal properties if enabled
   */
  private generateTemporalPropertiesIfEnabled(analysis: CodebaseAnalysis): void {
    if (this.options?.enableTemporalProperties) {
      const generator = new TemporalPropertyGenerator();
      this.temporalProperties = generator.generateProperties(analysis);
    }
  }

  /**
   * Perform all validations and return report
   */
  private async performAllValidations(
    spec: string,
    config: VerificationConfig,
    analysis: CodebaseAnalysis
  ): Promise<ValidationReport> {
    // Fast syntax validation
    const syntaxErrors = this.performSyntaxValidation(spec);

    // SANY validation (comprehensive)
    const sanyResult = await this.performSANYValidation(spec);

    // Round-trip validation
    const roundTripResult = await this.performRoundTripValidation(config, analysis, spec);

    // Build validation report
    const validation: ValidationReport = {
      syntaxValidation: {
        passed: syntaxErrors.length === 0,
        errors: syntaxErrors,
      },
      sanyValidation: {
        passed: sanyResult ? sanyResult.valid : true,
        result: sanyResult,
      },
      roundTripValidation: {
        passed: roundTripResult ? roundTripResult.valid : true,
        result: roundTripResult,
      },
    };

    // If any validation failed, throw error
    if (
      !validation.syntaxValidation.passed ||
      !validation.sanyValidation.passed ||
      !validation.roundTripValidation.passed
    ) {
      throw new TLAValidationError(this.buildValidationErrorMessage(validation), validation);
    }

    return validation;
  }

  /**
   * Perform fast syntax validation
   */
  private performSyntaxValidation(spec: string): ValidationError[] {
    const syntaxErrors: ValidationError[] = [];
    if (this.options?.validator) {
      const moduleErrors = this.options.validator.validateModuleStructure(spec);
      syntaxErrors.push(...moduleErrors);
    }
    return syntaxErrors;
  }

  /**
   * Perform SANY validation
   */
  private async performSANYValidation(spec: string): Promise<SANYValidationResult | null> {
    if (!this.options?.sanyRunner) {
      return null;
    }

    // Write spec to temp file for SANY
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-sany-"));
    const specPath = path.join(tempDir, "UserApp.tla");
    fs.writeFileSync(specPath, spec);

    try {
      return await this.options.sanyRunner.validateSpec(specPath);
    } finally {
      // Cleanup temp file
      try {
        fs.rmSync(tempDir, { recursive: true });
      } catch {
        // Ignore cleanup errors
      }
    }
  }

  /**
   * Perform round-trip validation
   */
  private async performRoundTripValidation(
    config: VerificationConfig,
    analysis: CodebaseAnalysis,
    spec: string
  ): Promise<RoundTripResult | null> {
    if (!this.options?.roundTripValidator) {
      return null;
    }

    return await this.options.roundTripValidator.validate(config, analysis, spec);
  }

  /**
   * Pre-validate inputs before generation
   */
  private validateInputs(_config: VerificationConfig, analysis: CodebaseAnalysis): void {
    // Validate message types are valid TLA+ identifiers
    for (const messageType of analysis.messageTypes) {
      if (!this.isValidTLAIdentifier(messageType)) {
        throw new Error(
          `Invalid message type '${messageType}'. TLA+ identifiers must start with a letter and contain only letters, digits, and underscores.`
        );
      }
    }

    // Note: State field names are sanitized (dots → underscores) during generation,
    // so we don't validate them here as strict TLA+ identifiers
  }

  /**
   * Build user-friendly error message from validation report
   */
  private buildValidationErrorMessage(validation: ValidationReport): string {
    const messages: string[] = ["TLA+ generation validation failed:"];

    this.appendSyntaxErrors(validation, messages);
    this.appendSANYErrors(validation, messages);
    this.appendRoundTripErrors(validation, messages);

    return messages.join("\n");
  }

  /**
   * Append syntax validation errors to message array
   */
  private appendSyntaxErrors(validation: ValidationReport, messages: string[]): void {
    if (!validation.syntaxValidation.passed) {
      messages.push(`\n  Syntax errors (${validation.syntaxValidation.errors.length}):`);
      for (const error of validation.syntaxValidation.errors.slice(0, 5)) {
        const location = error.line ? ` at line ${error.line}` : "";
        messages.push(`    - ${error.message}${location}`);
      }
      if (validation.syntaxValidation.errors.length > 5) {
        messages.push(`    ... and ${validation.syntaxValidation.errors.length - 5} more`);
      }
    }
  }

  /**
   * Append SANY validation errors to message array
   */
  private appendSANYErrors(validation: ValidationReport, messages: string[]): void {
    if (!validation.sanyValidation.passed && validation.sanyValidation.result) {
      messages.push(
        `\n  SANY validation errors (${validation.sanyValidation.result.errors.length}):`
      );
      for (const error of validation.sanyValidation.result.errors.slice(0, 5)) {
        const location = error.line ? ` at line ${error.line}` : "";
        messages.push(`    - ${error.message}${location}`);
        if (error.suggestion) {
          messages.push(`      Suggestion: ${error.suggestion}`);
        }
      }
      if (validation.sanyValidation.result.errors.length > 5) {
        messages.push(`    ... and ${validation.sanyValidation.result.errors.length - 5} more`);
      }
    }
  }

  /**
   * Append round-trip validation errors to message array
   */
  private appendRoundTripErrors(validation: ValidationReport, messages: string[]): void {
    if (!validation.roundTripValidation.passed && validation.roundTripValidation.result) {
      messages.push(
        `\n  Round-trip validation errors (${validation.roundTripValidation.result.errors.length}):`
      );
      for (const error of validation.roundTripValidation.result.errors.slice(0, 5)) {
        messages.push(`    - ${error.message}`);
      }
      if (validation.roundTripValidation.result.errors.length > 5) {
        messages.push(
          `    ... and ${validation.roundTripValidation.result.errors.length - 5} more`
        );
      }
    }
  }

  private generateSpec(config: VerificationConfig, analysis: CodebaseAnalysis): string {
    this.lines = [];
    this.indent = 0;

    this.addHeader();
    this.addExtends();
    this.addConstants(config);
    this.addMessageTypes(config, analysis);
    this.addStateType(config, analysis);
    this.addVariables();

    // Add delivered tracking if temporal properties enabled
    if (this.temporalProperties.length > 0) {
      this.addDeliveredTracking();
    }

    this.addInit(config, analysis);
    this.addActions(config, analysis);
    this.addRouteWithHandlers(config, analysis);
    this.addNext(config, analysis);
    this.addSpec();
    this.addInvariants(config, analysis);

    // Add temporal properties if enabled
    if (this.temporalProperties.length > 0) {
      this.addTemporalProperties();
    }

    return this.lines.join("\n");
  }

  private generateConfig(config: VerificationConfig): string {
    const lines: string[] = [];

    this.addConfigHeader(lines);
    this.addBasicConstants(lines, config);
    this.addProjectSpecificConstants(lines, config.messages);
    this.addStateBoundsConstants(lines, config.state);
    this.addInvariantsSection(lines);
    this.addTemporalPropertiesSection(lines);
    this.addConstraintSection(lines);
    this.addSymmetrySection(lines, config);

    return lines.join("\n");
  }

  /**
   * Add config file header
   */
  private addConfigHeader(lines: string[]): void {
    lines.push("SPECIFICATION UserSpec");
    lines.push("");
    lines.push("\\* Constants");
    lines.push("CONSTANTS");
  }

  /**
   * Add basic constants (Contexts, MaxMessages)
   */
  private addBasicConstants(lines: string[], config: VerificationConfig): void {
    lines.push("  Contexts = {background, content, popup}");
    lines.push(`  MaxMessages = ${config.messages.maxInFlight || 3}`);

    // Tier 1 Optimization: Per-message bounds
    if (config.messages.perMessageBounds) {
      for (const [msgType, bound] of Object.entries(config.messages.perMessageBounds)) {
        const constName = `MaxMessages_${msgType}`;
        lines.push(`  ${constName} = ${bound}`);
      }
    }
  }

  /**
   * Add project-specific constants (maxWorkers, maxRenderers, etc.)
   */
  private addProjectSpecificConstants(
    lines: string[],
    messages: VerificationConfig["messages"]
  ): void {
    let hasProjectConstant = false;

    if ("maxWorkers" in messages && messages.maxWorkers !== undefined) {
      lines.push(`  MaxWorkers = ${messages.maxWorkers}`);
      hasProjectConstant = true;
    }
    if ("maxRenderers" in messages && messages.maxRenderers !== undefined) {
      lines.push(`  MaxRenderers = ${messages.maxRenderers}`);
      hasProjectConstant = true;
    }
    if ("maxContexts" in messages && messages.maxContexts !== undefined) {
      lines.push(`  MaxContexts = ${messages.maxContexts}`);
      hasProjectConstant = true;
    }
    if ("maxClients" in messages && messages.maxClients !== undefined && !hasProjectConstant) {
      lines.push(`  MaxClients = ${messages.maxClients}`);
      hasProjectConstant = true;
    }

    // Handle MaxTabId
    if ("maxTabs" in messages && messages.maxTabs !== undefined) {
      lines.push(`  MaxTabId = ${messages.maxTabs}`);
    } else if (hasProjectConstant) {
      lines.push("  MaxTabId = 0");
    } else {
      lines.push("  MaxTabId = 1");
    }

    lines.push("  TimeoutLimit = 3");
  }

  /**
   * Add state bounds constants
   */
  private addStateBoundsConstants(lines: string[], state: VerificationConfig["state"]): void {
    for (const [field, fieldConfig] of Object.entries(state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const constName = this.fieldToConstName(field);

      if ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) {
        lines.push(`  ${constName}_MaxLength = ${fieldConfig.maxLength}`);
      }
      if ("max" in fieldConfig && fieldConfig.max !== null) {
        lines.push(`  ${constName}_Max = ${fieldConfig.max}`);
      }
      if ("maxSize" in fieldConfig && fieldConfig.maxSize !== null) {
        lines.push(`  ${constName}_MaxSize = ${fieldConfig.maxSize}`);
      }
    }
  }

  /**
   * Add invariants section to config
   */
  private addInvariantsSection(lines: string[]): void {
    lines.push("");
    lines.push("\\* Invariants to check");
    lines.push("INVARIANTS");
    lines.push("  TypeOK");
    lines.push("  NoRoutingLoops");
    lines.push("  UserStateTypeInvariant");

    for (const inv of this.extractedInvariants) {
      lines.push(`  ${inv.name}`);
    }
  }

  /**
   * Add temporal properties section to config
   */
  private addTemporalPropertiesSection(lines: string[]): void {
    if (this.temporalProperties.length === 0) return;

    lines.push("");
    lines.push("\\* Temporal properties to check");
    lines.push("PROPERTIES");
    for (const prop of this.temporalProperties) {
      lines.push(`  ${prop.name}`);
    }
  }

  /**
   * Add constraint section to config
   */
  private addConstraintSection(lines: string[]): void {
    lines.push("");
    lines.push("\\* State constraint");
    lines.push("CONSTRAINT");
    lines.push("  StateConstraint");
  }

  /**
   * Add symmetry section to config for Tier 1 optimization
   */
  private addSymmetrySection(lines: string[], _config: VerificationConfig): void {
    if (!this.symmetrySets || this.symmetrySets.length === 0) {
      return;
    }

    lines.push("");
    lines.push("\\* Symmetry sets for state space reduction");
    for (const setName of this.symmetrySets) {
      lines.push(`SYMMETRY ${setName}`);
    }
  }

  private addHeader(): void {
    this.line("------------------------- MODULE UserApp -------------------------");
    this.line("(*");
    this.line("  Auto-generated TLA+ specification for web extension");
    this.line("  ");
    this.line("  Generated from:");
    this.line("    - TypeScript type definitions");
    this.line("    - Verification configuration");
    this.line("  ");
    this.line("  This spec extends MessageRouter with:");
    this.line("    - Application-specific state types");
    this.line("    - Message type definitions");
    this.line("    - State transition actions");
    this.line("*)");
    this.line("");
  }

  private addExtends(): void {
    this.line("EXTENDS MessageRouter");
    this.line("");
  }

  private addConstants(config: VerificationConfig): void {
    // MessageRouter already defines: Contexts, MaxMessages, MaxTabId, TimeoutLimit
    // We only add application-specific constants

    if (!this.hasCustomConstants(config.state)) {
      return;
    }

    this.line("\\* Application-specific constants");
    this.line("CONSTANTS");
    this.indent++;

    this.generateConstantDeclarations(config.state);

    this.indent--;
    this.line("");
  }

  /**
   * Check if config has any custom constants
   */
  private hasCustomConstants(state: VerificationConfig["state"]): boolean {
    return Object.values(state).some((fieldConfig) => {
      if (typeof fieldConfig !== "object" || fieldConfig === null) return false;
      return (
        ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) ||
        ("max" in fieldConfig && fieldConfig.max !== null) ||
        ("maxSize" in fieldConfig && fieldConfig.maxSize !== null)
      );
    });
  }

  /**
   * Generate constant declarations for all state fields
   */
  private generateConstantDeclarations(state: VerificationConfig["state"]): void {
    let first = true;

    for (const [field, fieldConfig] of Object.entries(state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const constName = this.fieldToConstName(field);
      first = this.addFieldConstants(field, fieldConfig, constName, first);
    }
  }

  /**
   * Add constants for a single field
   */
  private addFieldConstants(
    field: string,
    fieldConfig: Record<string, unknown>,
    constName: string,
    first: boolean
  ): boolean {
    let isFirst = first;

    if ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) {
      this.line(`${isFirst ? "" : ","}${constName}_MaxLength  \\* Max length for ${field}`);
      isFirst = false;
    }
    if ("max" in fieldConfig && fieldConfig.max !== null) {
      this.line(`${isFirst ? "" : ","}${constName}_Max       \\* Max value for ${field}`);
      isFirst = false;
    }
    if ("maxSize" in fieldConfig && fieldConfig.maxSize !== null) {
      this.line(`${isFirst ? "" : ","}${constName}_MaxSize   \\* Max size for ${field}`);
      isFirst = false;
    }

    return isFirst;
  }

  private addStateType(config: VerificationConfig, _analysis: CodebaseAnalysis): void {
    // Define Value type for generic sequences and maps
    this.defineValueTypes();

    // Generate State type definition
    this.line("\\* Application state type definition");
    this.line("State == [");
    this.indent++;

    const stateFields = this.collectStateFields(config, _analysis);
    this.writeStateFields(stateFields);

    this.indent--;
    this.line("]");
    this.line("");
  }

  private defineValueTypes(): void {
    this.line("\\* Generic value type for sequences and maps");
    this.line("\\* Bounded to allow model checking");
    this.line('Value == {"v1", "v2", "v3"}');
    this.line("");

    this.line("\\* Generic key type for maps");
    this.line("\\* Bounded to allow model checking");
    this.line('Keys == {"k1", "k2", "k3"}');
    this.line("");
  }

  private collectStateFields(config: VerificationConfig, _analysis: CodebaseAnalysis): string[] {
    const stateFields: string[] = [];

    // Add fields from config.state
    for (const [fieldPath, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const fieldName = this.sanitizeFieldName(fieldPath);
      const tlaType = this.fieldConfigToTLAType(fieldPath, fieldConfig, config);
      stateFields.push(`${fieldName}: ${tlaType}`);
    }

    // Add fields from analysis
    for (const fieldAnalysis of _analysis.fields) {
      if (!fieldAnalysis.path || typeof fieldAnalysis.path !== "string") continue;

      const fieldName = this.sanitizeFieldName(fieldAnalysis.path);
      if (stateFields.some((f) => f.startsWith(`${fieldName}:`))) continue;

      const tlaType = this.inferTLATypeFromAnalysis(fieldAnalysis);
      stateFields.push(`${fieldName}: ${tlaType}`);
    }

    return stateFields;
  }

  private writeStateFields(fields: string[]): void {
    if (fields.length === 0) {
      this.line("dummy: BOOLEAN  \\* Placeholder for empty state");
      return;
    }

    for (let i = 0; i < fields.length; i++) {
      const field = fields[i];
      const suffix = i < fields.length - 1 ? "," : "";
      this.line(`${field}${suffix}`);
    }
  }

  private addMessageTypes(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    if (analysis.messageTypes.length === 0) {
      // No message types found, skip
      return;
    }

    // Filter out invalid TLA+ identifiers
    let validMessageTypes: string[] = [];
    const invalidMessageTypes: string[] = [];

    for (const msgType of analysis.messageTypes) {
      if (this.isValidTLAIdentifier(msgType)) {
        validMessageTypes.push(msgType);
      } else {
        invalidMessageTypes.push(msgType);
      }
    }

    // Log warnings about invalid message types
    if (invalidMessageTypes.length > 0 && process.env["POLLY_DEBUG"]) {
      console.log(
        `[WARN] [TLAGenerator] Filtered out ${invalidMessageTypes.length} invalid message type(s):`
      );
      for (const invalid of invalidMessageTypes) {
        console.log(`[WARN]   - "${invalid}" (not a valid TLA+ identifier)`);
      }
    }

    // Apply Tier 1 Optimization: Message filtering (Issue #12)
    const originalCount = validMessageTypes.length;
    const filteredOut: string[] = [];

    if (config.messages.include && config.messages.include.length > 0) {
      // Include mode: only keep specified message types
      const included = new Set(config.messages.include);
      const beforeFilter = validMessageTypes;
      validMessageTypes = validMessageTypes.filter(msg => included.has(msg));
      filteredOut.push(...beforeFilter.filter(msg => !included.has(msg)));
    } else if (config.messages.exclude && config.messages.exclude.length > 0) {
      // Exclude mode: filter out specified message types
      const excluded = new Set(config.messages.exclude);
      const beforeFilter = validMessageTypes;
      validMessageTypes = validMessageTypes.filter(msg => !excluded.has(msg));
      filteredOut.push(...beforeFilter.filter(msg => excluded.has(msg)));
    }

    // Log message filtering optimization
    if (filteredOut.length > 0) {
      const filterMode = config.messages.include ? "include" : "exclude";
      console.log(
        `[INFO] [TLAGenerator] Message filtering (${filterMode}): ${originalCount} → ${validMessageTypes.length} message types`
      );
      if (process.env["POLLY_DEBUG"]) {
        console.log(`[INFO]   Filtered out: ${filteredOut.join(", ")}`);
      }
    }

    if (validMessageTypes.length === 0) {
      // No valid message types, skip
      return;
    }

    this.line("\\* Message types from application");
    const messageTypeSet = validMessageTypes.map((t) => `"${t}"`).join(", ");
    this.line(`UserMessageTypes == {${messageTypeSet}}`);
    this.line("");

    // Store for symmetry reduction
    this.filteredMessageTypes = validMessageTypes;

    // Apply Tier 1 Optimization: Symmetry reduction
    if (config.messages.symmetry && config.messages.symmetry.length > 0) {
      this.addSymmetrySets(config.messages.symmetry, validMessageTypes);
    }
  }

  /**
   * Add symmetry set definitions for Tier 1 optimization
   */
  private addSymmetrySets(symmetryGroups: string[][], validMessageTypes: string[]): void {
    const validTypes = new Set(validMessageTypes);

    this.line("\\* Symmetry sets for state space reduction (Tier 1 optimization)");

    for (let i = 0; i < symmetryGroups.length; i++) {
      const group = symmetryGroups[i];
      if (!group || group.length < 2) continue;

      // Filter to only valid message types in this group
      const validGroupTypes = group.filter(t => validTypes.has(t));
      if (validGroupTypes.length < 2) {
        if (process.env["POLLY_DEBUG"]) {
          console.log(`[WARN] [TLAGenerator] Symmetry group ${i + 1} has < 2 valid types, skipping`);
        }
        continue;
      }

      const setName = `SymmetrySet${i + 1}`;
      const setValues = validGroupTypes.map(t => `"${t}"`).join(", ");
      this.line(`${setName} == {${setValues}}`);

      // Store for config generation
      if (!this.symmetrySets) {
        this.symmetrySets = [];
      }
      this.symmetrySets.push(setName);
    }

    if (this.symmetrySets && this.symmetrySets.length > 0) {
      console.log(
        `[INFO] [TLAGenerator] Symmetry reduction: ${this.symmetrySets.length} symmetry group(s) defined`
      );
    }

    this.line("");
  }

  private addVariables(): void {
    // MessageRouter already defines: ports, messages, pendingRequests, delivered, routingDepth, time
    // We add: contextStates for application state

    this.line("\\* Application state per context");
    this.line("VARIABLE contextStates");
    this.line("");
    this.line("\\* All variables (extending MessageRouter vars)");
    this.line(
      "allVars == <<ports, messages, pendingRequests, delivered, routingDepth, time, contextStates>>"
    );
    this.line("");
  }

  private addInit(config: VerificationConfig, _analysis: CodebaseAnalysis): void {
    // Generate InitialState first
    this.line("\\* Initial application state");
    this.line("InitialState == [");
    this.indent++;

    const fields = this.collectInitialStateFields(config, _analysis);
    this.writeInitialStateFields(fields);

    this.indent--;
    this.line("]");
    this.line("");

    // Init extends MessageRouter's Init
    this.line("\\* Initial state (extends MessageRouter)");
    this.line("UserInit ==");
    this.indent++;
    this.line("/\\ Init  \\* MessageRouter's init");
    this.line("/\\ contextStates = [c \\in Contexts |-> InitialState]");
    this.indent--;
    this.line("");
  }

  private collectInitialStateFields(
    config: VerificationConfig,
    _analysis: CodebaseAnalysis
  ): string[] {
    const fields: string[] = [];

    // Add fields from config.state
    for (const [fieldPath, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const fieldName = this.sanitizeFieldName(fieldPath);
      const initialValue = this.getInitialValue(fieldConfig);
      fields.push(`${fieldName} |-> ${initialValue}`);
    }

    // Add fields from analysis
    for (const fieldAnalysis of _analysis.fields) {
      if (!fieldAnalysis.path || typeof fieldAnalysis.path !== "string") continue;

      const fieldName = this.sanitizeFieldName(fieldAnalysis.path);
      if (fields.some((f) => f.startsWith(`${fieldName} |->`))) continue;

      const initialValue = this.getInitialValueFromAnalysis(fieldAnalysis);
      fields.push(`${fieldName} |-> ${initialValue}`);
    }

    return fields;
  }

  private writeInitialStateFields(fields: string[]): void {
    if (fields.length === 0) {
      this.line("dummy |-> FALSE  \\* Placeholder for empty state");
      return;
    }

    for (let i = 0; i < fields.length; i++) {
      const field = fields[i];
      const suffix = i < fields.length - 1 ? "," : "";
      this.line(`${field}${suffix}`);
    }
  }

  private addActions(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    this.line("\\* =============================================================================");
    this.line("\\* Application-specific actions");
    this.line("\\* =============================================================================");
    this.line("");

    if (analysis.handlers.length === 0) {
      this.generateNoHandlersStub();
      return;
    }

    const { validHandlers, invalidHandlers } = this.filterHandlersByValidity(analysis.handlers);
    this.logInvalidHandlers(invalidHandlers);

    if (validHandlers.length === 0) {
      this.generateNoValidHandlersStub();
      return;
    }

    const handlersByType = this.groupHandlersByType(validHandlers);
    this.generateHandlerActions(handlersByType, config);
    this.generateStateTransitionDispatcher(handlersByType);
  }

  /**
   * Generate stub for no handlers found
   */
  private generateNoHandlersStub(): void {
    this.line("\\* No message handlers found in codebase");
    this.line("\\* State remains unchanged for all messages");
    this.line("StateTransition(ctx, msgType) ==");
    this.indent++;
    this.line("UNCHANGED contextStates");
    this.indent--;
    this.line("");
  }

  /**
   * Generate stub for no valid handlers
   */
  private generateNoValidHandlersStub(): void {
    this.line("\\* No valid message handlers found (all had invalid TLA+ identifiers)");
    this.line("\\* State remains unchanged for all messages");
    this.line("StateTransition(ctx, msgType) ==");
    this.indent++;
    this.line("UNCHANGED contextStates");
    this.indent--;
    this.line("");
  }

  /**
   * Filter handlers into valid and invalid based on TLA+ identifier rules
   */
  private filterHandlersByValidity(handlers: MessageHandler[]): {
    validHandlers: MessageHandler[];
    invalidHandlers: MessageHandler[];
  } {
    const validHandlers: MessageHandler[] = [];
    const invalidHandlers: MessageHandler[] = [];

    for (const handler of handlers) {
      if (this.isValidTLAIdentifier(handler.messageType)) {
        validHandlers.push(handler);
      } else {
        invalidHandlers.push(handler);
      }
    }

    return { validHandlers, invalidHandlers };
  }

  /**
   * Log warnings about invalid handlers
   */
  private logInvalidHandlers(invalidHandlers: MessageHandler[]): void {
    if (invalidHandlers.length === 0 || !process.env["POLLY_DEBUG"]) return;

    console.log(
      `[WARN] [TLAGenerator] Filtered out ${invalidHandlers.length} handler(s) with invalid message types:`
    );
    for (const handler of invalidHandlers) {
      console.log(
        `[WARN]   - "${handler.messageType}" at ${handler.location.file}:${handler.location.line}`
      );
    }
  }

  /**
   * Group handlers by message type
   */
  private groupHandlersByType(handlers: MessageHandler[]): Map<string, MessageHandler[]> {
    const handlersByType = new Map<string, MessageHandler[]>();

    for (const handler of handlers) {
      if (!handlersByType.has(handler.messageType)) {
        handlersByType.set(handler.messageType, []);
      }
      handlersByType.get(handler.messageType)?.push(handler);
    }

    return handlersByType;
  }

  /**
   * Generate handler actions for all message types
   */
  private generateHandlerActions(
    handlersByType: Map<string, MessageHandler[]>,
    config: VerificationConfig
  ): void {
    this.line("\\* State transitions extracted from message handlers");
    this.line("");

    for (const [messageType, handlers] of handlersByType.entries()) {
      this.generateHandlerAction(messageType, handlers, config);
    }
  }

  /**
   * Generate main StateTransition dispatcher
   */
  private generateStateTransitionDispatcher(handlersByType: Map<string, MessageHandler[]>): void {
    this.line("\\* Main state transition action");
    this.line("StateTransition(ctx, msgType) ==");
    this.indent++;

    const messageTypes = Array.from(handlersByType.keys());
    for (let i = 0; i < messageTypes.length; i++) {
      const msgType = messageTypes[i];
      if (!msgType) continue;
      const actionName = this.messageTypeToActionName(msgType);

      if (i === 0) {
        this.line(`IF msgType = "${msgType}" THEN ${actionName}(ctx)`);
      } else if (i === messageTypes.length - 1) {
        this.line(`ELSE IF msgType = "${msgType}" THEN ${actionName}(ctx)`);
        this.line("ELSE UNCHANGED contextStates  \\* Unknown message type");
      } else {
        this.line(`ELSE IF msgType = "${msgType}" THEN ${actionName}(ctx)`);
      }
    }

    this.indent--;
    this.line("");
  }

  private generateHandlerAction(
    messageType: string,
    handlers: MessageHandler[],
    config: VerificationConfig
  ): void {
    const actionName = this.messageTypeToActionName(messageType);

    this.line(`\\* Handler for ${messageType}`);
    this.line(`${actionName}(ctx) ==`);
    this.indent++;

    // Collect conditions and assignments
    const allPreconditions = handlers.flatMap((h) => h.preconditions);
    const allAssignments = handlers.flatMap((h) => h.assignments);
    const allPostconditions = handlers.flatMap((h) => h.postconditions);

    // Emit preconditions
    this.emitPreconditions(allPreconditions);

    // Process and emit assignments
    const validAssignments = this.processAssignments(allAssignments, config.state);
    this.emitStateUpdates(validAssignments, allPreconditions);

    // Emit postconditions
    this.emitPostconditions(allPostconditions);

    this.indent--;
    this.line("");
  }

  /**
   * Emit precondition checks
   */
  private emitPreconditions(preconditions: Array<{ expression: string; message?: string }>): void {
    for (const precondition of preconditions) {
      const tlaExpr = this.tsExpressionToTLA(precondition.expression);
      const comment = precondition.message ? ` \\* ${precondition.message}` : "";
      this.line(`/\\ ${tlaExpr}${comment}`);
    }
  }

  /**
   * Emit postcondition checks
   */
  private emitPostconditions(
    postconditions: Array<{ expression: string; message?: string }>
  ): void {
    for (const postcondition of postconditions) {
      const tlaExpr = this.tsExpressionToTLA(postcondition.expression, true);
      const comment = postcondition.message ? ` \\* ${postcondition.message}` : "";
      this.line(`/\\ ${tlaExpr}${comment}`);
    }
  }

  /**
   * Process assignments, filtering and mapping null values
   */
  private processAssignments(
    assignments: Array<{ field: string; value: string | boolean | number | null }>,
    state: VerificationConfig["state"]
  ): Array<{ field: string; value: string | boolean | number | null }> {
    return assignments
      .filter((a) => this.shouldIncludeAssignment(a, state))
      .map((a) => this.mapNullAssignment(a, state));
  }

  /**
   * Check if assignment should be included
   */
  private shouldIncludeAssignment(
    assignment: { field: string; value: string | boolean | number | null },
    state: VerificationConfig["state"]
  ): boolean {
    if (assignment.value !== null) return true;

    // Check if null can be mapped to a valid value
    const fieldConfig = state[assignment.field];
    return !!(
      fieldConfig &&
      typeof fieldConfig === "object" &&
      "values" in fieldConfig &&
      fieldConfig.values
    );
  }

  /**
   * Map null assignment to a valid value if possible
   */
  private mapNullAssignment(
    assignment: { field: string; value: string | boolean | number | null },
    state: VerificationConfig["state"]
  ): { field: string; value: string | boolean | number | null } {
    if (assignment.value !== null) return assignment;

    const fieldConfig = state[assignment.field];
    if (
      fieldConfig &&
      typeof fieldConfig === "object" &&
      "values" in fieldConfig &&
      fieldConfig.values
    ) {
      const nullValue = fieldConfig.values[fieldConfig.values.length - 1];
      return { ...assignment, value: nullValue };
    }

    return assignment;
  }

  /**
   * Emit state updates or UNCHANGED
   */
  private emitStateUpdates(
    validAssignments: Array<{ field: string; value: string | boolean | number | null }>,
    preconditions: Array<{ expression: string; message?: string }>
  ): void {
    if (validAssignments.length === 0) {
      if (preconditions.length === 0) {
        this.line("\\* No state changes in handler");
      }
      this.line("/\\ UNCHANGED contextStates");
      return;
    }

    this.line("/\\ contextStates' = [contextStates EXCEPT");
    this.indent++;

    for (let i = 0; i < validAssignments.length; i++) {
      const assignment = validAssignments[i];
      if (!assignment || assignment.value === undefined) continue;

      const fieldName = this.sanitizeFieldName(assignment.field);
      const value = this.assignmentValueToTLA(assignment.value);
      const suffix = i < validAssignments.length - 1 ? "," : "";

      this.line(`![ctx].${fieldName} = ${value}${suffix}`);
    }

    this.indent--;
    this.line("]");
  }

  /**
   * Translate TypeScript expression to TLA+ syntax
   * @param expr - TypeScript expression from requires() or ensures()
   * @param isPrimed - If true, use contextStates' (for postconditions)
   */
  private tsExpressionToTLA(expr: string, isPrimed = false): string {
    // Early return for invalid expressions
    if (!expr || typeof expr !== "string") {
      return expr || "";
    }

    let tla = expr;

    // Replace state references with contextStates[ctx] or contextStates'[ctx]
    const statePrefix = isPrimed ? "contextStates'[ctx]" : "contextStates[ctx]";

    // Phase 0: Handle complex expressions FIRST (before state replacements)
    // These must come first because they have special operators (?., ??, ?) that
    // would be mangled by later replacements
    tla = this.translateComplexExpressions(tla, statePrefix);

    // Ensure tla is still a valid string after complex expression translation
    if (!tla || typeof tla !== "string") {
      return expr;
    }

    // Phase 1: Handle array/collection operations and string methods before generic replacements
    tla = this.translateArrayOperations(tla, statePrefix);
    if (!tla || typeof tla !== "string") {
      return expr;
    }

    tla = this.translateStringMethods(tla);
    if (!tla || typeof tla !== "string") {
      return expr;
    }

    // Phase 2: Replace state references with contextStates[ctx] or contextStates'[ctx]
    tla = tla.replace(/state\.([a-zA-Z_][a-zA-Z0-9_.]*)/g, (_match, path) => {
      return `${statePrefix}.${this.sanitizeFieldName(path)}`;
    });

    // Replace payload.field with payload.field (no change needed, but sanitize)
    tla = tla.replace(/payload\.([a-zA-Z_][a-zA-Z0-9_.]*)/g, (_match, path) => {
      return `payload.${this.sanitizeFieldName(path)}`;
    });

    // Phase 3: Replace comparison operators
    tla = tla.replace(/===/g, "=");
    tla = tla.replace(/!==/g, "#");
    tla = tla.replace(/!=/g, "#");
    tla = tla.replace(/==/g, "=");

    // Phase 4: Replace logical operators
    tla = tla.replace(/&&/g, "/\\");
    tla = tla.replace(/\|\|/g, "\\/");

    // Replace negation operator (careful with !== already handled)
    // Match ! that's not part of !== or !=
    tla = tla.replace(/!([^=])/g, "~$1");
    tla = tla.replace(/!$/g, "~"); // Handle ! at end of string

    // Phase 5: Replace boolean literals
    tla = tla.replace(/\btrue\b/g, "TRUE");
    tla = tla.replace(/\bfalse\b/g, "FALSE");

    // Replace null
    tla = tla.replace(/\bnull\b/g, "NULL");

    // Phase 6: Replace less than / greater than comparisons
    tla = tla.replace(/</g, "<");
    tla = tla.replace(/>/g, ">");
    tla = tla.replace(/<=/g, "<=");
    tla = tla.replace(/>=/g, ">=");

    return tla;
  }

  /**
   * Translate JavaScript array/collection operations to TLA+ equivalents
   *
   * Examples:
   * - items.length -> Len(items)
   * - items.includes(x) -> x \in items
   * - items[0] -> items[1]  (1-based indexing)
   * - items.some(i => i.active) -> \E item \in items : item.active
   * - items.every(i => i.active) -> \A item \in items : item.active
   * - items.find(i => i.id === x) -> CHOOSE item \in items : item.id = x
   */
  private translateArrayOperations(expr: string, _statePrefix: string): string {
    if (!expr || typeof expr !== "string") {
      return expr || "";
    }

    let result = expr;

    // Array.length -> Len(array)
    // Match: identifier.length or state.field.length
    result = result.replace(/(\w+(?:\.\w+)*)\.length\b/g, (_match, arrayRef) => {
      // If it's a state reference, keep it for later replacement
      if (arrayRef.startsWith("state.")) {
        return `Len(${arrayRef})`;
      }
      return `Len(${arrayRef})`;
    });

    // Array.includes(item) -> item \in array
    result = result.replace(/(\w+(?:\.\w+)*)\.includes\(([^)]+)\)/g, (_match, arrayRef, item) => {
      return `${item.trim()} \\in ${arrayRef}`;
    });

    // Array[index] -> Array[index+1] (convert to 1-based indexing)
    // Handle nested indices: arr[0][1] -> arr[1][2]
    // Pattern matches either: identifier OR closing bracket, followed by [number]
    const _indexMap = new Map<string, number>();
    result = result.replace(
      /(\w+(?:\.\w+)*)\[(\d+)\]|\]\[(\d+)\]/g,
      (_match, identPart, index1, index2) => {
        if (identPart) {
          // First bracket after identifier: items[0]
          const newIndex = Number.parseInt(index1, 10) + 1;
          return `${identPart}[${newIndex}]`;
        }
        // Subsequent bracket after ]: ][1]
        const newIndex = Number.parseInt(index2, 10) + 1;
        return `][${newIndex}]`;
      }
    );

    // Array.some(lambda) -> \E item \in array : condition
    // Match: array.some(item => condition) or array.some((item) => condition)
    result = result.replace(
      /(\w+(?:\.\w+)*)\.some\(\(?(\w+)\)?\s*=>\s*([^)]+)\)/g,
      (_match, arrayRef, param, condition) => {
        // Transform lambda parameter in condition
        const tlaCondition = condition.replace(new RegExp(`\\b${param}\\.`, "g"), `${param}.`);
        return `\\E ${param} \\in ${arrayRef} : ${tlaCondition}`;
      }
    );

    // Array.every(lambda) -> \A item \in array : condition
    result = result.replace(
      /(\w+(?:\.\w+)*)\.every\(\(?(\w+)\)?\s*=>\s*([^)]+)\)/g,
      (_match, arrayRef, param, condition) => {
        const tlaCondition = condition.replace(new RegExp(`\\b${param}\\.`, "g"), `${param}.`);
        return `\\A ${param} \\in ${arrayRef} : ${tlaCondition}`;
      }
    );

    // Array.find(lambda) -> CHOOSE item \in array : condition
    result = result.replace(
      /(\w+(?:\.\w+)*)\.find\(\(?(\w+)\)?\s*=>\s*([^)]+)\)/g,
      (_match, arrayRef, param, condition) => {
        const tlaCondition = condition.replace(new RegExp(`\\b${param}\\.`, "g"), `${param}.`);
        return `CHOOSE ${param} \\in ${arrayRef} : ${tlaCondition}`;
      }
    );

    // Array.filter(lambda).length -> Cardinality({item \in array : condition})
    result = result.replace(
      /(\w+(?:\.\w+)*)\.filter\(\(?(\w+)\)?\s*=>\s*([^)]+)\)\.length/g,
      (_match, arrayRef, param, condition) => {
        const tlaCondition = condition.replace(new RegExp(`\\b${param}\\.`, "g"), `${param}.`);
        return `Cardinality({${param} \\in ${arrayRef} : ${tlaCondition}})`;
      }
    );

    // String.startsWith(prefix) -> SubSeq(str, 1, Len(prefix)) = prefix
    result = result.replace(
      /(\w+(?:\.\w+)*)\.startsWith\("([^"]+)"\)/g,
      (_match, strRef, prefix) => {
        return `SubSeq(${strRef}, 1, ${prefix.length}) = "${prefix}"`;
      }
    );

    // String.endsWith(suffix) -> SubSeq(str, Len(str)-Len(suffix)+1, Len(str)) = suffix
    result = result.replace(/(\w+(?:\.\w+)*)\.endsWith\("([^"]+)"\)/g, (_match, strRef, suffix) => {
      return `SubSeq(${strRef}, Len(${strRef})-${suffix.length}+1, Len(${strRef})) = "${suffix}"`;
    });

    // String.includes(substring) -> \E i \in 1..Len(str) : SubSeq(str, i, i+Len(sub)-1) = sub
    result = result.replace(
      /(\w+(?:\.\w+)*)\.includes\("([^"]+)"\)/g,
      (_match, strRef, substring) => {
        return `\\E i \\in 1..Len(${strRef}) : SubSeq(${strRef}, i, i+${substring.length}-1) = "${substring}"`;
      }
    );

    // String.slice(start, end?).length -> Len(SubSeq(...))
    // Handle chained .length first before translating slice
    result = result.replace(
      /(\w+(?:\.\w+)*)\.slice\((-?\d+)(?:,\s*(-?\d+))?\)\.length/g,
      (_match, strRef, start, end) => {
        const startNum = Number.parseInt(start, 10);
        if (end !== undefined) {
          const endNum = Number.parseInt(end, 10);
          if (startNum < 0 && endNum < 0) {
            return `Len(SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, Len(${strRef}) - ${Math.abs(endNum)}))`;
          }
          if (startNum < 0) {
            return `Len(SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, ${endNum}))`;
          }
          if (endNum < 0) {
            return `Len(SubSeq(${strRef}, ${startNum + 1}, Len(${strRef}) - ${Math.abs(endNum)}))`;
          }
          return `Len(SubSeq(${strRef}, ${startNum + 1}, ${endNum}))`;
        }
        if (startNum < 0) {
          return `Len(SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, Len(${strRef})))`;
        }
        return `Len(SubSeq(${strRef}, ${startNum + 1}, Len(${strRef})))`;
      }
    );

    // String.substring(start, end?).length -> Len(SubSeq(...))
    result = result.replace(
      /(\w+(?:\.\w+)*)\.substring\((\d+)(?:,\s*(\d+))?\)\.length/g,
      (_match, strRef, start, end) => {
        const startNum = Number.parseInt(start, 10);
        if (end !== undefined) {
          const endNum = Number.parseInt(end, 10);
          if (startNum > endNum) {
            return `Len(SubSeq(${strRef}, ${endNum + 1}, ${startNum}))`;
          }
          return `Len(SubSeq(${strRef}, ${startNum + 1}, ${endNum}))`;
        }
        return `Len(SubSeq(${strRef}, ${startNum + 1}, Len(${strRef})))`;
      }
    );

    // String.slice(start, end?) -> SubSeq(str, start+1, end?) (1-based indexing)
    // slice(start) → SubSeq(str, start+1, Len(str))
    result = result.replace(/(\w+(?:\.\w+)*)\.slice\((-?\d+)\)(?!,)/g, (_match, strRef, start) => {
      const startNum = Number.parseInt(start, 10);
      if (startNum < 0) {
        // Negative index: slice(-2) → SubSeq(str, Len(str) - 2 + 1, Len(str))
        return `SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, Len(${strRef}))`;
      }
      // Positive index: slice(1) → SubSeq(str, 2, Len(str))
      return `SubSeq(${strRef}, ${startNum + 1}, Len(${strRef}))`;
    });

    // slice(start, end) → SubSeq(str, start+1, end)
    result = result.replace(
      /(\w+(?:\.\w+)*)\.slice\((-?\d+),\s*(-?\d+)\)/g,
      (_match, strRef, start, end) => {
        const startNum = Number.parseInt(start, 10);
        const endNum = Number.parseInt(end, 10);

        if (startNum < 0 && endNum < 0) {
          return `SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, Len(${strRef}) - ${Math.abs(endNum)})`;
        }
        if (startNum < 0) {
          return `SubSeq(${strRef}, Len(${strRef}) - ${Math.abs(startNum)} + 1, ${endNum})`;
        }
        if (endNum < 0) {
          return `SubSeq(${strRef}, ${startNum + 1}, Len(${strRef}) - ${Math.abs(endNum)})`;
        }
        // Both positive: slice(0, 3) → SubSeq(str, 1, 3)
        return `SubSeq(${strRef}, ${startNum + 1}, ${endNum})`;
      }
    );

    // String.substring(start, end?) -> SubSeq(str, start+1, end?) (1-based indexing)
    // substring(start) → SubSeq(str, start+1, Len(str))
    result = result.replace(
      /(\w+(?:\.\w+)*)\.substring\((\d+)\)(?!,)/g,
      (_match, strRef, start) => {
        const startNum = Number.parseInt(start, 10);
        return `SubSeq(${strRef}, ${startNum + 1}, Len(${strRef}))`;
      }
    );

    // substring(start, end) → SubSeq(str, start+1, end)
    // Note: substring auto-swaps if start > end
    result = result.replace(
      /(\w+(?:\.\w+)*)\.substring\((\d+),\s*(\d+)\)/g,
      (_match, strRef, start, end) => {
        const startNum = Number.parseInt(start, 10);
        const endNum = Number.parseInt(end, 10);

        // substring auto-swaps indices if start > end
        if (startNum > endNum) {
          return `SubSeq(${strRef}, ${endNum + 1}, ${startNum})`;
        }
        return `SubSeq(${strRef}, ${startNum + 1}, ${endNum})`;
      }
    );

    return result;
  }

  /**
   * Translate complex JavaScript expressions to TLA+
   *
   * Handles:
   * - Ternary operators: a ? b : c → IF a THEN b ELSE c
   * - Nullish coalescing: a ?? b → IF a # NULL THEN a ELSE b
   * - Optional chaining: a?.b → IF a # NULL THEN a.b ELSE NULL
   * - Logical short-circuit: a && b → IF a THEN b ELSE FALSE
   */
  private translateComplexExpressions(expr: string, _statePrefix: string): string {
    if (!expr || typeof expr !== "string") {
      return expr || "";
    }

    let result = expr;

    // Phase 1: Handle optional chaining (must come before other operators)
    result = this.translateOptionalChaining(result);

    // Phase 2: Handle nullish coalescing (before ternary to avoid ?? being confused with ?)
    result = this.translateNullishCoalescing(result);

    // Phase 3: Handle ternary operators (after nullish so ?? doesn't interfere)
    result = this.translateTernary(result);

    // Phase 4: Handle logical short-circuit (advanced)
    // Note: && and || are handled later as simple operators
    // This is for special cases where we want IF-THEN-ELSE semantics

    return result;
  }

  /**
   * Translate ternary operator: condition ? trueValue : falseValue
   * → IF condition THEN trueValue ELSE falseValue
   *
   * Handles nested ternaries recursively
   */
  private translateTernary(expr: string): string {
    if (!expr || typeof expr !== "string" || !expr.includes("?")) {
      return expr || "";
    }

    // Match ternary pattern: condition ? true_expr : false_expr
    // Use a simple approach for non-nested ternaries first
    // Pattern: anything ? anything : anything (non-greedy)
    const ternaryRegex = /([^?]+)\?([^:]+):([^:?]+)/;

    let result = expr;
    let match: RegExpMatchArray | null;
    let iterations = 0;
    const maxIterations = 10; // Prevent infinite loops

    // Process ternaries from innermost to outermost (right to left)
    match = result.match(ternaryRegex);
    while (match && iterations < maxIterations) {
      const condition = match[1]?.trim();
      const trueVal = match[2]?.trim();
      const falseVal = match[3]?.trim();

      const tlaIf = `IF ${condition} THEN ${trueVal} ELSE ${falseVal}`;

      // Replace the matched ternary
      if (match[0]) {
        result = result.replace(match[0], tlaIf);
      }
      iterations++;
      match = result.match(ternaryRegex);
    }

    return result;
  }

  /**
   * Translate nullish coalescing: a ?? b → IF a # NULL THEN a ELSE b
   *
   * Note: JavaScript ?? checks for null or undefined, but TLA+ only has NULL
   */
  private translateNullishCoalescing(expr: string): string {
    if (!expr || typeof expr !== "string" || !expr.includes("??")) {
      return expr || "";
    }

    // Match: expr ?? defaultValue
    // Use non-greedy matching to handle multiple ?? in sequence
    const nullishRegex = /([^?]+)\?\?([^?]+)/;

    let result = expr;
    let match: RegExpMatchArray | null;
    let iterations = 0;
    const maxIterations = 10;

    match = result.match(nullishRegex);
    while (match && iterations < maxIterations) {
      const value = match[1]?.trim();
      const defaultVal = match[2]?.trim();

      const tlaIf = `IF ${value} # NULL THEN ${value} ELSE ${defaultVal}`;

      if (match[0]) {
        result = result.replace(match[0], tlaIf);
      }
      iterations++;
      match = result.match(nullishRegex);
    }

    return result;
  }

  /**
   * Translate optional chaining: a?.b?.c → IF a # NULL /\ a.b # NULL THEN a.b.c ELSE NULL
   *
   * Strategy: Convert each ?. to explicit null check iteratively
   * Supports: a?.b, a?.[0], a?.['prop'], chained a?.b?.c
   */
  private translateOptionalChaining(expr: string): string {
    // If no optional chaining, return as-is
    if (!expr.includes("?.")) {
      return expr;
    }

    let result = expr;
    let iteration = 0;
    const maxIterations = 10;
    let previousResult = "";

    // Iteratively process ?. operators until none remain or no changes made
    while (result.includes("?.") && iteration < maxIterations && result !== previousResult) {
      previousResult = result;

      // Pattern 1: identifier?.property (simple property access)
      // Matches: a?.b, user?.name, etc.
      result = result.replace(
        /(\w+(?:\.\w+)*)\?\.(\w+)(?!\?\.)/g,
        (_match, obj, prop) => `IF ${obj} # NULL THEN ${obj}.${prop} ELSE NULL`
      );

      // Pattern 2: (expression)?.property (parenthesized expression)
      // Matches: (a.b.c)?.d, (user)?.name, etc.
      result = result.replace(
        /\(([^)]+)\)\?\.(\w+)/g,
        (_match, expr, prop) => `IF (${expr}) # NULL THEN (${expr}).${prop} ELSE NULL`
      );

      // Pattern 3: identifier?.[index] (bracket notation with number)
      // Matches: items?.[0], arr?.[5], etc.
      // Note: TLA+ uses 1-based indexing, so [0] becomes [1]
      result = result.replace(/(\w+(?:\.\w+)*)\?\.\[(\d+)\]/g, (_match, obj, index) => {
        const tlaIndex = Number.parseInt(index, 10) + 1; // Convert to 1-based
        return `IF ${obj} # NULL THEN ${obj}[${tlaIndex}] ELSE NULL`;
      });

      // Pattern 4: identifier?.['property'] or identifier?.["property"]
      // Matches: obj?.['name'], user?.["id"], etc.
      result = result.replace(
        /(\w+(?:\.\w+)*)\?\.\[['"](\w+)['"]\]/g,
        (_match, obj, prop) => `IF ${obj} # NULL THEN ${obj}.${prop} ELSE NULL`
      );

      iteration++;
    }

    // If ?. still remains after max iterations, warn and return original
    if (result.includes("?.") && iteration >= maxIterations) {
      // Return original rather than partially translated to avoid confusing output
      return expr;
    }

    return result;
  }

  /**
   * Translate string methods to TLA+ operators
   *
   * - str.startsWith(prefix) → SubSeq(str, 1, Len(prefix)) = prefix
   * - str.endsWith(suffix) → SubSeq(str, Len(str) - Len(suffix) + 1, Len(str)) = suffix
   * - str.includes(sub) → \E i \in 1..Len(str) : SubSeq(str, i, i + Len(sub) - 1) = sub
   */
  private translateStringMethods(expr: string): string {
    if (!expr || typeof expr !== "string") {
      return expr || "";
    }

    let result = expr;

    // String.startsWith(prefix)
    result = result.replace(/(\w+(?:\.\w+)*)\.startsWith\(([^)]+)\)/g, (_match, str, prefix) => {
      const trimmedPrefix = prefix.trim();
      return `SubSeq(${str}, 1, Len(${trimmedPrefix})) = ${trimmedPrefix}`;
    });

    // String.endsWith(suffix)
    result = result.replace(/(\w+(?:\.\w+)*)\.endsWith\(([^)]+)\)/g, (_match, str, suffix) => {
      const trimmedSuffix = suffix.trim();
      return `SubSeq(${str}, Len(${str}) - Len(${trimmedSuffix}) + 1, Len(${str})) = ${trimmedSuffix}`;
    });

    // String.includes(substring) - more complex, uses existential quantifier
    result = result.replace(/(\w+(?:\.\w+)*)\.includes\(([^)]+)\)/g, (_match, str, substring) => {
      const trimmedSub = substring.trim();
      return `\\E i \\in 1..Len(${str}) : SubSeq(${str}, i, i + Len(${trimmedSub}) - 1) = ${trimmedSub}`;
    });

    return result;
  }

  private messageTypeToActionName(messageType: string): string {
    // Defensive check: this method should only be called with valid TLA+ identifiers
    // (filtering happens earlier, but this adds an extra layer of safety)
    if (!this.isValidTLAIdentifier(messageType)) {
      // Sanitize by removing all invalid characters and replacing with underscores
      const sanitized = messageType.replace(/[^a-zA-Z0-9_]/g, "_");
      // Ensure it starts with a letter
      const validStart = sanitized.match(/[a-zA-Z]/);
      if (!validStart) {
        // No letters at all, can't create a valid identifier
        return "HandleInvalidMessageType";
      }
      // Use the sanitized version from the first letter onwards
      const validIdentifier = sanitized.slice(sanitized.indexOf(validStart[0]));
      return this.messageTypeToActionName(validIdentifier);
    }

    // Convert USER_LOGIN -> HandleUserLogin
    return `Handle${messageType
      .split("_")
      .map((part) => part.charAt(0).toUpperCase() + part.slice(1).toLowerCase())
      .join("")}`;
  }

  private assignmentValueToTLA(value: string | boolean | number | null): string {
    if (typeof value === "boolean") {
      return value ? "TRUE" : "FALSE";
    }
    if (typeof value === "number") {
      return String(value);
    }
    if (value === null) {
      return "NULL"; // Will need to handle this based on type
    }
    if (typeof value === "string") {
      // Check if this is already a TLA+ expression (compound operator or array mutation)
      // These contain @ (current value reference) or TLA+ operators
      if (this.isTLAExpression(value)) {
        return value; // Return as-is, already in TLA+ format
      }
      return `"${value}"`; // Regular string literal
    }
    return "NULL";
  }

  /**
   * Check if a string value is a TLA+ expression (not a literal string)
   * TLA+ expressions contain:
   * - @ (current value reference for EXCEPT)
   * - TLA+ operators: Append, SubSeq, Tail, Len, Head, etc.
   * - TLA+ syntax: \o (concatenation), << >> (sequences)
   */
  private isTLAExpression(value: string): boolean {
    // Check for @ symbol (used in EXCEPT expressions)
    if (value.includes("@")) {
      return true;
    }

    // Check for TLA+ sequence operators
    const tlaOperators = [
      "Append",
      "SubSeq",
      "Tail",
      "Head",
      "Len",
      "\\o", // Concatenation
      "<<", // Sequence start
      "Cardinality", // Set cardinality
      "CHOOSE", // Choice operator
      "\\E", // Exists quantifier
      "\\A", // Forall quantifier
    ];

    return tlaOperators.some((op) => value.includes(op));
  }

  private addRouteWithHandlers(_config: VerificationConfig, analysis: CodebaseAnalysis): void {
    this.line("\\* =============================================================================");
    this.line("\\* Message Routing with State Transitions");
    this.line("\\* =============================================================================");
    this.line("");

    if (analysis.handlers.length === 0) {
      // No handlers, just use base routing
      return;
    }

    this.line("\\* Route a message and invoke its handler");
    this.line("UserRouteMessage(msgIndex) ==");
    this.indent++;
    this.line("/\\ msgIndex \\in 1..Len(messages)");
    this.line("/\\ LET msg == messages[msgIndex]");
    this.line('   IN /\\ msg.status = "pending"');
    this.line("      /\\ routingDepth' = routingDepth + 1");
    this.line("      /\\ routingDepth < 5");
    this.line("      /\\ \\E target \\in msg.targets :");
    this.line('            /\\ IF target \\in Contexts /\\ ports[target] = "connected"');
    this.line("               THEN \\* Successful delivery - route AND invoke handler");
    this.line(
      '                    /\\ messages\' = [messages EXCEPT ![msgIndex].status = "delivered"]'
    );
    this.line("                    /\\ delivered' = delivered \\union {msg.id}");
    this.line(
      "                    /\\ pendingRequests' = [id \\in DOMAIN pendingRequests \\ {msg.id} |->"
    );
    this.line("                                           pendingRequests[id]]");
    this.line("                    /\\ time' = time + 1");
    this.line("                    /\\ StateTransition(target, msg.msgType)");
    this.line("               ELSE \\* Port not connected - message fails");
    this.line(
      '                    /\\ messages\' = [messages EXCEPT ![msgIndex].status = "failed"]'
    );
    this.line(
      "                    /\\ pendingRequests' = [id \\in DOMAIN pendingRequests \\ {msg.id} |->"
    );
    this.line("                                           pendingRequests[id]]");
    this.line("                    /\\ time' = time + 1");
    this.line("                    /\\ UNCHANGED <<delivered, contextStates>>");
    this.line("      /\\ UNCHANGED ports");
    this.indent--;
    this.line("");
  }

  private addNext(_config: VerificationConfig, analysis: CodebaseAnalysis): void {
    this.line("\\* Next state relation (extends MessageRouter)");
    this.line("UserNext ==");
    this.indent++;

    // Check if there are any valid handlers (not just any handlers)
    const hasValidHandlers = analysis.handlers.some((h) =>
      this.isValidTLAIdentifier(h.messageType)
    );

    if (hasValidHandlers) {
      // Use integrated routing + handlers
      this.line("\\/ \\E c \\in Contexts : ConnectPort(c) /\\ UNCHANGED contextStates");
      this.line("\\/ \\E c \\in Contexts : DisconnectPort(c) /\\ UNCHANGED contextStates");
      this.line(
        "\\/ \\E src \\in Contexts : \\E targetSet \\in (SUBSET Contexts \\ {{}}) : \\E tab \\in 0..MaxTabId : \\E msgType \\in UserMessageTypes :"
      );
      this.indent++;
      this.line("SendMessage(src, targetSet, tab, msgType) /\\ UNCHANGED contextStates");
      this.indent--;
      this.line("\\/ \\E i \\in 1..Len(messages) : UserRouteMessage(i)");
      this.line("\\/ CompleteRouting /\\ UNCHANGED contextStates");
      this.line("\\/ \\E i \\in 1..Len(messages) : TimeoutMessage(i) /\\ UNCHANGED contextStates");
    } else {
      // No valid handlers, all actions preserve contextStates
      this.line("\\/ Next /\\ UNCHANGED contextStates");
    }

    this.indent--;
    this.line("");
  }

  private addSpec(): void {
    this.line("\\* Specification");
    this.line("UserSpec == UserInit /\\ [][UserNext]_allVars /\\ WF_allVars(UserNext)");
    this.line("");
  }

  private addInvariants(config: VerificationConfig, _analysis: CodebaseAnalysis): void {
    this.line("\\* =============================================================================");
    this.line("\\* Application Invariants");
    this.line("\\* =============================================================================");
    this.line("");

    this.line("\\* TypeOK and NoRoutingLoops are inherited from MessageRouter");
    this.line("");

    this.line("\\* Application state type invariant");
    this.line("UserStateTypeInvariant ==");
    this.indent++;
    this.line("\\A ctx \\in Contexts :");
    this.indent++;
    this.line("contextStates[ctx] \\in State");
    this.indent--;
    this.indent--;
    this.line("");

    // Add extracted invariants from JSDoc
    if (this.extractedInvariants.length > 0) {
      this.line("\\* Extracted invariants from code annotations");
      this.line("");

      const invGenerator = new InvariantGenerator();
      const tlaInvariants = invGenerator.generateTLAInvariants(this.extractedInvariants, (expr) =>
        this.tsExpressionToTLA(expr, false)
      );

      for (const invDef of tlaInvariants) {
        this.line(invDef);
        this.line("");
      }
    }

    // Add Tier 2 Optimization: Temporal constraints
    if (config.tier2?.temporalConstraints && config.tier2.temporalConstraints.length > 0) {
      this.addTemporalConstraints(config.tier2.temporalConstraints);
    }

    this.line("\\* State constraint to bound state space");
    this.addStateConstraint(config);

    this.line("=============================================================================");
  }

  /**
   * Add temporal constraint invariants (Tier 2 optimization)
   */
  private addTemporalConstraints(constraints: Array<{before: string; after: string; description?: string}>): void {
    this.line("\\* Tier 2: Temporal constraint invariants");
    this.line("\\* Enforce ordering requirements between message types");
    this.line("");

    for (let i = 0; i < constraints.length; i++) {
      const constraint = constraints[i];
      const invName = `TemporalConstraint${i + 1}`;

      if (constraint.description) {
        this.line(`\\* ${constraint.description}`);
      }
      this.line(`${invName} ==`);
      this.indent++;
      this.line(`\\* If ${constraint.after} has been delivered, then ${constraint.before} must have been delivered`);
      this.line(`(\\E m \\in DOMAIN delivered : delivered[m].type = "${constraint.after}")`);
      this.line("=>");
      this.line(`(\\E m \\in DOMAIN delivered : delivered[m].type = "${constraint.before}")`);
      this.indent--;
      this.line("");

      // Track this invariant for config generation
      this.extractedInvariants.push({
        name: invName,
        description: constraint.description || `${constraint.before} must happen before ${constraint.after}`,
        condition: '',
        confidence: 'high',
        source: { file: '', line: 0, column: 0 }
      });
    }
  }

  /**
   * Generate StateConstraint with per-message bounds support (Tier 1 optimization)
   * and bounded exploration (Tier 2 optimization)
   */
  private addStateConstraint(config: VerificationConfig): void {
    const hasPerMessageBounds = config.messages.perMessageBounds &&
                                 Object.keys(config.messages.perMessageBounds).length > 0;
    const hasBoundedExploration = config.tier2?.boundedExploration?.maxDepth !== undefined;

    const needsConjunction = hasPerMessageBounds || hasBoundedExploration;

    this.line("StateConstraint ==");
    this.indent++;

    if (needsConjunction) {
      // Multiple constraints
      this.line("/\\ Len(messages) <= MaxMessages");

      // Tier 1: Per-message bounds
      if (hasPerMessageBounds) {
        for (const [msgType, _bound] of Object.entries(config.messages.perMessageBounds)) {
          const constName = `MaxMessages_${msgType}`;
          this.line(`/\\ Cardinality({m \\in DOMAIN messages : messages[m].type = "${msgType}"}) <= ${constName}`);
        }
      }

      // Tier 2: Bounded exploration (depth limit)
      if (hasBoundedExploration && config.tier2?.boundedExploration?.maxDepth) {
        this.line(`/\\ TLCGet("level") <= ${config.tier2.boundedExploration.maxDepth} \\* Tier 2: Bounded exploration`);
      }
    } else {
      // Simple global bound only
      this.line("Len(messages) <= MaxMessages");
    }

    this.indent--;
    this.line("");

    // Log bounded exploration
    if (hasBoundedExploration && config.tier2?.boundedExploration?.maxDepth) {
      console.log(
        `[INFO] [TLAGenerator] Tier 2: Bounded exploration with maxDepth = ${config.tier2.boundedExploration.maxDepth}`
      );
    }
  }

  /**
   * Add delivered tracking variables for temporal properties
   */
  private addDeliveredTracking(): void {
    this.line("");
    const tempGenerator = new TemporalTLAGenerator();
    const deliveredVars = tempGenerator.generateDeliveredVariables();
    this.line(deliveredVars);
    this.line("");
  }

  /**
   * Add temporal property definitions
   */
  private addTemporalProperties(): void {
    this.line("\\* =============================================================================");
    this.line("\\* Temporal Properties");
    this.line("\\* =============================================================================");
    this.line("");

    const tempGenerator = new TemporalTLAGenerator();
    const tlaProperties = tempGenerator.generateTLAProperties(this.temporalProperties);

    for (const propDef of tlaProperties) {
      this.line(propDef);
      this.line("");
    }

    this.line("=============================================================================");
  }

  private fieldConfigToTLAType(
    _fieldPath: string,
    fieldConfig: FieldConfig,
    _config: VerificationConfig
  ): string {
    // Try each type pattern in order
    const typeResult =
      this.tryBooleanType(fieldConfig) ||
      this.tryEnumType(fieldConfig) ||
      this.tryArrayType(fieldConfig) ||
      this.tryNumberType(fieldConfig) ||
      this.tryStringType(fieldConfig) ||
      this.tryMapType(fieldConfig);

    return typeResult || "Value";
  }

  /**
   * Try to match boolean type pattern
   */
  private tryBooleanType(fieldConfig: FieldConfig): string | null {
    if ("type" in fieldConfig && fieldConfig.type === "boolean") {
      return "BOOLEAN";
    }
    return null;
  }

  /**
   * Try to match enum type pattern
   */
  private tryEnumType(fieldConfig: FieldConfig): string | null {
    if ("type" in fieldConfig && fieldConfig.type === "enum" && fieldConfig.values) {
      const values = fieldConfig.values.map((v: string) => `"${v}"`).join(", ");
      return `{${values}}`;
    }
    return null;
  }

  /**
   * Try to match array type pattern
   */
  private tryArrayType(fieldConfig: FieldConfig): string | null {
    if ("maxLength" in fieldConfig) {
      return "Seq(Value)";
    }
    return null;
  }

  /**
   * Try to match number type pattern
   */
  private tryNumberType(fieldConfig: FieldConfig): string | null {
    if ("min" in fieldConfig && "max" in fieldConfig) {
      const min = fieldConfig.min || 0;
      const max = fieldConfig.max || 100;
      return `${min}..${max}`;
    }
    return null;
  }

  /**
   * Try to match string type pattern
   */
  private tryStringType(fieldConfig: FieldConfig): string | null {
    if (!("values" in fieldConfig)) return null;

    if (fieldConfig.values && Array.isArray(fieldConfig.values)) {
      const values = fieldConfig.values.map((v: string) => `"${v}"`).join(", ");
      return `{${values}}`;
    }

    return "STRING";
  }

  /**
   * Try to match map type pattern
   */
  private tryMapType(fieldConfig: FieldConfig): string | null {
    if ("maxSize" in fieldConfig) {
      return "[Keys -> Value]";
    }
    return null;
  }

  private getInitialValueFromAnalysis(fieldAnalysis: FieldAnalysis): string {
    const typeInfo = fieldAnalysis.type;

    switch (typeInfo.kind) {
      case "boolean":
        return "FALSE";
      case "string":
        return this.getInitialStringValue(typeInfo, fieldAnalysis.bounds);
      case "number":
        return this.getInitialNumberValue(fieldAnalysis.bounds);
      case "enum":
        return this.getInitialEnumValue(typeInfo);
      case "array":
        return "<<>>";
      case "set":
        return "{}";
      case "map":
        return "[x \\in {} |-> NULL]";
      case "object":
        return "NULL";
      case "null":
        return "NULL";
      case "union":
        return this.getInitialUnionValue(typeInfo, fieldAnalysis);
      default:
        return "NULL";
    }
  }

  /**
   * Get initial value for string type
   */
  private getInitialStringValue(
    typeInfo: { enumValues?: string[] },
    bounds?: { values?: string[] }
  ): string {
    if (typeInfo.enumValues && typeInfo.enumValues.length > 0) {
      return `"${typeInfo.enumValues[0]}"`;
    }
    if (bounds?.values && bounds.values.length > 0) {
      return `"${bounds.values[0]}"`;
    }
    return '""';
  }

  /**
   * Get initial value for number type
   */
  private getInitialNumberValue(bounds?: { min?: number }): string {
    if (bounds?.min !== undefined) {
      return `${bounds.min}`;
    }
    return "0";
  }

  /**
   * Get initial value for enum type
   */
  private getInitialEnumValue(typeInfo: { enumValues?: string[] }): string {
    if (typeInfo.enumValues && typeInfo.enumValues.length > 0) {
      return `"${typeInfo.enumValues[0]}"`;
    }
    return '""';
  }

  /**
   * Get initial value for union type
   */
  private getInitialUnionValue(
    typeInfo: { unionTypes?: Array<{ kind: string }> },
    fieldAnalysis: FieldAnalysis
  ): string {
    if (typeInfo.unionTypes && typeInfo.unionTypes.length > 0) {
      const firstType =
        typeInfo.unionTypes.find((t) => t.kind !== "null") || typeInfo.unionTypes[0];
      return this.getInitialValueFromAnalysis({
        ...fieldAnalysis,
        type: firstType as FieldAnalysis["type"],
      });
    }
    return "NULL";
  }

  private inferTLATypeFromAnalysis(fieldAnalysis: FieldAnalysis): string {
    const typeInfo = fieldAnalysis.type;

    // Handle nullable types
    const makeNullable = (baseType: string): string => {
      return typeInfo.nullable ? `${baseType} \\union {NULL}` : baseType;
    };

    // Convert TypeKind to TLA+ type
    switch (typeInfo.kind) {
      case "boolean":
        return makeNullable("BOOLEAN");

      case "string":
        // Check if there are enum values
        if (typeInfo.enumValues && typeInfo.enumValues.length > 0) {
          const values = typeInfo.enumValues.map((v) => `"${v}"`).join(", ");
          return makeNullable(`{${values}}`);
        }
        // Check bounds for bounded strings
        if (fieldAnalysis.bounds?.values && fieldAnalysis.bounds.values.length > 0) {
          const values = fieldAnalysis.bounds.values.map((v) => `"${v}"`).join(", ");
          return makeNullable(`{${values}}`);
        }
        return makeNullable("STRING");

      case "number":
        // Check for numeric bounds
        if (fieldAnalysis.bounds?.min !== undefined && fieldAnalysis.bounds?.max !== undefined) {
          return makeNullable(`${fieldAnalysis.bounds.min}..${fieldAnalysis.bounds.max}`);
        }
        return makeNullable("Int");

      case "enum":
        if (typeInfo.enumValues && typeInfo.enumValues.length > 0) {
          const values = typeInfo.enumValues.map((v) => `"${v}"`).join(", ");
          return makeNullable(`{${values}}`);
        }
        return makeNullable("STRING");

      case "array":
        // Sequence type
        if (typeInfo.elementType) {
          // For now, use simplified Value type
          return makeNullable("Seq(Value)");
        }
        return makeNullable("Seq(Value)");

      case "set":
        // Set type
        return makeNullable("SUBSET Value");

      case "map":
        // Function type (TLA+ records/functions)
        return makeNullable("[Keys -> Value]");

      case "object":
        // For nested objects, we'd need recursive handling
        // For now, use generic Value
        return makeNullable("Value");

      case "union":
        // For unions, try to find a common representation
        // For now, use generic Value
        return makeNullable("Value");

      case "null":
        return "NULL";
      default:
        return "Value";
    }
  }

  private getInitialValue(fieldConfig: FieldConfig): string {
    if ("type" in fieldConfig) {
      if (fieldConfig.type === "boolean") {
        return "FALSE";
      }
      if (fieldConfig.type === "enum" && fieldConfig.values && fieldConfig.values.length > 0) {
        return `"${fieldConfig.values[0]}"`;
      }
    }

    if ("maxLength" in fieldConfig) {
      return "<<>>"; // Empty sequence
    }

    if ("min" in fieldConfig) {
      return String(fieldConfig.min || 0);
    }

    if ("values" in fieldConfig && fieldConfig.values && fieldConfig.values.length > 0) {
      return `"${fieldConfig.values[0]}"`;
    }

    if ("maxSize" in fieldConfig) {
      // Map with all keys mapped to default value
      return '[k \\in Keys |-> "v1"]';
    }

    return "0"; // Default fallback
  }

  private fieldToConstName(fieldPath: string): string {
    return fieldPath.replace(/\./g, "_").toUpperCase();
  }

  private sanitizeFieldName(fieldPath: string): string {
    return fieldPath.replace(/\./g, "_");
  }

  private line(content: string): void {
    if (content === "") {
      this.lines.push("");
    } else {
      const indentation = "  ".repeat(this.indent);
      this.lines.push(indentation + content);
    }
  }
}

export async function generateTLA(
  config: VerificationConfig,
  analysis: CodebaseAnalysis
): Promise<{ spec: string; cfg: string; validation?: ValidationReport }> {
  const generator = new TLAGenerator();
  return await generator.generate(config, analysis);
}
