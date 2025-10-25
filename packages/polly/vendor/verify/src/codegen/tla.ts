// TLA+ specification generator

import type { VerificationConfig, CodebaseAnalysis } from "../types";
import type { MessageHandler } from "../core/model";

export class TLAGenerator {
  private lines: string[] = [];
  private indent = 0;

  generate(
    config: VerificationConfig,
    analysis: CodebaseAnalysis
  ): {
    spec: string;
    cfg: string;
  } {
    this.lines = [];
    this.indent = 0;

    const spec = this.generateSpec(config, analysis);
    const cfg = this.generateConfig(config, analysis);

    return { spec, cfg };
  }

  private generateSpec(config: VerificationConfig, analysis: CodebaseAnalysis): string {
    this.lines = [];
    this.indent = 0;

    this.addHeader();
    this.addExtends();
    this.addConstants(config, analysis);
    this.addMessageTypes(config, analysis);
    this.addStateType(config, analysis);
    this.addVariables();
    this.addInit(config, analysis);
    this.addActions(config, analysis);
    this.addRouteWithHandlers(config, analysis);
    this.addNext(config, analysis);
    this.addSpec();
    this.addInvariants(config, analysis);

    return this.lines.join("\n");
  }

  private generateConfig(config: VerificationConfig, analysis: CodebaseAnalysis): string {
    const lines: string[] = [];

    lines.push("SPECIFICATION UserSpec");
    lines.push("");
    lines.push("\\* Constants");
    lines.push("CONSTANTS");

    // Generate context set (reduced for faster verification)
    lines.push("  Contexts = {background, content, popup}");

    // Message bounds (defaults chosen for reasonable verification time)
    lines.push(`  MaxMessages = ${config.messages.maxInFlight || 3}`);
    lines.push(`  MaxTabId = ${config.messages.maxTabs || 1}`);
    lines.push("  TimeoutLimit = 3");

    // State bounds from config
    for (const [field, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig === "object" && fieldConfig !== null) {
        if ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) {
          const constName = this.fieldToConstName(field);
          lines.push(`  ${constName}_MaxLength = ${fieldConfig.maxLength}`);
        }
        if ("max" in fieldConfig && fieldConfig.max !== null) {
          const constName = this.fieldToConstName(field);
          lines.push(`  ${constName}_Max = ${fieldConfig.max}`);
        }
        if ("maxSize" in fieldConfig && fieldConfig.maxSize !== null) {
          const constName = this.fieldToConstName(field);
          lines.push(`  ${constName}_MaxSize = ${fieldConfig.maxSize}`);
        }
      }
    }

    lines.push("");
    lines.push("\\* Invariants to check");
    lines.push("INVARIANTS");
    lines.push("  TypeOK");
    lines.push("  NoRoutingLoops");
    lines.push("  UserStateTypeInvariant");
    lines.push("");
    lines.push("\\* State constraint");
    lines.push("CONSTRAINT");
    lines.push("  StateConstraint");

    return lines.join("\n");
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

  private addConstants(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    // MessageRouter already defines: Contexts, MaxMessages, MaxTabId, TimeoutLimit
    // We only add application-specific constants

    const hasCustomConstants = Object.entries(config.state).some(([field, fieldConfig]) => {
      if (typeof fieldConfig !== "object" || fieldConfig === null) return false;
      return (
        ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) ||
        ("max" in fieldConfig && fieldConfig.max !== null) ||
        ("maxSize" in fieldConfig && fieldConfig.maxSize !== null)
      );
    });

    if (!hasCustomConstants) {
      // No custom constants needed
      return;
    }

    this.line("\\* Application-specific constants");
    this.line("CONSTANTS");
    this.indent++;

    let first = true;
    for (const [field, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig === "object" && fieldConfig !== null) {
        const constName = this.fieldToConstName(field);

        if ("maxLength" in fieldConfig && fieldConfig.maxLength !== null) {
          this.line(`${first ? "" : ","}${constName}_MaxLength  \\* Max length for ${field}`);
          first = false;
        }
        if ("max" in fieldConfig && fieldConfig.max !== null) {
          this.line(`${first ? "" : ","}${constName}_Max       \\* Max value for ${field}`);
          first = false;
        }
        if ("maxSize" in fieldConfig && fieldConfig.maxSize !== null) {
          this.line(`${first ? "" : ","}${constName}_MaxSize   \\* Max size for ${field}`);
          first = false;
        }
      }
    }

    this.indent--;
    this.line("");
  }

  private addStateType(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    // Define Value type for generic sequences and maps
    // Use a finite set for model checking
    this.line("\\* Generic value type for sequences and maps");
    this.line("\\* Bounded to allow model checking");
    this.line('Value == {"v1", "v2", "v3"}');
    this.line("");

    // Define Keys type for map domains
    this.line("\\* Generic key type for maps");
    this.line("\\* Bounded to allow model checking");
    this.line('Keys == {"k1", "k2", "k3"}');
    this.line("");

    this.line("\\* Application state type definition");
    this.line("State == [");
    this.indent++;

    const stateFields: string[] = [];

    for (const [fieldPath, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const fieldName = this.sanitizeFieldName(fieldPath);
      const tlaType = this.fieldConfigToTLAType(fieldPath, fieldConfig, config);

      stateFields.push(`${fieldName}: ${tlaType}`);
    }

    for (let i = 0; i < stateFields.length; i++) {
      const field = stateFields[i];
      const suffix = i < stateFields.length - 1 ? "," : "";
      this.line(`${field}${suffix}`);
    }

    this.indent--;
    this.line("]");
    this.line("");
  }

  private addMessageTypes(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    if (analysis.messageTypes.length === 0) {
      // No message types found, skip
      return;
    }

    this.line("\\* Message types from application");
    const messageTypeSet = analysis.messageTypes.map((t) => `"${t}"`).join(", ");
    this.line(`UserMessageTypes == {${messageTypeSet}}`);
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

  private addInit(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    // Generate InitialState first
    this.line("\\* Initial application state");
    this.line("InitialState == [");
    this.indent++;

    const fields: string[] = [];
    for (const [fieldPath, fieldConfig] of Object.entries(config.state)) {
      if (typeof fieldConfig !== "object" || fieldConfig === null) continue;

      const fieldName = this.sanitizeFieldName(fieldPath);
      const initialValue = this.getInitialValue(fieldConfig);
      fields.push(`${fieldName} |-> ${initialValue}`);
    }

    for (let i = 0; i < fields.length; i++) {
      const field = fields[i];
      const suffix = i < fields.length - 1 ? "," : "";
      this.line(`${field}${suffix}`);
    }

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

  private addActions(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    this.line("\\* =============================================================================");
    this.line("\\* Application-specific actions");
    this.line("\\* =============================================================================");
    this.line("");

    if (analysis.handlers.length === 0) {
      // No handlers found, keep the stub
      this.line("\\* No message handlers found in codebase");
      this.line("\\* State remains unchanged for all messages");
      this.line("StateTransition(ctx, msgType) ==");
      this.indent++;
      this.line("UNCHANGED contextStates");
      this.indent--;
      this.line("");
      return;
    }

    // Generate state transition actions for each handler
    this.line("\\* State transitions extracted from message handlers");
    this.line("");

    // Group handlers by message type
    const handlersByType = new Map<string, typeof analysis.handlers>();
    for (const handler of analysis.handlers) {
      if (!handlersByType.has(handler.messageType)) {
        handlersByType.set(handler.messageType, []);
      }
      handlersByType.get(handler.messageType)!.push(handler);
    }

    // Generate an action for each message type
    for (const [messageType, handlers] of handlersByType.entries()) {
      this.generateHandlerAction(messageType, handlers, config);
    }

    // Generate the main StateTransition action that dispatches to specific handlers
    this.line("\\* Main state transition action");
    this.line("StateTransition(ctx, msgType) ==");
    this.indent++;

    const messageTypes = Array.from(handlersByType.keys());
    for (let i = 0; i < messageTypes.length; i++) {
      const msgType = messageTypes[i];
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

    // Collect all preconditions from all handlers
    const allPreconditions = handlers.flatMap((h) => h.preconditions);

    // Collect all assignments from all handlers for this message type
    const allAssignments = handlers.flatMap((h) => h.assignments);

    // Collect all postconditions from all handlers
    const allPostconditions = handlers.flatMap((h) => h.postconditions);

    // Emit preconditions first
    if (allPreconditions.length > 0) {
      for (const precondition of allPreconditions) {
        const tlaExpr = this.tsExpressionToTLA(precondition.expression);
        const comment = precondition.message ? ` \\* ${precondition.message}` : "";
        this.line(`/\\ ${tlaExpr}${comment}`);
      }
    }

    // Filter out null assignments and map them to valid values
    const validAssignments = allAssignments
      .filter((a) => {
        if (a.value === null) {
          // For null values, check if we can map to a valid value based on field config
          const fieldConfig = config.state[a.field];
          if (
            fieldConfig &&
            typeof fieldConfig === "object" &&
            "values" in fieldConfig &&
            fieldConfig.values
          ) {
            // Use the last value as the "null" value (often "guest", "none", etc.)
            return true;
          }
          // Skip null assignments if we can't map them
          return false;
        }
        return true;
      })
      .map((a) => {
        if (a.value === null) {
          const fieldConfig = config.state[a.field];
          if (
            fieldConfig &&
            typeof fieldConfig === "object" &&
            "values" in fieldConfig &&
            fieldConfig.values
          ) {
            // Use the last value as the "null" value
            const nullValue = fieldConfig.values[fieldConfig.values.length - 1];
            return { ...a, value: nullValue };
          }
        }
        return a;
      });

    if (validAssignments.length === 0) {
      // Handler exists but makes no state changes
      if (allPreconditions.length === 0) {
        this.line("\\* No state changes in handler");
      }
      this.line("/\\ UNCHANGED contextStates");
    } else {
      // Generate state updates
      this.line("/\\ contextStates' = [contextStates EXCEPT");
      this.indent++;

      for (let i = 0; i < validAssignments.length; i++) {
        const assignment = validAssignments[i];
        const fieldName = this.sanitizeFieldName(assignment.field);
        const value = this.assignmentValueToTLA(assignment.value);
        const suffix = i < validAssignments.length - 1 ? "," : "";

        this.line(`![ctx].${fieldName} = ${value}${suffix}`);
      }

      this.indent--;
      this.line("]");
    }

    // Emit postconditions last
    if (allPostconditions.length > 0) {
      for (const postcondition of allPostconditions) {
        const tlaExpr = this.tsExpressionToTLA(postcondition.expression, true);
        const comment = postcondition.message ? ` \\* ${postcondition.message}` : "";
        this.line(`/\\ ${tlaExpr}${comment}`);
      }
    }

    this.indent--;
    this.line("");
  }

  /**
   * Translate TypeScript expression to TLA+ syntax
   * @param expr - TypeScript expression from requires() or ensures()
   * @param isPrimed - If true, use contextStates' (for postconditions)
   */
  private tsExpressionToTLA(expr: string, isPrimed: boolean = false): string {
    let tla = expr;

    // Replace state references with contextStates[ctx] or contextStates'[ctx]
    const statePrefix = isPrimed ? "contextStates'[ctx]" : "contextStates[ctx]";

    // Replace state.field.subfield with contextStates[ctx].field_subfield
    tla = tla.replace(/state\.([a-zA-Z_][a-zA-Z0-9_.]*)/g, (match, path) => {
      return `${statePrefix}.${this.sanitizeFieldName(path)}`;
    });

    // Replace payload.field with payload.field (no change needed, but sanitize)
    tla = tla.replace(/payload\.([a-zA-Z_][a-zA-Z0-9_.]*)/g, (match, path) => {
      return `payload.${this.sanitizeFieldName(path)}`;
    });

    // Replace comparison operators
    tla = tla.replace(/===/g, "=");
    tla = tla.replace(/!==/g, "#");
    tla = tla.replace(/!=/g, "#");
    tla = tla.replace(/==/g, "=");

    // Replace logical operators
    tla = tla.replace(/&&/g, "/\\");
    tla = tla.replace(/\|\|/g, "\\/");

    // Replace negation operator (careful with !== already handled)
    // Match ! that's not part of !== or !=
    tla = tla.replace(/!([^=])/g, "~$1");
    tla = tla.replace(/!$/g, "~"); // Handle ! at end of string

    // Replace boolean literals
    tla = tla.replace(/\btrue\b/g, "TRUE");
    tla = tla.replace(/\bfalse\b/g, "FALSE");

    // Replace null
    tla = tla.replace(/\bnull\b/g, "NULL");

    // Replace less than / greater than comparisons
    tla = tla.replace(/</g, "<");
    tla = tla.replace(/>/g, ">");
    tla = tla.replace(/<=/g, "<=");
    tla = tla.replace(/>=/g, ">=");

    return tla;
  }

  private messageTypeToActionName(messageType: string): string {
    // Convert USER_LOGIN -> HandleUserLogin
    return (
      "Handle" +
      messageType
        .split("_")
        .map((part) => part.charAt(0).toUpperCase() + part.slice(1).toLowerCase())
        .join("")
    );
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
      return `"${value}"`;
    }
    return "NULL";
  }

  private addRouteWithHandlers(config: VerificationConfig, analysis: CodebaseAnalysis): void {
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

  private addNext(config: VerificationConfig, analysis: CodebaseAnalysis): void {
    this.line("\\* Next state relation (extends MessageRouter)");
    this.line("UserNext ==");
    this.indent++;

    if (analysis.handlers.length > 0) {
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
      // No handlers, all actions preserve contextStates
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

  private addInvariants(config: VerificationConfig, analysis: CodebaseAnalysis): void {
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

    this.line("\\* State constraint to bound state space");
    this.line("StateConstraint ==");
    this.indent++;
    this.line("Len(messages) <= MaxMessages");
    this.indent--;
    this.line("");

    this.line("=============================================================================");
  }

  private fieldConfigToTLAType(
    fieldPath: string,
    fieldConfig: any,
    config: VerificationConfig
  ): string {
    if ("type" in fieldConfig) {
      if (fieldConfig.type === "boolean") {
        return "BOOLEAN";
      }
      if (fieldConfig.type === "enum" && fieldConfig.values) {
        const values = fieldConfig.values.map((v: string) => `"${v}"`).join(", ");
        return `{${values}}`;
      }
    }

    if ("maxLength" in fieldConfig) {
      // Array type - represented as sequence with bounded length
      const constName = this.fieldToConstName(fieldPath);
      return `Seq(Value)`; // Simplified - would need element type
    }

    if ("min" in fieldConfig && "max" in fieldConfig) {
      // Number type
      const constName = this.fieldToConstName(fieldPath);
      const min = fieldConfig.min || 0;
      const max = fieldConfig.max || 100;
      return `${min}..${max}`;
    }

    if ("values" in fieldConfig) {
      if (fieldConfig.values && Array.isArray(fieldConfig.values)) {
        // String with concrete values
        const values = fieldConfig.values.map((v: string) => `"${v}"`).join(", ");
        return `{${values}}`;
      }
      if (fieldConfig.abstract) {
        // Abstract string
        return "STRING";
      }
      // Needs configuration
      return "STRING";
    }

    if ("maxSize" in fieldConfig) {
      // Map with bounded key set
      return "[Keys -> Value]";
    }

    return "Value"; // Generic fallback
  }

  private getInitialValue(fieldConfig: any): string {
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

export function generateTLA(
  config: VerificationConfig,
  analysis: CodebaseAnalysis
): { spec: string; cfg: string } {
  const generator = new TLAGenerator();
  return generator.generate(config, analysis);
}
