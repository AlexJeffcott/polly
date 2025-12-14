// Structurizr DSL generator

import type { ArchitectureAnalysis } from "../../analysis/src";
import type {
	StructurizrDSLOptions as EnhancedDSLOptions,
	ElementStyle,
	RelationshipStyle,
	ComponentProperties,
	ComponentRelationship,
	ComponentGroup,
	DynamicDiagram,
	DeploymentNode,
	ContainerInstance,
} from "../types/structurizr";
import {
	DEFAULT_ELEMENT_STYLES,
	DEFAULT_RELATIONSHIP_STYLES,
	DEFAULT_THEME,
} from "../types/structurizr";

// Re-export the enhanced type
export type { EnhancedDSLOptions as StructurizrDSLOptions };
export type StructurizrDSLOptions = EnhancedDSLOptions;

export class StructurizrDSLGenerator {
  private analysis: ArchitectureAnalysis;
  private options: StructurizrDSLOptions;

  constructor(analysis: ArchitectureAnalysis, options: StructurizrDSLOptions = {}) {
    this.analysis = analysis;
    this.options = {
      includeDynamicDiagrams: true,
      includeComponentDiagrams: true,
      componentDiagramContexts: ["background"],
      includeDefaultStyles: true,
      relationships: [],
      properties: {},
      groups: [],
      dynamicDiagrams: [],
      perspectives: {},
      deploymentNodes: [],
      ...options,
      styles: {
        theme: options.styles?.theme || DEFAULT_THEME,
        elements: {
          ...DEFAULT_ELEMENT_STYLES,
          ...options.styles?.elements,
        },
        relationships: {
          ...DEFAULT_RELATIONSHIP_STYLES,
          ...options.styles?.relationships,
        },
      },
    };
  }

  /**
   * Generate complete Structurizr DSL
   */
  generate(): string {
    const parts: string[] = [];

    parts.push(this.generateWorkspaceHeader());
    parts.push(this.generateModel());
    parts.push(this.generateViews());
    parts.push(this.generateWorkspaceFooter());

    return parts.join("\n\n");
  }

  /**
   * Generate workspace header
   */
  private generateWorkspaceHeader(): string {
    const { name, description } = this.analysis.system;

    const parts = [`workspace "${this.escape(name)}" "${this.escape(description || "")}" {`];
    parts.push("");
    parts.push("  !identifiers hierarchical");

    // Add ADRs if present
    if (this.analysis.adrs && this.analysis.adrs.adrs.length > 0) {
      parts.push("  !adrs " + this.analysis.adrs.directory);
    }

    return parts.join("\n");
  }

  /**
   * Generate workspace footer
   */
  private generateWorkspaceFooter(): string {
    return "}";
  }

  /**
   * Generate model section
   */
  private generateModel(): string {
    const parts: string[] = [];

    parts.push("  model {");
    parts.push(this.generatePeople());
    parts.push(this.generateExternalSystems());
    parts.push(this.generateMainSystem());

    // Add deployment environments if configured
    if (this.options.deploymentNodes && this.options.deploymentNodes.length > 0) {
      parts.push(this.generateDeploymentEnvironments());
    }

    parts.push("  }");

    return parts.join("\n\n");
  }

  /**
   * Generate people/actors
   */
  private generatePeople(): string {
    return `    user = person "User" "Extension user"`;
  }

  /**
   * Generate external systems
   */
  private generateExternalSystems(): string {
    const parts: string[] = [];

    for (const integration of this.analysis.integrations) {
      if (integration.type === "api" || integration.type === "websocket") {
        const tech =
          integration.technology || (integration.type === "websocket" ? "WebSocket" : "REST API");
        let desc = integration.description || "";

        // Generate better description from API calls if available
        if (!desc && integration.calls && integration.calls.length > 0) {
          const endpoints = integration.calls
            .slice(0, 3)
            .map((c) => c.endpoint)
            .join(", ");
          const methods = [...new Set(integration.calls.map((c) => c.method))].join(", ");
          desc = `External API with endpoints: ${endpoints}. Methods: ${methods}`;
        }

        parts.push(
          `    ${this.toId(integration.name)} = softwareSystem "${this.escape(integration.name)}" "${this.escape(desc)}" {`
        );
        parts.push(
          `      tags "External System" "${integration.type === "websocket" ? "WebSocket" : "REST API"}"`
        );
        parts.push(`    }`);
      }
    }

    return parts.join("\n");
  }

  /**
   * Generate main system (the extension)
   */
  private generateMainSystem(): string {
    const parts: string[] = [];

    parts.push(`    extension = softwareSystem "${this.escape(this.analysis.system.name)}" {`);

    // Generate containers (contexts)
    for (const [contextType, contextInfo] of Object.entries(this.analysis.contexts)) {
      parts.push(this.generateContainer(contextType, contextInfo));
    }

    // Generate relationships between containers
    parts.push(this.generateContainerRelationships());

    parts.push("    }");

    return parts.join("\n\n");
  }

  /**
   * Generate container (context)
   */
  private generateContainer(contextType: string, contextInfo: any): string {
    const parts: string[] = [];

    const technology = this.getContextTechnology(contextType);
    const description = contextInfo.description || `${this.capitalize(contextType)} context`;

    parts.push(
      `      ${contextType} = container "${this.capitalize(contextType)}" "${this.escape(description)}" "${technology}" {`
    );

    // Generate components if enabled
    if (
      this.options.includeComponentDiagrams &&
      this.options.componentDiagramContexts?.includes(contextType)
    ) {
      parts.push(this.generateComponents(contextType, contextInfo));
      parts.push("");
      parts.push(this.generateComponentRelationships(contextType, contextInfo));
    }

    parts.push("      }");

    return parts.join("\n");
  }

  /**
   * Generate components within a container
   */
  private generateComponents(contextType: string, contextInfo: any): string {
    const parts: string[] = [];

    // Build component definitions
    const componentDefs: Array<{
      id: string;
      name: string;
      description: string;
      tags: string[];
      properties: ComponentProperties;
      messageType: string;
    }> = [];

    // Generate components from handlers
    const handlersByType = new Map<string, any[]>();
    for (const handler of contextInfo.handlers) {
      if (!handlersByType.has(handler.messageType)) {
        handlersByType.set(handler.messageType, []);
      }
      handlersByType.get(handler.messageType)!.push(handler);
    }

    for (const [messageType, handlers] of handlersByType) {
      const componentName = this.toComponentName(messageType);
      const description = this.generateComponentDescription(messageType, handlers[0]);
      const tags = this.getComponentTags(messageType, handlers[0]);
      const properties = this.getComponentProperties(messageType, handlers[0], contextType);

      componentDefs.push({
        id: this.toId(componentName),
        name: componentName,
        description,
        tags,
        properties,
        messageType,
      });
    }

    // Apply grouping if configured, otherwise use automatic grouping
    if (this.options.groups && this.options.groups.length > 0) {
      // User-provided groups
      parts.push(...this.generateGroupedComponents(componentDefs, this.options.groups));
    } else {
      // Automatic grouping based on message type patterns
      const autoGroups = this.generateAutomaticGroups(componentDefs);
      if (autoGroups.length > 0) {
        parts.push(...this.generateGroupedComponents(componentDefs, autoGroups));
      } else {
        // No groups detected, render components directly
        for (const comp of componentDefs) {
          parts.push(this.generateComponentDefinition(comp, "        "));
        }
      }
    }

    // Collect and generate service components from detected relationships
    const serviceComponents = new Set<string>();
    for (const handler of contextInfo.handlers) {
      if (handler.relationships) {
        for (const rel of handler.relationships) {
          // Add the target component if it's not already a handler
          const targetId = this.toId(rel.to);
          const isHandler = componentDefs.some((c) => c.id === targetId);
          if (!isHandler) {
            serviceComponents.add(rel.to);
          }
        }
      }
    }

    // Generate service component definitions
    for (const serviceId of serviceComponents) {
      const serviceName = serviceId
        .split("_")
        .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
        .join(" ");

      parts.push(
        `        ${this.toId(serviceId)} = component "${serviceName}" "Business logic service" {`
      );
      parts.push(`          tags "Service" "Auto-detected"`);
      parts.push(`        }`);
    }

    // Generate components from UI components
    if (contextInfo.components) {
      for (const comp of contextInfo.components) {
        parts.push(
          `        ${this.toId(comp.name)} = component "${comp.name}" "${this.escape(comp.description || "UI component")}" {`
        );
        parts.push(`          tags "UI Component"`);
        parts.push(`        }`);
      }
    }

    // Add Chrome API components if used
    if (contextInfo.chromeAPIs && contextInfo.chromeAPIs.length > 0) {
      for (const api of contextInfo.chromeAPIs) {
        const apiId = this.toId(`chrome_${api}`);
        parts.push(
          `        ${apiId} = component "Chrome ${this.capitalize(api)} API" "Browser API for ${api}" {`
        );
        parts.push(`          tags "Chrome API" "External"`);
        parts.push(`        }`);
      }
    }

    return parts.join("\n");
  }

  /**
   * Generate better component descriptions based on message type
   */
  private generateComponentDescription(messageType: string, handler: any): string {
    const type = messageType.toLowerCase();

    // Authentication related
    if (type.includes("login")) {
      return "Authenticates users and establishes sessions";
    }
    if (type.includes("logout")) {
      return "Terminates user sessions and clears credentials";
    }

    // CRUD operations
    if (type.includes("add") || type.includes("create")) {
      const entity = type.replace(/_(add|create)/, "").replace(/_/g, " ");
      return `Creates new ${entity} items and persists to storage`;
    }
    if (type.includes("remove") || type.includes("delete")) {
      const entity = type.replace(/_(remove|delete)/, "").replace(/_/g, " ");
      return `Removes ${entity} items from storage`;
    }
    if (type.includes("update") || type.includes("toggle")) {
      const entity = type.replace(/_(update|toggle)/, "").replace(/_/g, " ");
      return `Updates ${entity} item state and syncs with storage`;
    }
    if (type.includes("clear")) {
      const entity = type.replace(/_clear.*/, "").replace(/_/g, " ");
      return `Clears all ${entity} items matching criteria`;
    }

    // Query operations
    if (type.includes("get") || type.includes("fetch") || type.includes("load")) {
      const entity = type.replace(/_(get|fetch|load)/, "").replace(/_/g, " ");
      return `Retrieves ${entity} data from storage`;
    }

    // Default
    return `Processes ${messageType} messages and coordinates business logic`;
  }

  /**
   * Determine appropriate tags for a component
   */
  private getComponentTags(messageType: string, handler: any): string[] {
    const tags: string[] = ["Message Handler"];
    const type = messageType.toLowerCase();

    // Add functional tags
    if (type.includes("login") || type.includes("logout") || type.includes("auth")) {
      tags.push("Authentication");
    } else if (
      type.includes("add") ||
      type.includes("create") ||
      type.includes("update") ||
      type.includes("delete") ||
      type.includes("remove") ||
      type.includes("toggle")
    ) {
      tags.push("CRUD");
    } else if (type.includes("get") || type.includes("fetch") || type.includes("load")) {
      tags.push("Query");
    }

    // Add domain tags
    if (type.includes("user")) {
      tags.push("User Management");
    }
    if (type.includes("todo")) {
      tags.push("Todo Management");
    }
    if (type.includes("state")) {
      tags.push("State Management");
    }

    return tags;
  }

  /**
   * Get component properties for traceability
   */
  private getComponentProperties(
    messageType: string,
    handler: any,
    contextType: string
  ): ComponentProperties {
    const properties: ComponentProperties = {};

    // Add source file and line number
    if (handler.location) {
      const relativePath = handler.location.file.replace(this.analysis.projectRoot + "/", "");
      properties["Source"] = `${relativePath}:${handler.location.line}`;
    }

    // Add technology stack
    const technologies: string[] = ["TypeScript"];

    // Detect framework/library from file path or context
    if (handler.location?.file.includes("ws") || contextType === "server") {
      technologies.push("WebSocket");
    }
    if (handler.location?.file.includes("socket.io")) {
      technologies.push("Socket.IO");
    }
    if (handler.location?.file.includes("elysia")) {
      technologies.push("Elysia");
    }

    properties["Technology"] = technologies.join(", ");

    // Add pattern/type
    const type = messageType.toLowerCase();
    let pattern = "Message Handler";

    if (type.includes("query") || type.includes("get") || type.includes("fetch") || type.includes("load")) {
      pattern = "Query Handler";
      properties["Message Type"] = "Query";
    } else if (
      type.includes("command") ||
      type.includes("add") ||
      type.includes("create") ||
      type.includes("update") ||
      type.includes("delete") ||
      type.includes("remove")
    ) {
      pattern = "Command Handler";
      properties["Message Type"] = "Command";
    } else if (type.includes("auth") || type.includes("login") || type.includes("logout")) {
      pattern = "Authentication Handler";
      properties["Message Type"] = "Authentication";
    } else if (type.includes("subscribe") || type.includes("watch") || type.includes("listen")) {
      pattern = "Subscription Handler";
      properties["Message Type"] = "Subscription";
    }

    properties["Pattern"] = pattern;

    // Merge with user-provided properties
    if (this.options.properties && this.options.properties[messageType]) {
      Object.assign(properties, this.options.properties[messageType]);
    }

    return properties;
  }

  /**
   * Generate relationships between components within a container
   */
  private generateComponentRelationships(contextType: string, contextInfo: any): string {
    const parts: string[] = [];

    // Build a map of handler components
    const handlersByType = new Map<string, any[]>();
    for (const handler of contextInfo.handlers) {
      if (!handlersByType.has(handler.messageType)) {
        handlersByType.set(handler.messageType, []);
      }
      handlersByType.get(handler.messageType)!.push(handler);
    }

    // Add relationships to Chrome APIs
    if (contextInfo.chromeAPIs && contextInfo.chromeAPIs.length > 0) {
      for (const api of contextInfo.chromeAPIs) {
        const apiId = this.toId(`chrome_${api}`);

        // Find handlers that use this API
        for (const [messageType, handlers] of handlersByType) {
          const componentId = this.toId(this.toComponentName(messageType));

          // Infer relationship based on API
          let description = `Uses ${api}`;
          if (api === "storage") {
            if (
              messageType.toLowerCase().includes("get") ||
              messageType.toLowerCase().includes("load")
            ) {
              description = "Reads from storage";
            } else {
              description = "Writes to storage";
            }
          } else if (api === "tabs") {
            description = "Manages browser tabs";
          } else if (api === "runtime") {
            description = "Sends messages";
          }

          parts.push(`        ${componentId} -> ${apiId} "${description}"`);
        }
      }
    }

    // Add user-provided explicit relationships
    if (this.options.relationships && this.options.relationships.length > 0) {
      for (const rel of this.options.relationships) {
        const fromId = this.toId(rel.from);
        const toId = this.toId(rel.to);
        const description = this.escape(rel.description);

        parts.push(`        ${fromId} -> ${toId} "${description}" {`);

        if (rel.technology) {
          parts.push(`          technology "${this.escape(rel.technology)}"`);
        }

        if (rel.tags && rel.tags.length > 0) {
          parts.push(`          tags "${rel.tags.join('" "')}"`);
        }

        parts.push(`        }`);
      }
    }

    // Add automatically detected relationships from handler code
    for (const handler of contextInfo.handlers) {
      if (handler.relationships && handler.relationships.length > 0) {
        for (const rel of handler.relationships) {
          const fromId = this.toId(rel.from);
          const toId = this.toId(rel.to);
          const description = this.escape(rel.description);

          parts.push(`        ${fromId} -> ${toId} "${description}" {`);

          if (rel.technology) {
            parts.push(`          technology "${this.escape(rel.technology)}"`);
          }

          parts.push(`          tags "Auto-detected"`);
          parts.push(`        }`);
        }
      }
    }

    // Add state management relationships (handlers that modify state)
    const stateHandlers: string[] = [];
    const queryHandlers: string[] = [];

    for (const [messageType, handlers] of handlersByType) {
      const type = messageType.toLowerCase();
      const componentId = this.toId(this.toComponentName(messageType));

      if (
        type.includes("add") ||
        type.includes("create") ||
        type.includes("update") ||
        type.includes("delete") ||
        type.includes("remove") ||
        type.includes("toggle") ||
        type.includes("clear") ||
        type.includes("login") ||
        type.includes("logout")
      ) {
        stateHandlers.push(componentId);
      } else if (type.includes("get") || type.includes("fetch") || type.includes("load")) {
        queryHandlers.push(componentId);
      }
    }

    // Create implicit state manager if we have state operations
    if (stateHandlers.length > 0 && queryHandlers.length > 0) {
      // Query handlers depend on state set by mutation handlers
      for (const queryHandler of queryHandlers) {
        for (const stateHandler of stateHandlers) {
          if (queryHandler !== stateHandler) {
            parts.push(`        ${stateHandler} -> ${queryHandler} "Updates state" {`);
            parts.push(`          tags "Implicit"`);
            parts.push(`        }`);
          }
        }
      }
    }

    return parts.join("\n");
  }

  /**
   * Generate relationships between containers
   */
  private generateContainerRelationships(): string {
    const parts: string[] = [];

    // Add user relationships
    const uiContexts = ["popup", "options", "devtools"];
    for (const contextType of Object.keys(this.analysis.contexts)) {
      if (uiContexts.includes(contextType)) {
        parts.push(`      user -> extension.${contextType} "Uses"`);
      }
    }

    // Add message flow relationships
    for (const flow of this.analysis.messageFlows) {
      const tech = `Sends ${flow.messageType}`;
      for (const to of flow.to) {
        parts.push(`      extension.${flow.from} -> extension.${to} "${tech}"`);
      }
    }

    // Add external API relationships
    for (const integration of this.analysis.integrations) {
      if (integration.type === "api" || integration.type === "websocket") {
        // Find which contexts use this integration
        for (const [contextType, contextInfo] of Object.entries(this.analysis.contexts)) {
          const usesIntegration = contextInfo.externalAPIs.some((api: any) =>
            integration.calls?.some((call) => call.endpoint === api.endpoint)
          );

          if (usesIntegration) {
            const method = integration.type === "websocket" ? "Connects to" : "Calls";
            parts.push(
              `      extension.${contextType} -> ${this.toId(integration.name)} "${method}"`
            );
          }
        }
      }
    }

    return parts.join("\n");
  }

  /**
   * Generate views section
   */
  private generateViews(): string {
    const parts: string[] = [];

    parts.push("  views {");
    parts.push(this.generateSystemContextView());
    parts.push(this.generateContainerView());

    if (this.options.includeComponentDiagrams) {
      for (const contextType of this.options.componentDiagramContexts || []) {
        if (this.analysis.contexts[contextType]) {
          parts.push(this.generateComponentView(contextType));
        }
      }
    }

    if (this.options.includeDynamicDiagrams) {
      parts.push(this.generateDynamicViews());
    }

    // Add deployment views if configured
    if (this.options.deploymentNodes && this.options.deploymentNodes.length > 0) {
      parts.push(this.generateDeploymentViews());
    }

    parts.push(this.generateStyles());
    parts.push("  }");

    // Add documentation section if ADRs exist
    if (this.analysis.adrs && this.analysis.adrs.adrs.length > 0) {
      parts.push("");
      parts.push(this.generateDocumentation());
    }

    return parts.join("\n\n");
  }

  /**
   * Generate documentation section for ADRs
   */
  private generateDocumentation(): string {
    if (!this.analysis.adrs || this.analysis.adrs.adrs.length === 0) {
      return "";
    }

    const parts: string[] = [];
    parts.push("  documentation {");

    for (const adr of this.analysis.adrs.adrs) {
      parts.push(`    decision "${adr.id}" {`);
      parts.push(`      title "${this.escape(adr.title)}"`);
      parts.push(`      status "${adr.status}"`);
      parts.push(`      date "${adr.date}"`);
      parts.push(`      content "${this.escape(adr.context)}"`);
      parts.push("    }");
    }

    parts.push("  }");

    return parts.join("\n");
  }

  /**
   * Generate system context view
   */
  private generateSystemContextView(): string {
    return `    systemContext extension "SystemContext" {
      include *
      autoLayout lr
    }`;
  }

  /**
   * Generate container view
   */
  private generateContainerView(): string {
    return `    container extension "Containers" {
      include *
      autoLayout lr
    }`;
  }

  /**
   * Generate component view
   */
  private generateComponentView(contextType: string): string {
    return `    component extension.${contextType} "Components_${this.capitalize(contextType)}" {
      include *
      autoLayout tb
    }`;
  }

  /**
   * Generate dynamic views for message flows
   */
  private generateDynamicViews(): string {
    const parts: string[] = [];

    // Generate user-provided dynamic diagrams first
    if (this.options.dynamicDiagrams && this.options.dynamicDiagrams.length > 0) {
      for (const diagram of this.options.dynamicDiagrams) {
        parts.push(this.generateUserDynamicDiagram(diagram));
      }
    }

    // Group flows by domain/feature for auto-generated diagrams
    const flowsByDomain = new Map<string, any[]>();

    for (const flow of this.analysis.messageFlows) {
      // Extract domain from message type (e.g., USER_LOGIN -> user, TODO_ADD -> todo)
      const messageType = flow.messageType.toLowerCase();
      let domain = "general";

      if (
        messageType.includes("user") ||
        messageType.includes("login") ||
        messageType.includes("logout") ||
        messageType.includes("auth")
      ) {
        domain = "authentication";
      } else if (messageType.includes("todo")) {
        domain = "todo";
      } else if (messageType.includes("state")) {
        domain = "state";
      }

      if (!flowsByDomain.has(domain)) {
        flowsByDomain.set(domain, []);
      }
      flowsByDomain.get(domain)!.push(flow);
    }

    // Generate a dynamic view for each domain
    let count = 0;
    for (const [domain, flows] of flowsByDomain) {
      if (count >= 5) break; // Limit to avoid too many diagrams

      const viewName = this.capitalize(domain) + " Flow";
      parts.push(this.generateDynamicView(viewName, flows, domain));
      count++;
    }

    return parts.join("\n\n");
  }

  /**
   * Generate a user-provided dynamic diagram
   */
  private generateUserDynamicDiagram(diagram: DynamicDiagram): string {
    const parts: string[] = [];

    parts.push(`    dynamic ${diagram.scope || "extension"} "${this.escape(diagram.title)}" "${this.escape(diagram.description || "")}" {`);

    for (const step of diagram.steps) {
      const from = step.from;
      const to = step.to;
      const description = this.escape(step.description);

      parts.push(`      ${from} -> ${to} "${description}"`);
    }

    parts.push("      autoLayout lr");
    parts.push("    }");

    return parts.join("\n");
  }

  /**
   * Generate single dynamic view
   */
  private generateDynamicView(flowName: string, flows: any[], domain: string): string {
    const parts: string[] = [];

    // Create a user-centric description
    const description = this.getDynamicViewDescription(domain);
    parts.push(`    dynamic extension "${flowName}" "${description}" {`);

    // Add user interaction if this is a UI flow
    const uiContexts = ["popup", "options", "devtools"];
    const hasUIFlow = flows.some((f) => uiContexts.includes(f.from));

    if (hasUIFlow) {
      // Start with user interaction
      const firstFlow = flows.find((f) => uiContexts.includes(f.from));
      if (firstFlow) {
        const action = this.getUserAction(domain);
        parts.push(`      user -> extension.${firstFlow.from} "${action}"`);
      }
    }

    // Generate message flows
    for (const flow of flows) {
      const messageDesc = this.getMessageDescription(flow.messageType);

      for (const to of flow.to) {
        parts.push(`      extension.${flow.from} -> extension.${to} "${messageDesc}"`);
      }
    }

    parts.push("      autoLayout lr");
    parts.push("    }");

    return parts.join("\n");
  }

  /**
   * Get description for dynamic view based on domain
   */
  private getDynamicViewDescription(domain: string): string {
    const descriptions: Record<string, string> = {
      authentication: "User authentication and session management",
      todo: "Todo item creation, updates, and retrieval",
      state: "Application state synchronization",
      general: "Message flow through the system",
    };
    return descriptions[domain] || descriptions.general;
  }

  /**
   * Get user action description for domain
   */
  private getUserAction(domain: string): string {
    const actions: Record<string, string> = {
      authentication: "Initiates login",
      todo: "Manages todo items",
      state: "Requests state",
      general: "Interacts",
    };
    return actions[domain] || actions.general;
  }

  /**
   * Get message description based on type
   */
  private getMessageDescription(messageType: string): string {
    const type = messageType.toLowerCase();

    if (type.includes("login")) return "Authenticate user";
    if (type.includes("logout")) return "End session";
    if (type.includes("add") || type.includes("create")) return "Create item";
    if (type.includes("remove") || type.includes("delete")) return "Delete item";
    if (type.includes("update") || type.includes("toggle")) return "Update item";
    if (type.includes("get") || type.includes("fetch")) return "Retrieve data";
    if (type.includes("clear")) return "Clear items";

    return messageType;
  }

  /**
   * Generate deployment environments (for model section)
   */
  private generateDeploymentEnvironments(): string {
    const parts: string[] = [];

    // Group deployment nodes by environment
    const nodesByEnvironment = new Map<string, DeploymentNode[]>();

    for (const node of this.options.deploymentNodes || []) {
      const env = node.tags?.find((tag) => tag.toLowerCase().includes("environment:"))
        ?.split(":")[1] || "Production";

      if (!nodesByEnvironment.has(env)) {
        nodesByEnvironment.set(env, []);
      }
      nodesByEnvironment.get(env)!.push(node);
    }

    // Generate deployment environment for each environment
    for (const [envName, nodes] of nodesByEnvironment) {
      parts.push(`    deploymentEnvironment "${envName}" {`);

      for (const node of nodes) {
        parts.push(this.generateDeploymentNode(node, "      "));
      }

      parts.push("    }");
    }

    return parts.join("\n");
  }

  /**
   * Generate a single deployment node
   */
  private generateDeploymentNode(node: DeploymentNode, indent: string): string {
    const parts: string[] = [];

    const description = node.description ? ` "${this.escape(node.description)}"` : "";
    const technology = node.technology ? ` "${this.escape(node.technology)}"` : "";

    parts.push(`${indent}deploymentNode "${this.escape(node.name)}"${description}${technology} {`);

    // Add tags if present
    if (node.tags && node.tags.length > 0) {
      const filteredTags = node.tags.filter((tag) => !tag.toLowerCase().includes("environment:"));
      if (filteredTags.length > 0) {
        parts.push(`${indent}  tags "${filteredTags.join('" "')}"`);
      }
    }

    // Add properties if present
    if (node.properties && Object.keys(node.properties).length > 0) {
      parts.push(`${indent}  properties {`);
      for (const [key, value] of Object.entries(node.properties)) {
        parts.push(`${indent}    "${this.escape(key)}" "${this.escape(value)}"`);
      }
      parts.push(`${indent}  }`);
    }

    // Add child deployment nodes (nested infrastructure)
    if (node.children && node.children.length > 0) {
      for (const child of node.children) {
        parts.push(this.generateDeploymentNode(child, indent + "  "));
      }
    }

    // Add container instances if specified
    if (node.containerInstances && node.containerInstances.length > 0) {
      for (const containerInstance of node.containerInstances) {
        const instancesStr = containerInstance.instances && containerInstance.instances > 1
          ? ` ${containerInstance.instances}`
          : "";
        parts.push(`${indent}  containerInstance extension.${containerInstance.container}${instancesStr}`);
      }
    } else if (!node.children || node.children.length === 0) {
      // If no container instances specified and no children, deploy all containers as fallback
      const contexts = Object.keys(this.analysis.contexts);
      if (contexts.length > 0) {
        for (const contextType of contexts) {
          parts.push(`${indent}  containerInstance extension.${contextType}`);
        }
      }
    }

    parts.push(`${indent}}`);

    return parts.join("\n");
  }

  /**
   * Generate deployment views
   */
  private generateDeploymentViews(): string {
    const parts: string[] = [];

    // Group deployment nodes by environment
    const nodesByEnvironment = new Map<string, DeploymentNode[]>();

    for (const node of this.options.deploymentNodes || []) {
      const env = node.tags?.find((tag) => tag.toLowerCase().includes("environment:"))
        ?.split(":")[1] || "Production";

      if (!nodesByEnvironment.has(env)) {
        nodesByEnvironment.set(env, []);
      }
      nodesByEnvironment.get(env)!.push(node);
    }

    // Generate deployment view for each environment
    for (const [envName] of nodesByEnvironment) {
      const description = `${envName} environment deployment architecture`;

      parts.push(`    deployment extension "${envName}" "${description}" {`);
      parts.push("      include *");
      parts.push("      autoLayout lr");
      parts.push("    }");
    }

    return parts.join("\n\n");
  }

  /**
   * Generate styles
   */
  /**
   * Generate styles section with element and relationship styles
   */
  private generateStyles(): string {
    const parts: string[] = [];

    parts.push("    styles {");

    // Generate element styles
    if (this.options.includeDefaultStyles && this.options.styles?.elements) {
      for (const [tag, style] of Object.entries(this.options.styles.elements)) {
        parts.push(this.generateElementStyle(tag, style));
      }
    }

    // Generate relationship styles
    if (this.options.includeDefaultStyles && this.options.styles?.relationships) {
      for (const [tag, style] of Object.entries(this.options.styles.relationships)) {
        parts.push(this.generateRelationshipStyle(tag, style));
      }
    }

    // Add theme if specified
    if (this.options.styles?.theme) {
      parts.push(`      theme ${this.options.styles.theme}`);
    }

    parts.push("    }");

    return parts.join("\n");
  }

  /**
   * Generate style block for an element tag
   */
  private generateElementStyle(tag: string, style: ElementStyle): string {
    const parts: string[] = [];

    parts.push(`      element "${tag}" {`);

    if (style.shape) {
      parts.push(`        shape ${style.shape}`);
    }
    if (style.icon) {
      parts.push(`        icon ${style.icon}`);
    }
    if (style.width) {
      parts.push(`        width ${style.width}`);
    }
    if (style.height) {
      parts.push(`        height ${style.height}`);
    }
    if (style.background) {
      parts.push(`        background ${style.background}`);
    }
    if (style.color) {
      parts.push(`        color ${style.color}`);
    }
    if (style.fontSize) {
      parts.push(`        fontSize ${style.fontSize}`);
    }
    if (style.border) {
      parts.push(`        border ${style.border}`);
    }
    if (style.opacity !== undefined) {
      parts.push(`        opacity ${style.opacity}`);
    }
    if (style.metadata !== undefined) {
      parts.push(`        metadata ${style.metadata}`);
    }
    if (style.description !== undefined) {
      parts.push(`        description ${style.description}`);
    }

    parts.push("      }");

    return parts.join("\n");
  }

  /**
   * Generate style block for a relationship tag
   */
  private generateRelationshipStyle(tag: string, style: RelationshipStyle): string {
    const parts: string[] = [];

    parts.push(`      relationship "${tag}" {`);

    if (style.thickness) {
      parts.push(`        thickness ${style.thickness}`);
    }
    if (style.color) {
      parts.push(`        color ${style.color}`);
    }
    if (style.style) {
      parts.push(`        style ${style.style}`);
    }
    if (style.routing) {
      parts.push(`        routing ${style.routing}`);
    }
    if (style.fontSize) {
      parts.push(`        fontSize ${style.fontSize}`);
    }
    if (style.width) {
      parts.push(`        width ${style.width}`);
    }
    if (style.position) {
      parts.push(`        position ${style.position}`);
    }
    if (style.opacity !== undefined) {
      parts.push(`        opacity ${style.opacity}`);
    }

    parts.push("      }");

    return parts.join("\n");
  }

  /**
   * Get technology label for context
   */
  private getContextTechnology(contextType: string): string {
    const technologies: Record<string, string> = {
      background: "Service Worker / Background Script",
      content: "Content Script",
      popup: "Browser Action Popup",
      devtools: "DevTools Panel",
      options: "Options Page",
      offscreen: "Offscreen Document",
    };

    return technologies[contextType] || "Extension Context";
  }

  /**
   * Convert message type to component name
   */
  private toComponentName(messageType: string): string {
    return (
      messageType
        .split("_")
        .map((part) => this.capitalize(part.toLowerCase()))
        .join(" ") + " Handler"
    );
  }

  /**
   * Convert name to identifier
   */
  private toId(name: string): string {
    return name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, "_")
      .replace(/^_|_$/g, "");
  }

  /**
   * Convert flow name to view name
   */
  private toViewName(flowName: string): string {
    return flowName
      .split(/[_-]/)
      .map((part) => this.capitalize(part))
      .join(" ");
  }

  /**
   * Capitalize first letter
   */
  private capitalize(str: string): string {
    return str.charAt(0).toUpperCase() + str.slice(1);
  }

  /**
   * Escape string for DSL
   */
  /**
   * Generate a single component definition
   */
  private generateComponentDefinition(
    comp: {
      id: string;
      name: string;
      description: string;
      tags: string[];
      properties: ComponentProperties;
    },
    indent: string
  ): string {
    const parts: string[] = [];

    parts.push(`${indent}${comp.id} = component "${comp.name}" "${this.escape(comp.description)}" {`);

    if (comp.tags.length > 0) {
      parts.push(`${indent}  tags "${comp.tags.join('" "')}"`);
    }

    if (comp.properties && Object.keys(comp.properties).length > 0) {
      parts.push(`${indent}  properties {`);
      for (const [key, value] of Object.entries(comp.properties)) {
        if (value) {
          parts.push(`${indent}    "${key}" "${this.escape(value)}"`);
        }
      }
      parts.push(`${indent}  }`);
    }

    // Add perspectives if configured for this component
    if (this.options.perspectives && this.options.perspectives[comp.id]) {
      const perspectives = this.options.perspectives[comp.id];
      parts.push(`${indent}  perspectives {`);
      for (const perspective of perspectives) {
        parts.push(`${indent}    "${this.escape(perspective.name)}" "${this.escape(perspective.description)}"`);
      }
      parts.push(`${indent}  }`);
    }

    parts.push(`${indent}}`);

    return parts.join("\n");
  }

  /**
   * Automatically generate groups based on message type patterns
   */
  private generateAutomaticGroups(
    componentDefs: Array<{
      id: string;
      name: string;
      description: string;
      tags: string[];
      properties: ComponentProperties;
      messageType: string;
    }>
  ): ComponentGroup[] {
    const groups: ComponentGroup[] = [];
    const assigned = new Set<string>();

    // Group 1: Authentication handlers
    const authHandlers = componentDefs.filter((comp) => {
      const type = comp.messageType.toLowerCase();
      return (
        type.includes("login") ||
        type.includes("logout") ||
        type.includes("auth") ||
        type.includes("verify") ||
        type.includes("register") ||
        type.includes("signup")
      );
    });

    if (authHandlers.length > 0) {
      groups.push({
        name: "Authentication",
        components: authHandlers.map((c) => c.id),
      });
      authHandlers.forEach((h) => assigned.add(h.id));
    }

    // Group 2: Subscription handlers
    const subscriptionHandlers = componentDefs.filter((comp) => {
      const type = comp.messageType.toLowerCase();
      return type.includes("subscribe") || type.includes("unsubscribe");
    });

    if (subscriptionHandlers.length > 0) {
      groups.push({
        name: "Subscriptions",
        components: subscriptionHandlers.map((c) => c.id),
      });
      subscriptionHandlers.forEach((h) => assigned.add(h.id));
    }

    // Group 3: Entity-based grouping
    // Extract entities from message types (e.g., "user_add", "todo_remove" → "user", "todo")
    const entityGroups = new Map<string, string[]>();

    for (const comp of componentDefs) {
      if (assigned.has(comp.id)) continue;

      const type = comp.messageType.toLowerCase();

      // Skip WebSocket lifecycle handlers
      if (type === "connection" || type === "message" || type === "close" || type === "error") {
        continue;
      }

      // Extract entity name (first part before underscore or action verb)
      let entity: string | null = null;

      // Pattern 1: entity_action (e.g., "user_add", "todo_remove")
      const underscoreMatch = type.match(/^([a-z]+)_(add|create|update|delete|remove|get|fetch|load|list|query)/);
      if (underscoreMatch) {
        entity = underscoreMatch[1];
      }

      // Pattern 2: actionEntity (e.g., "addUser", "removeTask")
      if (!entity) {
        const camelMatch = type.match(/(add|create|update|delete|remove|get|fetch|load|list|query)([a-z]+)/i);
        if (camelMatch) {
          entity = camelMatch[2].toLowerCase();
        }
      }

      // Pattern 3: plain entity name (e.g., "user", "todo")
      if (!entity && type.match(/^[a-z]+$/)) {
        entity = type;
      }

      if (entity) {
        if (!entityGroups.has(entity)) {
          entityGroups.set(entity, []);
        }
        entityGroups.get(entity)!.push(comp.id);
        assigned.add(comp.id);
      }
    }

    // Add entity groups (capitalize entity name for group title)
    for (const [entity, componentIds] of entityGroups) {
      if (componentIds.length >= 2) {
        // Only create group if there are at least 2 components
        const entityName = entity.charAt(0).toUpperCase() + entity.slice(1);
        groups.push({
          name: `${entityName} Management`,
          components: componentIds,
        });
      } else {
        // Remove from assigned if not enough for a group
        componentIds.forEach((id) => assigned.delete(id));
      }
    }

    // Group 4: Query/Command pattern for remaining handlers
    const queryHandlers = componentDefs.filter((comp) => {
      if (assigned.has(comp.id)) return false;
      const type = comp.messageType.toLowerCase();
      return (
        type.includes("query") ||
        type.includes("get") ||
        type.includes("fetch") ||
        type.includes("load") ||
        type.includes("list") ||
        type.includes("read")
      );
    });

    const commandHandlers = componentDefs.filter((comp) => {
      if (assigned.has(comp.id)) return false;
      const type = comp.messageType.toLowerCase();
      return (
        type.includes("command") ||
        type.includes("add") ||
        type.includes("create") ||
        type.includes("update") ||
        type.includes("delete") ||
        type.includes("remove") ||
        type.includes("set") ||
        type.includes("clear")
      );
    });

    if (queryHandlers.length >= 2) {
      groups.push({
        name: "Query Handlers",
        components: queryHandlers.map((c) => c.id),
      });
      queryHandlers.forEach((h) => assigned.add(h.id));
    }

    if (commandHandlers.length >= 2) {
      groups.push({
        name: "Command Handlers",
        components: commandHandlers.map((c) => c.id),
      });
      commandHandlers.forEach((h) => assigned.add(h.id));
    }

    // Only return groups if we successfully grouped most components
    const groupedCount = assigned.size;
    const totalCount = componentDefs.length;

    // Return groups if at least 50% are grouped OR we have at least 2 groups
    if (groupedCount >= totalCount * 0.5 || groups.length >= 2) {
      return groups;
    }

    // Not enough components grouped, return empty to skip grouping
    return [];
  }

  /**
   * Generate components organized into groups
   */
  private generateGroupedComponents(
    componentDefs: Array<{
      id: string;
      name: string;
      description: string;
      tags: string[];
      properties: ComponentProperties;
      messageType: string;
    }>,
    groups: ComponentGroup[]
  ): string[] {
    const parts: string[] = [];
    const assignedComponents = new Set<string>();

    for (const group of groups) {
      const groupComponents = componentDefs.filter((comp) =>
        group.components.includes(comp.id)
      );

      if (groupComponents.length === 0) continue;

      parts.push(`        group "${this.escape(group.name)}" {`);

      for (const comp of groupComponents) {
        parts.push(this.generateComponentDefinition(comp, "          "));
        assignedComponents.add(comp.id);
      }

      parts.push(`        }`);
      parts.push("");
    }

    // Add ungrouped components
    const ungroupedComponents = componentDefs.filter(
      (comp) => !assignedComponents.has(comp.id)
    );

    for (const comp of ungroupedComponents) {
      parts.push(this.generateComponentDefinition(comp, "        "));
    }

    return parts;
  }

  private escape(str: string): string {
    return str.replace(/"/g, '\\"');
  }
}

/**
 * Generate Structurizr DSL from architecture analysis
 */
export function generateStructurizrDSL(
  analysis: ArchitectureAnalysis,
  options?: StructurizrDSLOptions
): string {
  const generator = new StructurizrDSLGenerator(analysis, options);
  return generator.generate();
}
