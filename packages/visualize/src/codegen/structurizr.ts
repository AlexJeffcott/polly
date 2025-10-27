// Structurizr DSL generator

import type { ArchitectureAnalysis } from "@fairfox/polly-analysis";

export interface StructurizrDSLOptions {
	/** Include dynamic diagrams for message flows */
	includeDynamicDiagrams?: boolean;

	/** Include component diagrams for contexts */
	includeComponentDiagrams?: boolean;

	/** Which contexts to generate component diagrams for */
	componentDiagramContexts?: string[];

	/** Custom theme URL */
	theme?: string;

	/** Custom styles */
	styles?: Record<string, string>;
}

export class StructurizrDSLGenerator {
	private analysis: ArchitectureAnalysis;
	private options: StructurizrDSLOptions;

	constructor(
		analysis: ArchitectureAnalysis,
		options: StructurizrDSLOptions = {},
	) {
		this.analysis = analysis;
		this.options = {
			includeDynamicDiagrams: true,
			includeComponentDiagrams: true,
			componentDiagramContexts: ["background"],
			theme: "https://static.structurizr.com/themes/default",
			...options,
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

		const parts = [
			`workspace "${this.escape(name)}" "${this.escape(description || "")}" {`,
		];
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
		parts.push("  }");

		return parts.join("\n\n");
	}

	/**
	 * Generate people/actors
	 */
	private generatePeople(): string {
		// Use project type to determine user label
		const projectType = this.analysis.projectConfig?.type || "chrome-extension";
		const userLabels: Record<string, string> = {
			"chrome-extension": "Extension user",
			pwa: "PWA user",
			"websocket-app": "Application user",
			electron: "Desktop application user",
			generic: "Application user",
		};

		const userLabel = userLabels[projectType] || "User";
		return `    user = person "User" "${userLabel}"`;
	}

	/**
	 * Generate external systems
	 */
	private generateExternalSystems(): string {
		const parts: string[] = [];

		for (const integration of this.analysis.integrations) {
			if (integration.type === "api" || integration.type === "websocket") {
				const tech =
					integration.technology ||
					(integration.type === "websocket" ? "WebSocket" : "REST API");
				let desc = integration.description || "";

				// Generate better description from API calls if available
				if (!desc && integration.calls && integration.calls.length > 0) {
					const endpoints = integration.calls
						.slice(0, 3)
						.map((c) => c.endpoint)
						.join(", ");
					const methods = [
						...new Set(integration.calls.map((c) => c.method)),
					].join(", ");
					desc = `External API with endpoints: ${endpoints}. Methods: ${methods}`;
				}

				parts.push(
					`    ${this.toId(integration.name)} = softwareSystem "${this.escape(integration.name)}" "${this.escape(desc)}" {`,
				);
				parts.push(
					`      tags "External System" "${integration.type === "websocket" ? "WebSocket" : "REST API"}"`,
				);
				parts.push(`    }`);
			}
		}

		return parts.join("\n");
	}

	/**
	 * Generate main system (the application)
	 */
	private generateMainSystem(): string {
		const parts: string[] = [];

		const systemId = this.getSystemId();
		parts.push(
			`    ${systemId} = softwareSystem "${this.escape(this.analysis.system.name)}" {`,
		);

		// Generate containers (contexts)
		for (const [contextType, contextInfo] of Object.entries(
			this.analysis.contexts,
		)) {
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
		const description =
			contextInfo.description || `${this.capitalize(contextType)} context`;

		parts.push(
			`      ${contextType} = container "${this.capitalize(contextType)}" "${this.escape(description)}" "${technology}" {`,
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
			const description = this.generateComponentDescription(
				messageType,
				handlers[0],
			);
			const tags = this.getComponentTags(messageType, handlers[0]);

			parts.push(
				`        ${this.toId(componentName)} = component "${componentName}" "${description}" {`,
			);
			if (tags.length > 0) {
				parts.push(`          tags "${tags.join('" "')}"`);
			}
			parts.push(`        }`);
		}

		// Generate components from UI components
		if (contextInfo.components) {
			for (const comp of contextInfo.components) {
				parts.push(
					`        ${this.toId(comp.name)} = component "${comp.name}" "${this.escape(comp.description || "UI component")}" {`,
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
					`        ${apiId} = component "Chrome ${this.capitalize(api)} API" "Browser API for ${api}" {`,
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
	private generateComponentDescription(
		messageType: string,
		handler: any,
	): string {
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
		if (
			type.includes("get") ||
			type.includes("fetch") ||
			type.includes("load")
		) {
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
		if (
			type.includes("login") ||
			type.includes("logout") ||
			type.includes("auth")
		) {
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
		} else if (
			type.includes("get") ||
			type.includes("fetch") ||
			type.includes("load")
		) {
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
	 * Generate relationships between components within a container
	 */
	private generateComponentRelationships(
		contextType: string,
		contextInfo: any,
	): string {
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
			} else if (
				type.includes("get") ||
				type.includes("fetch") ||
				type.includes("load")
			) {
				queryHandlers.push(componentId);
			}
		}

		// Create implicit state manager if we have state operations
		if (stateHandlers.length > 0 && queryHandlers.length > 0) {
			// Query handlers depend on state set by mutation handlers
			for (const queryHandler of queryHandlers) {
				for (const stateHandler of stateHandlers) {
					if (queryHandler !== stateHandler) {
						parts.push(
							`        ${stateHandler} -> ${queryHandler} "Updates state" {`,
						);
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
		const systemId = this.getSystemId();

		// Add user relationships
		const uiContexts = ["popup", "options", "devtools", "client", "renderer"];
		for (const contextType of Object.keys(this.analysis.contexts)) {
			if (uiContexts.includes(contextType)) {
				parts.push(`      user -> ${systemId}.${contextType} "Uses"`);
			}
		}

		// Add message flow relationships
		for (const flow of this.analysis.messageFlows) {
			const tech = `Sends ${flow.messageType}`;
			for (const to of flow.to) {
				parts.push(
					`      ${systemId}.${flow.from} -> ${systemId}.${to} "${tech}"`,
				);
			}
		}

		// Add external API relationships
		for (const integration of this.analysis.integrations) {
			if (integration.type === "api" || integration.type === "websocket") {
				// Find which contexts use this integration
				for (const [contextType, contextInfo] of Object.entries(
					this.analysis.contexts,
				)) {
					const usesIntegration = contextInfo.externalAPIs.some((api: any) =>
						integration.calls?.some((call) => call.endpoint === api.endpoint),
					);

					if (usesIntegration) {
						const method =
							integration.type === "websocket" ? "Connects to" : "Calls";
						parts.push(
							`      ${systemId}.${contextType} -> ${this.toId(integration.name)} "${method}"`,
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
		const systemId = this.getSystemId();
		return `    component ${systemId}.${contextType} "Components_${this.capitalize(contextType)}" {
      include *
      autoLayout tb
    }`;
	}

	/**
	 * Generate dynamic views for message flows
	 */
	private generateDynamicViews(): string {
		const parts: string[] = [];

		// Group flows by domain/feature
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
	 * Generate single dynamic view
	 */
	private generateDynamicView(
		flowName: string,
		flows: any[],
		domain: string,
	): string {
		const parts: string[] = [];

		// Create a user-centric description
		const description = this.getDynamicViewDescription(domain);
		const systemId = this.getSystemId();
		parts.push(`    dynamic ${systemId} "${flowName}" "${description}" {`);

		// Add user interaction if this is a UI flow
		const uiContexts = ["popup", "options", "devtools", "client", "renderer"];
		const hasUIFlow = flows.some((f) => uiContexts.includes(f.from));

		if (hasUIFlow) {
			// Start with user interaction
			const firstFlow = flows.find((f) => uiContexts.includes(f.from));
			if (firstFlow) {
				const action = this.getUserAction(domain);
				parts.push(`      user -> ${systemId}.${firstFlow.from} "${action}"`);
			}
		}

		// Generate message flows
		for (const flow of flows) {
			const messageDesc = this.getMessageDescription(flow.messageType);

			for (const to of flow.to) {
				parts.push(
					`      ${systemId}.${flow.from} -> ${systemId}.${to} "${messageDesc}"`,
				);
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
		if (type.includes("remove") || type.includes("delete"))
			return "Delete item";
		if (type.includes("update") || type.includes("toggle"))
			return "Update item";
		if (type.includes("get") || type.includes("fetch")) return "Retrieve data";
		if (type.includes("clear")) return "Clear items";

		return messageType;
	}

	/**
	 * Generate styles
	 */
	private generateStyles(): string {
		const parts: string[] = [];

		// Skip theme directive - causes issues with Structurizr CLI export
		// The inline styles are sufficient for diagram generation
		parts.push("    styles {");

		// Default styles for containers (contexts)
		const contextStyles: Record<string, string> = {
			// Chrome Extension contexts
			background: "#2E7D32",
			content: "#F57C00",
			popup: "#1976D2",
			devtools: "#7B1FA2",
			options: "#0288D1",
			// Generic contexts
			server: "#2E7D32",
			client: "#1976D2",
			worker: "#F57C00",
			main: "#2E7D32",
			renderer: "#1976D2",
			...this.options.styles,
		};

		const systemId = this.getSystemId();
		for (const [context, color] of Object.entries(contextStyles)) {
			if (this.analysis.contexts[context]) {
				parts.push(`      element "${systemId}.${context}" {`);
				parts.push(`        background ${color}`);
				parts.push(`        color #ffffff`);
				parts.push("      }");
			}
		}

		parts.push("    }");

		return parts.join("\n");
	}

	/**
	 * Get system identifier (extension or application)
	 */
	private getSystemId(): string {
		return this.analysis.projectConfig ? "application" : "extension";
	}

	/**
	 * Get technology label for context
	 */
	private getContextTechnology(contextType: string): string {
		// Chrome Extension contexts
		const extensionTechnologies: Record<string, string> = {
			background: "Service Worker / Background Script",
			content: "Content Script",
			popup: "Browser Action Popup",
			devtools: "DevTools Panel",
			options: "Options Page",
			offscreen: "Offscreen Document",
		};

		// Generic project contexts
		const genericTechnologies: Record<string, string> = {
			server: "Server Runtime",
			client: "Client Application",
			worker: "Service Worker",
			main: "Main Process",
			renderer: "Renderer Process",
		};

		// Use contextMapping if available from ProjectConfig
		if (this.analysis.projectConfig?.contextMapping?.[contextType]) {
			return this.analysis.projectConfig.contextMapping[contextType];
		}

		return (
			extensionTechnologies[contextType] ||
			genericTechnologies[contextType] ||
			"Application Context"
		);
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
	private escape(str: string): string {
		return str.replace(/"/g, '\\"');
	}
}

/**
 * Generate Structurizr DSL from architecture analysis
 */
export function generateStructurizrDSL(
	analysis: ArchitectureAnalysis,
	options?: StructurizrDSLOptions,
): string {
	const generator = new StructurizrDSLGenerator(analysis, options);
	return generator.generate();
}
