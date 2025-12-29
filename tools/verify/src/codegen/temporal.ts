// Temporal property generation for message ordering and causality
// Generate LTL (Linear Temporal Logic) properties for TLC liveness checking

import type { CodebaseAnalysis } from "../../../analysis/src/extract/types";

/**
 * Temporal property types
 */
export type TemporalPropertyType =
	| "eventually" // <>P (eventually P)
	| "always" // []P (always P)
	| "until" // P U Q (P until Q)
	| "implies-eventually" // []( P => <>Q ) (always: if P then eventually Q)
	| "implies-next" // []( P => X Q ) (always: if P then next Q)
	| "order"; // Message ordering constraint

/**
 * Temporal property specification
 */
export type TemporalProperty = {
	/** Property name */
	name: string;
	/** Human-readable description */
	description: string;
	/** Property type */
	type: TemporalPropertyType;
	/** Trigger condition (if applicable) */
	trigger?: string;
	/** Target condition or message */
	target: string;
	/** Source location (if extracted from code) */
	location?: {
		file: string;
		line: number;
	};
};

/**
 * Ordering rule between messages
 */
export type MessageOrderRule = {
	/** Message that must come first */
	first: string;
	/** Message that must come after */
	second: string;
	/** Description of the ordering requirement */
	description: string;
};

/**
 * TemporalPropertyGenerator creates LTL properties for:
 * - Message ordering (init first, login before auth actions, etc.)
 * - Causality (request => response)
 * - Liveness (eventual completion)
 * - Safety (bad states never reached)
 */
export class TemporalPropertyGenerator {
	/**
	 * Generate temporal properties from codebase analysis
	 */
	generateProperties(analysis: CodebaseAnalysis): TemporalProperty[] {
		const properties: TemporalProperty[] = [];

		// 1. Generate init-first property if init message exists
		if (analysis.messageTypes.includes("init")) {
			properties.push(this.generateInitFirstProperty());
		}

		// 2. Detect request-response patterns
		properties.push(...this.detectRequestResponsePatterns(analysis));

		// 3. Detect state transitions that require ordering
		properties.push(...this.detectOrderingFromHandlers(analysis));

		// 4. Generate eventual completion properties
		properties.push(...this.generateCompletionProperties(analysis));

		return properties;
	}

	/**
	 * Generate property: init message must be delivered first
	 */
	private generateInitFirstProperty(): TemporalProperty {
		return {
			name: "InitMessageFirst",
			description: "Init message must be delivered before any other message",
			type: "order",
			target: "init",
		};
	}

	/**
	 * Detect request-response message pairs
	 */
	private detectRequestResponsePatterns(
		analysis: CodebaseAnalysis
	): TemporalProperty[] {
		const properties: TemporalProperty[] = [];

		// Common patterns: request/response, query/result, command/ack
		const patterns = [
			{ request: "request", response: "response" },
			{ request: "query", response: "result" },
			{ request: "command", response: "ack" },
			{ request: "send", response: "receive" },
		];

		for (const pattern of patterns) {
			const hasRequest = analysis.messageTypes.some((m) =>
				m.toLowerCase().includes(pattern.request)
			);
			const hasResponse = analysis.messageTypes.some((m) =>
				m.toLowerCase().includes(pattern.response)
			);

			if (hasRequest && hasResponse) {
				properties.push({
					name: `${this.capitalize(pattern.request)}EventuallyGets${this.capitalize(pattern.response)}`,
					description: `Every ${pattern.request} eventually gets a ${pattern.response}`,
					type: "implies-eventually",
					trigger: `delivered["${pattern.request}"]`,
					target: `delivered["${pattern.response}"]`,
				});
			}
		}

		return properties;
	}

	/**
	 * Detect ordering requirements from handler preconditions
	 */
	private detectOrderingFromHandlers(
		analysis: CodebaseAnalysis
	): TemporalProperty[] {
		const properties: TemporalProperty[] = [];

		for (const handler of analysis.handlers) {
			// Check preconditions for state requirements
			for (const precondition of handler.preconditions) {
				// If handler requires authenticated state, it must come after login
				if (
					precondition.expression.includes("authenticated") &&
					analysis.messageTypes.some((m) => m.toLowerCase().includes("login"))
				) {
					properties.push({
						name: `${handler.messageType}RequiresLogin`,
						description: `${handler.messageType} can only happen after login`,
						type: "implies-eventually",
						trigger: `msgType = "${handler.messageType}"`,
						target: 'delivered["login"]',
						location: handler.location,
					});
				}
			}
		}

		return properties;
	}

	/**
	 * Generate properties for eventual completion
	 */
	private generateCompletionProperties(
		analysis: CodebaseAnalysis
	): TemporalProperty[] {
		const properties: TemporalProperty[] = [];

		// Look for "start" messages that should eventually complete
		const startMessages = analysis.messageTypes.filter((m) =>
			m.toLowerCase().includes("start")
		);
		const completeMessages = analysis.messageTypes.filter(
			(m) =>
				m.toLowerCase().includes("complete") || m.toLowerCase().includes("finish")
		);

		if (startMessages.length > 0 && completeMessages.length > 0) {
			for (const start of startMessages) {
				properties.push({
					name: `${start}EventuallyCompletes`,
					description: `Every ${start} eventually leads to completion`,
					type: "implies-eventually",
					trigger: `delivered["${start}"]`,
					target: `\\E msg \\in {"${completeMessages.join('", "')}"}  : delivered[msg]`,
				});
			}
		}

		return properties;
	}

	/**
	 * Create custom ordering rule
	 */
	createOrderingRule(rule: MessageOrderRule): TemporalProperty {
		return {
			name: `${rule.first}Before${rule.second}`,
			description: rule.description,
			type: "order",
			trigger: `delivered["${rule.second}"]`,
			target: `delivered["${rule.first}"]`,
		};
	}

	/**
	 * Capitalize first letter
	 */
	private capitalize(str: string): string {
		return str.charAt(0).toUpperCase() + str.slice(1);
	}
}

/**
 * TemporalTLAGenerator converts temporal properties to TLA+ format
 */
export class TemporalTLAGenerator {
	/**
	 * Generate TLA+ temporal formulas from properties
	 */
	generateTLAProperties(properties: TemporalProperty[]): string[] {
		return properties.map((prop) => this.generateSingleProperty(prop));
	}

	/**
	 * Generate single TLA+ temporal property
	 */
	private generateSingleProperty(prop: TemporalProperty): string {
		const lines: string[] = [];

		// Add description
		if (prop.description) {
			lines.push(`\\* ${prop.description}`);
		}

		// Generate property based on type
		switch (prop.type) {
			case "eventually":
				lines.push(`${prop.name} == <>(${prop.target})`);
				break;

			case "always":
				lines.push(`${prop.name} == [](${prop.target})`);
				break;

			case "until":
				if (prop.trigger) {
					lines.push(`${prop.name} == (${prop.trigger}) U (${prop.target})`);
				}
				break;

			case "implies-eventually":
				if (prop.trigger) {
					lines.push(`${prop.name} == [](${prop.trigger} => <>(${prop.target}))`);
				}
				break;

			case "implies-next":
				if (prop.trigger) {
					lines.push(`${prop.name} == [](${prop.trigger} => X(${prop.target}))`);
				}
				break;

			case "order":
				// For ordering: "first must happen before second"
				// Expressed as: always (second => first already happened)
				if (prop.trigger) {
					lines.push(`${prop.name} == [](${prop.trigger} => ${prop.target})`);
				} else {
					// Init-first special case
					lines.push(
						`${prop.name} == [](delivered["${prop.target}"] \\/ (\\A msg \\in MessageTypes \\\\ {"${prop.target}"} : ~delivered[msg]))`
					);
				}
				break;
		}

		return lines.join("\n");
	}

	/**
	 * Generate PROPERTY declarations for TLA+ config file
	 */
	generateConfigProperties(properties: TemporalProperty[]): string[] {
		return properties.map((prop) => `PROPERTY ${prop.name}`);
	}

	/**
	 * Generate delivered tracking variables for temporal properties
	 */
	generateDeliveredVariables(): string {
		return [
			"\\* Track which messages have been delivered (for temporal properties)",
			"VARIABLE delivered",
			"",
			"\\* Initially no messages delivered",
			"InitDelivered == delivered = [msg \\in MessageTypes |-> FALSE]",
			"",
			"\\* Mark message as delivered when processed",
			"MarkDelivered(msgType) == delivered' = [delivered EXCEPT ![msgType] = TRUE]",
		].join("\n");
	}
}

/**
 * Helper to create common temporal patterns
 */
export class TemporalPatterns {
	/**
	 * Create "eventually" property: <>P
	 */
	static eventually(name: string, description: string, condition: string): TemporalProperty {
		return {
			name,
			description,
			type: "eventually",
			target: condition,
		};
	}

	/**
	 * Create "always" property: []P
	 */
	static always(name: string, description: string, condition: string): TemporalProperty {
		return {
			name,
			description,
			type: "always",
			target: condition,
		};
	}

	/**
	 * Create "implies eventually" property: [](P => <>Q)
	 */
	static impliesEventually(
		name: string,
		description: string,
		trigger: string,
		target: string
	): TemporalProperty {
		return {
			name,
			description,
			type: "implies-eventually",
			trigger,
			target,
		};
	}

	/**
	 * Create ordering property: first before second
	 */
	static ordering(first: string, second: string, description: string): TemporalProperty {
		return {
			name: `${first}Before${second}`,
			description,
			type: "order",
			trigger: `delivered["${second}"]`,
			target: `delivered["${first}"]`,
		};
	}

	/**
	 * Create request-response property
	 */
	static requestResponse(request: string, response: string): TemporalProperty {
		return {
			name: `${request}EventuallyGets${response}`,
			description: `Every ${request} eventually gets a ${response}`,
			type: "implies-eventually",
			trigger: `delivered["${request}"]`,
			target: `delivered["${response}"]`,
		};
	}
}
