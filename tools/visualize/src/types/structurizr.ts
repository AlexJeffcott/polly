// Strict types for Structurizr DSL generation

/**
 * Shape options for elements in Structurizr diagrams
 */
export type ElementShape =
	| "Box"
	| "RoundedBox"
	| "Circle"
	| "Ellipse"
	| "Hexagon"
	| "Cylinder"
	| "Component"
	| "Person"
	| "Robot"
	| "Folder"
	| "WebBrowser"
	| "MobileDevicePortrait"
	| "MobileDeviceLandscape"
	| "Pipe";

/**
 * Routing options for relationships
 */
export type RelationshipRouting = "Direct" | "Orthogonal" | "Curved";

/**
 * Line style for relationships
 */
export type LineStyle = "Solid" | "Dashed" | "Dotted";

/**
 * Style configuration for an element tag
 */
export interface ElementStyle {
	/** Shape of the element */
	shape?: ElementShape;
	/** Icon URL */
	icon?: string;
	/** Width in pixels */
	width?: number;
	/** Height in pixels */
	height?: number;
	/** Background color (hex) */
	background?: string;
	/** Text color (hex) */
	color?: string;
	/** Font size in pixels */
	fontSize?: number;
	/** Border style */
	border?: LineStyle;
	/** Opacity (0-100) */
	opacity?: number;
	/** Metadata display */
	metadata?: boolean;
	/** Description display */
	description?: boolean;
}

/**
 * Style configuration for a relationship tag
 */
export interface RelationshipStyle {
	/** Line thickness in pixels */
	thickness?: number;
	/** Line color (hex) */
	color?: string;
	/** Line style */
	style?: LineStyle;
	/** Routing algorithm */
	routing?: RelationshipRouting;
	/** Font size for labels */
	fontSize?: number;
	/** Width for lines */
	width?: number;
	/** Position of label (0-100) */
	position?: number;
	/** Opacity (0-100) */
	opacity?: number;
}

/**
 * Complete styling configuration
 */
export interface StructurizrStyles {
	/** Element styles keyed by tag */
	elements?: Record<string, ElementStyle>;
	/** Relationship styles keyed by tag */
	relationships?: Record<string, RelationshipStyle>;
	/** Theme URL */
	theme?: string;
}

/**
 * Component relationship in the architecture
 */
export interface ComponentRelationship {
	/** Source component ID */
	from: string;
	/** Destination component ID */
	to: string;
	/** Description of the relationship */
	description: string;
	/** Technology used (e.g., "HTTP", "SQL", "Function Call") */
	technology?: string;
	/** Tags for the relationship */
	tags?: string[];
}

/**
 * Component properties (metadata)
 */
export interface ComponentProperties {
	/** Source file path and line numbers */
	Source?: string;
	/** Technology stack */
	Technology?: string;
	/** Detection pattern used */
	Pattern?: string;
	/** Message type handled */
	"Message Type"?: string;
	/** Additional custom properties */
	[key: string]: string | undefined;
}

/**
 * Group of related components
 */
export interface ComponentGroup {
	/** Group name */
	name: string;
	/** Component IDs in this group */
	components: string[];
}

/**
 * Step in a dynamic diagram sequence
 */
export interface DynamicDiagramStep {
	/** Step number */
	order: number;
	/** Source element ID */
	from: string;
	/** Destination element ID */
	to: string;
	/** Description of the interaction */
	description: string;
	/** Technology used */
	technology?: string;
}

/**
 * Dynamic diagram (sequence/flow diagram)
 */
export interface DynamicDiagram {
	/** Unique key for the diagram */
	key: string;
	/** Container scope */
	scope: string;
	/** Diagram title */
	title: string;
	/** Diagram description */
	description?: string;
	/** Sequence of steps */
	steps: DynamicDiagramStep[];
}

/**
 * Architectural perspective
 */
export interface Perspective {
	/** Perspective name (e.g., "Security", "Performance") */
	name: string;
	/** Description/reasoning */
	description: string;
}

/**
 * Container instance in a deployment node
 */
export interface ContainerInstance {
	/** Container context name (e.g., "server", "client", "background") */
	container: string;
	/** Number of instances */
	instances?: number;
}

/**
 * Deployment node in infrastructure
 */
export interface DeploymentNode {
	/** Node name */
	name: string;
	/** Description */
	description?: string;
	/** Technology */
	technology?: string;
	/** Tags (use "environment:Production" to specify environment) */
	tags?: string[];
	/** Properties */
	properties?: Record<string, string>;
	/** Container instances deployed to this node */
	containerInstances?: ContainerInstance[];
	/** Child deployment nodes (nested infrastructure) */
	children?: DeploymentNode[];
}

/**
 * Enhanced options for Structurizr DSL generation
 */
export interface StructurizrDSLOptions {
	/** Include dynamic diagrams for message flows */
	includeDynamicDiagrams?: boolean;

	/** Include component diagrams for contexts */
	includeComponentDiagrams?: boolean;

	/** Which contexts to generate component diagrams for */
	componentDiagramContexts?: string[];

	/** Styling configuration */
	styles?: StructurizrStyles;

	/** Whether to include default styles */
	includeDefaultStyles?: boolean;

	/** Component relationships to include */
	relationships?: ComponentRelationship[];

	/** Component properties to include */
	properties?: Record<string, ComponentProperties>;

	/** Component groups */
	groups?: ComponentGroup[];

	/** Dynamic diagrams to generate */
	dynamicDiagrams?: DynamicDiagram[];

	/** Architectural perspectives */
	perspectives?: Record<string, Perspective[]>;

	/** Deployment nodes */
	deploymentNodes?: DeploymentNode[];
}

/**
 * Default style palette
 */
export const DEFAULT_COLORS = {
	// Message handler types
	messageHandler: "#1168bd",
	queryHandler: "#51cf66",
	commandHandler: "#ff922b",
	authHandler: "#ff6b6b",
	subscribeHandler: "#845ef7",

	// Architectural layers
	service: "#95a5a6",
	repository: "#74b9ff",
	database: "#0984e3",
	externalSystem: "#e17055",

	// Infrastructure
	container: "#6c5ce7",
	deployment: "#00b894",

	// Text
	textLight: "#ffffff",
	textDark: "#2d3436",

	// Relationships
	relationship: "#707070",
} as const;

/**
 * Default element styles based on common tags
 */
export const DEFAULT_ELEMENT_STYLES: Record<string, ElementStyle> = {
	"Message Handler": {
		shape: "Hexagon",
		background: DEFAULT_COLORS.messageHandler,
		color: DEFAULT_COLORS.textLight,
		fontSize: 14,
	},
	Query: {
		background: DEFAULT_COLORS.queryHandler,
		color: DEFAULT_COLORS.textDark,
	},
	Command: {
		background: DEFAULT_COLORS.commandHandler,
		color: DEFAULT_COLORS.textDark,
	},
	Authentication: {
		background: DEFAULT_COLORS.authHandler,
		color: DEFAULT_COLORS.textLight,
	},
	Subscribe: {
		background: DEFAULT_COLORS.subscribeHandler,
		color: DEFAULT_COLORS.textLight,
	},
	Service: {
		shape: "RoundedBox",
		background: DEFAULT_COLORS.service,
		color: DEFAULT_COLORS.textLight,
	},
	Repository: {
		shape: "Cylinder",
		background: DEFAULT_COLORS.repository,
		color: DEFAULT_COLORS.textDark,
	},
	Database: {
		shape: "Cylinder",
		background: DEFAULT_COLORS.database,
		color: DEFAULT_COLORS.textLight,
	},
	"External System": {
		background: DEFAULT_COLORS.externalSystem,
		color: DEFAULT_COLORS.textLight,
	},
	Container: {
		background: DEFAULT_COLORS.container,
		color: DEFAULT_COLORS.textLight,
	},
};

/**
 * Default relationship styles
 */
export const DEFAULT_RELATIONSHIP_STYLES: Record<string, RelationshipStyle> = {
	Relationship: {
		routing: "Orthogonal",
		thickness: 2,
		color: DEFAULT_COLORS.relationship,
		fontSize: 12,
	},
	Sync: {
		style: "Solid",
		thickness: 2,
	},
	Async: {
		style: "Dashed",
		thickness: 2,
	},
	Database: {
		style: "Solid",
		thickness: 3,
		color: DEFAULT_COLORS.database,
	},
};

/**
 * Default theme URL
 */
export const DEFAULT_THEME =
	"https://static.structurizr.com/themes/default/theme.json";
