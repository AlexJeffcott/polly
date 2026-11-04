// A C4 model a project declares, as opposed to one polly infers from source.
//
// `polly visualize generate --model <file>` imports the file and calls its
// default export, which returns a DeclaredModel. polly checks it and writes
// it as Structurizr DSL. Nothing in it is inferred and nothing has a default:
// every view states its layout, and an element states what it is.

import type { ElementStyle, RelationshipStyle } from "../types/structurizr";

/** An identifier the DSL can use: a letter, then letters, digits and underscores. */
export type ElementId = string;

/** Key-value rows the viewer shows in an element's or relationship's tooltip, not on the diagram. */
export type Properties = Record<string, string>;

/**
 * The identifier of an element that another workspace owns, in that workspace:
 * `ss-next` for a system, `c-webui` for a container of it. A fragment refers to
 * such an element by its path (`ss-next.c-webui`) and does not declare it. The
 * full workspace declares it like any other element, so a local site shows it.
 */
export type ElementRef = string;

export type Person = {
  id: ElementId;
  ref?: ElementRef;
  name: string;
  description?: string;
  tags?: string[];
  properties?: Properties;
};

export type Component = {
  id: ElementId;
  name: string;
  description?: string;
  technology?: string;
  tags?: string[];
  properties?: Properties;
};

export type Container = {
  id: ElementId;
  ref?: ElementRef;
  name: string;
  description?: string;
  technology?: string;
  tags?: string[];
  properties?: Properties;
  components?: Component[];
};

export type SoftwareSystem = {
  id: ElementId;
  ref?: ElementRef;
  name: string;
  description?: string;
  tags?: string[];
  properties?: Properties;
  containers?: Container[];
};

export type Relationship = {
  from: ElementId;
  to: ElementId;
  description: string;
  technology?: string;
  tags?: string[];
  properties?: Properties;
};

export type DeploymentNode = {
  name: string;
  description?: string;
  technology?: string;
  properties?: Properties;
  /** Ids of the containers that run on this node. */
  containers?: ElementId[];
  nodes?: DeploymentNode[];
};

export type DeploymentEnvironment = {
  id: ElementId;
  name: string;
  nodes: DeploymentNode[];
};

export type Layout = "lr" | "rl" | "tb" | "bt";

type ViewBase = {
  /** The view's key: letters, digits, `_` and `-`, unique in the model. */
  key: string;
  description?: string;
  layout: Layout;
};

export type SystemContextView = ViewBase & { kind: "systemContext"; system: ElementId };

export type ContainerView = ViewBase & { kind: "container"; system: ElementId };

export type ComponentView = ViewBase & { kind: "component"; container: ElementId };

export type DynamicStep = { from: ElementId; to: ElementId; description: string };

export type DynamicView = ViewBase & {
  kind: "dynamic";
  /** The software system or container the sequence runs in. */
  scope: ElementId;
  /** Each step names a relationship the model declares, in the order it happens. */
  steps: DynamicStep[];
};

export type DeploymentView = ViewBase & {
  kind: "deployment";
  /** A software system id, or `*` for every system in the environment. */
  scope: ElementId | "*";
  environment: ElementId;
};

export type View = SystemContextView | ContainerView | ComponentView | DynamicView | DeploymentView;

export type DeclaredModel = {
  name: string;
  description?: string;
  people: Person[];
  systems: SoftwareSystem[];
  relationships: Relationship[];
  deployments?: DeploymentEnvironment[];
  views: View[];
  styles?: {
    elements?: Record<string, ElementStyle>;
    relationships?: Record<string, RelationshipStyle>;
  };
};

/** The default export of a `--model` file. */
export type DeclaredModelSource = () => DeclaredModel | Promise<DeclaredModel>;
