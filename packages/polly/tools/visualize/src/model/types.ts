// A C4 model a project declares, as opposed to one polly infers from source.
//
// `polly visualize generate --model <file>` imports the file and calls its
// default export, which returns a DeclaredModel. polly checks it and writes
// it as Structurizr DSL. Nothing in it is inferred and nothing has a default:
// every view states its layout, and an element states what it is.

import type { ElementStyle, RelationshipStyle } from "../types/structurizr";

/** An identifier the DSL can use: a letter, then letters, digits and underscores. */
export type ElementId = string;

export type Person = {
  id: ElementId;
  name: string;
  description?: string;
  tags?: string[];
};

export type Component = {
  id: ElementId;
  name: string;
  description?: string;
  technology?: string;
  tags?: string[];
};

export type Container = {
  id: ElementId;
  name: string;
  description?: string;
  technology?: string;
  tags?: string[];
  components?: Component[];
};

export type SoftwareSystem = {
  id: ElementId;
  name: string;
  description?: string;
  tags?: string[];
  containers?: Container[];
};

export type Relationship = {
  from: ElementId;
  to: ElementId;
  description: string;
  technology?: string;
  tags?: string[];
};

export type DeploymentNode = {
  name: string;
  description?: string;
  technology?: string;
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
