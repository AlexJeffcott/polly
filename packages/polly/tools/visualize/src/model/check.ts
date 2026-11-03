// Reads a declared model from an untyped value and checks it before any DSL
// is written. Every problem is collected, so one run reports all of them.
// A model with any problem is refused whole: no partial DSL is written.

import { isRecord, readRecord, readString } from "../../../../src/shared/lib/guards";
import type {
  ElementShape,
  ElementStyle,
  LineStyle,
  RelationshipRouting,
  RelationshipStyle,
} from "../types/structurizr";
import type {
  Component,
  Container,
  DeclaredModel,
  DeploymentEnvironment,
  DeploymentNode,
  DynamicStep,
  Layout,
  Person,
  Relationship,
  SoftwareSystem,
  View,
} from "./types";

export class DeclaredModelError extends Error {
  override name = "DeclaredModelError";
  constructor(readonly problems: string[]) {
    super(
      `The declared model has ${problems.length} problem(s):\n${problems.map((p) => `  - ${p}`).join("\n")}`
    );
  }
}

const ID = /^[A-Za-z][A-Za-z0-9_]*$/;
const VIEW_KEY = /^[A-Za-z0-9_-]+$/;
const COLOUR = /^#[0-9A-Fa-f]{6}$/;
const LAYOUTS: readonly Layout[] = ["lr", "rl", "tb", "bt"];
const SHAPES: readonly ElementShape[] = [
  "Box",
  "RoundedBox",
  "Circle",
  "Ellipse",
  "Hexagon",
  "Cylinder",
  "Component",
  "Person",
  "Robot",
  "Folder",
  "WebBrowser",
  "MobileDevicePortrait",
  "MobileDeviceLandscape",
  "Pipe",
];
const LINE_STYLES: readonly LineStyle[] = ["Solid", "Dashed", "Dotted"];
const ROUTINGS: readonly RelationshipRouting[] = ["Direct", "Orthogonal", "Curved"];

type ElementKind = "person" | "system" | "container" | "component";

/** `{ [key]: value }`, or `{}` where the value is absent, so absent stays absent. */
function opt<K extends string, V>(key: K, value: V | undefined): Partial<Record<K, V>> {
  if (value === undefined) return {};
  const present: Partial<Record<K, V>> = {};
  present[key] = value;
  return present;
}

function oneOf<T extends string>(values: readonly T[], value: unknown): value is T {
  return values.some((allowed) => allowed === value);
}

class Reader {
  readonly problems: string[] = [];

  problem(message: string): void {
    this.problems.push(message);
  }

  /** A required string with no line break. */
  text(value: unknown, where: string): string {
    const text = readString(value);
    if (text === undefined || text === "") {
      this.problem(`${where} must be a non-empty string`);
      return "";
    }
    if (/[\r\n]/.test(text)) this.problem(`${where} must not contain a line break`);
    return text;
  }

  /** An optional string with no line break; absent stays absent. */
  optionalText(value: unknown, where: string): string | undefined {
    return value === undefined ? undefined : this.text(value, where);
  }

  id(value: unknown, where: string): string {
    const id = this.text(value, where);
    if (id !== "" && !ID.test(id)) {
      this.problem(`${where} "${id}" must start with a letter and hold only letters, digits and _`);
    }
    return id;
  }

  /** Optional tags; a tag holds no comma, since the DSL joins tags with commas. */
  tags(value: unknown, where: string): string[] | undefined {
    if (value === undefined) return undefined;
    if (!Array.isArray(value)) {
      this.problem(`${where} must be an array of strings`);
      return undefined;
    }
    return value.map((tag, index) => {
      const text = this.text(tag, `${where}[${index}]`);
      if (text.includes(",")) this.problem(`${where}[${index}] "${text}" must not contain a comma`);
      return text;
    });
  }

  list(value: unknown, where: string): unknown[] {
    if (!Array.isArray(value)) {
      this.problem(`${where} must be an array`);
      return [];
    }
    return value;
  }

  optionalList(value: unknown, where: string): unknown[] | undefined {
    return value === undefined ? undefined : this.list(value, where);
  }

  record(value: unknown, where: string): Record<string, unknown> {
    const record = readRecord(value);
    if (record === undefined) {
      this.problem(`${where} must be an object`);
      return {};
    }
    return record;
  }

  /** One of `values`, where present. */
  optionalOneOf<T extends string>(
    values: readonly T[],
    value: unknown,
    where: string
  ): T | undefined {
    if (value === undefined) return undefined;
    if (oneOf(values, value)) return value;
    this.problem(`${where} must be one of ${values.join(", ")}`);
    return undefined;
  }

  optionalNumber(value: unknown, where: string): number | undefined {
    if (value === undefined) return undefined;
    if (typeof value === "number" && Number.isFinite(value)) return value;
    this.problem(`${where} must be a number`);
    return undefined;
  }

  optionalBoolean(value: unknown, where: string): boolean | undefined {
    if (value === undefined) return undefined;
    if (typeof value === "boolean") return value;
    this.problem(`${where} must be true or false`);
    return undefined;
  }

  /** A colour as `#rrggbb`, where present. */
  optionalColour(value: unknown, where: string): string | undefined {
    if (value === undefined) return undefined;
    const text = readString(value);
    if (text !== undefined && COLOUR.test(text)) return text;
    this.problem(`${where} must be a colour as #rrggbb`);
    return undefined;
  }

  /** Every key of `raw` is one of `known`. */
  onlyKeys(raw: Record<string, unknown>, known: readonly string[], where: string): void {
    for (const key of Object.keys(raw)) {
      if (!known.includes(key))
        this.problem(`${where}.${key} is not a known field; known: ${known.join(", ")}`);
    }
  }
}

function readPerson(r: Reader, value: unknown, where: string): Person {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["id", "name", "description", "tags"], where);
  return {
    id: r.id(raw["id"], `${where}.id`),
    name: r.text(raw["name"], `${where}.name`),
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
    ...opt("tags", r.tags(raw["tags"], `${where}.tags`)),
  };
}

function readComponent(r: Reader, value: unknown, where: string): Component {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["id", "name", "description", "technology", "tags"], where);
  return {
    id: r.id(raw["id"], `${where}.id`),
    name: r.text(raw["name"], `${where}.name`),
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
    ...opt("technology", r.optionalText(raw["technology"], `${where}.technology`)),
    ...opt("tags", r.tags(raw["tags"], `${where}.tags`)),
  };
}

function readContainer(r: Reader, value: unknown, where: string): Container {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["id", "name", "description", "technology", "tags", "components"], where);
  const components = r
    .optionalList(raw["components"], `${where}.components`)
    ?.map((c, i) => readComponent(r, c, `${where}.components[${i}]`));
  return {
    id: r.id(raw["id"], `${where}.id`),
    name: r.text(raw["name"], `${where}.name`),
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
    ...opt("technology", r.optionalText(raw["technology"], `${where}.technology`)),
    ...opt("tags", r.tags(raw["tags"], `${where}.tags`)),
    ...opt("components", components),
  };
}

function readSystem(r: Reader, value: unknown, where: string): SoftwareSystem {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["id", "name", "description", "tags", "containers"], where);
  const containers = r
    .optionalList(raw["containers"], `${where}.containers`)
    ?.map((c, i) => readContainer(r, c, `${where}.containers[${i}]`));
  return {
    id: r.id(raw["id"], `${where}.id`),
    name: r.text(raw["name"], `${where}.name`),
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
    ...opt("tags", r.tags(raw["tags"], `${where}.tags`)),
    ...opt("containers", containers),
  };
}

function readRelationship(r: Reader, value: unknown, where: string): Relationship {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["from", "to", "description", "technology", "tags"], where);
  return {
    from: r.id(raw["from"], `${where}.from`),
    to: r.id(raw["to"], `${where}.to`),
    description: r.text(raw["description"], `${where}.description`),
    ...opt("technology", r.optionalText(raw["technology"], `${where}.technology`)),
    ...opt("tags", r.tags(raw["tags"], `${where}.tags`)),
  };
}

function readNode(r: Reader, value: unknown, where: string): DeploymentNode {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["name", "description", "technology", "containers", "nodes"], where);
  const containers = r
    .optionalList(raw["containers"], `${where}.containers`)
    ?.map((c, i) => r.id(c, `${where}.containers[${i}]`));
  const nodes = r
    .optionalList(raw["nodes"], `${where}.nodes`)
    ?.map((n, i) => readNode(r, n, `${where}.nodes[${i}]`));
  return {
    name: r.text(raw["name"], `${where}.name`),
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
    ...opt("technology", r.optionalText(raw["technology"], `${where}.technology`)),
    ...opt("containers", containers),
    ...opt("nodes", nodes),
  };
}

function readEnvironment(r: Reader, value: unknown, where: string): DeploymentEnvironment {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["id", "name", "nodes"], where);
  return {
    id: r.id(raw["id"], `${where}.id`),
    name: r.text(raw["name"], `${where}.name`),
    nodes: r
      .list(raw["nodes"], `${where}.nodes`)
      .map((n, i) => readNode(r, n, `${where}.nodes[${i}]`)),
  };
}

function readStep(r: Reader, value: unknown, where: string): DynamicStep {
  const raw = r.record(value, where);
  r.onlyKeys(raw, ["from", "to", "description"], where);
  return {
    from: r.id(raw["from"], `${where}.from`),
    to: r.id(raw["to"], `${where}.to`),
    description: r.text(raw["description"], `${where}.description`),
  };
}

const VIEW_FIELDS = {
  systemContext: ["system"],
  container: ["system"],
  component: ["container"],
  dynamic: ["scope", "steps"],
  deployment: ["scope", "environment"],
} as const;
const VIEW_KINDS = Object.keys(VIEW_FIELDS);

function readView(r: Reader, value: unknown, where: string): View | undefined {
  const raw = r.record(value, where);
  const kind = raw["kind"];
  if (!oneOf(["systemContext", "container", "component", "dynamic", "deployment"], kind)) {
    r.problem(`${where}.kind must be one of ${VIEW_KINDS.join(", ")}; got ${JSON.stringify(kind)}`);
    return undefined;
  }
  r.onlyKeys(raw, ["kind", "key", "description", "layout", ...VIEW_FIELDS[kind]], where);

  const key = r.text(raw["key"], `${where}.key`);
  if (key !== "" && !VIEW_KEY.test(key)) {
    r.problem(`${where}.key "${key}" must hold only letters, digits, _ and -`);
  }
  const layout = raw["layout"];
  if (!oneOf(LAYOUTS, layout)) {
    r.problem(`${where}.layout must be one of ${LAYOUTS.join(", ")}`);
    return undefined;
  }
  const base = {
    key,
    layout,
    ...opt("description", r.optionalText(raw["description"], `${where}.description`)),
  };

  switch (kind) {
    case "systemContext":
    case "container":
      return { ...base, kind, system: r.id(raw["system"], `${where}.system`) };
    case "component":
      return { ...base, kind, container: r.id(raw["container"], `${where}.container`) };
    case "dynamic": {
      const steps = r
        .list(raw["steps"], `${where}.steps`)
        .map((s, i) => readStep(r, s, `${where}.steps[${i}]`));
      if (steps.length === 0) r.problem(`${where}.steps must hold at least one step`);
      return { ...base, kind, scope: r.id(raw["scope"], `${where}.scope`), steps };
    }
    case "deployment": {
      const scope = raw["scope"] === "*" ? "*" : r.id(raw["scope"], `${where}.scope`);
      return {
        ...base,
        kind,
        scope,
        environment: r.id(raw["environment"], `${where}.environment`),
      };
    }
  }
}

function readElementStyle(r: Reader, value: unknown, where: string): ElementStyle {
  const raw = r.record(value, where);
  r.onlyKeys(
    raw,
    [
      "shape",
      "icon",
      "width",
      "height",
      "background",
      "color",
      "fontSize",
      "border",
      "opacity",
      "metadata",
      "description",
    ],
    where
  );
  const icon = r.optionalText(raw["icon"], `${where}.icon`);
  if (icon !== undefined && /[\s"]/.test(icon)) {
    r.problem(`${where}.icon must not contain whitespace or quotes`);
  }
  return {
    ...opt("shape", r.optionalOneOf(SHAPES, raw["shape"], `${where}.shape`)),
    ...opt("icon", icon),
    ...opt("width", r.optionalNumber(raw["width"], `${where}.width`)),
    ...opt("height", r.optionalNumber(raw["height"], `${where}.height`)),
    ...opt("background", r.optionalColour(raw["background"], `${where}.background`)),
    ...opt("color", r.optionalColour(raw["color"], `${where}.color`)),
    ...opt("fontSize", r.optionalNumber(raw["fontSize"], `${where}.fontSize`)),
    ...opt("border", r.optionalOneOf(LINE_STYLES, raw["border"], `${where}.border`)),
    ...opt("opacity", r.optionalNumber(raw["opacity"], `${where}.opacity`)),
    ...opt("metadata", r.optionalBoolean(raw["metadata"], `${where}.metadata`)),
    ...opt("description", r.optionalBoolean(raw["description"], `${where}.description`)),
  };
}

function readRelationshipStyle(r: Reader, value: unknown, where: string): RelationshipStyle {
  const raw = r.record(value, where);
  r.onlyKeys(
    raw,
    ["thickness", "color", "style", "routing", "fontSize", "width", "position", "opacity"],
    where
  );
  return {
    ...opt("thickness", r.optionalNumber(raw["thickness"], `${where}.thickness`)),
    ...opt("color", r.optionalColour(raw["color"], `${where}.color`)),
    ...opt("style", r.optionalOneOf(LINE_STYLES, raw["style"], `${where}.style`)),
    ...opt("routing", r.optionalOneOf(ROUTINGS, raw["routing"], `${where}.routing`)),
    ...opt("fontSize", r.optionalNumber(raw["fontSize"], `${where}.fontSize`)),
    ...opt("width", r.optionalNumber(raw["width"], `${where}.width`)),
    ...opt("position", r.optionalNumber(raw["position"], `${where}.position`)),
    ...opt("opacity", r.optionalNumber(raw["opacity"], `${where}.opacity`)),
  };
}

function readStylesByTag<T>(
  r: Reader,
  value: unknown,
  where: string,
  readStyle: (r: Reader, value: unknown, where: string) => T
): Record<string, T> | undefined {
  if (value === undefined) return undefined;
  const byTag = r.record(value, where);
  const result: Record<string, T> = {};
  for (const [tag, style] of Object.entries(byTag)) {
    result[tag] = readStyle(r, style, `${where}["${tag}"]`);
  }
  return result;
}

/** Every element id the model declares, by the kind of element it names. */
function indexElements(r: Reader, model: DeclaredModel): Map<string, ElementKind> {
  const kinds = new Map<string, ElementKind>();
  const declare = (id: string, kind: ElementKind): void => {
    if (kinds.has(id)) {
      r.problem(`id "${id}" is declared more than once`);
      return;
    }
    kinds.set(id, kind);
  };
  for (const person of model.people) declare(person.id, "person");
  for (const system of model.systems) {
    declare(system.id, "system");
    for (const container of system.containers ?? []) {
      declare(container.id, "container");
      for (const component of container.components ?? []) declare(component.id, "component");
    }
  }
  const environments = new Set<string>();
  for (const environment of model.deployments ?? []) {
    if (kinds.has(environment.id) || environments.has(environment.id)) {
      r.problem(`id "${environment.id}" is declared more than once`);
    }
    environments.add(environment.id);
  }
  return kinds;
}

function checkNodes(
  r: Reader,
  nodes: DeploymentNode[],
  kinds: Map<string, ElementKind>,
  where: string
): void {
  const names = new Set<string>();
  nodes.forEach((node, index) => {
    const at = `${where}[${index}]`;
    if (names.has(node.name)) r.problem(`${at}.name "${node.name}" is used twice under one parent`);
    names.add(node.name);
    for (const id of node.containers ?? []) {
      if (kinds.get(id) !== "container") {
        r.problem(`${at}.containers names "${id}", which is not a container`);
      }
    }
    checkNodes(r, node.nodes ?? [], kinds, `${at}.nodes`);
  });
}

function checkRelationships(
  r: Reader,
  model: DeclaredModel,
  kinds: Map<string, ElementKind>
): Set<string> {
  const pairs = new Set<string>();
  const seen = new Set<string>();
  model.relationships.forEach((rel, index) => {
    const at = `relationships[${index}]`;
    if (!kinds.has(rel.from)) r.problem(`${at}.from "${rel.from}" names no element`);
    if (!kinds.has(rel.to)) r.problem(`${at}.to "${rel.to}" names no element`);
    if (rel.from === rel.to) r.problem(`${at} runs from "${rel.from}" to itself`);
    const identity = JSON.stringify([rel.from, rel.to, rel.description]);
    if (seen.has(identity)) {
      r.problem(`${at} repeats ${rel.from} -> ${rel.to} "${rel.description}"`);
    }
    seen.add(identity);
    pairs.add(JSON.stringify([rel.from, rel.to]));
  });
  return pairs;
}

function checkView(
  r: Reader,
  view: View,
  at: string,
  kinds: Map<string, ElementKind>,
  pairs: Set<string>,
  environments: Set<string>
): void {
  switch (view.kind) {
    case "systemContext":
    case "container":
      if (kinds.get(view.system) !== "system") {
        r.problem(`${at}.system "${view.system}" is not a software system`);
      }
      return;
    case "component":
      if (kinds.get(view.container) !== "container") {
        r.problem(`${at}.container "${view.container}" is not a container`);
      }
      return;
    case "dynamic": {
      const scopeKind = kinds.get(view.scope);
      if (scopeKind !== "system" && scopeKind !== "container") {
        r.problem(`${at}.scope "${view.scope}" is not a software system or a container`);
      }
      view.steps.forEach((step, stepIndex) => {
        const stepAt = `${at}.steps[${stepIndex}]`;
        if (!pairs.has(JSON.stringify([step.from, step.to]))) {
          r.problem(`${stepAt} ${step.from} -> ${step.to} matches no declared relationship`);
        }
        if (step.from === view.scope || step.to === view.scope) {
          r.problem(`${stepAt} names the view's own scope "${view.scope}"`);
        }
      });
      return;
    }
    case "deployment":
      if (view.scope !== "*" && kinds.get(view.scope) !== "system") {
        r.problem(`${at}.scope "${view.scope}" is not a software system or "*"`);
      }
      if (!environments.has(view.environment)) {
        r.problem(`${at}.environment "${view.environment}" names no deployment environment`);
      }
      return;
  }
}

function checkReferences(r: Reader, model: DeclaredModel): void {
  const kinds = indexElements(r, model);
  // A duplicate id makes every reference to it ambiguous, so references are
  // checked only once each id names one element.
  if (r.problems.length > 0) return;
  const pairs = checkRelationships(r, model, kinds);
  const environments = new Set((model.deployments ?? []).map((e) => e.id));

  (model.deployments ?? []).forEach((environment, index) => {
    checkNodes(r, environment.nodes, kinds, `deployments[${index}].nodes`);
  });

  const keys = new Set<string>();
  model.views.forEach((view, index) => {
    const at = `views[${index}]`;
    if (keys.has(view.key)) r.problem(`${at}.key "${view.key}" is used by another view`);
    keys.add(view.key);
    checkView(r, view, at, kinds, pairs, environments);
  });
}

function readStyles(r: Reader, value: unknown): DeclaredModel["styles"] {
  if (value === undefined) return undefined;
  const raw = r.record(value, "styles");
  r.onlyKeys(raw, ["elements", "relationships"], "styles");
  return {
    ...opt("elements", readStylesByTag(r, raw["elements"], "styles.elements", readElementStyle)),
    ...opt(
      "relationships",
      readStylesByTag(r, raw["relationships"], "styles.relationships", readRelationshipStyle)
    ),
  };
}

/** The declared model in `value`, or a DeclaredModelError listing every problem. */
export function readDeclaredModel(value: unknown): DeclaredModel {
  if (!isRecord(value)) {
    throw new DeclaredModelError(["the model must be an object"]);
  }
  const r = new Reader();
  r.onlyKeys(
    value,
    ["name", "description", "people", "systems", "relationships", "deployments", "views", "styles"],
    "model"
  );
  const people = r.list(value["people"], "people").map((p, i) => readPerson(r, p, `people[${i}]`));
  const systems = r
    .list(value["systems"], "systems")
    .map((s, i) => readSystem(r, s, `systems[${i}]`));
  const relationships = r
    .list(value["relationships"], "relationships")
    .map((rel, i) => readRelationship(r, rel, `relationships[${i}]`));
  const deployments = r
    .optionalList(value["deployments"], "deployments")
    ?.map((e, i) => readEnvironment(r, e, `deployments[${i}]`));
  const views = r
    .list(value["views"], "views")
    .map((v, i) => readView(r, v, `views[${i}]`))
    .filter((v): v is View => v !== undefined);
  if (systems.length === 0) r.problem("systems must hold at least one software system");
  if (views.length === 0) r.problem("views must hold at least one view");

  const model: DeclaredModel = {
    name: r.text(value["name"], "name"),
    people,
    systems,
    relationships,
    views,
    ...opt("description", r.optionalText(value["description"], "description")),
    ...opt("deployments", deployments),
    ...opt("styles", readStyles(r, value["styles"])),
  };

  // References are checked only on a model whose shape is sound, so a
  // malformed id does not also report every reference to it.
  if (r.problems.length === 0) checkReferences(r, model);
  if (r.problems.length > 0) throw new DeclaredModelError(r.problems);
  return model;
}
