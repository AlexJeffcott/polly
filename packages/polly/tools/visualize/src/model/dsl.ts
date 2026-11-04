// Writes a checked DeclaredModel as Structurizr DSL. It writes exactly what
// the model declares: no element, relationship, view or style is added.
//
// Two outputs: a whole workspace, and a fragment that joins another
// workspace. The fragment leaves out what that workspace owns: each element
// with a ref, each relationship between two of them, and each view of one.

import { DeclaredModelError } from "./check";
import type {
  Component,
  Container,
  DeclaredModel,
  DeploymentEnvironment,
  DeploymentNode,
  Person,
  Properties,
  Relationship,
  SoftwareSystem,
  View,
} from "./types";

/** A DSL string literal. The checker has already refused line breaks. */
function quote(text: string): string {
  return `"${text.replace(/\\/g, "\\\\").replace(/"/g, '\\"')}"`;
}

/**
 * Positional DSL arguments. An absent argument before a present one is
 * written as "" so the later one keeps its position; trailing absent ones
 * are left out.
 */
function args(...values: Array<string | undefined>): string {
  let last = values.length - 1;
  while (last >= 0 && values[last] === undefined) last--;
  return values
    .slice(0, last + 1)
    .map((value) => quote(value ?? ""))
    .join(" ");
}

function tagList(tags: string[] | undefined): string | undefined {
  return tags === undefined || tags.length === 0 ? undefined : tags.join(",");
}

/** A properties block at `indent`, or nothing where the element declares none. */
function propertyLines(properties: Properties | undefined, indent: string): string[] {
  const entries = Object.entries(properties ?? {});
  if (entries.length === 0) return [];
  return [
    `${indent}properties {`,
    ...entries.map(([key, value]) => `${indent}  ${quote(key)} ${quote(value)}`),
    `${indent}}`,
  ];
}

/** `head`, with a block holding `body` where the body has lines. */
function withBlock(head: string, body: string[], indent: string): string[] {
  return body.length === 0 ? [head] : [`${head} {`, ...body, `${indent}}`];
}

function personLines(person: Person): string[] {
  return withBlock(
    `    ${person.id} = person ${args(person.name, person.description, tagList(person.tags))}`,
    propertyLines(person.properties, "      "),
    "    "
  );
}

function componentLines(component: Component): string[] {
  return withBlock(
    `        ${component.id} = component ${args(
      component.name,
      component.description,
      component.technology,
      tagList(component.tags)
    )}`,
    propertyLines(component.properties, "          "),
    "        "
  );
}

function containerLines(container: Container): string[] {
  const head = `      ${container.id} = container ${args(
    container.name,
    container.description,
    container.technology,
    tagList(container.tags)
  )}`;
  return withBlock(
    head,
    [
      ...propertyLines(container.properties, "        "),
      ...(container.components ?? []).flatMap(componentLines),
    ],
    "      "
  );
}

function systemLines(system: SoftwareSystem): string[] {
  const head = `    ${system.id} = softwareSystem ${args(system.name, system.description, tagList(system.tags))}`;
  return withBlock(
    head,
    [
      ...propertyLines(system.properties, "      "),
      ...(system.containers ?? []).flatMap(containerLines),
    ],
    "    "
  );
}

/** How a reference names an element: its id in a workspace, its path in a fragment. */
type PathOf = (id: string) => string;

const byId: PathOf = (id) => id;

function relationshipLines(rel: Relationship, path: PathOf): string[] {
  return withBlock(
    `    ${path(rel.from)} -> ${path(rel.to)} ${args(rel.description, rel.technology, tagList(rel.tags))}`,
    propertyLines(rel.properties, "      "),
    "    "
  );
}

function nodeLines(node: DeploymentNode, indent: string, path: PathOf): string[] {
  return [
    `${indent}deploymentNode ${args(node.name, node.description, node.technology)} {`,
    ...propertyLines(node.properties, `${indent}  `),
    ...(node.containers ?? []).map((id) => `${indent}  containerInstance ${path(id)}`),
    ...(node.nodes ?? []).flatMap((child) => nodeLines(child, `${indent}  `, path)),
    `${indent}}`,
  ];
}

function environmentLines(environment: DeploymentEnvironment, path: PathOf): string[] {
  return [
    `    ${environment.id} = deploymentEnvironment ${quote(environment.name)} {`,
    ...environment.nodes.flatMap((node) => nodeLines(node, "      ", path)),
    "    }",
  ];
}

function viewLines(view: View, path: PathOf): string[] {
  const titled = args(view.key, view.description);
  const layout = `      autoLayout ${view.layout}`;
  switch (view.kind) {
    case "systemContext":
      return [
        `    systemContext ${path(view.system)} ${titled} {`,
        "      include *",
        layout,
        "    }",
      ];
    case "container":
      return [`    container ${path(view.system)} ${titled} {`, "      include *", layout, "    }"];
    case "component":
      return [
        `    component ${path(view.container)} ${titled} {`,
        "      include *",
        layout,
        "    }",
      ];
    case "dynamic":
      return [
        `    dynamic ${path(view.scope)} ${titled} {`,
        ...view.steps.map(
          (step) => `      ${path(step.from)} -> ${path(step.to)} ${quote(step.description)}`
        ),
        layout,
        "    }",
      ];
    case "deployment":
      return [
        `    deployment ${view.scope === "*" ? "*" : path(view.scope)} ${view.environment} ${titled} {`,
        "      include *",
        layout,
        "    }",
      ];
  }
}

function styleLines(
  kind: "element" | "relationship",
  byTag: Record<string, object> | undefined
): string[] {
  return Object.entries(byTag ?? {}).flatMap(([tag, style]) => [
    `      ${kind} ${quote(tag)} {`,
    ...Object.entries(style).map(([property, value]) => `        ${property} ${String(value)}`),
    "      }",
  ]);
}

/** The Structurizr DSL for a model readDeclaredModel has checked. */
export function declaredModelDSL(model: DeclaredModel): string {
  const styles = [
    ...styleLines("element", model.styles?.elements),
    ...styleLines("relationship", model.styles?.relationships),
  ];
  const lines = [
    "// Written by polly visualize generate --model, from a declared model. Edit the model, not this file.",
    `workspace ${args(model.name, model.description)} {`,
    "",
    "  !identifiers flat",
    "",
    "  model {",
    ...model.people.flatMap(personLines),
    ...model.systems.flatMap(systemLines),
    "",
    ...model.relationships.flatMap((rel) => relationshipLines(rel, byId)),
    ...(model.deployments ?? []).flatMap((environment) => [
      "",
      ...environmentLines(environment, byId),
    ]),
    "  }",
    "",
    "  views {",
    // The viewer lists the views, and opens the first, in the order the model declares them,
    // and shows each element's description and properties in a tooltip on hover.
    "    properties {",
    '      "structurizr.sort" "created"',
    '      "structurizr.tooltips" "true"',
    "    }",
    ...model.views.flatMap((view) => viewLines(view, byId)),
    ...(styles.length === 0 ? [] : ["    styles {", ...styles, "    }"]),
    "  }",
    "}",
    "",
  ];
  return lines.join("\n");
}

/** The two files of a fragment, and what it leaves to the workspace it joins. */
export type DeclaredModelFragment = {
  /** Goes inside that workspace's `model` block. */
  model: string;
  /** Goes inside that workspace's `views` block. */
  views: string;
  /** One line for each element, relationship and view the fragment leaves out. */
  omitted: string[];
};

/** Each element's path in a workspace with hierarchical identifiers, and which have a ref. */
function fragmentPaths(model: DeclaredModel): { paths: Map<string, string>; owned: Set<string> } {
  const paths = new Map<string, string>();
  const owned = new Set<string>();
  const place = (id: string, path: string, ref: string | undefined): void => {
    paths.set(id, path);
    if (ref !== undefined) owned.add(id);
  };
  for (const person of model.people) place(person.id, person.ref ?? person.id, person.ref);
  for (const system of model.systems) {
    const systemPath = system.ref ?? system.id;
    place(system.id, systemPath, system.ref);
    for (const container of system.containers ?? []) {
      const containerPath = `${systemPath}.${container.ref ?? container.id}`;
      place(container.id, containerPath, container.ref);
      for (const component of container.components ?? []) {
        place(component.id, `${containerPath}.${component.id}`, undefined);
      }
    }
  }
  for (const environment of model.deployments ?? [])
    place(environment.id, environment.id, undefined);
  return { paths, owned };
}

/** The view's subject, which decides whether the view belongs to the other workspace. */
function viewSubject(view: View): string | undefined {
  switch (view.kind) {
    case "systemContext":
    case "container":
      return view.system;
    case "component":
      return view.container;
    case "dynamic":
      return view.scope;
    case "deployment":
      return view.scope === "*" ? undefined : view.scope;
  }
}

/** Lines one level less deep, for a file included inside a block. */
function outdented(lines: string[]): string {
  return lines.map((line) => line.replace(/^ {4}/, "")).join("\n");
}

/**
 * A fragment of a model readDeclaredModel has checked, for a workspace that
 * uses `!identifiers hierarchical` and holds each element the model gives a
 * ref. A dynamic step between two such elements is refused: the fragment
 * leaves their relationship out, so the step would name no relationship.
 */
export function declaredModelFragment(model: DeclaredModel): DeclaredModelFragment {
  const { paths, owned } = fragmentPaths(model);
  const path: PathOf = (id) => paths.get(id) ?? id;
  const omitted: string[] = [];
  const problems: string[] = [];

  for (const person of model.people) {
    if (person.ref !== undefined) omitted.push(`person ${person.id}, owned as ${person.ref}`);
  }
  for (const system of model.systems) {
    if (system.ref !== undefined) omitted.push(`system ${system.id}, owned as ${system.ref}`);
  }
  const relationships = model.relationships.filter((rel) => {
    const theirs = owned.has(rel.from) && owned.has(rel.to);
    if (theirs) omitted.push(`relationship ${rel.from} -> ${rel.to} "${rel.description}"`);
    return !theirs;
  });
  const views = model.views.filter((view, index) => {
    const subject = viewSubject(view);
    const theirs = subject !== undefined && owned.has(subject);
    if (theirs) omitted.push(`view ${view.key}, of ${subject}`);
    if (!theirs && view.kind === "dynamic") {
      view.steps.forEach((step, stepIndex) => {
        if (owned.has(step.from) && owned.has(step.to)) {
          problems.push(
            `views[${index}].steps[${stepIndex}] ${step.from} -> ${step.to} joins two elements with a ref, whose relationship the fragment leaves out`
          );
        }
      });
    }
    return !theirs;
  });
  if (problems.length > 0) throw new DeclaredModelError(problems);

  const header =
    "// Written by polly visualize generate --model --fragment, from a declared model. Edit the model, not this file.";
  const modelLines = [
    header,
    "// The workspace must use hierarchical identifiers and declare each element this file names by a path it does not declare.",
    ...model.people.filter((person) => person.ref === undefined).flatMap(personLines),
    ...model.systems.filter((system) => system.ref === undefined).flatMap(systemLines),
    "",
    ...relationships.flatMap((rel) => relationshipLines(rel, path)),
    ...(model.deployments ?? []).flatMap((environment) => [
      "",
      ...environmentLines(environment, path),
    ]),
    "",
  ];
  const viewLinesOut = [header, ...views.flatMap((view) => viewLines(view, path)), ""];
  return { model: outdented(modelLines), views: outdented(viewLinesOut), omitted };
}
