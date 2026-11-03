// Writes a checked DeclaredModel as Structurizr DSL. It writes exactly what
// the model declares: no element, relationship, view or style is added.

import type {
  Component,
  Container,
  DeclaredModel,
  DeploymentEnvironment,
  DeploymentNode,
  Person,
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

function personLines(person: Person): string[] {
  return [
    `    ${person.id} = person ${args(person.name, person.description, tagList(person.tags))}`,
  ];
}

function componentLines(component: Component): string[] {
  return [
    `        ${component.id} = component ${args(
      component.name,
      component.description,
      component.technology,
      tagList(component.tags)
    )}`,
  ];
}

function containerLines(container: Container): string[] {
  const head = `      ${container.id} = container ${args(
    container.name,
    container.description,
    container.technology,
    tagList(container.tags)
  )}`;
  const components = container.components ?? [];
  if (components.length === 0) return [head];
  return [`${head} {`, ...components.flatMap(componentLines), "      }"];
}

function systemLines(system: SoftwareSystem): string[] {
  const head = `    ${system.id} = softwareSystem ${args(system.name, system.description, tagList(system.tags))}`;
  const containers = system.containers ?? [];
  if (containers.length === 0) return [head];
  return [`${head} {`, ...containers.flatMap(containerLines), "    }"];
}

function relationshipLines(rel: Relationship): string[] {
  return [
    `    ${rel.from} -> ${rel.to} ${args(rel.description, rel.technology, tagList(rel.tags))}`,
  ];
}

function nodeLines(node: DeploymentNode, indent: string): string[] {
  return [
    `${indent}deploymentNode ${args(node.name, node.description, node.technology)} {`,
    ...(node.containers ?? []).map((id) => `${indent}  containerInstance ${id}`),
    ...(node.nodes ?? []).flatMap((child) => nodeLines(child, `${indent}  `)),
    `${indent}}`,
  ];
}

function environmentLines(environment: DeploymentEnvironment): string[] {
  return [
    `    ${environment.id} = deploymentEnvironment ${quote(environment.name)} {`,
    ...environment.nodes.flatMap((node) => nodeLines(node, "      ")),
    "    }",
  ];
}

function viewLines(view: View): string[] {
  const titled = args(view.key, view.description);
  const layout = `      autoLayout ${view.layout}`;
  switch (view.kind) {
    case "systemContext":
      return [`    systemContext ${view.system} ${titled} {`, "      include *", layout, "    }"];
    case "container":
      return [`    container ${view.system} ${titled} {`, "      include *", layout, "    }"];
    case "component":
      return [`    component ${view.container} ${titled} {`, "      include *", layout, "    }"];
    case "dynamic":
      return [
        `    dynamic ${view.scope} ${titled} {`,
        ...view.steps.map((step) => `      ${step.from} -> ${step.to} ${quote(step.description)}`),
        layout,
        "    }",
      ];
    case "deployment":
      return [
        `    deployment ${view.scope} ${view.environment} ${titled} {`,
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
    ...model.relationships.flatMap(relationshipLines),
    ...(model.deployments ?? []).flatMap((environment) => ["", ...environmentLines(environment)]),
    "  }",
    "",
    "  views {",
    ...model.views.flatMap(viewLines),
    ...(styles.length === 0 ? [] : ["    styles {", ...styles, "    }"]),
    "  }",
    "}",
    "",
  ];
  return lines.join("\n");
}
