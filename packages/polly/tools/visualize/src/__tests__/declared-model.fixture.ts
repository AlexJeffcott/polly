// A declared model that uses every part of the model: two people, a host
// system and a system with containers and components, external systems,
// tagged elements and relationships, a nested deployment, every view kind,
// element and relationship styles, and tooltip properties on each kind of element.

import type { DeclaredModel } from "../model/types";

export function fullModel(): DeclaredModel {
  return {
    name: "Parts",
    description: "Parts that load into a host page at run time.",
    people: [
      {
        id: "reader",
        name: "Reader",
        description: "Reads pages.",
        properties: { Role: "Any reader" },
      },
      { id: "engineer", name: "Engineer", tags: ["Staff"] },
    ],
    systems: [
      {
        id: "host",
        name: "Host app",
        tags: ["Host"],
        containers: [
          { id: "renderer", name: "Page renderer", technology: "Node" },
          { id: "page", name: "Page", description: "Pushes config.", tags: ["Browser"] },
        ],
      },
      {
        id: "parts",
        name: "Parts",
        description: "Loaded at run time.",
        properties: { Source: "parts/" },
        containers: [
          { id: "loader", name: "Loader", description: "Starts the shell.", tags: ["Browser"] },
          {
            id: "shell",
            name: "Shell",
            technology: "TypeScript",
            properties: { Files: "shell/src", Detail: 'Holds the "bus".' },
            components: [
              { id: "hostHandle", name: "Host handle", description: "Takes each config." },
              {
                id: "bus",
                name: "Bus",
                technology: "shell/src/store.ts",
                properties: { Files: "store.ts" },
              },
              { id: "element", name: "Unit element", description: 'Places a "unit".' },
            ],
          },
          { id: "unit", name: "Unit", tags: ["Browser", "Unit"] },
          { id: "store", name: "Store", technology: "S3", tags: ["Store"] },
        ],
      },
      { id: "ci", name: "CI", tags: ["External"] },
    ],
    relationships: [
      { from: "reader", to: "page", description: "Reads pages in" },
      { from: "engineer", to: "ci", description: "Starts" },
      { from: "renderer", to: "page", description: "Serves the page" },
      { from: "page", to: "loader", description: "Imports the loader", technology: "ES module" },
      { from: "page", to: "element", description: "Places a unit element", tags: ["Dom"] },
      {
        from: "loader",
        to: "store",
        description: "Reads the shell pointer",
        technology: "HTTPS",
        properties: { Path: "unit-manifests/<namespace>.shell.json" },
      },
      { from: "loader", to: "hostHandle", description: "Passes on each config" },
      { from: "hostHandle", to: "bus", description: "Writes host topics" },
      { from: "element", to: "store", description: "Reads the unit pointer" },
      { from: "element", to: "unit", description: "Calls mount" },
      { from: "unit", to: "bus", description: "Subscribes to topics" },
      { from: "ci", to: "store", description: "Uploads builds" },
    ],
    deployments: [
      {
        id: "qa",
        name: "QA",
        nodes: [
          {
            name: "Browser",
            technology: "Chrome",
            containers: ["page", "loader", "shell", "unit"],
          },
          {
            name: "Web server",
            properties: { Host: "<branch>.example" },
            containers: ["renderer"],
          },
          {
            name: "AWS",
            nodes: [{ name: "CDN", nodes: [{ name: "S3", containers: ["store"] }] }],
          },
        ],
      },
    ],
    views: [
      { kind: "systemContext", system: "parts", key: "SystemContext", layout: "lr" },
      { kind: "container", system: "parts", key: "Containers", layout: "lr" },
      { kind: "component", container: "shell", key: "ShellComponents", layout: "tb" },
      {
        kind: "dynamic",
        scope: "shell",
        key: "PageStart",
        description: "A page starts the shell and mounts one unit.",
        layout: "lr",
        steps: [
          { from: "renderer", to: "page", description: "Serves the page" },
          { from: "page", to: "loader", description: "Imports the loader" },
          { from: "loader", to: "hostHandle", description: "Starts the shell" },
          { from: "page", to: "element", description: "Places the unit" },
          { from: "element", to: "unit", description: "Mounts it" },
        ],
      },
      { kind: "deployment", scope: "*", environment: "qa", key: "QADeployment", layout: "lr" },
    ],
    styles: {
      elements: {
        Person: { shape: "Person", background: "#08427b", color: "#ffffff" },
        Browser: { shape: "WebBrowser" },
        Store: { shape: "Cylinder" },
        External: { background: "#999999", border: "Dashed", metadata: false },
      },
      relationships: { Dom: { style: "Dotted", routing: "Orthogonal", thickness: 2 } },
    },
  };
}
