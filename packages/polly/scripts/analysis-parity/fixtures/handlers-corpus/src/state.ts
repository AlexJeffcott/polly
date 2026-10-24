import { initialAuth } from "./defaults";
import { $sharedState } from "./runtime";

// Fields read through an imported identifier.
export const auth = $sharedState("auth", initialAuth, { verify: true });

// Fields read through a local identifier.
const counterDefaults = { count: 0, label: "start" };
export const counter = $sharedState("counter", counterDefaults, { verify: true });

// An identifier that resolves to something other than an object literal.
const notAnObject = 42;
export const plain = $sharedState("plain", notAnObject, { verify: true });
