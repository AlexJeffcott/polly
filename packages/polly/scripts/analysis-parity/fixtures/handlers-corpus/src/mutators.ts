import { ensures, requires } from "./runtime";
import { auth, counter } from "./state";

// Exported by `export { login }`: lifted.
function login(user: string) {
  requires(!auth.value.loggedIn, "already logged in");
  auth.value = { loggedIn: true, user };
  ensures(auth.value.loggedIn);
}

// Exported under another name: lifted under its own name.
function logout() {
  auth.value.loggedIn = false;
}

// Exported as the default: lifted.
function bumpCounter() {
  counter.value.count = 1;
}

// Not exported: off-surface.
function relabel() {
  counter.value.label = "hidden";
}

// Exported by keyword: lifted.
export function resetCounter() {
  counter.value = { count: 0, label: "reset" };
}

// Exported by keyword, as a const arrow: lifted.
export const setLabel = (label: string) => {
  counter.value.label = label;
};

// Exported by name but not a mutator: not lifted.
function readOnly() {
  return counter.value.count;
}

relabel();

export { login, logout as signOut, readOnly };
export default bumpCounter;
