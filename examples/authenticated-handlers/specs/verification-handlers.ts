import { state } from "./verification-state";

// Handler functions for verification
// These model the state transitions that occur in the runtime handlers

export function handleConnect() {
  state.connected = true;
  state.authenticated = false;
  state.pendingOperations = 0;
}

export function handleAuthenticate() {
  // Precondition: state.connected === true (enforced by constraint)
  state.authenticated = true;
}

export function handleQuery() {
  // Preconditions enforced by constraints:
  // - state.authenticated === true
  // - state.connected === true
  if (state.pendingOperations < 2) {
    state.pendingOperations++;
  }
}

export function handleCommand() {
  // Precondition: state.authenticated === true (enforced by constraint)
  if (state.pendingOperations < 2) {
    state.pendingOperations++;
  }
}

// Handler map for verification analysis
// The extractor will discover these handlers and extract state transitions
export const handlers = {
  connect: handleConnect,
  authenticate: handleAuthenticate,
  query: handleQuery,
  command: handleCommand,
};
