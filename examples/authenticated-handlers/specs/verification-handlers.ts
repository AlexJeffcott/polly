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

// Register handlers with message bus for verification analysis
// The extractor will resolve these function references and extract state transitions
import { getMessageBus } from "../../../tools/verify/src/index";

const bus = getMessageBus<any>("verification");
bus.on("connect", handleConnect);
bus.on("authenticate", handleAuthenticate);
bus.on("query", handleQuery);
bus.on("command", handleCommand);
