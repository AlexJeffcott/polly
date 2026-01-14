import { $constraints } from "../../../tools/verify/src/index";

// Authentication constraints
$constraints("authenticated", {
  query: {
    requires: "state.authenticated === true",
    message: "Must authenticate before querying",
  },
  command: {
    requires: "state.authenticated === true",
    message: "Must authenticate before commands",
  },
});

// Connection constraints
$constraints("connected", {
  query: {
    requires: "state.connected === true",
    message: "Must be connected to query",
  },
  authenticate: {
    requires: "state.connected === true",
    message: "Must be connected to authenticate",
  },
});
