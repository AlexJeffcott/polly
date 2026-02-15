// Verification constraints for workspace-gated operations
import { $constraints } from "@fairfox/polly/verify";

export const workspaceConstraints = $constraints("workspace", {
  CREATE_TASK: {
    requires: "state.workspace !== null",
    message: "Must have a workspace to create tasks",
  },
  DELETE_TASK: {
    requires: "state.workspace !== null",
    message: "Must have a workspace to delete tasks",
  },
  COMPLETE_TASK: {
    requires: "state.workspace !== null",
    message: "Must have a workspace to complete tasks",
  },
});
