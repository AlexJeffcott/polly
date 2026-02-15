// Verified state-mutating functions wrapping existing task logic
// Demonstrates requires/ensures, parameter tracing, and role constraints
import { ensures, requires } from "@fairfox/polly/verify";
import type { Priority } from "../../shared/types";
import {
  canCompleteTask,
  canDeleteTask,
  currentUser,
  tasks,
  urgentTaskCount,
  workspace,
} from "./state";

// Create task - the priority parameter exercises parameter tracing for TLA+ generation
export function verifyCreateTask(text: string, priority: Priority, assignedTo: string | null) {
  requires(currentUser.value !== null, "Must be authenticated");
  requires(workspace.value !== null, "Must have a workspace");

  if (priority === "urgent") {
    requires(
      urgentTaskCount.value < (workspace.value?.maxUrgentTasks ?? 0),
      "Cannot exceed urgent task limit"
    );
    urgentTaskCount.value += 1;
  }

  ensures(tasks.value !== null, "Tasks must exist after create");
}

// Complete task - requires dependencies met
export function verifyCompleteTask(taskId: string) {
  requires(currentUser.value !== null, "Must be authenticated");
  requires(canCompleteTask(taskId), "Dependencies must be met to complete task");
}

// Delete task - requires permission (role constraint)
export function verifyDeleteTask(taskId: string) {
  requires(currentUser.value !== null, "Must be authenticated");
  requires(canDeleteTask(taskId), "Must have permission to delete task");
}
