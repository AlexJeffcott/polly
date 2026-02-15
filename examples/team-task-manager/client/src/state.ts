// Application state using Polly's universal state management
// All state automatically persists to IndexedDB and syncs across tabs via BroadcastChannel

import { $sharedState, $state } from "@fairfox/polly/state";
import type { Activity, Comment, Task, User, Workspace } from "../../shared/types";

// User identity (keypair stored as base64 strings)
export const currentUser = $sharedState<User | null>("currentUser", null);

// All workspaces user has accessed
export const workspaces = $sharedState<Workspace[]>("workspaces", []);

// Current active workspace with decrypted workspace key (verified for TLA+ generation)
export const workspace = $sharedState<Workspace | null>("workspace", null, { verify: true });

// Tasks (decrypted locally, verified for TLA+ generation)
export const tasks = $sharedState<Task[]>("tasks", [], { verify: true });

// Comments (decrypted locally)
export const comments = $sharedState<Comment[]>("comments", []);

// Activity feed
export const activities = $sharedState<Activity[]>("activities", []);

// Verified urgent task count (exercises { type: "number" } verification)
export const urgentTaskCount = $sharedState("urgentTaskCount", 0, { verify: true });

// Connection status
export const isOnline = $state(true);

// UI state (not persisted)
export const selectedTask = $state<Task | null>(null);
export const showCreateTask = $state(false);
export const showInviteModal = $state(false);

// Computed values - filter by current workspace
export function getTasksForCurrentWorkspace(): Task[] {
  if (!workspace.value) return [];
  return tasks.value.filter((t) => t.workspaceId === workspace.value!.id);
}

export function getCommentsForCurrentWorkspace(): Comment[] {
  if (!workspace.value) return [];
  return comments.value.filter((c) => c.workspaceId === workspace.value!.id);
}

export function getTaskById(id: string): Task | undefined {
  return getTasksForCurrentWorkspace().find((t) => t.id === id);
}

export function getCommentsForTask(taskId: string): Comment[] {
  return getCommentsForCurrentWorkspace().filter((c) => c.taskId === taskId);
}

export function getUrgentTasks(): Task[] {
  return getTasksForCurrentWorkspace().filter(
    (t) => t.priority === "urgent" && t.status !== "done"
  );
}

export function canCreateUrgentTask(): boolean {
  if (!workspace.value) return false;
  return getUrgentTasks().length < workspace.value.maxUrgentTasks;
}

export function canDeleteTask(taskId: string): boolean {
  if (!currentUser.value || !workspace.value) return false;

  const task = getTaskById(taskId);
  if (!task) return false;

  const member = workspace.value.members.find((m) => m.userId === currentUser.value!.id);

  if (!member) return false;

  // Admins can delete any task, creators can delete their own
  return member.role === "admin" || task.createdBy === currentUser.value.id;
}

export function canAssignTask(): boolean {
  if (!currentUser.value || !workspace.value) return false;

  const member = workspace.value.members.find((m) => m.userId === currentUser.value!.id);

  return member?.role !== "viewer";
}

export function canCompleteTask(taskId: string): boolean {
  const task = getTaskById(taskId);
  if (!task) return false;

  // Check dependencies
  const dependenciesMet = task.dependencies.every((depId) => {
    const dep = getTaskById(depId);
    return dep?.status === "done";
  });

  if (!dependenciesMet) return false;

  // Check approval requirement
  if (task.requiresApproval && !task.approvedBy) {
    return false;
  }

  return true;
}

// Reset all state (for logout)
export function resetState() {
  currentUser.value = null;
  workspaces.value = [];
  workspace.value = null;
  tasks.value = [];
  comments.value = [];
  activities.value = [];
  selectedTask.value = null;
}
