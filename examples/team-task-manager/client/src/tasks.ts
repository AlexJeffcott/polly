// Task management with encryption

import type { Task, Comment, Priority, TaskStatus } from "../../shared/types";
import { encryptText, decryptText, bytesToBase64, base64ToBytes } from "./crypto";
import {
  currentUser,
  workspace,
  tasks,
  comments,
  activities,
  canCreateUrgentTask,
  canDeleteTask,
  canCompleteTask,
} from "./state";
import { api } from "./api";

// Create a new task
export async function createTask(
  text: string,
  priority: Priority = "medium",
  options: {
    description?: string;
    assignedTo?: string | null;
    requiresApproval?: boolean;
    dependencies?: string[];
  } = {}
): Promise<Task> {
  if (!currentUser.value || !workspace.value) {
    throw new Error("Not authenticated or no workspace");
  }

  // Check urgent task limit
  if (priority === "urgent" && !canCreateUrgentTask()) {
    throw new Error(
      `Maximum ${workspace.value.maxUrgentTasks} urgent tasks allowed. Complete or downgrade existing urgent tasks.`
    );
  }

  const task: Task = {
    id: crypto.randomUUID(),
    text,
    description: options.description,
    createdBy: currentUser.value.id,
    assignedTo: options.assignedTo || null,
    priority,
    status: "todo",
    dependencies: options.dependencies || [],
    requiresApproval: options.requiresApproval || false,
    createdAt: Date.now(),
    updatedAt: Date.now(),
  };

  // Encrypt task
  const encrypted = await encryptText(
    JSON.stringify(task),
    workspace.value.workspaceKey
  );

  // Send to server
  await api.createTask(
    task.id,
    bytesToBase64(encrypted),
    currentUser.value.id,
    workspace.value.id
  );

  // Store locally (optimistic update)
  tasks.value = [...tasks.value, task];

  // Add activity
  addActivity("task_created", currentUser.value.id, task.id);

  return task;
}

// Update task
export async function updateTask(
  taskId: string,
  updates: Partial<Task>
): Promise<Task> {
  if (!currentUser.value || !workspace.value) {
    throw new Error("Not authenticated or no workspace");
  }

  const existingTask = tasks.value.find((t) => t.id === taskId);
  if (!existingTask) {
    throw new Error("Task not found");
  }

  // Check urgent task limit if upgrading priority
  if (
    updates.priority === "urgent" &&
    existingTask.priority !== "urgent" &&
    !canCreateUrgentTask()
  ) {
    throw new Error("Cannot upgrade to urgent: workspace limit reached");
  }

  const updatedTask: Task = {
    ...existingTask,
    ...updates,
    updatedAt: Date.now(),
  };

  // Encrypt updated task
  const encrypted = await encryptText(
    JSON.stringify(updatedTask),
    workspace.value.workspaceKey
  );

  // Send to server
  await api.updateTask(taskId, bytesToBase64(encrypted), workspace.value.id);

  // Update locally
  tasks.value = tasks.value.map((t) => (t.id === taskId ? updatedTask : t));

  // Add activity
  addActivity("task_updated", currentUser.value.id, taskId);

  return updatedTask;
}

// Delete task
export async function deleteTask(taskId: string): Promise<void> {
  if (!currentUser.value || !workspace.value) {
    throw new Error("Not authenticated or no workspace");
  }

  if (!canDeleteTask(taskId)) {
    throw new Error("You don't have permission to delete this task");
  }

  // Delete from server
  await api.deleteTask(taskId, workspace.value.id);

  // Delete locally
  tasks.value = tasks.value.filter((t) => t.id !== taskId);

  // Delete associated comments
  comments.value = comments.value.filter((c) => c.taskId !== taskId);
}

// Assign task
export async function assignTask(taskId: string, userId: string | null): Promise<void> {
  await updateTask(taskId, { assignedTo: userId });

  if (userId) {
    addActivity("task_assigned", currentUser.value!.id, taskId, { assignedTo: userId });
  }
}

// Update task status
export async function updateTaskStatus(
  taskId: string,
  status: TaskStatus
): Promise<void> {
  if (status === "done" && !canCompleteTask(taskId)) {
    const task = tasks.value.find((t) => t.id === taskId);
    if (task?.requiresApproval && !task.approvedBy) {
      throw new Error("Task requires approval before completion");
    }
    throw new Error("Cannot complete task: dependent tasks not finished");
  }

  await updateTask(taskId, {
    status,
    completedAt: status === "done" ? Date.now() : undefined,
  });

  if (status === "done") {
    addActivity("task_completed", currentUser.value!.id, taskId);
  }
}

// Approve task
export async function approveTask(taskId: string): Promise<void> {
  if (!currentUser.value) throw new Error("Not authenticated");

  const task = tasks.value.find((t) => t.id === taskId);
  if (!task) throw new Error("Task not found");

  if (task.createdBy === currentUser.value.id) {
    throw new Error("Cannot approve your own task");
  }

  await updateTask(taskId, { approvedBy: currentUser.value.id });
}

// Add comment
export async function addComment(taskId: string, text: string): Promise<Comment> {
  if (!currentUser.value || !workspace.value) {
    throw new Error("Not authenticated or no workspace");
  }

  const comment: Comment = {
    id: crypto.randomUUID(),
    taskId,
    authorId: currentUser.value.id,
    text,
    createdAt: Date.now(),
  };

  // Encrypt comment
  const encrypted = await encryptText(
    JSON.stringify(comment),
    workspace.value.workspaceKey
  );

  // Send to server
  await api.createComment(
    comment.id,
    taskId,
    bytesToBase64(encrypted),
    currentUser.value.id,
    workspace.value.id
  );

  // Store locally
  comments.value = [...comments.value, comment];

  // Add activity
  addActivity("comment_added", currentUser.value.id, taskId);

  return comment;
}

// Handle incoming encrypted task from WebSocket
export async function handleIncomingTask(encryptedTask: any) {
  if (!workspace.value) return;

  try {
    const decrypted = await decryptText(
      base64ToBytes(encryptedTask.encrypted),
      workspace.value.workspaceKey
    );
    const task: Task = JSON.parse(decrypted);

    // Check if task already exists
    const existingIndex = tasks.value.findIndex((t) => t.id === task.id);

    if (existingIndex >= 0) {
      // Update existing task
      tasks.value = tasks.value.map((t) => (t.id === task.id ? task : t));
    } else {
      // Add new task
      tasks.value = [...tasks.value, task];
    }
  } catch (error) {
    console.error("Failed to decrypt incoming task:", error);
  }
}

// Handle incoming encrypted comment from WebSocket
export async function handleIncomingComment(encryptedComment: any) {
  if (!workspace.value) return;

  try {
    const decrypted = await decryptText(
      base64ToBytes(encryptedComment.encrypted),
      workspace.value.workspaceKey
    );
    const comment: Comment = JSON.parse(decrypted);

    // Add comment if not already exists
    if (!comments.value.find((c) => c.id === comment.id)) {
      comments.value = [...comments.value, comment];
    }
  } catch (error) {
    console.error("Failed to decrypt incoming comment:", error);
  }
}

// Handle task deletion from WebSocket
export function handleTaskDeleted(taskId: string) {
  tasks.value = tasks.value.filter((t) => t.id !== taskId);
  comments.value = comments.value.filter((c) => c.taskId !== taskId);
}

// Add activity
function addActivity(
  type: "task_created" | "task_updated" | "task_completed" | "task_assigned" | "comment_added" | "member_joined",
  userId: string,
  taskId?: string,
  metadata?: Record<string, any>
) {
  activities.value = [
    ...activities.value,
    {
      id: crypto.randomUUID(),
      type,
      userId,
      taskId,
      timestamp: Date.now(),
      metadata,
    },
  ];

  // Keep only last 100 activities
  if (activities.value.length > 100) {
    activities.value = activities.value.slice(-100);
  }
}
