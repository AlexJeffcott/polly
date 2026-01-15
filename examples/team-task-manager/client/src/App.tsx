import { useEffect } from "preact/hooks";
import { currentUser, workspace, tasks } from "./state";
import { Onboarding } from "./components/Onboarding";
import { WorkspaceView } from "./components/WorkspaceView";
import { InstallPrompt } from "./components/InstallPrompt";
import { NetworkStatus } from "./components/NetworkStatus";
import { parseInviteLink, joinWorkspace } from "./workspace";
import { api } from "./api";
import {
  handleIncomingTask,
  handleIncomingComment,
  handleTaskDeleted,
} from "./tasks";

export function App() {
  // Check for invite link on mount and when user identity changes
  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const inviteCode = params.get("invite");

    if (inviteCode && currentUser.value && !workspace.value) {
      try {
        const invite = parseInviteLink(inviteCode);
        joinWorkspace(invite.workspaceId, invite.workspaceName, invite.encryptedKey);
        // Clear invite from URL
        window.history.replaceState({}, "", window.location.pathname);
      } catch (error) {
        console.error("Failed to join workspace from invite:", error);
      }
    }
  }, [currentUser.value]); // Re-run when user identity changes

  // Set up WebSocket message handlers
  useEffect(() => {
    if (!workspace.value) return;

    const cleanup = api.onMessage("app", (data) => {
      switch (data.type) {
        case "task_created":
        case "task_updated":
          if (data.task) {
            handleIncomingTask(data.task);
          }
          break;

        case "task_deleted":
          if (data.taskId) {
            handleTaskDeleted(data.taskId);
          }
          break;

        case "comment_added":
          if (data.comment) {
            handleIncomingComment(data.comment);
          }
          break;

        case "member_joined":
          console.log("Member joined:", data.userId);
          break;

        case "sync_response":
          // A peer is sharing their data with us (we just joined)
          if (data.tasks && Array.isArray(data.tasks)) {
            console.log(`Received ${data.tasks.length} tasks from peer`);
            // Merge their tasks with ours (they have the full dataset)
            // This happens when we join an existing workspace
            for (const task of data.tasks) {
              // Tasks are already decrypted on the peer's device
              // Just merge them into our local state
              const existingIndex = tasks.value.findIndex((t) => t.id === task.id);
              if (existingIndex >= 0) {
                // Update existing if peer's version is newer
                if (task.updatedAt > tasks.value[existingIndex].updatedAt) {
                  const newTasks = [...tasks.value];
                  newTasks[existingIndex] = task;
                  tasks.value = newTasks;
                }
              } else {
                // Add new task
                tasks.value = [...tasks.value, task];
              }
            }
          }
          break;
      }
    });

    return cleanup;
  }, [workspace.value]);

  // Show onboarding if no user or no workspace
  if (!currentUser.value || !workspace.value) {
    return (
      <>
        <Onboarding />
        <NetworkStatus />
        <InstallPrompt />
      </>
    );
  }

  // Show main workspace view
  return (
    <>
      <WorkspaceView />
      <NetworkStatus />
      <InstallPrompt />
    </>
  );
}
