import { useEffect } from "preact/hooks";
import { currentUser, workspace } from "./state";
import { Onboarding } from "./components/Onboarding";
import { WorkspaceView } from "./components/WorkspaceView";
import { parseInviteLink, joinWorkspace } from "./workspace";
import { api } from "./api";
import {
  handleIncomingTask,
  handleIncomingComment,
  handleTaskDeleted,
} from "./tasks";

export function App() {
  // Check for invite link on mount
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
  }, []);

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
      }
    });

    return cleanup;
  }, [workspace.value]);

  // Show onboarding if no user or no workspace
  if (!currentUser.value || !workspace.value) {
    return <Onboarding />;
  }

  // Show main workspace view
  return <WorkspaceView />;
}
