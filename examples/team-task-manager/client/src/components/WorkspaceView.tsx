import { useState } from "preact/hooks";
import type { Priority } from "../../../shared/types";
import {
  currentUser,
  getTasksForCurrentWorkspace,
  getUrgentTasks,
  resetState,
  workspace,
} from "../state";
import { createTask, deleteTask, updateTaskStatus } from "../tasks";
import { exportUserKey, generateInviteLink, leaveWorkspace } from "../workspace";
import { Button } from "./Button";
import { Layout } from "./Layout";
import { Modal } from "./Modal";
import { WorkspaceSwitcher } from "./WorkspaceSwitcher";

const BACKUP_DISMISSED_KEY = "backup-banner-dismissed";

function hasBackupBeenDismissed(): boolean {
  return localStorage.getItem(BACKUP_DISMISSED_KEY) === "true";
}

function dismissBackupBanner(): void {
  localStorage.setItem(BACKUP_DISMISSED_KEY, "true");
}

export function WorkspaceView() {
  const [newTaskText, setNewTaskText] = useState("");
  const [newTaskPriority, setNewTaskPriority] = useState<Priority>("medium");
  const [showInvite, setShowInvite] = useState(false);
  const [filter, setFilter] = useState<"all" | "active" | "done">("all");
  const [showBackupBanner, setShowBackupBanner] = useState(!hasBackupBeenDismissed());
  const [showBackupModal, setShowBackupModal] = useState(false);

  const handleCreateTask = async (e: Event) => {
    e.preventDefault();

    if (!newTaskText.trim()) return;

    try {
      await createTask(newTaskText, newTaskPriority);
      setNewTaskText("");
      setNewTaskPriority("medium");
    } catch (err: any) {
      alert(err.message);
    }
  };

  const handleLogout = () => {
    if (confirm("Are you sure you want to leave this workspace?")) {
      leaveWorkspace();
      resetState();
    }
  };

  const handleInvite = () => {
    const link = generateInviteLink();
    navigator.clipboard.writeText(link);
    setShowInvite(true);
    setTimeout(() => setShowInvite(false), 3000);
  };

  const handleDismissBackup = () => {
    dismissBackupBanner();
    setShowBackupBanner(false);
  };

  const handleCloseBackupModal = () => {
    setShowBackupModal(false);
  };

  const copyKeyToClipboard = async () => {
    if (!currentUser.value) return;
    try {
      const backup = exportUserKey(currentUser.value);
      await navigator.clipboard.writeText(backup);
      alert("Key copied to clipboard! Store it somewhere safe.");
      handleCloseBackupModal();
      handleDismissBackup();
    } catch {
      alert("Failed to copy. Please try the download option.");
    }
  };

  const downloadKey = () => {
    if (!currentUser.value) return;
    const backup = exportUserKey(currentUser.value);
    const blob = new Blob([backup], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `task-manager-backup-${currentUser.value.id.slice(0, 8)}.json`;
    a.click();
    URL.revokeObjectURL(url);
    handleCloseBackupModal();
    handleDismissBackup();
  };

  const workspaceTasks = getTasksForCurrentWorkspace();
  const filteredTasks = workspaceTasks.filter((task) => {
    if (filter === "active") return task.status !== "done";
    if (filter === "done") return task.status === "done";
    return true;
  });

  const urgentTasks = getUrgentTasks();

  // Show backup banner only after user has created at least one task
  const shouldShowBackupBanner = showBackupBanner && workspaceTasks.length > 0;

  return (
    <Layout rows="auto 1fr auto" className="workspace">
      <header class="workspace-header">
        <Layout columns="1fr auto" alignItems="center">
          <div>
            <h1>{workspace.value?.name}</h1>
            <p class="user-info">{currentUser.value?.name}</p>
          </div>
          <Layout columns="auto auto" gap="var(--space-md)">
            <Button onPress={handleInvite} tier="secondary">
              Invite Teammate
            </Button>
            <Button onPress={handleLogout} tier="secondary">
              Leave
            </Button>
          </Layout>
        </Layout>
      </header>

      <div>
        {showInvite && (
          <div class="notification-success">
            <div class="notification-success-title">Invite link copied to clipboard!</div>
            <div class="notification-success-text">
              Share this link with teammates. It contains the workspace key so they can decrypt and
              collaborate on tasks.
            </div>
          </div>
        )}

        {shouldShowBackupBanner && (
          <div class="backup-banner">
            <Layout columns="1fr auto auto" gap="var(--space-md)" alignItems="center">
              <span>Secure your account — back up your key to avoid losing access</span>
              <Button onPress={() => setShowBackupModal(true)} tier="primary" size="small">
                Back up now
              </Button>
              <Button onPress={handleDismissBackup} tier="tertiary" size="small">
                Dismiss
              </Button>
            </Layout>
          </div>
        )}

        {urgentTasks.length >= (workspace.value?.maxUrgentTasks || 3) && (
          <div class="warning-banner">
            Urgent task limit reached ({urgentTasks.length}/{workspace.value?.maxUrgentTasks}).
            Complete or downgrade urgent tasks to create more.
          </div>
        )}

        <div class="workspace-content">
          <div class="create-task-section">
            <form onSubmit={handleCreateTask}>
              <Layout columns="1fr auto auto" gap="var(--space-md)" className="create-task-form">
                <input
                  type="text"
                  value={newTaskText}
                  onInput={(e) => setNewTaskText((e.target as HTMLInputElement).value)}
                  placeholder="What needs to be done?"
                  class="task-input"
                />
                <select
                  value={newTaskPriority}
                  onChange={(e) =>
                    setNewTaskPriority((e.target as HTMLSelectElement).value as Priority)
                  }
                  class="priority-select"
                >
                  <option value="low">Low</option>
                  <option value="medium">Medium</option>
                  <option value="high">High</option>
                  <option value="urgent">Urgent</option>
                </select>
                <Button type="submit" tier="primary">
                  Add Task
                </Button>
              </Layout>
            </form>
          </div>

          <Layout columns="auto auto auto" gap="var(--space-sm)" className="filter-tabs">
            <button
              class={`filter-btn ${filter === "all" ? "active" : ""}`}
              onClick={() => setFilter("all")}
            >
              All ({workspaceTasks.length})
            </button>
            <button
              class={`filter-btn ${filter === "active" ? "active" : ""}`}
              onClick={() => setFilter("active")}
            >
              Active ({workspaceTasks.filter((t) => t.status !== "done").length})
            </button>
            <button
              class={`filter-btn ${filter === "done" ? "active" : ""}`}
              onClick={() => setFilter("done")}
            >
              Done ({workspaceTasks.filter((t) => t.status === "done").length})
            </button>
          </Layout>

          <Layout autoRows="auto" gap="var(--space-lg)">
            {filteredTasks.length === 0 ? (
              <div class="empty-state">
                <p>No tasks yet. Create one above!</p>
              </div>
            ) : (
              filteredTasks.map((task) => (
                <div key={task.id} class={`task-card ${task.status}`}>
                  <Layout columns="auto auto 1fr" gap="var(--space-sm)" className="task-header">
                    <span class={`priority-badge ${task.priority}`}>{task.priority}</span>
                    <span class={`status-badge ${task.status}`}>
                      {task.status.replace("_", " ")}
                    </span>
                  </Layout>

                  <div class="task-content">
                    <h3>{task.text}</h3>
                    {task.description && <p>{task.description}</p>}
                  </div>

                  <Layout columns="auto auto" gap="var(--space-sm)" className="task-actions">
                    {task.status !== "done" && (
                      <button
                        onClick={() => updateTaskStatus(task.id, "done")}
                        class="action-btn"
                        title="Mark as done"
                      >
                        Done
                      </button>
                    )}
                    <button
                      onClick={() => deleteTask(task.id)}
                      class="action-btn danger"
                      title="Delete"
                    >
                      Delete
                    </button>
                  </Layout>
                </div>
              ))
            )}
          </Layout>
        </div>
      </div>

      <footer class="workspace-footer">
        <p>End-to-end encrypted • Server cannot read your data</p>
      </footer>

      <WorkspaceSwitcher />

      <Modal isOpen={showBackupModal} onClose={handleCloseBackupModal} title="Back Up Your Key">
        <p>
          Your key is your identity. Save it to restore access on other devices or if you clear your
          browser data.
        </p>

        <Layout columns="1fr 1fr" gap="var(--space-md)" style={{ marginTop: "var(--space-xl)" }}>
          <Button onPress={copyKeyToClipboard} tier="primary">
            Copy to Clipboard
          </Button>
          <Button onPress={downloadKey} tier="primary">
            Download File
          </Button>
        </Layout>
      </Modal>
    </Layout>
  );
}
