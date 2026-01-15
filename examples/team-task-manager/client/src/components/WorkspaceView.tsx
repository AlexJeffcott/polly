import { useState } from "preact/hooks";
import { currentUser, workspace, tasks, resetState, getUrgentTasks } from "../state";
import { createTask, updateTaskStatus, deleteTask, assignTask } from "../tasks";
import { generateInviteLink, leaveWorkspace } from "../workspace";
import type { Priority } from "../../../shared/types";
import "./WorkspaceView.css";

export function WorkspaceView() {
  const [newTaskText, setNewTaskText] = useState("");
  const [newTaskPriority, setNewTaskPriority] = useState<Priority>("medium");
  const [showInvite, setShowInvite] = useState(false);
  const [filter, setFilter] = useState<"all" | "active" | "done">("all");

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

  const filteredTasks = tasks.value.filter((task) => {
    if (filter === "active") return task.status !== "done";
    if (filter === "done") return task.status === "done";
    return true;
  });

  const urgentTasks = getUrgentTasks();

  return (
    <div class="workspace">
      <header class="workspace-header">
        <div>
          <h1>{workspace.value?.name}</h1>
          <p class="user-info">
            {currentUser.value?.name}
          </p>
        </div>
        <div class="header-actions">
          <button
            onClick={handleInvite}
            class="secondary"
            title="Generate and copy an invite link to share with teammates"
          >
            Invite Teammate
          </button>
          <button onClick={handleLogout} class="secondary">
            Leave
          </button>
        </div>
      </header>

      {showInvite && (
        <div class="notification" style={{ padding: '16px', background: '#dcfce7', color: '#166534', borderRadius: '8px', marginBottom: '16px' }}>
          <div style={{ fontWeight: 600, marginBottom: '4px' }}>Invite link copied to clipboard!</div>
          <div style={{ fontSize: '13px', lineHeight: '1.4' }}>
            Share this link with teammates. It contains the workspace key so they can decrypt and collaborate on tasks.
          </div>
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
          <form onSubmit={handleCreateTask} class="create-task-form">
            <input
              type="text"
              value={newTaskText}
              onInput={(e) => setNewTaskText((e.target as HTMLInputElement).value)}
              placeholder="What needs to be done?"
              class="task-input"
            />
            <select
              value={newTaskPriority}
              onChange={(e) => setNewTaskPriority((e.target as HTMLSelectElement).value as Priority)}
              class="priority-select"
            >
              <option value="low">Low</option>
              <option value="medium">Medium</option>
              <option value="high">High</option>
              <option value="urgent">Urgent</option>
            </select>
            <button type="submit" class="primary">
              Add Task
            </button>
          </form>
        </div>

        <div class="filter-tabs">
          <button
            class={filter === "all" ? "active" : ""}
            onClick={() => setFilter("all")}
          >
            All ({tasks.value.length})
          </button>
          <button
            class={filter === "active" ? "active" : ""}
            onClick={() => setFilter("active")}
          >
            Active ({tasks.value.filter((t) => t.status !== "done").length})
          </button>
          <button
            class={filter === "done" ? "active" : ""}
            onClick={() => setFilter("done")}
          >
            Done ({tasks.value.filter((t) => t.status === "done").length})
          </button>
        </div>

        <div class="tasks-list">
          {filteredTasks.length === 0 ? (
            <div class="empty-state">
              <p>No tasks yet. Create one above!</p>
            </div>
          ) : (
            filteredTasks.map((task) => (
              <div key={task.id} class={`task-card ${task.status}`}>
                <div class="task-header">
                  <span class={`priority-badge ${task.priority}`}>
                    {task.priority}
                  </span>
                  <span class={`status-badge ${task.status}`}>
                    {task.status.replace("_", " ")}
                  </span>
                </div>

                <div class="task-content">
                  <h3>{task.text}</h3>
                  {task.description && <p>{task.description}</p>}
                </div>

                <div class="task-actions">
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
                </div>
              </div>
            ))
          )}
        </div>
      </div>

      <footer class="workspace-footer">
        <p>
          End-to-end encrypted • Server cannot read your data
        </p>
      </footer>
    </div>
  );
}
