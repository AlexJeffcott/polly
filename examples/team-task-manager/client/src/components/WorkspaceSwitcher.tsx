import { workspace, workspaces } from "../state";
import { switchWorkspace } from "../workspace";
import "./WorkspaceSwitcher.css";

export function WorkspaceSwitcher() {
  if (workspaces.value.length <= 1) {
    return null; // Don't show switcher if only one workspace
  }

  const handleSwitch = async (workspaceId: string) => {
    if (workspaceId === workspace.value?.id) return;

    try {
      await switchWorkspace(workspaceId);
    } catch (error) {
      console.error("Failed to switch workspace:", error);
    }
  };

  return (
    <div class="workspace-switcher">
      <div class="workspace-switcher-label">Workspaces:</div>
      <div class="workspace-list">
        {workspaces.value.map((ws) => (
          <button
            key={ws.id}
            class={`workspace-item ${ws.id === workspace.value?.id ? "active" : ""}`}
            onClick={() => handleSwitch(ws.id)}
          >
            {ws.name}
          </button>
        ))}
      </div>
    </div>
  );
}
