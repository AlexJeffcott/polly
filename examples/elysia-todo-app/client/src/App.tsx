import { useSignal } from "@preact/signals";
import { api, clientState } from "./api";
import "./App.css";

export function App() {
  const newTodoText = useSignal("");
  const username = useSignal("demo");

  async function handleLogin() {
    try {
      await api.auth.login.post({ username: username.value });
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
      console.error("Login failed:", error);
      alert("Login failed");
    }
  }

  async function handleLogout() {
    try {
      await api.auth.logout.post({});
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
      console.error("Logout failed:", error);
    }
  }

  async function handleAddTodo() {
    if (!newTodoText.value.trim()) return;

    try {
      // Automatically handles:
      // - Optimistic update if offline
      // - Queue for retry
      // - Execute client effect on success
      // - Broadcast to other clients
      await api.todos.post({ text: newTodoText.value });
      newTodoText.value = "";
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
      console.error("Failed to add todo:", error);
      alert("Failed to add todo");
    }
  }

  async function handleToggle(id: number, completed: boolean) {
    try {
      await api.todos[id].patch({ completed: !completed });
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
      console.error("Failed to toggle todo:", error);
    }
  }

  async function handleDelete(id: number) {
    try {
      await api.todos[id].delete();
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
      console.error("Failed to delete todo:", error);
    }
  }

  return (
    <div class="app">
      <header>
        <h1>Polly + Elysia Todo App</h1>
        <div class="status">
          <span class={api.$polly.state.isOnline.value ? "online" : "offline"}>
            {api.$polly.state.isOnline.value ? "🟢 Online" : "🔴 Offline"}
          </span>
          {api.$polly.state.isSyncing.value && <span>⏳ Syncing...</span>}
          {api.$polly.state.queuedRequests.value.length > 0 && (
            <span class="queue">📋 {api.$polly.state.queuedRequests.value.length} queued</span>
          )}
        </div>
      </header>

      {clientState.user.value ? (
        <div class="todo-app">
          <div class="user-info">
            <span>Welcome, {clientState.user.value.username}!</span>
            <button type="button" onClick={handleLogout} class="logout">
              Logout
            </button>
          </div>

          <div class="add-todo">
            <input
              type="text"
              value={newTodoText.value}
              onInput={(e) => {
                newTodoText.value = e.currentTarget.value;
              }}
              placeholder="What needs to be done?"
              onKeyDown={(e) => e.key === "Enter" && handleAddTodo()}
            />
            <button type="button" onClick={handleAddTodo}>
              Add
            </button>
          </div>

          <ul class="todo-list">
            {clientState.todos.value.length === 0 ? (
              <li class="empty">No todos yet. Add one above!</li>
            ) : (
              clientState.todos.value.map((todo) => (
                <li key={todo.id} class={todo.completed ? "completed" : ""}>
                  <input
                    type="checkbox"
                    checked={todo.completed}
                    onChange={() => handleToggle(todo.id, todo.completed)}
                  />
                  <span class="text">{todo.text}</span>
                  <button type="button" onClick={() => handleDelete(todo.id)} class="delete">
                    ×
                  </button>
                </li>
              ))
            )}
          </ul>

          <div class="stats">
            <span>{clientState.todos.value.filter((t) => !t.completed).length} items left</span>
            <span>{clientState.todos.value.filter((t) => t.completed).length} completed</span>
          </div>
        </div>
      ) : (
        <div class="login-form">
          <h2>Login</h2>
          <input
            type="text"
            value={username.value}
            onInput={(e) => {
              username.value = e.currentTarget.value;
            }}
            placeholder="Username (try 'demo')"
            onKeyDown={(e) => e.key === "Enter" && handleLogin()}
          />
          <button type="button" onClick={handleLogin}>
            Login
          </button>
        </div>
      )}

      <footer>
        <p>
          <strong>Try it:</strong> Open this app in multiple tabs/windows to see real-time sync!
        </p>
        <p>
          <strong>Offline mode:</strong> Disable network in DevTools to test offline queueing
        </p>
      </footer>
    </div>
  );
}
