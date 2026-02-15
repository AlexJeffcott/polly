import { getMessageBus } from "@fairfox/polly/message-bus";
// Popup UI for todo list
import { render } from "preact";
import { useState } from "preact/hooks";
import { todos, user } from "../background/state";
import type { TodoMessages } from "../shared/messages";
import type { Todo } from "../shared/types";
import "./styles.css";

const bus = getMessageBus<TodoMessages>("popup");

function App() {
  // Use reactive state signals directly - they automatically sync!
  const [newTodoText, setNewTodoText] = useState("");

  const handleLogin = async () => {
    // State automatically syncs - no need to manually update!
    await bus.send(
      {
        type: "USER_LOGIN",
        userId: "user-123",
        name: "Demo User",
        role: "user",
      },
      { target: "background" }
    );
  };

  const handleLogout = async () => {
    // State automatically syncs - no need to manually update!
    await bus.send({ type: "USER_LOGOUT" }, { target: "background" });
  };

  const handleAddTodo = async (e: Event) => {
    e.preventDefault();
    e.stopPropagation();

    const text = newTodoText.trim();
    if (!text) return;

    // Clear input immediately to prevent double submission
    setNewTodoText("");

    // State automatically syncs - no need to manually update!
    const result = await bus.send(
      { type: "TODO_ADD", text, priority: "medium" },
      { target: "background" }
    );
    if (!result?.success) {
      // Restore text if failed
      setNewTodoText(text);
    }
  };

  const handleToggleTodo = async (id: string) => {
    // State automatically syncs - no need to manually update!
    await bus.send({ type: "TODO_TOGGLE", id }, { target: "background" });
  };

  const handleRemoveTodo = async (id: string) => {
    // State automatically syncs - no need to manually update!
    await bus.send({ type: "TODO_REMOVE", id }, { target: "background" });
  };

  const handleClearCompleted = async () => {
    // State automatically syncs - no need to manually update!
    await bus.send({ type: "TODO_CLEAR_COMPLETED" }, { target: "background" });
  };

  // Access reactive state directly - it updates automatically!
  const activeTodos = todos.value.filter((t) => !t.completed);
  const completedTodos = todos.value.filter((t) => t.completed);

  return (
    <div class="app">
      <header>
        <h1>📝 Todo List</h1>
        <div class="user-info">
          {user.value.loggedIn ? (
            <>
              <span>👤 {user.value.name}</span>
              <button type="button" onClick={handleLogout}>
                Logout
              </button>
            </>
          ) : (
            <button type="button" onClick={handleLogin}>
              Login
            </button>
          )}
        </div>
      </header>

      <form onSubmit={handleAddTodo} class="add-todo">
        <input
          type="text"
          value={newTodoText}
          onInput={(e) => setNewTodoText((e.target as HTMLInputElement).value)}
          placeholder="What needs to be done?"
          maxLength={500}
        />
        <button type="submit">Add</button>
      </form>

      <div class="todo-list">
        {todos.value.length === 0 ? (
          <p class="empty">No todos yet. Add one above!</p>
        ) : (
          <>
            {activeTodos.map((todo) => (
              <TodoItem
                key={todo.id}
                todo={todo}
                onToggle={handleToggleTodo}
                onRemove={handleRemoveTodo}
              />
            ))}
            {completedTodos.length > 0 && (
              <div class="completed-section">
                <h3>Completed ({completedTodos.length})</h3>
                {completedTodos.map((todo) => (
                  <TodoItem
                    key={todo.id}
                    todo={todo}
                    onToggle={handleToggleTodo}
                    onRemove={handleRemoveTodo}
                  />
                ))}
              </div>
            )}
          </>
        )}
      </div>

      {completedTodos.length > 0 && (
        <footer>
          <button type="button" onClick={handleClearCompleted} class="clear-completed">
            Clear Completed ({completedTodos.length})
          </button>
        </footer>
      )}

      <div class="stats">
        <span>{activeTodos.length} active</span>
        <span>{todos.value.length} / 100 total</span>
      </div>
    </div>
  );
}

function TodoItem({
  todo,
  onToggle,
  onRemove,
}: {
  todo: Todo;
  onToggle: (id: string) => void;
  onRemove: (id: string) => void;
}) {
  return (
    <div class={`todo-item ${todo.completed ? "completed" : ""}`}>
      <input type="checkbox" checked={todo.completed} onChange={() => onToggle(todo.id)} />
      <span class="todo-text">{todo.text}</span>
      <button type="button" onClick={() => onRemove(todo.id)} class="remove">
        ×
      </button>
    </div>
  );
}

const rootElement = document.getElementById("root");
if (rootElement) {
  render(<App />, rootElement);
}
