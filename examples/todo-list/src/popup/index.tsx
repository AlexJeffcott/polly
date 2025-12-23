import { getMessageBus } from "@fairfox/polly/message-bus";
// Popup UI for todo list
import { render } from "preact";
import { useEffect, useState } from "preact/hooks";
import type { TodoMessages } from "../shared/messages";
import type { AppState, Todo } from "../shared/types";
import "./styles.css";

const bus = getMessageBus<TodoMessages>("popup");

function App() {
  const [state, setState] = useState<AppState | null>(null);
  const [newTodoText, setNewTodoText] = useState("");

  useEffect(() => {
    // Load initial state
    bus.send({ type: "GET_STATE" }, { target: "background" }).then((state) => {
      if (state) setState(state);
    });
  }, []);

  const handleLogin = async () => {
    const result = await bus.send(
      {
        type: "USER_LOGIN",
        userId: "user-123",
        name: "Demo User",
        role: "user",
      },
      { target: "background" }
    );
    if (result?.success) {
      setState((prev) => (prev ? { ...prev, user: result.user } : null));
    }
  };

  const handleLogout = async () => {
    await bus.send({ type: "USER_LOGOUT" }, { target: "background" });
    const newState = await bus.send({ type: "GET_STATE" }, { target: "background" });
    if (newState) setState(newState);
  };

  const handleAddTodo = async (e: Event) => {
    e.preventDefault();
    e.stopPropagation();

    const text = newTodoText.trim();
    if (!text) return;

    // Clear input immediately to prevent double submission
    setNewTodoText("");

    const result = await bus.send({ type: "TODO_ADD", text }, { target: "background" });
    if (result?.success) {
      const newState = await bus.send({ type: "GET_STATE" }, { target: "background" });
      if (newState) setState(newState);
    } else {
      // Restore text if failed
      setNewTodoText(text);
    }
  };

  const handleToggleTodo = async (id: string) => {
    await bus.send({ type: "TODO_TOGGLE", id }, { target: "background" });
    const newState = await bus.send({ type: "GET_STATE" }, { target: "background" });
    if (newState) setState(newState);
  };

  const handleRemoveTodo = async (id: string) => {
    await bus.send({ type: "TODO_REMOVE", id }, { target: "background" });
    const newState = await bus.send({ type: "GET_STATE" }, { target: "background" });
    if (newState) setState(newState);
  };

  const handleClearCompleted = async () => {
    await bus.send({ type: "TODO_CLEAR_COMPLETED" }, { target: "background" });
    const newState = await bus.send({ type: "GET_STATE" }, { target: "background" });
    if (newState) setState(newState);
  };

  if (!state) {
    return <div class="loading">Loading...</div>;
  }

  const activeTodos = state.todos.filter((t) => !t.completed);
  const completedTodos = state.todos.filter((t) => t.completed);

  return (
    <div class="app">
      <header>
        <h1>📝 Todo List</h1>
        <div class="user-info">
          {state.user.loggedIn ? (
            <>
              <span>👤 {state.user.name}</span>
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
        {state.todos.length === 0 ? (
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
        <span>{state.todos.length} / 100 total</span>
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
