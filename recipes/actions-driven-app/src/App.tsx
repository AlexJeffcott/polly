/**
 * App root.
 *
 * Components are logic-free: they read signals and emit markup with
 * data-action attributes. Every state mutation happens through the
 * action registry in `actions.ts`.
 */

import {
  ActionForm,
  ActionInput,
  Layout,
  Modal,
  OverlayRoot,
  TextInput,
  Toast,
} from "@fairfox/polly/ui";
import { useStores } from "@fairfox/polly/actions";
import { createTodoForm } from "./forms.ts";
import type { RootStore } from "./stores.ts";

export function App() {
  const stores = useStores<RootStore>();
  const theme = stores.view.theme.value;

  return (
    <div data-polly-theme={theme}>
      <Layout
        padding="var(--polly-space-lg)"
        gap="var(--polly-space-md)"
        rows="auto 1fr auto"
        minHeight="100vh"
      >
        <Layout as="header" columns="1fr auto" alignItems="center">
          <h1>Todos</h1>
          <button
            type="button"
            data-polly-ui
            data-polly-interactive
            data-action="theme:toggle"
          >
            {theme === "dark" ? "Light" : "Dark"}
          </button>
        </Layout>

        <Layout as="main" gap="var(--polly-space-sm)">
          <p>{stores.todos.remaining.value} remaining</p>
          <ul>
            {stores.todos.todos.value.map((todo) => (
              <Layout
                as="li"
                key={todo.id}
                columns="auto 1fr auto"
                gap="var(--polly-space-sm)"
                alignItems="center"
              >
                <input
                  type="checkbox"
                  checked={todo.done}
                  data-action="todo:toggle"
                  data-action-todo-id={todo.id}
                />
                <ActionInput
                  value={todo.title}
                  action="todo:rename"
                  actionData={{ todoId: todo.id }}
                  saveOn="enter"
                  ariaLabel="Rename todo"
                />
                <button
                  type="button"
                  data-polly-ui
                  data-polly-interactive
                  data-action="todo:remove"
                  data-action-todo-id={todo.id}
                >
                  Remove
                </button>
              </Layout>
            ))}
          </ul>
        </Layout>

        <Layout as="footer">
          <button
            type="button"
            data-polly-ui
            data-polly-interactive
            data-action="todo:create:open"
          >
            New todo
          </button>
        </Layout>
      </Layout>

      <OverlayRoot />
      <Toast.Viewport />

      <Modal.Root
        when={createTodoForm.isOpen}
        onClose={() => createTodoForm.close()}
      >
        <Modal.Backdrop />
        <Modal.Content>
          <Modal.Header>
            <Modal.Title>New todo</Modal.Title>
            <Modal.Close>Close</Modal.Close>
          </Modal.Header>
          <Modal.Body>
            <ActionForm form={createTodoForm}>
              <Layout gap="var(--polly-space-md)">
                <label>
                  Title
                  <TextInput name="title" required autoFocus />
                </label>
                {createTodoForm.errors.value.title ? (
                  <p role="alert">{createTodoForm.errors.value.title}</p>
                ) : null}
                <Layout columns="1fr auto auto" gap="var(--polly-space-sm)">
                  <span />
                  <Modal.Close>Cancel</Modal.Close>
                  <button
                    type="submit"
                    data-polly-ui
                    data-polly-interactive
                    disabled={createTodoForm.isSubmitting.value}
                  >
                    Save
                  </button>
                </Layout>
              </Layout>
            </ActionForm>
          </Modal.Body>
        </Modal.Content>
      </Modal.Root>
    </div>
  );
}
