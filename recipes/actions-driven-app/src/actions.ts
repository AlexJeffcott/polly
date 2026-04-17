/**
 * Action registry.
 *
 * Every state-mutating interaction flows through here. Components emit
 * `data-action` markup; the event delegation runtime dispatches to the
 * handler by name. Business logic for todos, view state, and the form
 * all live together — no callbacks threaded through components.
 */

import type { ActionRegistry } from "@fairfox/polly/actions";
import { submitError } from "@fairfox/polly/actions";
import { createTodoForm } from "./forms.ts";
import type { RootStore } from "./stores.ts";

export const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  ...createTodoForm.actions,

  "todo:toggle": ({ data, stores }) => {
    const id = data["todoId"];
    if (!id) return;
    stores.todos.toggle(id);
  },

  "todo:remove": ({ data, stores }) => {
    const id = data["todoId"];
    if (!id) return;
    stores.todos.remove(id);
  },

  "todo:rename": ({ data, stores }) => {
    const id = data["todoId"];
    const title = data["value"];
    if (!id || typeof title !== "string") return;
    if (title.trim() === "") {
      submitError("todo:rename", new Error("Title cannot be empty"));
      return;
    }
    stores.todos.rename(id, title.trim());
  },

  "theme:toggle": ({ stores }) => {
    stores.view.toggleTheme();
  },
};
