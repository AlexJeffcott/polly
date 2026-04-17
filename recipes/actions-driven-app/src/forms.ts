/**
 * Forms live next to their features.
 *
 * The create form lives here because it has no entity backing. If the
 * app grew, an edit form with a guard and onOpen override would live
 * alongside it — one createForm call per form.
 */

import { createForm } from "@fairfox/polly/actions";
import type { RootStore } from "./stores.ts";

export type CreateTodoValues = { title: string };

export const createTodoForm = createForm<CreateTodoValues, RootStore>({
  name: "todo:create",
  initialValues: { title: "" },
  validate: (v) => (v.title.trim() === "" ? { title: "Title required" } : null),
  onSubmit: async ({ values, stores }) => {
    stores.todos.add(values.title);
  },
});
