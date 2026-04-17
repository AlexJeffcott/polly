/**
 * App entry point.
 *
 * Wires up the stores bag, late-binds forms, installs the event
 * delegation, registers the StoreProvider, and mounts.
 */

import { installEventDelegation, StoreProvider, submitError } from "@fairfox/polly/actions";
import "@fairfox/polly/ui/styles.css";
import "@fairfox/polly/ui/theme.css";
import "@fairfox/polly/ui/components.css";
import { render } from "preact";
import { App } from "./App.tsx";
import { ACTION_REGISTRY } from "./actions.ts";
import { createTodoForm } from "./forms.ts";
import { makeRootStore } from "./stores.ts";

const stores = makeRootStore();
createTodoForm.bindStores(() => stores);

installEventDelegation(async (dispatch) => {
  const handler = ACTION_REGISTRY[dispatch.action];
  if (!handler) return;
  try {
    await handler({
      stores,
      event: dispatch.event,
      element: dispatch.element,
      data: dispatch.data,
    });
  } catch (err) {
    submitError(dispatch.action, err);
  }
});

const root = document.getElementById("app");
if (!root) throw new Error("missing #app mount point");
render(
  <StoreProvider stores={stores}>
    <App />
  </StoreProvider>,
  root
);
