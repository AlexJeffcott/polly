/**
 * The gallery's browser entry point. Bundled by server.ts (one Bun.build pass)
 * — its transitive `.module.css` imports plus the global stylesheets below come
 * out as a single CSS artifact the server serves alongside this script.
 *
 * Boot mirrors a real consumer app: bind the demo form, install the document
 * event delegation that routes `data-action` clicks/submits into the gallery's
 * action registry, then render. The overlay hosts live inside <GalleryApp />.
 */

import { render } from "preact";
import { installEventDelegation } from "../../../src/actions";
import { GALLERY_ACTIONS } from "./actions.ts";
import { GalleryApp } from "./gallery-app.tsx";
import { type GalleryStores, galleryForm } from "./stores.ts";
import "../../../src/polly-ui/theme.css";
import "../../../src/polly-ui/styles.css";
import "./gallery.css";

const stores: GalleryStores = {};
galleryForm.bindStores(() => stores);

installEventDelegation(async (dispatch) => {
  const handler = GALLERY_ACTIONS[dispatch.action];
  if (handler) {
    await handler({
      stores,
      event: dispatch.event,
      element: dispatch.element,
      data: dispatch.data,
    });
  }
});

const root = document.getElementById("app") ?? document.body;
render(<GalleryApp />, root);
