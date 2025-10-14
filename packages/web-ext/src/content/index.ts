// Content script entry point

import { getMessageBus } from "@/shared/lib/message-bus";
import { injectPageScript } from "./page-bridge";

const bus = getMessageBus("content");

// Connect with long-lived port (we'll get tabId from background)
// For now, use a placeholder - background will route messages correctly
bus.connect(`content-${Math.random().toString(36).substr(2, 9)}`);

// Inject page script
injectPageScript();

// Register DOM operation handlers
bus.on("DOM_QUERY", async (payload) => {
  const elements = Array.from(document.querySelectorAll(payload.selector));
  return {
    elements: elements.map((el) => ({
      tag: el.tagName.toLowerCase(),
      text: el.textContent || "",
      html: el.innerHTML,
      attrs: Object.fromEntries(Array.from(el.attributes).map((a) => [a.name, a.value])),
      rect: el.getBoundingClientRect(),
    })),
  };
});

bus.on("DOM_UPDATE", async (payload) => {
  const el = document.querySelector(payload.selector);
  if (el) {
    el.textContent = payload.content;
    return { success: true };
  }
  return { success: false };
});

bus.on("DOM_INSERT", async (payload) => {
  const target = document.querySelector("body") || document.documentElement;
  target.insertAdjacentHTML(payload.position, payload.html);
  return { success: true };
});

bus.on("DOM_REMOVE", async (payload) => {
  const elements = document.querySelectorAll(payload.selector);
  for (const el of Array.from(elements)) {
    el.remove();
  }
  return { success: true, count: elements.length };
});

bus.on("DEVTOOLS_INSPECT_ELEMENT", async (payload) => {
  const el = document.querySelector(payload.selector);
  if (el) {
    el.scrollIntoView({ behavior: "smooth", block: "center" });
    // Add visual highlight
    const originalOutline = (el as HTMLElement).style.outline;
    (el as HTMLElement).style.outline = "2px solid red";
    setTimeout(() => {
      (el as HTMLElement).style.outline = originalOutline;
    }, 2000);
    return { success: true };
  }
  return { success: false };
});
