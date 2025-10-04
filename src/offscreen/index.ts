// Offscreen document for clipboard operations

import { getMessageBus } from "@/shared/lib/message-bus";

const bus = getMessageBus("offscreen");

// Connect with port
bus.connect("offscreen");

// Register clipboard handlers
bus.on("CLIPBOARD_WRITE", async (payload) => {
  try {
    await navigator.clipboard.writeText(payload.text);
    return { success: true };
  } catch (error) {
    console.error("[Offscreen] Failed to write to clipboard:", error);
    return { success: false };
  }
});

bus.on("CLIPBOARD_WRITE_HTML", async (payload) => {
  try {
    const blob = new Blob([payload.html], { type: "text/html" });
    const item = new ClipboardItem({ "text/html": blob });
    await navigator.clipboard.write([item]);
    return { success: true };
  } catch (error) {
    console.error("[Offscreen] Failed to write HTML to clipboard:", error);
    return { success: false };
  }
});

bus.on("CLIPBOARD_WRITE_RICH", async (payload) => {
  try {
    const textBlob = new Blob([payload.data.text], { type: "text/plain" });
    const htmlBlob = new Blob([payload.data.html], { type: "text/html" });
    const item = new ClipboardItem({
      "text/plain": textBlob,
      "text/html": htmlBlob,
    });
    await navigator.clipboard.write([item]);
    return { success: true };
  } catch (error) {
    console.error("[Offscreen] Failed to write rich content to clipboard:", error);
    return { success: false };
  }
});

bus.on("CLIPBOARD_READ", async () => {
  try {
    const text = await navigator.clipboard.readText();
    return { text };
  } catch (error) {
    console.error("[Offscreen] Failed to read from clipboard:", error);
    return { text: "" };
  }
});
