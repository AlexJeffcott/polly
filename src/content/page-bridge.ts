// Bridge to inject page script into page's JavaScript environment

export function injectPageScript(): void {
  const script = document.createElement("script");
  script.src = chrome.runtime.getURL("page/index.js");
  script.type = "module";
  script.onload = () => {
    script.remove();
  };
  script.onerror = (error) => {
    console.log("[Content Script] Failed to inject page script:", error);
  };

  // Inject as early as possible
  (document.head || document.documentElement).appendChild(script);
}
