/**
 * Context-Specific Helpers
 *
 * Provides context-specific utility methods to make common patterns easier.
 */

import type { ExtensionAdapters } from "../adapters";

/**
 * View types for extension views.
 * This is a local type definition since chrome.extension.ViewType is deprecated.
 */
type ExtensionViewType = "tab" | "popup" | "notification";

/**
 * Helpers for content script context.
 * Content scripts have access to the DOM and page context.
 */
export interface ContentScriptHelpers {
  /**
   * Get basic page information.
   */
  getPageInfo(): {
    url: string;
    title: string;
    host: string;
    pathname: string;
    readyState: DocumentReadyState;
  };

  /**
   * Query DOM elements (returns serializable data).
   */
  queryElements(selector: string): Array<{
    tagName: string;
    id: string;
    className: string;
    textContent: string;
  }>;

  /**
   * Get page metadata (meta tags).
   */
  getPageMetadata(): Record<string, string>;

  /**
   * Inject CSS into the page.
   */
  injectCSS(css: string): void;

  /**
   * Remove injected CSS.
   */
  removeCSS(styleId: string): void;
}

export function createContentScriptHelpers(): ContentScriptHelpers {
  return {
    getPageInfo() {
      return {
        url: window.location.href,
        title: document.title,
        host: window.location.host,
        pathname: window.location.pathname,
        readyState: document.readyState,
      };
    },

    queryElements(selector: string) {
      const elements = document.querySelectorAll(selector);
      return Array.from(elements).map((el) => ({
        tagName: el.tagName,
        id: el.id,
        className: el.className,
        textContent: el.textContent?.slice(0, 100) || "",
      }));
    },

    getPageMetadata() {
      const metadata: Record<string, string> = {};
      const metaTags = document.querySelectorAll("meta");

      metaTags.forEach((tag) => {
        const name = tag.getAttribute("name") || tag.getAttribute("property");
        const content = tag.getAttribute("content");

        if (name && content) {
          metadata[name] = content;
        }
      });

      return metadata;
    },

    injectCSS(css: string) {
      const styleId = `ext-injected-${Date.now()}`;
      const style = document.createElement("style");
      style.id = styleId;
      style.textContent = css;
      document.head.appendChild(style);
    },

    removeCSS(styleId: string) {
      const style = document.getElementById(styleId);
      if (style) {
        style.remove();
      }
    },
  };
}

/**
 * Helpers for DevTools panel context.
 * DevTools can inspect the page and access Chrome DevTools APIs.
 */
export interface DevToolsHelpers {
  /**
   * Get the ID of the tab being inspected.
   */
  get inspectedTabId(): number | undefined;

  /**
   * Execute code in the inspected page context.
   */
  evalInPage<T = unknown>(code: string): Promise<T>;

  /**
   * Get page resource content (HTML, CSS, JS files).
   */
  getPageResource(url: string): Promise<string>;

  /**
   * Reload the inspected page.
   */
  reloadInspectedPage(options?: { ignoreCache?: boolean; userAgent?: string }): void;
}

export function createDevToolsHelpers(): DevToolsHelpers {
  return {
    get inspectedTabId() {
      return chrome.devtools?.inspectedWindow?.tabId;
    },

    evalInPage<T = unknown>(code: string): Promise<T> {
      return new Promise((resolve, reject) => {
        if (!chrome.devtools?.inspectedWindow) {
          reject(new Error("DevTools inspectedWindow not available"));
          return;
        }

        chrome.devtools.inspectedWindow.eval(code, (result, error) => {
          if (error) {
            reject(new Error(error.isException ? error.value : "Execution error"));
          } else {
            resolve(result as T);
          }
        });
      });
    },

    getPageResource(url: string): Promise<string> {
      return new Promise((resolve, reject) => {
        if (!chrome.devtools?.inspectedWindow) {
          reject(new Error("DevTools inspectedWindow not available"));
          return;
        }

        chrome.devtools.inspectedWindow.getResources((resources) => {
          const resource = resources.find((r) => r.url === url);
          if (!resource) {
            reject(new Error(`Resource not found: ${url}`));
            return;
          }

          resource.getContent((content, encoding) => {
            if (encoding === "base64") {
              resolve(atob(content));
            } else {
              resolve(content);
            }
          });
        });
      });
    },

    reloadInspectedPage(options = {}) {
      if (!chrome.devtools?.inspectedWindow) {
        console.warn("DevTools inspectedWindow not available");
        return;
      }

      chrome.devtools.inspectedWindow.reload(options);
    },
  };
}

/**
 * Helpers for popup context.
 * Popups are short-lived UI windows.
 */
export interface PopupHelpers {
  /**
   * Get current active tab.
   */
  getCurrentTab(): Promise<chrome.tabs.Tab | undefined>;

  /**
   * Close the popup programmatically.
   */
  closePopup(): void;

  /**
   * Set popup dimensions.
   */
  setDimensions(width: number, height: number): void;
}

export function createPopupHelpers(adapters: ExtensionAdapters): PopupHelpers {
  return {
    async getCurrentTab() {
      const tabs = await adapters.tabs.query({ active: true, currentWindow: true });
      return tabs[0];
    },

    closePopup() {
      window.close();
    },

    setDimensions(width: number, height: number) {
      document.body.style.width = `${width}px`;
      document.body.style.height = `${height}px`;
    },
  };
}

/**
 * Helpers for options page context.
 * Options pages are full-page settings interfaces.
 */
export interface OptionsHelpers {
  /**
   * Open extension in new tab (for external links).
   */
  openInNewTab(path: string): void;

  /**
   * Show save confirmation message.
   */
  showSaveConfirmation(message?: string, duration?: number): void;

  /**
   * Show error message.
   */
  showError(message: string, duration?: number): void;
}

export function createOptionsHelpers(adapters: ExtensionAdapters): OptionsHelpers {
  return {
    openInNewTab(path: string) {
      adapters.tabs.create({ url: path });
    },

    showSaveConfirmation(message = "Settings saved!", duration = 3000) {
      const notification = document.createElement("div");
      notification.textContent = message;
      notification.style.cssText = `
        position: fixed;
        top: 20px;
        right: 20px;
        background: #4caf50;
        color: white;
        padding: 12px 24px;
        border-radius: 4px;
        box-shadow: 0 2px 8px rgba(0,0,0,0.2);
        z-index: 10000;
        animation: slideIn 0.3s ease;
      `;

      document.body.appendChild(notification);

      setTimeout(() => {
        notification.style.animation = "slideOut 0.3s ease";
        setTimeout(() => notification.remove(), 300);
      }, duration);
    },

    showError(message: string, duration = 5000) {
      const notification = document.createElement("div");
      notification.textContent = message;
      notification.style.cssText = `
        position: fixed;
        top: 20px;
        right: 20px;
        background: #f44336;
        color: white;
        padding: 12px 24px;
        border-radius: 4px;
        box-shadow: 0 2px 8px rgba(0,0,0,0.2);
        z-index: 10000;
        animation: slideIn 0.3s ease;
      `;

      document.body.appendChild(notification);

      setTimeout(() => {
        notification.style.animation = "slideOut 0.3s ease";
        setTimeout(() => notification.remove(), 300);
      }, duration);
    },
  };
}

/**
 * Helpers for side panel context.
 * Side panels are persistent companion interfaces.
 */
export interface SidePanelHelpers {
  /**
   * Get current active tab.
   */
  getCurrentTab(): Promise<chrome.tabs.Tab | undefined>;

  /**
   * Check if side panel is currently visible.
   */
  isVisible(): boolean;

  /**
   * Set side panel width (if supported by browser).
   */
  setWidth(width: number): void;
}

export function createSidePanelHelpers(adapters: ExtensionAdapters): SidePanelHelpers {
  return {
    async getCurrentTab() {
      const tabs = await adapters.tabs.query({ active: true, currentWindow: true });
      return tabs[0];
    },

    isVisible() {
      return document.visibilityState === "visible";
    },

    setWidth(width: number) {
      document.body.style.width = `${width}px`;
    },
  };
}

/**
 * Helpers for background context.
 * Background scripts coordinate extension behavior.
 */
export interface BackgroundHelpers {
  /**
   * Get all open tabs.
   */
  getAllTabs(): Promise<chrome.tabs.Tab[]>;

  /**
   * Get extension views (popup, options, devtools, etc).
   */
  getExtensionViews(type?: ExtensionViewType): Window[];

  /**
   * Open options page.
   */
  openOptionsPage(): void;

  /**
   * Set extension badge.
   */
  setBadge(text: string, color?: string): void;

  /**
   * Clear extension badge.
   */
  clearBadge(): void;
}

export function createBackgroundHelpers(adapters: ExtensionAdapters): BackgroundHelpers {
  return {
    async getAllTabs() {
      return adapters.tabs.query({});
    },

    getExtensionViews(type?: ExtensionViewType) {
      return chrome.extension.getViews(type ? { type } : undefined);
    },

    openOptionsPage() {
      adapters.runtime.openOptionsPage();
    },

    setBadge(text: string, color = "#f44336") {
      chrome.action.setBadgeText({ text });
      chrome.action.setBadgeBackgroundColor({ color });
    },

    clearBadge() {
      chrome.action.setBadgeText({ text: "" });
    },
  };
}
