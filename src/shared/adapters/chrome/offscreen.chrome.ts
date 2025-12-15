// Chrome offscreen adapter implementation

import type { CreateOffscreenDocumentParameters, OffscreenAdapter } from "../offscreen.adapter";

export class ChromeOffscreenAdapter implements OffscreenAdapter {
  async createDocument(parameters: CreateOffscreenDocumentParameters): Promise<void> {
    await chrome.offscreen.createDocument({
      url: parameters.url,
      reasons: parameters.reasons as chrome.offscreen.Reason[],
      justification: parameters.justification,
    });
  }

  async closeDocument(): Promise<void> {
    await chrome.offscreen.closeDocument();
  }

  async hasDocument(): Promise<boolean> {
    // Chrome doesn't provide a direct API, so we query for offscreen contexts
    const existingContexts = await chrome.runtime.getContexts({
      contextTypes: ["OFFSCREEN_DOCUMENT" as chrome.runtime.ContextType],
    });
    return existingContexts.length > 0;
  }
}
