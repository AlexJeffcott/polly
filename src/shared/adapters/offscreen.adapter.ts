// Offscreen adapter interface (wraps chrome.offscreen)

export interface OffscreenAdapter {
  /**
   * Create offscreen document
   */
  createDocument(parameters: CreateOffscreenDocumentParameters): Promise<void>;

  /**
   * Close offscreen document
   */
  closeDocument(): Promise<void>;

  /**
   * Check if offscreen document exists
   */
  hasDocument(): Promise<boolean>;
}

export interface CreateOffscreenDocumentParameters {
  url: string;
  reasons: OffscreenReason[];
  justification: string;
}

export type OffscreenReason =
  | "AUDIO_PLAYBACK"
  | "BLOBS"
  | "CLIPBOARD"
  | "DOM_PARSER"
  | "DOM_SCRAPING"
  | "IFRAME_SCRIPTING"
  | "LOCAL_STORAGE"
  | "MATCH_MEDIA"
  | "TESTING"
  | "USER_MEDIA"
  | "WEB_RTC"
  | "WORKERS";
