import type {
  CreateOffscreenDocumentParameters,
  OffscreenAdapter,
} from "@/shared/adapters/offscreen.adapter";

export interface MockOffscreen extends OffscreenAdapter {
  _hasDocument: boolean;
}

export function createMockOffscreen(): MockOffscreen {
  let hasDocument = false;

  return {
    createDocument: async (_parameters: CreateOffscreenDocumentParameters): Promise<void> => {
      hasDocument = true;
    },
    closeDocument: async (): Promise<void> => {
      hasDocument = false;
    },
    hasDocument: async (): Promise<boolean> => {
      return hasDocument;
    },
    _hasDocument: hasDocument,
  };
}
