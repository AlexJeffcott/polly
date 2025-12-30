// Offscreen document manager

import type { OffscreenAdapter } from "@/shared/adapters";
import { ErrorHandler } from "@/shared/lib/errors";
import { getMessageBus, type MessageBus } from "@/shared/lib/message-bus";

export class OffscreenManager {
  private bus: MessageBus;
  private isCreated = false;
  private offscreen: OffscreenAdapter;
  private errorHandler: ErrorHandler;

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus("background");
    this.offscreen = this.bus.adapters.offscreen;
    this.errorHandler = new ErrorHandler(this.bus.adapters.logger);
  }

  async ensureOffscreenDocument(): Promise<void> {
    if (this.isCreated) return;

    try {
      // Check if already exists
      const hasDoc = await this.offscreen.hasDocument();
      if (hasDoc) {
        this.isCreated = true;
        return;
      }

      // Create offscreen document
      await this.offscreen.createDocument({
        url: "offscreen/offscreen.html",
        reasons: ["CLIPBOARD"],
        justification: "Access clipboard for copy/paste operations",
      });

      this.isCreated = true;
      this.bus.adapters.logger.info("Offscreen document created");
    } catch (error) {
      throw this.errorHandler.wrap(
        error,
        "Failed to create offscreen document",
        "OFFSCREEN_CREATE_ERROR"
      );
    }
  }

  async closeOffscreenDocument(): Promise<void> {
    if (!this.isCreated) return;

    try {
      await this.offscreen.closeDocument();
      this.isCreated = false;
      this.bus.adapters.logger.info("Offscreen document closed");
    } catch (error) {
      throw this.errorHandler.wrap(
        error,
        "Failed to close offscreen document",
        "OFFSCREEN_CLOSE_ERROR"
      );
    }
  }
}
