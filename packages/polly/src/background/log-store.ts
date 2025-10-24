// Centralized logging service - collects logs from all contexts
import type { MessageBus } from "@/shared/lib/message-bus";
import { getMessageBus } from "@/shared/lib/message-bus";
import type { LogEntry } from "@/shared/types/messages";

export interface LogStoreOptions {
  maxLogs?: number;
  persistToStorage?: boolean;
  storageKey?: string;
}

export class LogStore {
  private bus: MessageBus;
  private logs: LogEntry[] = [];
  private maxLogs: number;

  constructor(bus?: MessageBus, options?: LogStoreOptions) {
    this.bus = bus || getMessageBus("background");
    this.maxLogs = options?.maxLogs || 1000;
    this.setupHandlers();
  }

  private setupHandlers(): void {
    // Handle LOG messages from all contexts
    this.bus.on("LOG", async (payload) => {
      const entry: LogEntry = {
        id: crypto.randomUUID(),
        level: payload.level,
        message: payload.message,
        ...(payload.context && { context: payload.context }),
        ...(payload.error && { error: payload.error }),
        ...(payload.stack && { stack: payload.stack }),
        source: payload.source,
        timestamp: payload.timestamp,
      };

      // Add to circular buffer
      this.logs.push(entry);

      // Remove oldest if exceeding max
      if (this.logs.length > this.maxLogs) {
        this.logs.shift();
      }

      return { success: true };
    });

    // Handle LOGS_GET with filtering
    this.bus.on("LOGS_GET", async (payload) => {
      let filtered = this.logs;

      // Filter by level
      if (payload.filters?.level) {
        filtered = filtered.filter((log) => log.level === payload.filters?.level);
      }

      // Filter by source context
      if (payload.filters?.source) {
        filtered = filtered.filter((log) => log.source === payload.filters?.source);
      }

      // Filter by timestamp (since)
      if (payload.filters?.since !== undefined) {
        const since = payload.filters.since;
        filtered = filtered.filter((log) => log.timestamp >= since);
      }

      // Limit results
      if (payload.filters?.limit) {
        filtered = filtered.slice(-payload.filters.limit);
      }

      return { logs: filtered };
    });

    // Handle LOGS_CLEAR
    this.bus.on("LOGS_CLEAR", async () => {
      const count = this.logs.length;
      this.logs = [];
      return { success: true, count };
    });

    // Handle LOGS_EXPORT
    this.bus.on("LOGS_EXPORT", async () => {
      const json = JSON.stringify(this.logs, null, 2);
      return { json, count: this.logs.length };
    });
  }

  /**
   * Get current log count (for debugging)
   */
  getCount(): number {
    return this.logs.length;
  }

  /**
   * Get all logs (for debugging)
   */
  getAllLogs(): LogEntry[] {
    return [...this.logs];
  }
}
