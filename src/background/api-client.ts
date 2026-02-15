// API client for cross-origin requests

import { getMessageBus, type MessageBus } from "@/shared/lib/message-bus";

export class APIClient {
  private bus: MessageBus;

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus("background");
    this.setupHandlers();
  }

  private setupHandlers(): void {
    // Handle API_REQUEST messages
    this.bus.on("API_REQUEST", async (payload) => {
      const { endpoint, method, body, headers } = payload;

      this.bus.adapters.logger.info("API request", { endpoint, method });

      try {
        const startTime = performance.now();
        const response = await this.bus.adapters.fetch.fetch(endpoint, {
          method,
          headers: {
            "Content-Type": "application/json",
            ...(headers || {}),
          },
          ...(body !== undefined && { body: JSON.stringify(body) }),
        });
        const duration = performance.now() - startTime;

        const data = await response.json().catch(() => null);

        this.bus.adapters.logger.debug("API response", {
          endpoint,
          method,
          status: response.status,
          duration: Math.round(duration),
        });

        if (!response.ok) {
          this.bus.adapters.logger.error(
            "API request failed",
            new Error(`${response.status} ${response.statusText}`),
            { endpoint, method, status: response.status }
          );
        }

        const responseHeaders: Record<string, string> = {};
        response.headers.forEach((value, key) => {
          responseHeaders[key] = value;
        });

        return {
          data,
          status: response.status,
          statusText: response.statusText,
          headers: responseHeaders,
        };
      } catch (error) {
        this.bus.adapters.logger.error(
          "API request error",
          error instanceof Error ? error : new Error(String(error)),
          { endpoint, method }
        );

        return {
          data: null,
          status: 0,
          statusText: "Network Error",
          headers: {},
          error: error instanceof Error ? error.message : "Unknown error",
        };
      }
    });

    // Handle API_BATCH messages
    this.bus.on("API_BATCH", async (payload) => {
      const { requests } = payload;

      this.bus.adapters.logger.info("API batch request", {
        count: requests.length,
      });

      const results = await Promise.all(
        requests.map(async (req) => {
          try {
            const response = await this.bus.adapters.fetch.fetch(req.endpoint, {
              method: req.method,
              headers: {
                "Content-Type": "application/json",
              },
              ...(req.body !== undefined && { body: JSON.stringify(req.body) }),
            });

            const data = await response.json().catch(() => null);

            return {
              data,
              status: response.status,
            };
          } catch (error) {
            this.bus.adapters.logger.error(
              "API batch request error",
              error instanceof Error ? error : new Error(String(error)),
              { endpoint: req.endpoint, method: req.method }
            );

            return {
              data: null,
              status: 0,
              error: error instanceof Error ? error.message : "Unknown error",
            };
          }
        })
      );

      this.bus.adapters.logger.debug("API batch complete", {
        count: results.length,
        successful: results.filter((r) => r.status >= 200 && r.status < 300).length,
      });

      return { results };
    });
  }
}

// Export alias for backwards compatibility
export { APIClient as ApiClient };
