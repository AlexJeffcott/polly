import type { FetchAdapter } from "@/shared/adapters/fetch.adapter";

export interface MockFetch extends FetchAdapter {
  _responses: Array<Partial<Response>>;
  _calls: Array<{ input: string | URL; init?: RequestInit }>;
}

export function createMockFetch(): MockFetch {
  const responses: Array<Partial<Response>> = [];
  const calls: Array<{ input: string | URL; init?: RequestInit }> = [];

  return {
    fetch: async (input: string | URL, init?: RequestInit): Promise<Response> => {
      calls.push({ input, ...(init && { init }) });

      const mockResponse = responses.shift() || {
        ok: true,
        status: 200,
        headers: new Headers(),
        statusText: "OK",
        json: async () => ({}),
        text: async () => "",
        blob: async () => new Blob(),
        arrayBuffer: async () => new ArrayBuffer(0),
        formData: async () => new FormData(),
      };

      return mockResponse as Response;
    },
    _responses: responses,
    _calls: calls,
  };
}
