// Fetch adapter interface (wraps fetch API)

export interface FetchAdapter {
  fetch(input: string | URL, init?: RequestInit): Promise<Response>;
}

export class BrowserFetchAdapter implements FetchAdapter {
  fetch(input: string | URL, init?: RequestInit): Promise<Response> {
    return fetch(input, init);
  }
}
