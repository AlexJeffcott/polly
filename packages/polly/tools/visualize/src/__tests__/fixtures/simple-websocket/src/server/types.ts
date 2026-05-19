// Message type definitions

export interface QueryMessage {
  type: "query";
  id: string;
}

export interface CommandMessage {
  type: "command";
  action: string;
  payload: unknown;
}

export interface AuthMessage {
  type: "auth";
  token: string;
}

export type RequestMessage = QueryMessage | CommandMessage | AuthMessage;

export interface User {
  id: string;
  name: string;
  email: string;
}

export interface QueryResult {
  data: User[];
  count: number;
}
