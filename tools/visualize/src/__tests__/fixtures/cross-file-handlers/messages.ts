// Message types for cross-file handler test

export type RequestMessage = QueryMessage | CommandMessage;

export type QueryMessage = {
  type: "query";
  data: string;
};

export type CommandMessage = {
  type: "command";
  action: string;
};

// Type guards
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === "query";
}

export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === "command";
}
