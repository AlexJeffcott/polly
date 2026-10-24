// Message-type shapes findMessageTypes recognises, and some it only warns on.

export type SimpleMessage = "PING" | "PONG";

export type Discriminated =
  | { type: "USER_LOGIN"; userId: string }
  | { type: "USER_LOGOUT" }
  | { type: "SET_ROLE"; role: "admin" | "user" };

export type AliasOfAlias = SimpleMessage;

export type Composite = Discriminated | SimpleMessage | "RESET";

export type Keys = "OPEN" | "CLOSE";

export type Mapped = { [K in Keys]: { type: K } };

export type Templated = `EVENT_${string}`;

export type DiscriminatedTemplate = { type: `CMD_${number}` } | { type: "CMD_STOP" };

export type Conditional<T> = T extends string ? "STRING_MSG" : "OTHER_MSG";
