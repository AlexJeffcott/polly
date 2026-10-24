import type { AppState } from "./types/state";

type Handler = (payload: unknown) => void;

const handlers = new Map<string, Handler>();

const bus = {
  on(type: string, handler: Handler): void {
    handlers.set(type, handler);
  },
};

declare function requires(condition: boolean, message: string): void;
declare function ensures(condition: boolean, message: string): void;

export const state: AppState = {
  flag: false,
  literalTrue: true,
  role: "guest",
  inlineEnum: "off",
  count: 0,
  literalNumber: 42,
  label: "",
  literalString: "fixed",
  maybeName: null,
  nullableRole: null,
  mixed: 0,
  tags: [],
  profiles: [],
  matrix: [],
  byId: new Map(),
  seen: new Set(),
  record: {},
  nested: { inner: { depth: 0, mode: "a" }, list: [] },
  callback: () => undefined,
  anything: undefined,
  nothing: null,
};

bus.on("USER_LOGIN", () => {
  requires(state.role === "guest", "Must be a guest");
  state.role = "user";
  state.flag = true;
  state.count += 1;
  ensures(state.role === "user", "Must be a user");
});

bus.on("USER_LOGOUT", () => {
  state.role = "guest";
  state.flag = false;
  state.maybeName = null;
});

bus.on("SET_ROLE", () => {
  state.role = "admin";
  state.nested.inner.mode = "b";
});
