// Every TypeInfo kind convertType distinguishes, nested and nullable.

export type Role = "admin" | "user" | "guest";

export type Profile = {
  name: string;
  age: number;
  verified: boolean;
};

export type AppState = {
  flag: boolean;
  literalTrue: true;
  role: Role;
  inlineEnum: "on" | "off";
  count: number;
  literalNumber: 42;
  label: string;
  literalString: "fixed";
  maybeName: string | null;
  optionalCount?: number;
  nullableRole: Role | null;
  mixed: string | number;
  tags: string[];
  profiles: Profile[];
  matrix: number[][];
  byId: Map<string, Profile>;
  seen: Set<number>;
  record: Record<string, boolean>;
  nested: {
    inner: {
      depth: number;
      mode: "a" | "b" | "c";
    };
    list: Array<"x" | "y">;
  };
  callback: () => void;
  anything: unknown;
  nothing: null;
};
