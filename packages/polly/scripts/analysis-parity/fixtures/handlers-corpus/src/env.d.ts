// Ambient modules and globals the corpus reads syntactically.
declare module "elysia" {
  export class Elysia {
    get(path: string, handler: (...args: unknown[]) => unknown): Elysia;
    post(path: string, handler: (...args: unknown[]) => unknown): Elysia;
  }
}

/** An ambient type guard: a declaration with a predicate and no body. */
declare function isAmbientMessage(m: unknown): m is AmbientMessage;
interface AmbientMessage {
  type: "ambient";
}
