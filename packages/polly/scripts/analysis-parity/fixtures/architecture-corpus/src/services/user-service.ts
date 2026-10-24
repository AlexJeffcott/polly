import { db } from "../db/client";

export function createUser(payload: unknown): { id: number; payload: unknown } {
  db.execute("insert");
  return { id: 1, payload };
}

export const getDatabase = () => db;

// biome-ignore lint/complexity/useArrowFunction: a function expression is the case under test
export const notifyAll = function (): void {
  getLoggerService();
};

function getLoggerService(): void {
  // noop
}
