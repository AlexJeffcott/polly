export const db = {
  query: async (_sql: string): Promise<unknown[]> => [],
  insert: async (_table: string, _row: unknown): Promise<void> => {
    // noop
  },
  execute: (_sql: string): void => {
    // noop
  },
};
