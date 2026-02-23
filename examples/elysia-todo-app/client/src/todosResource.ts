import { $resource } from "@fairfox/polly";
import { clientState } from "./api";

type Todo = { id: number; text: string; completed: boolean };

/**
 * Async resource that fetches todos when the user changes.
 *
 * `source` is synchronous and fully tracked — when clientState.user changes,
 * the fetcher re-runs automatically. Signal reads inside `fetcher` would be
 * invisible to the dependency graph (async boundary), which is why the split
 * exists.
 */
export const todosResource = $resource<{ userId: number | null }, Todo[]>("todos", {
  source: () => ({
    userId: clientState.user.value?.id ?? null,
  }),
  fetcher: async ({ userId }) => {
    if (userId === null) return [];
    const res = await fetch(`http://localhost:3000/todos`);
    if (!res.ok) throw new Error(`Failed to fetch todos: ${res.status}`);
    return (await res.json()) as Todo[];
  },
  initialValue: [],
});
