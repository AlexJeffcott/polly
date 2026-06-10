/**
 * Route pattern matcher
 * Supports:
 * - Exact match: 'POST /todos'
 * - Param match: 'GET /todos/:id'
 * - Wildcard: '/todos/*'
 */
export function matchRoute(pattern: string, method: string, path: string): boolean {
  const spaceIdx = pattern.indexOf(" ");
  const patternMethod = spaceIdx === -1 ? null : pattern.slice(0, spaceIdx);
  const patternPath = spaceIdx === -1 ? pattern : pattern.slice(spaceIdx + 1);

  if (patternMethod && patternMethod !== method) {
    return false;
  }

  const patternSegments = patternPath.split("/").filter(Boolean);
  const pathSegments = path.split("/").filter(Boolean);

  if (patternSegments.length !== pathSegments.length && !patternPath.includes("*")) {
    return false;
  }

  for (let i = 0; i < patternSegments.length; i++) {
    const patternSeg = patternSegments[i];
    const pathSeg = pathSegments[i];

    if (patternSeg === "*") return true;
    if (patternSeg?.startsWith(":")) continue;
    if (patternSeg !== pathSeg) return false;
  }

  return true;
}

export function findMatchingConfig<T>(
  configs: Record<string, T> | undefined,
  method: string,
  path: string
): T | undefined {
  return findMatchingEntry(configs, method, path)?.config;
}

/**
 * Like {@link findMatchingConfig} but also returns the pattern that matched, so
 * callers can extract path params (e.g. `:id`) with {@link extractRouteParams}.
 */
export function findMatchingEntry<T>(
  configs: Record<string, T> | undefined,
  method: string,
  path: string
): { pattern: string; config: T } | undefined {
  if (!configs) return undefined;

  for (const [pattern, config] of Object.entries(configs)) {
    if (matchRoute(pattern, method, path)) {
      return { pattern, config };
    }
  }

  return undefined;
}

/**
 * Extract named params from a concrete path using a route pattern.
 * `extractRouteParams('PATCH /todos/:id', '/todos/5')` → `{ id: '5' }`.
 */
export function extractRouteParams(pattern: string, path: string): Record<string, string> {
  const spaceIdx = pattern.indexOf(" ");
  const patternPath = spaceIdx === -1 ? pattern : pattern.slice(spaceIdx + 1);

  const patternSegments = patternPath.split("/").filter(Boolean);
  const pathSegments = path.split("/").filter(Boolean);

  const params: Record<string, string> = {};
  for (let i = 0; i < patternSegments.length; i++) {
    const seg = patternSegments[i];
    if (seg?.startsWith(":")) {
      const value = pathSegments[i];
      if (value !== undefined) params[seg.slice(1)] = value;
    }
  }
  return params;
}
