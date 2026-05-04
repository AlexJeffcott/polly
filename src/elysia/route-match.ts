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
  if (!configs) return undefined;

  for (const [pattern, config] of Object.entries(configs)) {
    if (matchRoute(pattern, method, path)) {
      return config;
    }
  }

  return undefined;
}
