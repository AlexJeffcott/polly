// ts-morph's `project.getSourceFiles(glob)` match rule, without minimatch.
//
// ts-morph anchored a relative glob at the process cwd (`./` stripped, then
// joined onto cwd) and matched it against each absolute file path with
// minimatch's defaults: case-sensitive, and `*`, `?` and `**` never match a
// path segment that starts with a dot. Bun.Glob does match dot segments under
// `**`, and matches `../x` against `**/x`, so it is not a drop-in.
//
// Only the syntax the extractors use is supported: literal characters, `*`,
// `?` and `**` segments. Anything else (`[...]`, `{a,b}`, negation, extglobs)
// throws rather than silently matching differently.

const UNSUPPORTED = /[[\]{}]|[!+@](?=\()|^!/;

/** `*` / `?` wildcard match of one path segment (greedy with backtracking to the last `*`; no RegExp). */
function wildcardMatch(pattern: string, name: string): boolean {
  let p = 0;
  let n = 0;
  let star = -1;
  let resume = 0;
  while (n < name.length) {
    const c = pattern[p];
    if (c === "*") {
      star = p++;
      resume = n;
    } else if (c !== undefined && (c === "?" || c === name[n])) {
      p++;
      n++;
    } else if (star === -1) {
      return false;
    } else {
      p = star + 1;
      n = ++resume;
    }
  }
  while (pattern[p] === "*") p++;
  return p === pattern.length;
}

function segmentMatcher(segment: string): (name: string) => boolean {
  if (!/[*?]/.test(segment)) return (name) => name === segment;
  const allowsDot = segment.startsWith(".");
  return (name) => (allowsDot || !name.startsWith(".")) && wildcardMatch(segment, name);
}

type Segment = "**" | ((name: string) => boolean);

function compile(segments: readonly string[]): Segment[] {
  return segments.map((s) => (s === "**" ? "**" : segmentMatcher(s)));
}

function matchFrom(
  pattern: readonly Segment[],
  i: number,
  path: readonly string[],
  j: number
): boolean {
  const head = pattern[i];
  if (head === undefined) return j === path.length;
  if (head === "**") return matchGlobstar(pattern, i, path, j);
  const name = path[j];
  return name !== undefined && head(name) && matchFrom(pattern, i + 1, path, j + 1);
}

/** `**` at pattern[i]: zero or more segments, none starting with a dot; at least one when trailing (minimatch). */
function matchGlobstar(
  pattern: readonly Segment[],
  i: number,
  path: readonly string[],
  j: number
): boolean {
  const trailing = i + 1 === pattern.length;
  for (let k = j; ; k++) {
    if ((!trailing || k > j) && matchFrom(pattern, i + 1, path, k)) return true;
    const name = path[k];
    if (name === undefined || name.startsWith(".")) return false;
  }
}

/**
 * A predicate over absolute, `/`-separated file paths that answers as
 * ts-morph's `getSourceFiles(glob)` did with `cwd` as the current directory.
 */
export function createSourceGlob(glob: string, cwd: string): (filePath: string) => boolean {
  if (UNSUPPORTED.test(glob)) {
    throw new Error(`sourceFilesMatching: unsupported glob syntax in ${JSON.stringify(glob)}`);
  }
  const relative = glob.startsWith("./") ? glob.slice(2) : glob === "." ? "" : glob;
  const base = cwd.endsWith("/") ? cwd.slice(0, -1) : cwd;
  // cwd is a literal prefix; only the caller's glob carries wildcards.
  const pattern = relative.startsWith("/")
    ? compile(relative.split("/"))
    : [
        ...base.split("/").map(
          (name): Segment =>
            (candidate) =>
              candidate === name
        ),
        ...(relative ? compile(relative.split("/")) : []),
      ];
  return (filePath) => matchFrom(pattern, 0, filePath.split("/"), 0);
}
