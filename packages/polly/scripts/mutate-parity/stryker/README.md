# Stryker reference install

Polly's mutation engine replaced Stryker. This directory keeps one pinned Stryker
so `scripts/mutate-parity.ts` can still compare the two on the current tree:

```sh
bun packages/polly/scripts/mutate-parity.ts                       # four default targets
bun packages/polly/scripts/mutate-parity.ts --files a.ts,b.tsx    # any targets
```

The script copies this directory into a cache (`~/.cache/polly/stryker-reference/<hash>`),
runs `bun install --frozen-lockfile` there, and runs that Stryker from the monorepo root.
Nothing here is a workspace member, a dependency of `@fairfox/polly`, or shipped.

| File | Why |
|---|---|
| `package.json` | Stryker 9.6.1 and the bun runner 0.4.0, exact. 10.0.0 crashes in the instrumenter with Babel 7. `typescript` 6.0.3 because Stryker's tsconfig preprocessor imports it from its own install, not the project. |
| `bun.lock` | Makes the install reproducible. |
| `patches/` | The bun runner patch: no-bail kill matrix, junit per-test results. |
