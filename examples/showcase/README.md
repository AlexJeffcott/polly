# Polly UI Showcase

Visual gallery of every `@fairfox/polly` UI primitive in its prop variants.
Doubles as the UI testing playground: every component change should be
visible here, and the test suite catches regressions before they reach
real consumers.

## Dev

```sh
bun install
bun run dev
```

Opens a Bun-served HTML page at the printed URL with hot reload. No build
step. Edit anything under `src/` or `packages/polly/src/polly-ui/` and the
page reloads.

## Tests

The showcase carries two layers of test coverage:

- **Browser unit tests** under `tests/browser/*.browser.tsx` — render
  individual components into a sandbox div and assert behaviour
  (signal-bound state, class application, ARIA attributes, etc.). Runs
  in real Puppeteer via the `@fairfox/polly/test/browser` harness.
- **Visual regression** under `tests/visual/run.ts` — screenshots each
  `[data-section]` in `src/index.tsx` and diffs against a committed PNG
  baseline using `@fairfox/polly/test/visual`. Catches "theme change
  broke layout in component X" automatically.

```sh
bun run test:browser           # browser unit tests
bun run test:visual            # visual regression compare
bun run test:visual:update     # regenerate baselines (local only, refused in CI)
bun run test                   # browser + visual
bun run test:all               # lint + typecheck + test
```

Baselines live under `tests/visual/__baselines__/` and are committed.
Diffs land in `tests/visual/__diffs__/` (gitignored) when a comparison
fails — open the `.diff.png` to see what changed pixel by pixel.

## Adding a component

1. Add a new `<Section id="…" title="…">` to `src/index.tsx`. Exercise
   the prop axes that matter visually (tier/size/state/disabled, plus
   a long-label/short-label pair where width handling is non-trivial).
2. Append the section id to the `SECTIONS` list in `tests/visual/run.ts`.
3. Run `bun run test:visual:update` once to capture the baseline, then
   commit the PNG.
4. Optionally add a `tests/browser/<component>.browser.tsx` for any
   interaction or state-binding contract that's not visible from a
   static screenshot.
