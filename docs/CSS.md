# CSS conformance

`polly quality` ships four CSS checks that enforce the styling contract
behind `@fairfox/polly/ui`. Apps opt in by pointing the tool at their
own CSS modules; Polly eats its own dog food.

```
polly quality                # all checks (TS + CSS)
polly quality css            # just the CSS family
polly quality css-quality    # hardcoded values
polly quality css-layout     # <Layout> enforcement
polly quality css-vars       # undefined variable references
polly quality css-unused     # dead selectors (advisory)
```

## css-quality

Rejects values that have a semantic token equivalent. Hardcoded hex
colours, rgba literals, rem units, numeric font-weights, magic z-indexes,
hardcoded border-radius / border-width / box-shadow, inline transitions,
and `!important` all fail.

Every rejected line carries a suggestion pointing at the right token
family. Rules are individually disableable:

```ts
import { checkCssQuality } from '@fairfox/polly/quality';

await checkCssQuality({
  rootDir: process.cwd(),
  disableRules: ['no-rem-units'],
});
```

A file can opt out entirely with a `polly-ignore-all` marker in a CSS
comment on its first line — for imported third-party CSS or other
exceptional cases.

## css-layout

Forbids `display: flex` and `display: grid` outside the `<Layout>`
primitive. Apps that use this rule get two things: greppable layout
decisions, and the guarantee that all layout in the app flows through
one generalised component.

Escape hatches for legitimate exceptions (Modal's own positioning,
for example, uses `display: grid` to center its backdrop):

```css
.special {
  display: grid; /* layout-ignore */
  grid-template-columns: 1fr 1fr;
}
```

The suppression comment may be on the violating line or the preceding
one. Consumer configuration can extend the exempt paths:

```ts
await checkCssLayout({
  rootDir: process.cwd(),
  layoutExemptPaths: ['Layout.module.css', 'MyStack.module.css'],
});
```

## css-vars

Every `var(--name)` reference in `.css`, `.ts`, or `.tsx` files must
resolve to a definition in some `.css` file under the scan root.
Catches typos and references to removed tokens.

Variables that are set at runtime via inline styles can be listed so
the check treats them as defined:

```ts
await checkCssVars({
  rootDir: process.cwd(),
  dynamicVars: ['--l-cols', '--l-rows', '--max-lines'],
});
```

## css-unused

Advisory. Finds classes and locally-defined custom properties in
`.module.css` files that appear to have no reference. The check is
textual and cannot see through dynamic lookups (`styles[key]` with a
computed key), so treat the output as a hint rather than a hard
failure.

## Configuration

Each check takes a common shape:

```ts
{
  rootDir: string;       // scan target
  skipDirs?: string[];   // directory names to skip during recursion
  // plus check-specific options
}
```

Defaults skip `node_modules`, `dist`, `.git`, `.bun`, `dist-test`,
`build`, and `coverage`.

## Programmatic use

Each check is available as a library function for custom pipelines:

```ts
import { checkCssQuality, checkCssLayout } from '@fairfox/polly/quality';

const results = await Promise.all([
  checkCssQuality({ rootDir }),
  checkCssLayout({ rootDir }),
]);
for (const r of results) r.print();
if (results.some((r) => r.violations.length > 0)) process.exit(1);
```

The output sink goes through the quality tool's `logger` singleton,
which tests replace at runtime by assigning to `logger.log`,
`logger.error`, etc. — call `resetLogger()` to restore the defaults
after a test. See `tests/unit/quality/logger.test.ts` for the pattern.
