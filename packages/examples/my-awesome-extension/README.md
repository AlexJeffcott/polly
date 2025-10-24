# my-awesome-extension

A Chrome extension built with [@fairfox/web-ext](https://github.com/fairfox/web-ext).

## Getting Started

1. Install dependencies:
   ```bash
   bun install
   ```

2. Build the extension:
   ```bash
   bun run build
   ```

3. Load the extension in Chrome:
   - Open `chrome://extensions`
   - Enable "Developer mode"
   - Click "Load unpacked"
   - Select the `dist/` folder

## Development

- `bun run build` - Build the extension
- `bun run check` - Run all checks (typecheck, lint, test, build)
- `bun run typecheck` - Type check your code
- `bun run lint` - Lint your code
- `bun run format` - Format your code
- `bun run verify` - Run formal verification
- `bun run visualize` - Generate architecture diagrams

## Project Structure

```
my-awesome-extension/
├── src/
│   ├── background/
│   │   └── index.ts    # Background service worker
│   └── popup/
│       ├── popup.html  # Popup HTML
│       └── index.ts    # Popup script
├── manifest.json       # Extension manifest
├── dist/               # Build output (load this in Chrome)
├── package.json
├── tsconfig.json
└── biome.json
```
