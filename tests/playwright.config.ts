import { defineConfig, devices } from "@playwright/test";

// biome-ignore lint/style/noDefaultExport: Playwright requires default export
export default defineConfig({
  testDir: ".",
  fullyParallel: true,
  forbidOnly: !!process.env["CI"],
  retries: process.env["CI"] ? 2 : 0,
  ...(process.env["CI"] && { workers: 1 }),
  reporter: "html",
  use: {
    trace: "on-first-retry",
  },
  projects: [
    {
      name: "chromium",
      use: { ...devices["Desktop Chrome"] },
    },
  ],
});
