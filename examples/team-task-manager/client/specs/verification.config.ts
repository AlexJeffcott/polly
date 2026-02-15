// Verification configuration for Team Task Manager
// Richest domain model: { type: "number" }, enums, role constraints, parameter tracing
import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: verification configs use default export by convention
export default defineVerification({
  state: {
    // Verified urgent task count (exercises { type: "number" })
    urgentTaskCount: { type: "number", min: 0, max: 5 },
    // Task list with bounded length
    tasks: { maxLength: 20 },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },

  onBuild: "warn",
  onRelease: "error",
});
