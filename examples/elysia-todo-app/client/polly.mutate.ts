import { defineMutation } from "@fairfox/polly/mutate";

export default defineMutation({
  targets: ["src/**/*.{ts,tsx}", "!src/__tests__/**", "!src/**/*.d.ts"],
  tests: {
    include: ["src/__tests__/**/*.test.tsx"],
  },
});
