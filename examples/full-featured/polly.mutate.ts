import { defineMutation } from "@fairfox/polly/mutate";

export default defineMutation({
  targets: [
    "src/**/*.ts",
    "!src/**/*.test.ts",
    "!src/**/*.d.ts",
  ],
  tests: {
    include: [
      "tests/**/*.test.ts",
    ],
  },
});
