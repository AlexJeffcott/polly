import { describe, expect, test } from "bun:test";
import { CONTAINER_NAME_PREFIX, mintContainerName } from "../../runner/container-name";

describe("mintContainerName (polly#173)", () => {
  test("carries the sweepable prefix", () => {
    expect(mintContainerName("tlc").startsWith(CONTAINER_NAME_PREFIX)).toBe(true);
  });

  test("embeds the workload tag so a hanging stage is identifiable in docker ps", () => {
    expect(mintContainerName("sany")).toContain("sany");
  });

  test("never collides, including within one millisecond", () => {
    // The defect this guards: a Date.now()-only name is millisecond-granular,
    // so two names minted in the same tick collide — and the timeout arm then
    // removes the WRONG container.
    const start = Date.now();
    const names = new Set<string>();
    let minted = 0;
    while (Date.now() === start && minted < 5000) {
      names.add(mintContainerName("tlc"));
      minted += 1;
    }

    expect(minted).toBeGreaterThan(1);
    expect(names.size).toBe(minted);
  });

  test("produces a docker-legal name", () => {
    // Docker requires [a-zA-Z0-9][a-zA-Z0-9_.-]*
    for (const kind of ["tlc", "sany", "weird kind/with:chars", ""]) {
      expect(mintContainerName(kind)).toMatch(/^[a-zA-Z0-9][a-zA-Z0-9_.-]*$/);
    }
  });
});
