// polly#169 / polly#170 — two ways an object-literal signal update reached TLC
// as a lie about the code.
//
// #169: the `EXPR:` capture takes source text out of the function that gave its
// identifiers meaning. A handler reading through `const state = sig.value`
// emitted `state.field`, which the codegen's `state.` rule rewrote to
// `contextStates[ctx].field` — a member that does not exist, because the record
// carries `sig_field`. An alias under any other name survived into the spec as
// a free identifier.
//
// #170: a ternary initializer was excluded by `isTranslatableInitializer`, so
// the assignment vanished and the field was modelled as never moving. Every
// property written over it then held vacuously.

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor — aliases and ternaries in object literals", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-169-170-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function createTsConfig(): string {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["*.ts"],
      })
    );
    fs.writeFileSync(
      path.join(tempDir, "package.json"),
      JSON.stringify({ name: "test-pkg", version: "0.0.1" })
    );
    return tsConfigPath;
  }

  function extract(body: string) {
    fs.writeFileSync(
      path.join(tempDir, "handlers.ts"),
      `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: {
  on: <T>(type: string, fn: (payload: T) => void) => void;
};

const offlineQueue = $sharedState("offlineQueue", {
  unsyncedChanges: 0,
  syncState: "synced",
});
const other = $sharedState("other", { count: 0 });

${body}
`
    );
    return new HandlerExtractor(createTsConfig()).extractHandlers();
  }

  function assignmentsFor(body: string, messageType: string) {
    const result = extract(body);
    const handler = result.handlers.find((h) => h.messageType === messageType);
    expect(handler).toBeDefined();
    return handler!.assignments;
  }

  describe("alias resolution (polly#169)", () => {
    test("an alias named `state` resolves to the signal, not to the framework `state.` form", () => {
      // The dangerous shape: `state.unsyncedChanges` matches the codegen's
      // Phase-2c rule and silently becomes `contextStates[ctx].unsyncedChanges`
      // — a field that does not exist. The record member is
      // `offlineQueue_unsyncedChanges`.
      const assignments = assignmentsFor(
        `
bus.on("QUEUE_OP", () => {
  const state = offlineQueue.value;
  offlineQueue.value = {
    ...state,
    unsyncedChanges: state.unsyncedChanges + 1,
  };
});
`,
        "QUEUE_OP"
      );

      expect(assignments).toEqual(
        expect.arrayContaining([
          {
            field: "offlineQueue_unsyncedChanges",
            value: "EXPR:offlineQueue.value.unsyncedChanges + 1",
          },
        ])
      );
    });

    test("an alias under any other name resolves too", () => {
      const assignments = assignmentsFor(
        `
bus.on("QUEUE_OP2", () => {
  const q = offlineQueue.value;
  offlineQueue.value = { ...q, unsyncedChanges: q.unsyncedChanges + 1 };
});
`,
        "QUEUE_OP2"
      );

      expect(assignments).toEqual(
        expect.arrayContaining([
          {
            field: "offlineQueue_unsyncedChanges",
            value: "EXPR:offlineQueue.value.unsyncedChanges + 1",
          },
        ])
      );
    });

    test("an alias of a different signal resolves to that signal", () => {
      const assignments = assignmentsFor(
        `
bus.on("COPY", () => {
  const o = other.value;
  offlineQueue.value = { unsyncedChanges: o.count };
});
`,
        "COPY"
      );

      expect(assignments).toEqual(
        expect.arrayContaining([
          { field: "offlineQueue_unsyncedChanges", value: "EXPR:other.value.count" },
        ])
      );
    });

    test("only the enclosing function's aliases apply", () => {
      // A sibling handler's `const state = other.value` must not leak into this
      // one. Keying on extractor instance state instead of the enclosing
      // function would resolve to `other` here.
      const assignments = assignmentsFor(
        `
bus.on("SIBLING", () => {
  const state = other.value;
  other.value = { count: state.count + 1 };
});
bus.on("TARGET", () => {
  const state = offlineQueue.value;
  offlineQueue.value = { ...state, unsyncedChanges: state.unsyncedChanges + 1 };
});
`,
        "TARGET"
      );

      expect(assignments).toEqual(
        expect.arrayContaining([
          {
            field: "offlineQueue_unsyncedChanges",
            value: "EXPR:offlineQueue.value.unsyncedChanges + 1",
          },
        ])
      );
    });

    test("a destructured binding is not treated as an alias", () => {
      // Narrow by design: a wrong entry rewrites an expression into a field
      // that DOES exist, which is worse than one that fails loudly.
      const assignments = assignmentsFor(
        `
bus.on("DESTRUCTURED", () => {
  const { unsyncedChanges } = offlineQueue.value;
  offlineQueue.value = { unsyncedChanges: unsyncedChanges + 1 };
});
`,
        "DESTRUCTURED"
      );

      const captured = assignments.find((a) => a.field === "offlineQueue_unsyncedChanges");
      expect(captured?.value).not.toBe("EXPR:offlineQueue.value.unsyncedChanges + 1");
    });

    test("a reassigned `let` is not treated as an alias", () => {
      const assignments = assignmentsFor(
        `
bus.on("REASSIGNED", () => {
  let state = offlineQueue.value;
  state = other.value as never;
  offlineQueue.value = { unsyncedChanges: state.unsyncedChanges + 1 };
});
`,
        "REASSIGNED"
      );

      const captured = assignments.find((a) => a.field === "offlineQueue_unsyncedChanges");
      expect(captured?.value).not.toBe("EXPR:offlineQueue.value.unsyncedChanges + 1");
    });
  });

  describe("ternary initializers (polly#170)", () => {
    test("a single ternary is captured rather than dropped", () => {
      const assignments = assignmentsFor(
        `
bus.on("MARK_PENDING", () => {
  offlineQueue.value = {
    syncState: offlineQueue.value.syncState === "synced" ? "pending" : offlineQueue.value.syncState,
  };
});
`,
        "MARK_PENDING"
      );

      const captured = assignments.find((a) => a.field === "offlineQueue_syncState");
      expect(captured).toBeDefined();
      expect(captured!.value).toStartWith("EXPR:");
      expect(captured!.value).toContain("?");
    });

    test("a ternary through an alias is both resolved and captured", () => {
      const assignments = assignmentsFor(
        `
bus.on("MARK_PENDING_ALIAS", () => {
  const state = offlineQueue.value;
  offlineQueue.value = {
    ...state,
    syncState: state.syncState === "synced" ? "pending" : state.syncState,
  };
});
`,
        "MARK_PENDING_ALIAS"
      );

      const captured = assignments.find((a) => a.field === "offlineQueue_syncState");
      expect(captured).toBeDefined();
      expect(captured!.value).not.toContain("state.syncState");
      expect(captured!.value).toContain("offlineQueue.value.syncState");
    });

    test("a nested ternary is rejected, not mistranslated", () => {
      // translateTernary is a regex; nesting produces stacked IF IF IF.
      const assignments = assignmentsFor(
        `
bus.on("NESTED", () => {
  offlineQueue.value = {
    unsyncedChanges: other.value.count > 2 ? (other.value.count > 5 ? 3 : 2) : 1,
  };
});
`,
        "NESTED"
      );

      expect(assignments.find((a) => a.field === "offlineQueue_unsyncedChanges")).toBeUndefined();
    });

    test("a parenthesised ternary is unwrapped so the codegen regex cannot mangle it", () => {
      // Today `isTranslatableInitializer` admits ParenthesizedExpression, so
      // this reached translateTernary and produced `IF (a THEN "y" ELSE "n")`
      // — unbalanced parens that SANY rejects. Unwrapping keeps the capability
      // and removes the shape the regex gets wrong.
      const assignments = assignmentsFor(
        `
bus.on("PARENS", () => {
  offlineQueue.value = {
    unsyncedChanges: (other.value.count > 2 ? 3 : 1),
  };
});
`,
        "PARENS"
      );

      const captured = assignments.find((a) => a.field === "offlineQueue_unsyncedChanges");
      expect(captured?.value).toStartWith("EXPR:");
      expect(captured!.value).not.toContain("(");
    });

    test("a ternary nested inside arithmetic is rejected", () => {
      const assignments = assignmentsFor(
        `
bus.on("MIXED", () => {
  offlineQueue.value = {
    unsyncedChanges: other.value.count + (other.value.count > 2 ? 1 : 0),
  };
});
`,
        "MIXED"
      );

      expect(assignments.find((a) => a.field === "offlineQueue_unsyncedChanges")).toBeUndefined();
    });

    test("a call expression anywhere in the subtree is rejected", () => {
      const assignments = assignmentsFor(
        `
bus.on("CALL", () => {
  offlineQueue.value = { unsyncedChanges: other.value.count + Date.now() };
});
`,
        "CALL"
      );

      expect(assignments.find((a) => a.field === "offlineQueue_unsyncedChanges")).toBeUndefined();
    });

    test("a commented ternary is rejected", () => {
      // A `//` inside the source text is carried into the generated line.
      const assignments = assignmentsFor(
        `
bus.on("COMMENTED", () => {
  offlineQueue.value = {
    unsyncedChanges: other.value.count > 2 // why
      ? 3
      : 1,
  };
});
`,
        "COMMENTED"
      );

      expect(assignments.find((a) => a.field === "offlineQueue_unsyncedChanges")).toBeUndefined();
    });
  });
});
