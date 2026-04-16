import { describe, expect, test } from "bun:test";
import {
  assertOpVersion,
  checkOpVersion,
  getDocVersion,
  type Migrations,
  runMigrations,
  SCHEMA_VERSION_FIELD,
  SchemaVersionError,
  setDocVersion,
} from "@/shared/lib/schema-version";

describe("getDocVersion", () => {
  test("returns 0 for an empty object", () => {
    expect(getDocVersion({})).toBe(0);
  });

  test("returns 0 for null", () => {
    expect(getDocVersion(null)).toBe(0);
  });

  test("returns 0 for undefined", () => {
    expect(getDocVersion(undefined)).toBe(0);
  });

  test("returns 0 for primitive values", () => {
    expect(getDocVersion("string")).toBe(0);
    expect(getDocVersion(42)).toBe(0);
    expect(getDocVersion(true)).toBe(0);
  });

  test("returns the stamped version for a versioned doc", () => {
    expect(getDocVersion({ [SCHEMA_VERSION_FIELD]: 3 })).toBe(3);
  });

  test("returns 0 for a non-integer version field", () => {
    expect(getDocVersion({ [SCHEMA_VERSION_FIELD]: 1.5 })).toBe(0);
    expect(getDocVersion({ [SCHEMA_VERSION_FIELD]: "1" })).toBe(0);
  });

  test("returns 0 for a negative version field", () => {
    expect(getDocVersion({ [SCHEMA_VERSION_FIELD]: -1 })).toBe(0);
  });
});

describe("setDocVersion", () => {
  test("stamps the version onto an object", () => {
    const doc: Record<string, unknown> = {};
    setDocVersion(doc, 5);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(5);
  });

  test("overwrites a previous version", () => {
    const doc: Record<string, unknown> = { [SCHEMA_VERSION_FIELD]: 2 };
    setDocVersion(doc, 3);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(3);
  });

  test("leaves other fields alone", () => {
    const doc: Record<string, unknown> = { title: "hello" };
    setDocVersion(doc, 1);
    expect(doc["title"]).toBe("hello");
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(1);
  });
});

describe("runMigrations", () => {
  test("no-ops when doc is already at target version", () => {
    const doc: Record<string, unknown> = { [SCHEMA_VERSION_FIELD]: 2, field: "x" };
    const migrations: Migrations = {
      1: () => {
        throw new Error("should not run");
      },
      2: () => {
        throw new Error("should not run");
      },
    };
    runMigrations(doc, 2, migrations);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(2);
    expect(doc["field"]).toBe("x");
  });

  test("runs the single missing migration and stamps the version", () => {
    const doc: Record<string, unknown> = {};
    const migrations: Migrations = {
      1: (d) => {
        d["title"] = "";
      },
    };
    runMigrations(doc, 1, migrations);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(1);
    expect(doc["title"]).toBe("");
  });

  test("runs multiple migrations in order", () => {
    const doc: Record<string, unknown> = {};
    const migrations: Migrations = {
      1: (d) => {
        d["title"] = "";
      },
      2: (d) => {
        d["tags"] = [];
      },
      3: (d) => {
        d["archived"] = false;
      },
    };
    runMigrations(doc, 3, migrations);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(3);
    expect(doc["title"]).toBe("");
    expect(doc["tags"]).toEqual([]);
    expect(doc["archived"]).toBe(false);
  });

  test("resumes from the doc's current version", () => {
    const doc: Record<string, unknown> = { [SCHEMA_VERSION_FIELD]: 2, title: "existing" };
    let v1Ran = false;
    let v2Ran = false;
    let v3Ran = false;
    const migrations: Migrations = {
      1: () => {
        v1Ran = true;
      },
      2: () => {
        v2Ran = true;
      },
      3: (d) => {
        v3Ran = true;
        d["archived"] = false;
      },
    };
    runMigrations(doc, 3, migrations);
    expect(v1Ran).toBe(false);
    expect(v2Ran).toBe(false);
    expect(v3Ran).toBe(true);
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(3);
    expect(doc["title"]).toBe("existing");
  });

  test("stamps each intermediate version during the walk", () => {
    const doc: Record<string, unknown> = {};
    const observed: number[] = [];
    const migrations: Migrations = {
      1: (d) => {
        observed.push(getDocVersion(d));
      },
      2: (d) => {
        observed.push(getDocVersion(d));
      },
      3: (d) => {
        observed.push(getDocVersion(d));
      },
    };
    runMigrations(doc, 3, migrations);
    // Each migration sees the document stamped at its *previous* version.
    // Migration 1 sees version 0 (empty doc), then the runner stamps 1.
    // Migration 2 sees version 1, then the runner stamps 2.
    // Migration 3 sees version 2, then the runner stamps 3.
    expect(observed).toEqual([0, 1, 2]);
  });

  test("throws when the doc is ahead of the application target", () => {
    const doc: Record<string, unknown> = { [SCHEMA_VERSION_FIELD]: 5 };
    expect(() => runMigrations(doc, 3, {})).toThrow(SchemaVersionError);
    try {
      runMigrations(doc, 3, {});
    } catch (err) {
      const error = err as unknown as SchemaVersionError;
      expect(error.code).toBe("doc-ahead-of-app");
      expect(error.docVersion).toBe(5);
      expect(error.targetVersion).toBe(3);
    }
  });

  test("throws when an intermediate migration is missing", () => {
    const doc: Record<string, unknown> = {};
    let v1Called = false;
    let v3Called = false;
    const migrations: Migrations = {
      1: () => {
        v1Called = true;
      },
      // 2 missing
      3: () => {
        v3Called = true;
      },
    };
    expect(() => runMigrations(doc, 3, migrations)).toThrow(SchemaVersionError);
    // v1 runs before the missing-migration check reaches v2.
    expect(v1Called).toBe(true);
    expect(v3Called).toBe(false);
    try {
      runMigrations({}, 3, migrations);
    } catch (err) {
      const error = err as unknown as SchemaVersionError;
      expect(error.code).toBe("missing-migration");
      expect(error.missingVersion).toBe(2);
    }
  });

  test("throws when the first migration (v1) is missing", () => {
    const doc: Record<string, unknown> = {};
    let v2Called = false;
    const migrations: Migrations = {
      // 1 missing
      2: () => {
        v2Called = true;
      },
    };
    expect(() => runMigrations(doc, 2, migrations)).toThrow(SchemaVersionError);
    expect(v2Called).toBe(false);
    try {
      runMigrations({}, 2, migrations);
    } catch (err) {
      const error = err as unknown as SchemaVersionError;
      expect(error.missingVersion).toBe(1);
    }
  });

  test("is idempotent when run twice on the same doc", () => {
    const doc: Record<string, unknown> = {};
    const migrations: Migrations = {
      1: (d) => {
        d["title"] = "hello";
      },
    };
    runMigrations(doc, 1, migrations);
    const after = { ...doc };
    runMigrations(doc, 1, migrations);
    expect(doc).toEqual(after);
  });
});

describe("checkOpVersion", () => {
  test("returns compatible when versions match", () => {
    expect(checkOpVersion(3, 3)).toEqual({ compatible: true });
  });

  test("rejects ops older than the doc", () => {
    const result = checkOpVersion(2, 3);
    expect(result.compatible).toBe(false);
    if (!result.compatible) {
      expect(result.reason).toBe("op-older-than-doc");
      expect(result.opVersion).toBe(2);
      expect(result.docVersion).toBe(3);
    }
  });

  test("rejects ops newer than the doc", () => {
    const result = checkOpVersion(4, 3);
    expect(result.compatible).toBe(false);
    if (!result.compatible) {
      expect(result.reason).toBe("op-newer-than-doc");
      expect(result.opVersion).toBe(4);
      expect(result.docVersion).toBe(3);
    }
  });

  test("rejects v0 op against v1 doc", () => {
    const result = checkOpVersion(0, 1);
    expect(result.compatible).toBe(false);
  });
});

describe("assertOpVersion", () => {
  test("returns silently when versions match", () => {
    expect(() => assertOpVersion(3, 3)).not.toThrow();
  });

  test("throws a SchemaVersionError when the op is older", () => {
    expect(() => assertOpVersion(2, 3)).toThrow(SchemaVersionError);
    try {
      assertOpVersion(2, 3);
    } catch (err) {
      const error = err as unknown as SchemaVersionError;
      expect(error.code).toBe("op-older-than-doc");
      expect(error.opVersion).toBe(2);
      expect(error.docVersion).toBe(3);
    }
  });

  test("throws a SchemaVersionError when the op is newer", () => {
    expect(() => assertOpVersion(4, 3)).toThrow(SchemaVersionError);
    try {
      assertOpVersion(4, 3);
    } catch (err) {
      const error = err as unknown as SchemaVersionError;
      expect(error.code).toBe("op-newer-than-doc");
    }
  });
});
