/**
 * bun:sqlite types a row by whatever type argument the caller names and
 * checks nothing, so `queryAll`/`queryGet` take a row parser instead: a row
 * whose field has the wrong type fails where it is read, naming the query and
 * the field, rather than as `undefined` or `null` printed into the report.
 */
import { Database } from "bun:sqlite";
import { afterAll, describe, expect, test } from "bun:test";
import { buildDb, queryAll, queryGet } from "../ingest.ts";
import { report } from "../report.ts";

const db = new Database(":memory:");
db.run("CREATE TABLE t (name TEXT, n INTEGER, note TEXT)");
db.run("INSERT INTO t VALUES ('a', 1, NULL), ('b', 2, 'x')");
afterAll(() => db.close());

describe("queryAll", () => {
  test("a well-formed row parses into the parser's type", () => {
    const rows = queryAll(db, "SELECT name, n, note FROM t ORDER BY name", (r) => [
      r.string("name"),
      r.number("n"),
      r.stringOrNull("note"),
    ]);
    expect(rows).toEqual([
      ["a", 1, null],
      ["b", 2, "x"],
    ]);
  });

  test("a wrong-typed field throws naming the query and the field", () => {
    expect(() => queryAll(db, "SELECT name, n FROM t", (r) => r.number("name"))).toThrow(
      'query "SELECT name, n FROM t" row 0: field "name" is not a number (got "a")'
    );
  });

  test("a NULL where a string is read throws naming the field", () => {
    expect(() => queryAll(db, "SELECT note FROM t ORDER BY name", (r) => r.string("note"))).toThrow(
      'field "note" is not a string (got null)'
    );
  });
});

describe("queryGet", () => {
  test("a missing field throws naming it", () => {
    expect(() => queryGet(db, "SELECT count(*) n FROM t", (r) => r.number("count"))).toThrow(
      'query "SELECT count(*) n FROM t" row 0: field "count" is not a number (got missing)'
    );
  });

  test("returns the parsed row, and null when there is none", () => {
    expect(queryGet(db, "SELECT count(*) n FROM t", (r) => r.number("n"))).toBe(2);
    expect(queryGet(db, "SELECT n FROM t WHERE n > 9", (r) => r.number("n"))).toBeNull();
  });
});

describe("report over an empty matrix", () => {
  test("prints zero counts, not null", () => {
    const empty = buildDb({ schemaVersion: "1", files: {} });
    const out = report(empty);
    empty.close();
    expect(out).toContain(
      "0 killed · 0 timeout · 0 survived · 0 no-coverage   (0 mutants, 0 tests)"
    );
  });
});
