/**
 * Stryker's own mutator expectation tables, run against this engine.
 *
 * Source: stryker-js v9.6.1, packages/instrumenter/test/unit/mutators/*.spec.ts
 * (Apache-2.0). Each row is one `expectJSMutation(sut, input, ...outputs)`
 * call: the whole-program texts the named mutator must produce for `input`,
 * and nothing else. Stryker regenerates the mutated node with Babel; this
 * engine swaps a source span, so where only formatting differs the row
 * carries this engine's text and a note. Every difference in substance is
 * listed in tools/mutate/README.md.
 *
 * Mutants the mutated text cannot parse (`compileErrors`) count as produced,
 * because Stryker's tables list them too.
 */
import { describe, expect, test } from "bun:test";
import { applyMutant, generateMutants } from "../engine/generate.ts";
import type { MutatorName } from "../engine/types.ts";

/** Every program text `mutator` produces for `input`, as a tsx module, else ts. */
function produced(mutator: MutatorName, input: string): string[] {
  let error: unknown;
  for (const file of ["t.tsx", "t.ts"]) {
    try {
      const { mutants, compileErrors } = generateMutants(file, input, {
        ignoreVerifyCallsites: false,
      });
      return [...mutants, ...compileErrors]
        .filter((m) => m.mutatorName === mutator)
        .map((m) => applyMutant(input, m))
        .sort();
    } catch (e) {
      error = e;
    }
  }
  throw error;
}

type Row = [input: string, ...outputs: string[]];

function table(mutator: MutatorName, rows: Record<string, Row[]>): void {
  describe(mutator, () => {
    for (const [title, cases] of Object.entries(rows)) {
      test(title, () => {
        for (const [input, ...outputs] of cases) {
          expect(produced(mutator, input)).toEqual([...outputs].sort());
        }
      });
    }
  });
}

table("OptionalChaining", {
  "should mutate an optional member expression": [["foo?.bar", "foo.bar"]],
  "should mutate an optional call expression": [["foo?.()", "foo()"]],
  "should mutate an optional member expression with computed syntax": [["foo?.[0]", "foo[0]"]],
  "should not mutate an optional member expression inside an optional call expression": [
    ["qux()?.map()", "qux().map()"],
  ],
  "should mutate an optional chain": [
    ["foo?.bar?.()?.[0]", "foo.bar?.()?.[0]", "foo?.bar()?.[0]", "foo?.bar?.()[0]"],
  ],
  "should not mutate the non-optional parts of a chain": [
    ["foo.bar()?.[0]", "foo.bar()[0]"],
    ["foo.bar?.()[0]", "foo.bar()[0]"],
    ["foo.bar()?.baz", "foo.bar().baz"],
  ],
});

table("BlockStatement", {
  "blocks / should mutate a single block": [["const a = 3; { const b = a; }", "const a = 3; {}"]],
  "blocks / should not mutate an object declaration, as not a block": [
    ['const o = { foo: "bar" }'],
  ],
  "functions / should mutate the block of a function into an empty block": [
    ["(function() { return 4; })", "(function() {})"],
  ],
  "functions / should not mutate an already empty block": [["(function() {  })"]],
  "functions / should mutate the body of an anonymous function if defined as a block": [
    ["const b = () => { return 4; }", "const b = () => {}"],
  ],
  "functions / should not mutate the body of an anonymous function if not defined as a block": [
    ["const b = () => 4;"],
  ],
  "switch/case / should not mutate the body of a switch or case statement, as not a block": [
    ['switch (v) { case 42: a = "spam"; break; }'],
  ],
  "switch/case / should mutate the body of a case statement if defined as a block": [
    ['switch (v) { case 42: { a = "spam"; break; } }', "switch (v) { case 42: {} }"],
  ],
  "classes / should mutate a constructor": [
    ["class Foo { constructor() { bar(); } }", "class Foo { constructor() {} }"],
  ],
  "classes / should mutate a constructor with (typescript) parameter properties without a `super()` call":
    [
      [
        "class Foo { constructor(private baz: string) { bar(); } }",
        "class Foo { constructor(private baz: string) {} }",
      ],
    ],
  "classes / should mutate a constructor with a super call": [
    [
      "class Foo extends Bar { constructor(baz) { super(baz); } }",
      "class Foo extends Bar { constructor(baz) {} }",
    ],
  ],
  "classes / should not mutate a constructor containing a super call and has (typescript) parameter properties":
    [
      ["class Foo extends Bar { constructor(private baz: string) { super(); } }"],
      [
        `class Foo extends Bar { constructor(private baz: string) { const errorBody: Body = { message: \`msg: \${baz}\` }; super(errorBody);  } }`,
      ],
    ],
  "classes / should not mutate a constructor containing a super call and contains initialized properties":
    [
      ['class Foo extends Bar { private baz = "qux"; constructor() { super(); } }'],
      [
        `class Foo extends Bar { private baz = "qux"; constructor() { const errorBody: Body = { message: \`msg: \${baz}\` }; super(errorBody);  } }`,
      ],
    ],
});

table("ConditionalExpression", {
  "should mutate ternary operator": [["a < 3? b : c", "false? b : c", "true? b : c"]],
  "should mutate < and >": [
    ["a < b", "true", "false"],
    ["a > b", "true", "false"],
  ],
  "should mutate <= and >=": [
    ["a <= b", "true", "false"],
    ["a >= b", "true", "false"],
  ],
  "should mutate == and ===": [
    ["a == b", "true", "false"],
    ["a === b", "true", "false"],
  ],
  "should mutate != and !==": [
    ["a != b", "true", "false"],
    ["a !== b", "true", "false"],
  ],
  "should mutate && and ||": [
    ["a && b", "true", "false"],
    ["a || b", "true", "false"],
  ],
  "should not mutate + and -": [["a + b"], ["a - b"]],
  "should not mutate *, % and /": [["a * b"], ["a / b"], ["a % b"]],
  "should not mutate assignments": [['let displayName; displayName = "Label";']],
  "should mutate the expression of a do statement": [
    ["do { console.log(); } while(a < b);", "do { console.log(); } while(false);"],
  ],
  "should mutate the condition of a for statement": [
    ["for(let i=0;i<10; i++) { console.log(); }", "for(let i=0;false; i++) { console.log(); }"],
  ],
  "should mutate the condition of a for statement without a condition": [
    // Stryker: "for (let i = 0; false; i++) {\n  console.log();\n}" (formatting; see README for the ?? case)
    ["for(let i=0;; i++) { console.log(); }", "for(let i=0;false; i++) { console.log(); }"],
  ],
  "should not mutate (a || b) condition to (a || true)": [
    [
      "if (b === 5 || c === 3) { a++ }",
      "if (true) { a++ }",
      "if (false) { a++ }",
      "if (false || c === 3) { a++ }",
      "if (b === 5 || false) { a++ }",
    ],
  ],
  "should not mutate (a && b) condition to (a && false)": [
    [
      "if (b === 5 && c === 3) { a++ }",
      "if (true) { a++ }",
      "if (false) { a++ }",
      "if (true && c === 3) { a++ }",
      "if (b === 5 && true) { a++ }",
    ],
  ],
  "should mutate ((c1 && c2) || (c3 && c4))": [
    [
      "if ((c1 && c2) || (c3 && c4)) { a++ }",
      "if (true) { a++ }",
      "if (false) { a++ }",
      "if ((false) || (c3 && c4)) { a++ }",
      "if ((c1 && c2) || (false)) { a++ }",
    ],
  ],
  "should mutate ((c1 || c2) && (c3 || c4))": [
    [
      "if ((c1 || c2) && (c3 || c4)) { a++ }",
      "if (true) { a++ }",
      "if (false) { a++ }",
      "if ((true) && (c3 || c4)) { a++ }",
      "if ((c1 || c2) && (true)) { a++ }",
    ],
  ],
  "should mutate an expression to `true` and `false`": [
    ["if (something) { a++ }", "if (true) { a++ }", "if (false) { a++ }"],
  ],
  "should remove all cases one at a time": [
    // Stryker: "switch (v) {case 0: a = \"foo\"; case 1: a = \"qux\"; break; default:}", "switch (v) {case 0: a = \"foo\"; case 1: default: a = \"spam\";}", "switch (v) {case 0: case 1: a = \"qux\"; break; default: a = \"spam\";}" (formatting; see README for the ?? case)
    [
      'switch (v) {case 0: a = "foo"; case 1: a = "qux"; break; default: a = "spam";}',
      'switch (v) {case 0:  case 1: a = "qux"; break; default: a = "spam";}',
      'switch (v) {case 0: a = "foo"; case 1:  default: a = "spam";}',
      'switch (v) {case 0: a = "foo"; case 1: a = "qux"; break; default: }',
    ],
  ],
  "should not mutate empty cases (0 consequent statements)": [
    // Stryker: "switch (v) {case 0: case 1: break; default:}", "switch (v) {case 0: case 1: default: a = \"spam\";}" (formatting; see README for the ?? case)
    [
      'switch (v) {case 0: case 1: break; default: a = "spam";}',
      'switch (v) {case 0: case 1:  default: a = "spam";}',
      "switch (v) {case 0: case 1: break; default: }",
    ],
  ],
  "should mutate the expression of a while statement": [
    ["while(a < b) { console.log(); }", "while(false) { console.log(); }"],
  ],
});

table("LogicalOperator", {
  "should mutate &&": [["a && b", "a || b"]],
  "should mutate ||": [["a || b", "a && b"]],
  "should not mutate & and |": [["a & b"], ["a | b"]],
  "should mutate ?? to &&": [
    // Stryker: "a && b" (formatting; see README for the ?? case)
    ["a ?? b", "(a && b)"],
  ],
});

table("BooleanLiteral", {
  "should mutate `true` into `false`": [["true", "false"]],
  "should mutate `false` into `true`": [["false", "true"]],
  "should mutate !a to a": [["!a", "a"]],
});

table("StringLiteral", {
  "string literals / should mutate a string literal with double quotes": [
    ['const b = "Hello world!";', 'const b = "";'],
  ],
  "string literals / should mutate a string literal with single quotes": [
    ["const b = 'Hello world!';", 'const b = "";'],
  ],
  "string literals / should mutate a template string": [
    ["const b = `Hello world!`;", "const b = ``;"],
  ],
  "string literals / should mutate a template string referencing another variable": [
    [`const a = 10; const b = \`\${a} mutations\`;`, "const a = 10; const b = ``;"],
    [`const a = 10; const b = \`mutations: \${a}\`;`, "const a = 10; const b = ``;"],
    [`const a = 10; const b = \`mutations: \${a} out of 10\`;`, "const a = 10; const b = ``;"],
  ],
  "string literals / should mutate empty strings": [
    ['const b = "";', 'const b = "Stryker was here!";'],
  ],
  "string literals / should mutate empty template strings": [
    ["const b = ``;", "const b = `Stryker was here!`;"],
  ],
  "string literals / should not mutate directive prologues": [
    ['"use strict";"use asm";'],
    ['function a() {"use strict";"use asm";}'],
  ],
  "string literals / should not mutate string literals in symbols with descriptions": [
    ["const a = Symbol('foo');"],
    ['const a = Symbol("foo");'],
  ],
  "string literals / should not mutate symbols without description": [["const a = Symbol();"]],
  "string literals / should mutate template literals in symbols with descriptions": [
    ["const a = Symbol(`foo`);", "const a = Symbol(``);"],
    [
      "const a = Symbol('foo' + 'bar');",
      "const a = Symbol('foo' + \"\");",
      "const a = Symbol(\"\" + 'bar');",
    ],
  ],
  "imports/exports / should not mutate import statements": [
    ['import * as foo from "foo";'],
    ['import { foo } from "foo";'],
    ['import foo from "foo";'],
    ['import "foo";'],
  ],
  "imports/exports / should not mutate require call statements": [['require("./lib/square");']],
  "imports/exports / should not mutate import call expressions": [['import("foo/bar");']],
  "imports/exports / should mutate other call statements": [
    ['require2("./lib/square");', 'require2("");'],
  ],
  "imports/exports / should not mutate export statements": [
    ['export * from "./foo";'],
    ['export { foo as boo } from "./foo";'],
  ],
  "type declarations / should not mutate type declarations": [
    ['const a: "hello" = "hello";', 'const a: "hello" = "";'],
    ['const a: Record<"id", number> = { id: 10 }'],
  ],
  "object properties / should not mutate inside object property keys": [
    ['const { className, "aria-label": label } = props;'],
    ['const foo = { className, ["aria-label"]: label };'],
  ],
  "object properties / should still mutate inside object property values": [
    ['const foo = { bar: "baz" };', 'const foo = { bar: "" };'],
  ],
  "object properties / should not mutate class property keys": [['class Foo { "baz-bar" = 4; }']],
  "object properties / should not mutate method names": [
    ['const watchers = {"category.type"(categoryType) { }}'],
  ],
  "object properties / should mutate class property values": [
    ['class Foo { bar = "4"; }', 'class Foo { bar = ""; }'],
  ],
  "jsx / should not mutate string JSX attributes": [['<Record class="row" />']],
});

table("UnaryOperator", {
  "should mutate -a to +a": [["-a", "+a"]],
  "should mutate +a to -a": [["+a", "-a"]],
  "should mutate ~a to a": [["~a", "a"]],
  "should not mutate a+a": [["a+a"]],
  "should not mutate a-a": [["a-a"]],
});

table("MethodExpression", {
  "functions / should ignore a non-method function": [["function endsWith() {} endsWith();"]],
  "methods / should be removed, non-optional": [["text.trim();", "text;"]],
  "methods / should be removed, optional member": [["text?.trim();", "text;"]],
  "methods / should be removed, optional call": [["text.trim?.();", "text;"]],
  "methods / should be removed, optional member, optional call": [["text?.trim?.();", "text;"]],
  "methods / should be removed, optional member in a non-optional parent": [
    ["parent.text?.trim();", "parent.text;"],
  ],
  "methods / should be removed, optional call in a non-optional parent": [
    ["parent.text.trim?.();", "parent.text;"],
  ],
  "methods / should be removed, optional member, optional call in a non-optional parent": [
    ["parent.text?.trim?.();", "parent.text;"],
  ],
  "methods / should be removed, optional member in an optional parent": [
    ["parent?.text?.trim();", "parent?.text;"],
  ],
  "methods / should be removed, optional call in an optional parent": [
    ["parent?.text.trim?.();", "parent?.text;"],
  ],
  "methods / should be removed, optional member, optional call in an optional parent": [
    ["parent?.text?.trim?.();", "parent?.text;"],
  ],
  "methods / should be replaced, non-optional": [["text.startsWith();", "text.endsWith();"]],
  "methods / should be replaced, optional member": [["text?.startsWith();", "text?.endsWith();"]],
  "methods / should be replaced, optional call": [["text.startsWith?.();", "text.endsWith?.();"]],
  "methods / should be replaced, optional member, optional call": [
    ["text?.startsWith?.();", "text?.endsWith?.();"],
  ],
  "methods / should be replaced in the middle of a chain": [
    ['text.startsWith("foo").valueOf();', 'text.endsWith("foo").valueOf();'],
  ],
  "methods / should be replaced, optional member in a non-optional parent": [
    ["parent.text?.startsWith();", "parent.text?.endsWith();"],
  ],
  "methods / should be replaced, optional call in a non-optional parent": [
    ["parent.text.startsWith?.();", "parent.text.endsWith?.();"],
  ],
  "methods / should be replaced, optional member, optional call in a non-optional parent": [
    ["parent.text?.startsWith?.();", "parent.text?.endsWith?.();"],
  ],
  "methods / should be replaced, optional member in an optional parent": [
    ["parent?.text?.startsWith();", "parent?.text?.endsWith();"],
  ],
  "methods / should be replaced, optional call in an optional parent": [
    ["parent?.text.startsWith?.();", "parent?.text.endsWith?.();"],
  ],
  "methods / should be replaced, optional member, optional call in an optional parent": [
    ["parent?.text?.startsWith?.();", "parent?.text?.endsWith?.();"],
  ],
  "methods / should be removed, non-optional with an argument": [["text.trim(abc);", "text;"]],
  "methods / should be removed, optional member with an argument": [["text?.trim(abc);", "text;"]],
  "methods / should be removed, optional call with an argument": [["text.trim?.(abc);", "text;"]],
  "methods / should be removed, optional member, optional call with an argument": [
    ["text?.trim?.(abc);", "text;"],
  ],
  "methods / should be removed, optional member in a non-optional parent with an argument": [
    ["parent.text?.trim(abc);", "parent.text;"],
  ],
  "methods / should be removed, optional call in a non-optional parent with an argument": [
    ["parent.text.trim?.(abc);", "parent.text;"],
  ],
  "methods / should be removed, optional member, optional call in a non-optional parent with an argument":
    [["parent.text?.trim?.(abc);", "parent.text;"]],
  "methods / should be removed, optional member in an optional parent with an argument": [
    ["parent?.text?.trim(abc);", "parent?.text;"],
  ],
  "methods / should be removed, optional call in an optional parent with an argument": [
    ["parent?.text.trim?.(abc);", "parent?.text;"],
  ],
  "methods / should be removed, optional member, optional call in an optional parent with an argument":
    [["parent?.text?.trim?.(abc);", "parent?.text;"]],
  "methods / should be replaced, non-optional with an argument": [
    ["text.startsWith(abc);", "text.endsWith(abc);"],
  ],
  "methods / should be replaced, optional member with an argument": [
    ["text?.startsWith(abc);", "text?.endsWith(abc);"],
  ],
  "methods / should be replaced, optional call with an argument": [
    ["text.startsWith?.(abc);", "text.endsWith?.(abc);"],
  ],
  "methods / should be replaced, optional member, optional call with an argument": [
    ["text?.startsWith?.(abc);", "text?.endsWith?.(abc);"],
  ],
  "methods / should be replaced, optional member in a non-optional parent with an argument": [
    ["parent.text?.startsWith(abc);", "parent.text?.endsWith(abc);"],
  ],
  "methods / should be replaced, optional call in a non-optional parent with an argument": [
    ["parent.text.startsWith?.(abc);", "parent.text.endsWith?.(abc);"],
  ],
  "methods / should be replaced, optional member, optional call in a non-optional parent with an argument":
    [["parent.text?.startsWith?.(abc);", "parent.text?.endsWith?.(abc);"]],
  "methods / should be replaced, optional member in an optional parent with an argument": [
    ["parent?.text?.startsWith(abc);", "parent?.text?.endsWith(abc);"],
  ],
  "methods / should be replaced, optional call in an optional parent with an argument": [
    ["parent?.text.startsWith?.(abc);", "parent?.text.endsWith?.(abc);"],
  ],
  "methods / should be replaced, optional member, optional call in an optional parent with an argument":
    [["parent?.text?.startsWith?.(abc);", "parent?.text?.endsWith?.(abc);"]],
  "methods / should be removed, non-optional with multiple arguments": [
    ["text.trim(abc, def);", "text;"],
  ],
  "methods / should be removed, optional member with multiple arguments": [
    ["text?.trim(abc, def);", "text;"],
  ],
  "methods / should be removed, optional call with multiple arguments": [
    ["text.trim?.(abc, def);", "text;"],
  ],
  "methods / should be removed, optional member, optional call with multiple arguments": [
    ["text?.trim?.(abc, def);", "text;"],
  ],
  "methods / should be removed in the middle of a chain": [["text.trim().length;", "text.length;"]],
  "methods / should be removed, optional member in a non-optional parent with multiple arguments": [
    ["parent.text?.trim(abc, def);", "parent.text;"],
  ],
  "methods / should be removed, optional call in a non-optional parent with multiple arguments": [
    ["parent.text.trim?.(abc, def);", "parent.text;"],
  ],
  "methods / should be removed, optional member, optional call in a non-optional parent with multiple arguments":
    [["parent.text?.trim?.(abc, def);", "parent.text;"]],
  "methods / should be removed, optional member in an optional parent with multiple arguments": [
    ["parent?.text?.trim(abc, def);", "parent?.text;"],
  ],
  "methods / should be removed, optional call in an optional parent with multiple arguments": [
    ["parent?.text.trim?.(abc, def);", "parent?.text;"],
  ],
  "methods / should be removed, optional member, optional call in an optional parent with multiple arguments":
    [["parent?.text?.trim?.(abc, def);", "parent?.text;"]],
  "methods / should be replaced, non-optional with multiple arguments": [
    ["text.startsWith(abc, def);", "text.endsWith(abc, def);"],
  ],
  "methods / should be replaced, optional member with multiple arguments": [
    ["text?.startsWith(abc, def);", "text?.endsWith(abc, def);"],
  ],
  "methods / should be replaced, optional call with multiple arguments": [
    ["text.startsWith?.(abc, def);", "text.endsWith?.(abc, def);"],
  ],
  "methods / should be replaced, optional member, optional call with multiple arguments": [
    ["text?.startsWith?.(abc, def);", "text?.endsWith?.(abc, def);"],
  ],
  "methods / should be replaced, optional member in a non-optional parent with multiple arguments":
    [["parent.text?.startsWith(abc, def);", "parent.text?.endsWith(abc, def);"]],
  "methods / should be replaced, optional call in a non-optional parent with multiple arguments": [
    ["parent.text.startsWith?.(abc, def);", "parent.text.endsWith?.(abc, def);"],
  ],
  "methods / should be replaced, optional member, optional call in a non-optional parent with multiple arguments":
    [["parent.text?.startsWith?.(abc, def);", "parent.text?.endsWith?.(abc, def);"]],
  "methods / should be replaced, optional member in an optional parent with multiple arguments": [
    ["parent?.text?.startsWith(abc, def);", "parent?.text?.endsWith(abc, def);"],
  ],
  "methods / should be replaced, optional call in an optional parent with multiple arguments": [
    ["parent?.text.startsWith?.(abc, def);", "parent?.text.endsWith?.(abc, def);"],
  ],
  "methods / should be replaced, optional member, optional call in an optional parent with multiple arguments":
    [["parent?.text?.startsWith?.(abc, def);", "parent?.text?.endsWith?.(abc, def);"]],
  "methods / should replace endsWith with startsWith": [["text.endsWith();", "text.startsWith();"]],
  "methods / should replace startsWith with endsWith": [["text.startsWith();", "text.endsWith();"]],
  "methods / should replace every with some": [["text.every();", "text.some();"]],
  "methods / should replace some with every": [["text.some();", "text.every();"]],
  "methods / should replace toLocaleLowerCase with toLocaleUpperCase": [
    ["text.toLocaleLowerCase();", "text.toLocaleUpperCase();"],
  ],
  "methods / should replace toLocaleUpperCase with toLocaleLowerCase": [
    ["text.toLocaleUpperCase();", "text.toLocaleLowerCase();"],
  ],
  "methods / should replace toLowerCase with toUpperCase": [
    ["text.toLowerCase();", "text.toUpperCase();"],
  ],
  "methods / should replace toUpperCase with toLowerCase": [
    ["text.toUpperCase();", "text.toLowerCase();"],
  ],
  "methods / should replace trimEnd with trimStart": [["text.trimEnd();", "text.trimStart();"]],
  "methods / should replace trimStart with trimEnd": [["text.trimStart();", "text.trimEnd();"]],
  "methods / should replace min with max": [["text.min();", "text.max();"]],
  "methods / should replace max with min": [["text.max();", "text.min();"]],
  "methods / should replace setDate with setTime": [["text.setDate();", "text.setTime();"]],
  "methods / should replace setTime with setDate": [["text.setTime();", "text.setDate();"]],
  "methods / should replace setFullYear with setMonth": [
    ["text.setFullYear();", "text.setMonth();"],
  ],
  "methods / should replace setMonth with setFullYear": [
    ["text.setMonth();", "text.setFullYear();"],
  ],
  "methods / should replace setHours with setMinutes": [["text.setHours();", "text.setMinutes();"]],
  "methods / should replace setMinutes with setHours": [["text.setMinutes();", "text.setHours();"]],
  "methods / should replace setSeconds with setMilliseconds": [
    ["text.setSeconds();", "text.setMilliseconds();"],
  ],
  "methods / should replace setMilliseconds with setSeconds": [
    ["text.setMilliseconds();", "text.setSeconds();"],
  ],
  "methods / should replace setUTCDate with setTime": [["text.setUTCDate();", "text.setTime();"]],
  "methods / should replace setUTCFullYear with setUTCMonth": [
    ["text.setUTCFullYear();", "text.setUTCMonth();"],
  ],
  "methods / should replace setUTCMonth with setUTCFullYear": [
    ["text.setUTCMonth();", "text.setUTCFullYear();"],
  ],
  "methods / should replace setUTCHours with setUTCMinutes": [
    ["text.setUTCHours();", "text.setUTCMinutes();"],
  ],
  "methods / should replace setUTCMinutes with setUTCHours": [
    ["text.setUTCMinutes();", "text.setUTCHours();"],
  ],
  "methods / should replace setUTCSeconds with setUTCMilliseconds": [
    ["text.setUTCSeconds();", "text.setUTCMilliseconds();"],
  ],
  "methods / should replace setUTCMilliseconds with setUTCSeconds": [
    ["text.setUTCMilliseconds();", "text.setUTCSeconds();"],
  ],
  "methods / should remove charAt": [["text.charAt();", "text;"]],
  "methods / should remove filter": [["text.filter();", "text;"]],
  "methods / should remove reverse": [["text.reverse();", "text;"]],
  "methods / should remove slice": [["text.slice();", "text;"]],
  "methods / should remove sort": [["text.sort();", "text;"]],
  "methods / should remove substr": [["text.substr();", "text;"]],
  "methods / should remove substring": [["text.substring();", "text;"]],
  "methods / should remove trim": [["text.trim();", "text;"]],
  "methods / should ignore computed properties": [["text['trim']();"]],
  "methods / should ignore new expressions": [["new text.trim();"]],
});

table("UpdateOperator", {
  "should mutate a++ to a--": [["a++", "a--"]],
  "should mutate a-- to a++": [["a--", "a++"]],
  "should mutate ++a to --a": [["++a", "--a"]],
  "should mutate --a to ++a": [["--a", "++a"]],
});

table("ArrayDeclaration", {
  "should mutate filled array literals as empty arrays": [
    ["[a, 1 + 1]", "[]"],
    ["['val']", "[]"],
  ],
  "should mutate empty array literals as a filled array": [["[]", '["Stryker was here"]']],
  "should mutate filled Array constructor calls as empty arrays": [
    ["new Array(a, 1 + 1)", "new Array()"],
    ["new Array('val')", "new Array()"],
    ["Array('val')", "Array()"],
    ["Array(a, 1 + 1)", "Array()"],
  ],
  "should not mutate other new expressions": [["new Object(21, 2)"], ["new Arrays(21, 2)"]],
  "should mutate empty array constructor call as a filled array": [
    ["new Array()", "new Array([])"],
    ["Array()", "Array([])"],
  ],
  "should not mutate other function call expressions": [
    ["window.Array(21, 2)"],
    ['window["Array"](21, 2)'],
  ],
});

table("EqualityOperator", {
  "should mutate < and >": [
    ["a < b", "a >= b", "a <= b"],
    ["a > b", "a <= b", "a >= b"],
  ],
  "should mutate <= and >=": [
    ["a <= b", "a < b", "a > b"],
    ["a >= b", "a < b", "a > b"],
  ],
  "should mutate == and ===": [
    ["a == b", "a != b"],
    ["a === b", "a !== b"],
  ],
  "should mutate != and !==": [
    ["a != b", "a == b"],
    ["a !== b", "a === b"],
  ],
});

table("AssignmentOperator", {
  "should mutate += and -=": [
    ["a += b", "a -= b"],
    ["a -= b", "a += b"],
  ],
  "should mutate *=, %= and /=": [
    ["a *= b", "a /= b"],
    ["a /= b", "a *= b"],
    ["a %= b", "a *= b"],
    ["a *= b", "a /= b"],
    ["a /= b", "a *= b"],
    ["a %= b", "a *= b"],
  ],
  "should mutate <<=, >>=, &= and |=": [
    ["a *= b", "a /= b"],
    ["a /= b", "a *= b"],
    ["a %= b", "a *= b"],
  ],
  "should mutate &&=, ||= and ??=": [
    ["a &&= b", "a ||= b"],
    ["a ||= b", "a &&= b"],
    ["a ??= b", "a &&= b"],
  ],
  "should not mutate a string literal unless it is &&=, ||=, ??=": [
    ['a += "b"'],
    ['a -= "b"'],
    ['a *= "b"'],
    ['a /= "b"'],
    ['a %= "b"'],
    ['a <<= "b"'],
    ['a >>= "b"'],
    ['a &= "b"'],
    ['a |= "b"'],
  ],
  "should mutate a string literal using &&=, ||=, ??=": [
    ['a &&= "b"', 'a ||= "b"'],
    ['a ||= "b"', 'a &&= "b"'],
    ['a ??= "b"', 'a &&= "b"'],
  ],
  "should not mutate string template unless it is &&=, ||=, ??=": [
    ["a += `b`"],
    ["a -= `b`"],
    ["a *= `b`"],
    ["a /= `b`"],
    ["a %= `b`"],
    ["a <<= `b`"],
    ["a >>= `b`"],
    ["a &= `b`"],
    ["a |= `b`"],
  ],
  "should mutate string template using &&=, ||=, ??=": [
    ["a &&= `b`", "a ||= `b`"],
    ["a ||= `b`", "a &&= `b`"],
    ["a ??= `b`", "a &&= `b`"],
  ],
});

table("Regex", {
  "should not mutate normal string literals": [['""']],
  "should mutate a regex literal": [["/\\d{4}/", "/\\d/", "/\\D{4}/"]],
  "should not crash if a regex couldn't be parsed": [['new RegExp("*(a|$]")']],
  "should mutate obvious Regex string literals": [
    ['new RegExp("\\\\d{4}")', 'new RegExp("\\\\d")', 'new RegExp("\\\\D{4}")'],
  ],
  "should not mutate the flags of a new RegExp constructor": [['new RegExp("", "\\\\d{4}")']],
  "should not pass flags if no flags are defined": [["/\\u{20}/", "/\\u/"]],
  "should pass flags in regex literals": [["/\\u{20}/u"]],
  "should pass flags in new RegExp constructors": [['new RegExp("\\\\u{20}", "u")']],
  "should only pass flags in new RegExp constructors if it is a string literal": [
    ['new RegExp("\\\\u{20}", foo)', 'new RegExp("\\\\u", foo)'],
  ],
});

table("ArrowFunction", {
  "should mutate an anonymous function with an inline return": [
    ["const b = () => 4;", "const b = () => undefined;"],
  ],
  "should not mutate an anonymous function with a block as a body": [
    ["const b = () => { return 4; }"],
  ],
  "should not mutate an anonymous function with undefined as a body": [
    ["const b = () => undefined"],
  ],
});

table("ObjectLiteral", {
  "should empty an object declaration": [['const o = { foo: "bar" }', "const o = {}"]],
  "should empty an object declaration of all properties": [
    ['const o = { foo: "bar", baz: "qux" }', "const o = {}"],
  ],
  "should empty string object keys": [['const o = { ["foo"]: "bar" }', "const o = {}"]],
  "shoud not mutate empty object declarations": [["const o = {}"]],
});

table("ArithmeticOperator", {
  "should mutate + and -": [
    ["a + b", "a - b"],
    ["a - b", "a + b"],
  ],
  "should mutate *, % and /": [
    ["a * b", "a / b"],
    ["a / b", "a * b"],
    ["a % b", "a * b"],
  ],
  "should not mutate string literal concatenation": [
    ['"a" + "b"'],
    ['const a = 1; "a" + a'],
    ['3 + "a"'],
    ["`a` + `b`"],
    ["const a = 1; `a` + a"],
    ["3 + `a`"],
    ['"a" + b + "c" + d + "e"'],
  ],
});
