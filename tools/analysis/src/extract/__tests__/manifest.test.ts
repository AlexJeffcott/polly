import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { ManifestParser } from "../manifest";

describe("ManifestParser", () => {
  let tempDir: string;

  beforeAll(() => {
    // Create a temporary directory for test files
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-test-"));
  });

  afterAll(() => {
    // Clean up temporary directory
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  describe("with optional=true", () => {
    test("should not throw when manifest.json is missing", () => {
      expect(() => {
        new ManifestParser(tempDir, true);
      }).not.toThrow();
    });

    test("hasManifest() should return false when manifest is missing", () => {
      const parser = new ManifestParser(tempDir, true);
      expect(parser.hasManifest()).toBe(false);
    });

    test("getContextEntryPoints() should return empty object when manifest is missing", () => {
      const parser = new ManifestParser(tempDir, true);
      const entryPoints = parser.getContextEntryPoints();
      expect(entryPoints).toEqual({});
    });

    test("parse() should throw helpful error when manifest is missing", () => {
      const parser = new ManifestParser(tempDir, true);
      expect(() => {
        parser.parse();
      }).toThrow("Cannot parse manifest: manifest.json not loaded");
    });
  });

  describe("with optional=false (default)", () => {
    test("should throw when manifest.json is missing", () => {
      expect(() => {
        new ManifestParser(tempDir);
      }).toThrow("manifest.json not found");
    });
  });

  describe("with valid manifest.json", () => {
    beforeAll(() => {
      // Create a valid manifest.json
      const manifest = {
        name: "Test Extension",
        version: "1.0.0",
        description: "A test extension",
        manifest_version: 3,
        background: {
          service_worker: "background.js",
        },
        content_scripts: [
          {
            matches: ["<all_urls>"],
            js: ["content.js"],
          },
        ],
        action: {
          default_popup: "popup.html",
        },
        permissions: ["storage", "tabs"],
      };

      fs.writeFileSync(path.join(tempDir, "manifest.json"), JSON.stringify(manifest, null, 2));
    });

    test("hasManifest() should return true when manifest exists", () => {
      const parser = new ManifestParser(tempDir, true);
      expect(parser.hasManifest()).toBe(true);
    });

    test("parse() should return manifest info", () => {
      const parser = new ManifestParser(tempDir);
      const manifest = parser.parse();

      expect(manifest.name).toBe("Test Extension");
      expect(manifest.version).toBe("1.0.0");
      expect(manifest.description).toBe("A test extension");
      expect(manifest.manifestVersion).toBe(3);
      expect(manifest.permissions).toEqual(["storage", "tabs"]);
    });

    test("parse() should extract background configuration", () => {
      const parser = new ManifestParser(tempDir);
      const manifest = parser.parse();

      expect(manifest.background).toBeDefined();
      expect(manifest.background?.type).toBe("service_worker");
      expect(manifest.background?.files).toEqual(["background.js"]);
    });

    test("parse() should extract content scripts", () => {
      const parser = new ManifestParser(tempDir);
      const manifest = parser.parse();

      expect(manifest.contentScripts).toBeDefined();
      expect(manifest.contentScripts?.length).toBe(1);
      expect(manifest.contentScripts?.[0]?.matches).toEqual(["<all_urls>"]);
      expect(manifest.contentScripts?.[0]?.js).toEqual(["content.js"]);
    });

    test("parse() should extract popup configuration", () => {
      const parser = new ManifestParser(tempDir);
      const manifest = parser.parse();

      expect(manifest.popup).toBeDefined();
      expect(manifest.popup?.html).toBe("popup.html");
      expect(manifest.popup?.default).toBe(true);
    });
  });

  describe("backward compatibility", () => {
    test("should work identically when optional=false and manifest exists", () => {
      // Create a valid manifest
      const manifest = {
        name: "Test",
        version: "1.0.0",
        manifest_version: 3,
      };

      fs.writeFileSync(path.join(tempDir, "manifest.json"), JSON.stringify(manifest));

      const parser1 = new ManifestParser(tempDir, false);
      const parser2 = new ManifestParser(tempDir, true);

      const result1 = parser1.parse();
      const result2 = parser2.parse();

      expect(result1.name).toBe(result2.name);
      expect(result1.version).toBe(result2.version);
    });
  });
});
