// Loads the declared model a `--model` file exports.

import * as fs from "node:fs";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import { readDeclaredModel } from "./check";
import type { DeclaredModel } from "./types";

export class ModelSourceError extends Error {
  override name = "ModelSourceError";
}

/**
 * Imports `file`, calls its default export, and checks what it returns. The
 * default export must be a function; a missing file, a missing or non-function
 * default export, and a model with any problem all throw.
 */
export async function loadDeclaredModel(file: string): Promise<DeclaredModel> {
  const absolute = path.resolve(file);
  if (!fs.existsSync(absolute)) {
    throw new ModelSourceError(`--model names ${absolute}, which does not exist`);
  }
  const module: { default?: unknown } = await import(pathToFileURL(absolute).href);
  const source = module.default;
  if (typeof source !== "function") {
    throw new ModelSourceError(
      `${absolute} must default-export a function that returns the model; its default export is ${typeof source}`
    );
  }
  return readDeclaredModel(await source());
}
