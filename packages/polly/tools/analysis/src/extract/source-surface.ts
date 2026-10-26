// Which source files are the application's own surface.

const OFF_SURFACE_PATH =
  /(?:\.(?:test|spec|stories)\.[cm]?[jt]sx?$)|(?:\/(?:__tests__|tests|test|features|e2e|stories|__mocks__)\/)/i;

/**
 * True for a test, spec, story, BDD step or mock file. Such a file drives the
 * application from outside: a `fetch` in it is not an integration of the app,
 * and a `send` in it is not one of the app's message flows.
 *
 * Pass a path relative to the project root, prefixed with `/`, so a project
 * that itself sits under a `__tests__` fixture directory still counts.
 */
export function isOffSurfacePath(filePath: string): boolean {
  return OFF_SURFACE_PATH.test(filePath);
}
