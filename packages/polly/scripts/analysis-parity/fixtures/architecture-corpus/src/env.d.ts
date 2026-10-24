// Untyped extension globals: the extractors read these calls syntactically.
interface ApiTree {
  [key: string]: ApiTree & ((...args: unknown[]) => unknown);
}
declare const chrome: ApiTree;
declare const browser: ApiTree;
