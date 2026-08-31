/** Bun bundles a plain CSS import for its side effect; TypeScript needs the
 *  module declared before it will accept `import "./App.css"`. */
declare module "*.css";
