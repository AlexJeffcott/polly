declare module "*.module.css" {
  const classes: Record<string, string>;
  // biome-ignore lint/style/noDefaultExport: CSS-module imports are default-exported by convention.
  export default classes;
}
