declare module "*.wasm" {
  const url: string;
  // biome-ignore lint/style/noDefaultExport: TypeScript module declarations for asset imports require default export.
  export default url;
}
