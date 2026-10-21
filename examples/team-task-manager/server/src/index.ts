import { createApp } from "./app";

const app = createApp();

// Check if SSL certificates exist
const CERTS_DIR = process.env.CERTS_DIR ?? `${import.meta.dir}/../certs`;
const certFile = Bun.file(`${CERTS_DIR}/cert.pem`);
const keyFile = Bun.file(`${CERTS_DIR}/key.pem`);
const hasCerts = (await certFile.exists()) && (await keyFile.exists());

if (!hasCerts) {
  console.error("ERROR: SSL certificates not found!");
  console.error("   This example requires HTTPS for E2EE to work properly.");
  console.error("");
  console.error("   Run the following command to generate certificates:");
  console.error("   bun run setup:ssl");
  console.error("");
  process.exit(1);
}

// Start server with HTTPS
app.listen({
  port: 3000,
  tls: {
    cert: certFile,
    key: keyFile,
  },
});

const port = app.server?.port ?? 3000;
const hostname = app.server?.hostname ?? "localhost";

console.log(`Team Task Manager server running at https://${hostname}:${port}`);
console.log("Pure local-first mode: Server stores NO data, only relays messages");
console.log("All data lives in client IndexedDB - server is a stateless message broker");
console.log("HTTPS enabled");

// Export app type for Eden treaty client
export type { App } from "./app";
