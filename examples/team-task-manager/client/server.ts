/**
 * Client Development Server
 *
 * Builds and serves the Preact app with hot reloading.
 */

const CERTS_DIR = `${import.meta.dir}/certs`;
const CLIENT_PORT = 5173;
const API_PORT = 3000;
const isDevelopment = true;

// In-memory storage for built files
const buildCache = new Map<string, BuildArtifact>();

interface BuildArtifact {
  content: BufferSource;
  type: string;
}

// Build the app
async function buildApp() {
  console.log("[BUILD] Starting build process...");

  // Build API URLs for client-side code (always HTTPS)
  const apiUrl = `https://localhost:${API_PORT}`;
  const wsUrl = `wss://localhost:${API_PORT}/ws`;

  console.log("[BUILD] Building main app...");
  const result = await Bun.build({
    entrypoints: ["./src/main.tsx"],
    target: "browser",
    minify: false,
    sourcemap: "external",
    splitting: true,
    naming: {
      entry: "[dir]/[name].[hash].[ext]",
      chunk: "[dir]/[name].[hash].[ext]",
      asset: "[dir]/[name].[hash].[ext]",
    },
    define: {
      "process.env.API_URL": JSON.stringify(apiUrl),
      "process.env.WS_URL": JSON.stringify(wsUrl),
    },
  });

  if (!result.success) {
    console.error("ERROR: Build failed:");
    for (const log of result.logs) {
      console.error(log);
    }
    return false;
  }

  console.log("[BUILD] Build completed");

  // Cache build outputs
  buildCache.clear();

  // Find the main JS file (has hash in name)
  let mainJsPath = "";
  for (const output of result.outputs) {
    const content = await output.arrayBuffer();
    const path = output.path.split("/").pop() || "";

    if (path.endsWith(".js")) {
      if (path.includes(".") && !path.startsWith("chunk")) {
        mainJsPath = `/${path}`;
      }
      buildCache.set(`/${path}`, {
        content: new Uint8Array(content),
        type: "application/javascript",
      });
    } else if (path.endsWith(".css")) {
      buildCache.set(`/${path}`, {
        content: new Uint8Array(content),
        type: "text/css",
      });
    } else if (path.endsWith(".map")) {
      buildCache.set(`/${path}`, {
        content: new Uint8Array(content),
        type: "application/json",
      });
    }
  }

  // Read and modify index.html to include the built JS file
  const indexHtml = await Bun.file("./index.html").text();
  const modifiedHtml = indexHtml.replace(
    '<script type="module" src="/src/main.tsx"></script>',
    `<script type="module" src="${mainJsPath}"></script>`
  );

  buildCache.set("/", {
    content: new TextEncoder().encode(modifiedHtml),
    type: "text/html",
  });

  // Cache static PWA files
  const manifestFile = Bun.file("./manifest.json");
  if (await manifestFile.exists()) {
    const manifestContent = await manifestFile.arrayBuffer();
    buildCache.set("/manifest.json", {
      content: new Uint8Array(manifestContent),
      type: "application/manifest+json",
    });
  }

  const serviceWorkerFile = Bun.file("./service-worker.js");
  if (await serviceWorkerFile.exists()) {
    const swContent = await serviceWorkerFile.arrayBuffer();
    buildCache.set("/service-worker.js", {
      content: new Uint8Array(swContent),
      type: "application/javascript",
    });
  }

  return true;
}

async function checkCerts(): Promise<boolean> {
  const certFile = Bun.file(`${CERTS_DIR}/cert.pem`);
  const keyFile = Bun.file(`${CERTS_DIR}/key.pem`);
  return (await certFile.exists()) && (await keyFile.exists());
}

// Check if SSL certificates exist BEFORE building
const hasCerts = await checkCerts();
if (!hasCerts) {
  console.error("\nERROR: SSL certificates not found!");
  console.error("   This example requires HTTPS for E2EE to work properly.");
  console.error("");
  console.error("   Run the following command to generate certificates:");
  console.error("   bun run setup:ssl");
  console.error("");
  process.exit(1);
}

// Build on startup
const buildSuccess = await buildApp();
if (!buildSuccess) {
  process.exit(1);
}

const certFile = Bun.file(`${CERTS_DIR}/cert.pem`);
const keyFile = Bun.file(`${CERTS_DIR}/key.pem`);

// Start server with HTTPS
const server = Bun.serve({
  port: CLIENT_PORT,
  tls: {
    cert: certFile,
    key: keyFile,
  },
  development: isDevelopment,
  async fetch(req) {
    const url = new URL(req.url);
    let path = url.pathname;

    // Normalize root path
    if (path === "/") {
      path = "/";
    }

    // Serve from build cache
    const artifact = buildCache.get(path);
    if (artifact) {
      const headers: Record<string, string> = {
        "Content-Type": artifact.type,
        "Cache-Control": "no-cache, must-revalidate",
      };

      // Add Service-Worker-Allowed header for service worker
      if (path === "/service-worker.js") {
        headers["Service-Worker-Allowed"] = "/";
      }

      return new Response(artifact.content, { headers });
    }

    // Serve icon files (fallback to a simple SVG icon)
    if (path.startsWith("/icons/") && path.endsWith(".png")) {
      // For now, redirect missing icons to a placeholder
      // In production, you'd generate proper icons
      return new Response(
        '<svg xmlns="http://www.w3.org/2000/svg" width="512" height="512" viewBox="0 0 512 512"><rect fill="#4f46e5" width="512" height="512"/><text x="256" y="280" text-anchor="middle" font-size="240" fill="white">📋</text></svg>',
        {
          headers: {
            "Content-Type": "image/svg+xml",
            "Cache-Control": "public, max-age=3600",
          },
        }
      );
    }

    // SPA fallback - serve index.html for all routes
    const indexArtifact = buildCache.get("/");
    if (indexArtifact) {
      return new Response(indexArtifact.content, {
        headers: {
          "Content-Type": "text/html",
          "Cache-Control": "no-cache, must-revalidate",
        },
      });
    }

    return new Response("Not Found", { status: 404 });
  },
});

const port = server.port;

console.log(`\nClient server running at https://localhost:${port}`);
console.log("HTTPS enabled");
console.log("");
