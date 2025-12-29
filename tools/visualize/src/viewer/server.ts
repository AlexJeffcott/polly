// Interactive viewer HTTP server using Bun

import * as fs from "node:fs";
import * as path from "node:path";

export interface ViewerOptions {
  /** Port to run server on */
  port?: number;

  /** Path to docs directory */
  docsDir: string;

  /** Auto-open browser */
  open?: boolean;
}

export class ViewerServer {
  private options: ViewerOptions;
  private server: ReturnType<typeof Bun.serve> | null = null;

  constructor(options: ViewerOptions) {
    this.options = {
      port: 3000,
      open: true,
      ...options,
    };
  }

  /**
   * Start the viewer server
   */
  async start(): Promise<void> {
    const { port, docsDir } = this.options;

    // Check if DSL file exists
    const dslPath = path.join(docsDir, "architecture.dsl");
    if (!fs.existsSync(dslPath)) {
      throw new Error(`DSL file not found: ${dslPath}`);
    }

    // Read DSL content
    const dsl = fs.readFileSync(dslPath, "utf-8");

    // Use Bun's server (dynamically accessed to avoid TS errors during build)
    const BunGlobal = (globalThis as typeof globalThis & { Bun: typeof Bun }).Bun;
    if (!BunGlobal) {
      throw new Error("Bun runtime is required to run the viewer");
    }

    try {
      this.server = BunGlobal.serve({
        port,
        fetch: (req: Request) => this.handleRequest(req, dsl, docsDir),
      });
    } catch (_error) {
      throw new Error(`Failed to start server. Is port ${port} in use?`);
    }

    console.log(`Viewer running at http://localhost:${port}`);

    // Auto-open browser
    if (this.options.open) {
      const url = `http://localhost:${port}`;
      if (process.platform === "darwin") {
        await BunGlobal.spawn(["open", url]);
      } else if (process.platform === "linux") {
        await BunGlobal.spawn(["xdg-open", url]);
      } else if (process.platform === "win32") {
        await BunGlobal.spawn(["cmd", "/c", "start", url]);
      }
    }
  }

  /**
   * Stop the server
   */
  stop(): void {
    if (this.server) {
      this.server.stop();
    }
  }

  /**
   * Handle HTTP request
   */
  private handleRequest(req: Request, dsl: string, docsDir: string): Response {
    const url = new URL(req.url);

    // Serve main viewer page
    if (url.pathname === "/" || url.pathname === "/index.html") {
      return new Response(this.generateViewerHTML(dsl), {
        headers: { "Content-Type": "text/html" },
      });
    }

    // Serve DSL file
    if (url.pathname === "/architecture.dsl") {
      return new Response(dsl, {
        headers: { "Content-Type": "text/plain" },
      });
    }

    // List available diagrams
    if (url.pathname === "/diagrams/list") {
      const diagramsDir = path.join(docsDir, "diagrams");

      if (fs.existsSync(diagramsDir)) {
        const files = fs
          .readdirSync(diagramsDir)
          .filter((file) => file.endsWith(".png") && !file.includes("-key"))
          .sort();

        return new Response(JSON.stringify(files), {
          headers: { "Content-Type": "application/json" },
        });
      }

      return new Response(JSON.stringify([]), {
        headers: { "Content-Type": "application/json" },
      });
    }

    // Serve diagram images from diagrams directory
    if (url.pathname.startsWith("/diagrams/")) {
      const fileName = path.basename(url.pathname);
      const filePath = path.join(docsDir, "diagrams", fileName);

      if (fs.existsSync(filePath)) {
        const content = fs.readFileSync(filePath);
        const ext = path.extname(fileName).toLowerCase();
        const contentType =
          ext === ".png"
            ? "image/png"
            : ext === ".svg"
              ? "image/svg+xml"
              : "application/octet-stream";

        return new Response(content, {
          headers: { "Content-Type": contentType },
        });
      }
    }

    return new Response("Not found", { status: 404 });
  }

  /**
   * Generate viewer HTML page
   */
  private generateViewerHTML(dsl: string): string {
    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Architecture Viewer</title>
  <style>
    * {
      margin: 0;
      padding: 0;
      box-sizing: border-box;
    }

    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, Cantarell, sans-serif;
      background: #f5f5f5;
      color: #333;
    }

    header {
      background: #2c3e50;
      color: white;
      padding: 1rem 2rem;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }

    h1 {
      font-size: 1.5rem;
      font-weight: 600;
    }

    .container {
      display: flex;
      height: calc(100vh - 60px);
    }

    .sidebar {
      width: 300px;
      background: white;
      border-right: 1px solid #ddd;
      overflow-y: auto;
    }

    .content {
      flex: 1;
      padding: 2rem;
      overflow-y: auto;
    }

    .nav-section {
      padding: 1rem;
      border-bottom: 1px solid #eee;
    }

    .nav-section h2 {
      font-size: 0.875rem;
      text-transform: uppercase;
      color: #666;
      margin-bottom: 0.5rem;
      font-weight: 600;
    }

    .nav-item {
      padding: 0.5rem;
      cursor: pointer;
      border-radius: 4px;
      transition: background 0.2s;
    }

    .nav-item:hover {
      background: #f0f0f0;
    }

    .nav-item.active {
      background: #3498db;
      color: white;
    }

    .card {
      background: white;
      border-radius: 8px;
      padding: 1.5rem;
      margin-bottom: 1.5rem;
      box-shadow: 0 1px 3px rgba(0,0,0,0.1);
    }

    .card h2 {
      margin-bottom: 1rem;
      color: #2c3e50;
    }

    pre {
      background: #f8f9fa;
      padding: 1rem;
      border-radius: 4px;
      overflow-x: auto;
      font-size: 0.875rem;
      line-height: 1.5;
    }

    .diagram {
      width: 100%;
      max-width: 800px;
      border: 1px solid #ddd;
      border-radius: 4px;
      background: white;
    }

    .badge {
      display: inline-block;
      padding: 0.25rem 0.5rem;
      border-radius: 4px;
      font-size: 0.75rem;
      font-weight: 600;
      margin-right: 0.5rem;
    }

    .badge-context {
      background: #3498db;
      color: white;
    }

    .badge-handler {
      background: #2ecc71;
      color: white;
    }

    .badge-api {
      background: #e74c3c;
      color: white;
    }

    .list-item {
      padding: 0.5rem 0;
      border-bottom: 1px solid #eee;
    }

    .list-item:last-child {
      border-bottom: none;
    }

    .empty-state {
      text-align: center;
      padding: 3rem;
      color: #999;
    }

    .tabs {
      display: flex;
      border-bottom: 2px solid #ddd;
      margin-bottom: 1rem;
    }

    .tab {
      padding: 0.75rem 1.5rem;
      cursor: pointer;
      border-bottom: 2px solid transparent;
      margin-bottom: -2px;
      transition: all 0.2s;
    }

    .tab:hover {
      background: #f8f9fa;
    }

    .tab.active {
      border-bottom-color: #3498db;
      color: #3498db;
      font-weight: 600;
    }

    .tab-content {
      display: none;
    }

    .tab-content.active {
      display: block;
    }
  </style>
</head>
<body>
  <header>
    <h1>🏗️ Architecture Viewer</h1>
  </header>

  <div class="container">
    <aside class="sidebar">
      <div class="nav-section">
        <h2>Views</h2>
        <div class="nav-item active" data-view="overview">Overview</div>
        <div class="nav-item" data-view="dsl">DSL Source</div>
        <div class="nav-item" data-view="diagrams">Diagrams</div>
      </div>
    </aside>

    <main class="content">
      <div id="overview-view" class="view-content">
        <div class="card">
          <h2>Architecture Overview</h2>
          <div id="overview-content"></div>
        </div>
      </div>

      <div id="dsl-view" class="view-content" style="display: none;">
        <div class="card">
          <h2>Structurizr DSL</h2>
          <pre id="dsl-content"></pre>
        </div>
      </div>

      <div id="diagrams-view" class="view-content" style="display: none;">
        <div class="card">
          <h2>Exported Diagrams</h2>
          <div id="diagrams-content"></div>
        </div>
      </div>
    </main>
  </div>

  <script>
    const dsl = ${JSON.stringify(dsl)};

    // Parse DSL to extract information
    function parseDSL(dsl) {
      const lines = dsl.split('\\n');
      const info = {
        workspace: '',
        contexts: [],
        components: [],
        relationships: []
      };

      // Extract workspace name
      const workspaceMatch = dsl.match(/workspace "([^"]+)"/);
      if (workspaceMatch) {
        info.workspace = workspaceMatch[1];
      }

      // Extract containers (contexts)
      const containerMatches = dsl.matchAll(/container "([^"]+)" "([^"]*)"/g);
      for (const match of containerMatches) {
        info.contexts.push({ name: match[1], description: match[2] });
      }

      // Extract components
      const componentMatches = dsl.matchAll(/component "([^"]+)" "([^"]*)"/g);
      for (const match of componentMatches) {
        info.components.push({ name: match[1], description: match[2] });
      }

      return info;
    }

    const info = parseDSL(dsl);

    // Render overview
    const overviewContent = document.getElementById('overview-content');
    let html = '<h3>' + info.workspace + '</h3>';

    if (info.contexts.length > 0) {
      html += '<h4 style="margin-top: 1.5rem;">Contexts</h4>';
      info.contexts.forEach(ctx => {
        html += '<div class="list-item">';
        html += '<span class="badge badge-context">' + ctx.name + '</span>';
        html += '<div style="margin-top: 0.25rem; color: #666;">' + ctx.description + '</div>';
        html += '</div>';
      });
    }

    if (info.components.length > 0) {
      html += '<h4 style="margin-top: 1.5rem;">Components</h4>';
      info.components.forEach(comp => {
        html += '<div class="list-item">';
        html += '<span class="badge badge-handler">' + comp.name + '</span>';
        html += '<div style="margin-top: 0.25rem; color: #666;">' + comp.description + '</div>';
        html += '</div>';
      });
    }

    overviewContent.innerHTML = html;

    // Render DSL
    document.getElementById('dsl-content').textContent = dsl;

    // Check for diagrams
    fetch('/diagrams/list')
      .then(res => res.ok ? res.json() : null)
      .then(diagrams => {
        const diagramsContent = document.getElementById('diagrams-content');
        if (diagrams && diagrams.length > 0) {
          // Display diagrams
          let html = '';
          diagrams.forEach(diagram => {
            html += '<div style="margin-bottom: 2rem;">';
            html += '<h3>' + diagram.replace(/^structurizr-/, '').replace(/\\.png$/, '').replace(/_/g, ' ') + '</h3>';
            html += '<img src="/diagrams/' + diagram + '" class="diagram" alt="' + diagram + '" />';
            html += '</div>';
          });
          diagramsContent.innerHTML = html;
        } else {
          diagramsContent.innerHTML = '<div class="empty-state">No diagrams exported yet.<br><br>Run <code>bun visualize --export</code> to generate diagrams.</div>';
        }
      })
      .catch(() => {
        const diagramsContent = document.getElementById('diagrams-content');
        diagramsContent.innerHTML = '<div class="empty-state">No diagrams exported yet.<br><br>Run <code>bun visualize --export</code> to generate diagrams.</div>';
      });

    // Navigation
    document.querySelectorAll('.nav-item').forEach(item => {
      item.addEventListener('click', () => {
        // Update active nav
        document.querySelectorAll('.nav-item').forEach(i => i.classList.remove('active'));
        item.classList.add('active');

        // Show corresponding view
        const view = item.dataset.view;
        document.querySelectorAll('.view-content').forEach(v => v.style.display = 'none');
        document.getElementById(view + '-view').style.display = 'block';
      });
    });
  </script>
</body>
</html>`;
  }
}

/**
 * Start interactive viewer
 */
export async function startViewer(options: ViewerOptions): Promise<ViewerServer> {
  const server = new ViewerServer(options);
  await server.start();
  return server;
}
