import { html } from "@elysiajs/html";
import { Elysia } from "elysia";

const app = new Elysia()
  .use(html())
  .get("/", () => {
    return `
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>WebRTC P2P Chat - Polly Example</title>
    <style>
      * { margin: 0; padding: 0; box-sizing: border-box; }
      body {
        font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
        background: #0f0f0f;
        color: #fff;
      }
    </style>
  </head>
  <body>
    <div id="app"></div>
    <script type="module">
      import('./client.js');
    </script>
  </body>
</html>
    `.trim();
  })
  .get("/client.js", async () => {
    // Bundle client code on-the-fly
    const result = await Bun.build({
      entrypoints: ["./src/client.tsx"],
      target: "browser",
      minify: process.env.NODE_ENV === "production",
    });

    if (!result.success) {
      console.error("Build failed:", result.logs);
      return new Response("Build failed", { status: 500 });
    }

    const output = result.outputs[0];
    const text = await output.text();

    return new Response(text, {
      headers: {
        "Content-Type": "application/javascript",
      },
    });
  })
  .listen(5173);

console.log(`🎨 Client dev server running at http://localhost:${app.server?.port}`);
