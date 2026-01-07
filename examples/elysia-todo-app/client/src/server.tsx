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
    <title>Polly + Elysia Todo App</title>
  </head>
  <body>
    <div id="app"></div>
    <script type="module">
      // Import and run client code
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
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional for debugging
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
