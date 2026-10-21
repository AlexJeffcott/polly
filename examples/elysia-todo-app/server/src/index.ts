import { app } from "./app";

app.listen(3000);

console.log(`🦊 Elysia server running at ${app.server?.hostname}:${app.server?.port}`);

export type { App } from "./app";
