// Shared state - automatically syncs across popup, options, background, etc.
import { $sharedState } from "@fairfox/web-ext/state";

export const counter = $sharedState("counter", 0);
