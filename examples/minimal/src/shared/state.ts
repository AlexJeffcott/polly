// Shared state - automatically syncs across popup, options, background, etc.
import { $sharedState } from "@fairfox/polly/state";

export const counter = $sharedState("counter", 0);
