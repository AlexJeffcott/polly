// Router/Server file - this is where Polly detects handlers
// The actual business logic is in separate handler files

import {
	isQueryMessage,
	isCommandMessage,
	type RequestMessage,
} from "./messages";
import { handleQuery } from "./handlers/query";
import { handleCommand } from "./handlers/command";

// WebSocket server simulation
declare const ws: {
	on(event: string, handler: (data: any) => void): void;
};

// Message router - Polly detects handlers here
ws.on("message", async (data: string) => {
	const message = JSON.parse(data) as RequestMessage;
	let response: any;

	// Type guard pattern - Polly detects handleQuery as query handler
	if (isQueryMessage(message)) {
		response = await handleQuery(message);
	}
	// Type guard pattern - Polly detects handleCommand as command handler
	else if (isCommandMessage(message)) {
		response = await handleCommand(message);
	}

	return response;
});
