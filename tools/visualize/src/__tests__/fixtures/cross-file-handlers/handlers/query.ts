// Query handler implementation (separate file from router)
// This file contains the actual business logic with service calls

import type { QueryMessage } from "../messages";

// Mock service objects
declare const userService: {
	listUsers(): Promise<any>;
	findById(id: number): Promise<any>;
};

declare const db: {
	query(sql: string): Promise<any>;
};

// Handler implementation - this is where the relationships should be detected
export async function handleQuery(_message: QueryMessage) {
	// This should be detected as: query_handler -> user_service
	const users = await userService.listUsers();

	// This should be detected as: query_handler -> database
	const result = await db.query("SELECT * FROM users");

	return {
		type: "result",
		data: { users, result },
	};
}
