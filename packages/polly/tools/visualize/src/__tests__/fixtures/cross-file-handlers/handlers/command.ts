// Command handler implementation (separate file from router)

import type { CommandMessage } from "../messages";

// Mock repository service
declare const repositories: {
  users: {
    create(data: any): Promise<any>;
    update(id: number, data: any): Promise<any>;
  };
};

// Handler implementation
export async function handleCommand(message: CommandMessage) {
  // This should be detected as: command_handler -> repositories
  if (message.action === "create") {
    return await repositories.users.create({ name: "test" });
  }

  // This should also be detected as: command_handler -> repositories
  return await repositories.users.update(1, { name: "updated" });
}
