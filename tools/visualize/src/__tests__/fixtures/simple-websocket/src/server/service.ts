// Business logic service layer

import { db } from './database';
import type { User, QueryResult } from './types';

/**
 * User service for business logic
 */
export class UserService {
  /**
   * Get user by ID
   */
  async getUser(id: string): Promise<User | null> {
    return await db.findUserById(id);
  }

  /**
   * List all users
   */
  async listUsers(): Promise<QueryResult> {
    return await db.queryUsers();
  }

  /**
   * Execute user command
   */
  async executeUserCommand(action: string, payload: unknown): Promise<boolean> {
    // Add business logic validation here
    if (!action) {
      throw new Error('Action is required');
    }

    return await db.executeCommand(action, payload);
  }
}

/**
 * Authentication service
 */
export class AuthService {
  /**
   * Authenticate user with token
   */
  async authenticate(token: string): Promise<boolean> {
    if (!token) {
      return false;
    }

    return await db.verifyToken(token);
  }
}

export const userService = new UserService();
export const authService = new AuthService();
