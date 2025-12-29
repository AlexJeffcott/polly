// ═══════════════════════════════════════════════════════════════
// Routing Adapter Interface
// ═══════════════════════════════════════════════════════════════
//
// Adapters translate domain-specific code into the core verification model.
// Each adapter implements pattern matching and extraction logic for a
// specific messaging paradigm.

import type { Node } from "ts-morph";
import type {
  CoreVerificationModel,
  MessageHandler,
  StateAssignment,
  VerificationCondition,
} from "../core/model";

// ─────────────────────────────────────────────────────────────────
// Adapter Configuration
// ─────────────────────────────────────────────────────────────────

/**
 * Base configuration for all adapters
 */
export type AdapterConfig = {
  /** Root directory to analyze */
  rootDir?: string;

  /** TypeScript config path */
  tsConfigPath: string;

  /** Adapter-specific options */
  [key: string]: unknown;
};

// ─────────────────────────────────────────────────────────────────
// Adapter Interface
// ─────────────────────────────────────────────────────────────────

/**
 * Base interface that all routing adapters must implement.
 *
 * Adapters are responsible for:
 * 1. Extracting the abstract model from domain-specific code
 * 2. Recognizing domain-specific patterns (how messages are sent/received)
 * 3. Mapping domain concepts to abstract model concepts
 */
export interface RoutingAdapter<TConfig extends AdapterConfig = AdapterConfig> {
  /** Unique name for this adapter */
  readonly name: string;

  /** Configuration */
  readonly config: TConfig;

  /**
   * Extract the complete abstract model from a codebase
   *
   * This is the main entry point for the adapter. It should:
   * 1. Discover nodes in the system
   * 2. Extract message types
   * 3. Infer routing rules
   * 4. Extract message handlers and state mutations
   * 5. Return a complete CoreVerificationModel
   */
  extractModel(): CoreVerificationModel;

  /**
   * Recognize if an AST node is a message handler registration
   *
   * @param node - TypeScript AST node to analyze
   * @returns MessageHandler if recognized, null otherwise
   *
   * @example
   * // Web extension adapter recognizes:
   * bus.on("USER_LOGIN", (payload) => { ... })
   *
   * // Actor adapter recognizes:
   * actor.receive((msg) => { if (msg.type === "USER_LOGIN") { ... } })
   */
  recognizeMessageHandler(node: Node): MessageHandler | null;

  /**
   * Recognize if an AST node is a state mutation
   *
   * @param node - TypeScript AST node to analyze
   * @returns StateAssignment if recognized, null otherwise
   *
   * @example
   * // Most adapters recognize:
   * state.user.loggedIn = true
   */
  recognizeStateUpdate(node: Node): StateAssignment | null;

  /**
   * Recognize if an AST node is a verification condition
   *
   * @param node - TypeScript AST node to analyze
   * @param type - "precondition" or "postcondition"
   * @returns VerificationCondition if recognized, null otherwise
   *
   * @example
   * // All adapters should recognize:
   * requires(state.user.loggedIn === false, "Must not be logged in")
   * ensures(state.user.loggedIn === true, "Must be logged in")
   */
  recognizeVerificationCondition(
    node: Node,
    type: "precondition" | "postcondition"
  ): VerificationCondition | null;

  /**
   * Optional: Provide custom TLA+ invariants specific to this domain
   *
   * @example
   * // Actor adapter might add:
   * ["ActorMailboxBounded", "\\A actor \\in Actors : Len(mailbox[actor]) <= MaxMailboxSize"]
   */
  customInvariants?(): Array<[name: string, tlaExpression: string]>;
}

// ─────────────────────────────────────────────────────────────────
// Helper: Base Adapter Class
// ─────────────────────────────────────────────────────────────────

/**
 * Base class providing common extraction logic that adapters can extend.
 * This reduces boilerplate in adapter implementations.
 */
export abstract class BaseRoutingAdapter<TConfig extends AdapterConfig = AdapterConfig>
  implements RoutingAdapter<TConfig>
{
  abstract readonly name: string;
  abstract readonly config: TConfig;

  abstract extractModel(): CoreVerificationModel;
  abstract recognizeMessageHandler(node: Node): MessageHandler | null;
  abstract recognizeStateUpdate(node: Node): StateAssignment | null;
  abstract recognizeVerificationCondition(
    node: Node,
    type: "precondition" | "postcondition"
  ): VerificationCondition | null;

  /**
   * Common pattern: Extract verification conditions from requires()/ensures() calls
   *
   * Subclasses can use this helper to avoid duplicating condition extraction logic.
   */
  protected extractConditionFromCall(): VerificationCondition | null {
    // Shared implementation for requires()/ensures() extraction
    // This will be implemented when we refactor the existing handler extraction
    return null;
  }

  /**
   * Common pattern: Extract state assignments from binary expressions
   */
  protected extractAssignmentFromBinaryExpr(): StateAssignment | null {
    // Shared implementation for state.field = value extraction
    return null;
  }
}
