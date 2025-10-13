// High-level verification primitives API
// TODO: Implement full API

/**
 * Specify that msg1 must be sent before msg2
 */
export function before(msg1: string, msg2: string | string[]): any {
  return {
    type: "before",
    msg1,
    msg2: Array.isArray(msg2) ? msg2 : [msg2]
  }
}

/**
 * Specify that msg1 must be sent after msg2
 */
export function after(msg1: string, msg2: string | string[]): any {
  return {
    type: "after",
    msg1,
    msg2: Array.isArray(msg2) ? msg2 : [msg2]
  }
}

/**
 * Specify that messages must be sent in sequence
 */
export function sequence(messages: string[]): any {
  return {
    type: "sequence",
    messages
  }
}

/**
 * Specify that messages cannot be in flight simultaneously
 */
export const never = {
  concurrent(messages: string[]): any {
    return {
      type: "never.concurrent",
      messages
    }
  }
}

/**
 * Specify that condition eventually becomes true
 */
export const eventually = {
  delivers(message: string, options?: { timeout?: number }): any {
    return {
      type: "eventually.delivers",
      message,
      options
    }
  }
}

/**
 * Specify a message precondition (state must satisfy predicate)
 */
export function requires(message: string, predicate: Function | { raw: string }): any {
  return {
    type: "requires",
    message,
    predicate: typeof predicate === "function" ? predicate.toString() : predicate.raw
  }
}

/**
 * Specify a message postcondition (state must satisfy predicate after message)
 */
export function ensures(message: string, predicate: Function | { raw: string }): any {
  return {
    type: "ensures",
    message,
    predicate: typeof predicate === "function" ? predicate.toString() : predicate.raw
  }
}

/**
 * Specify a state invariant (predicate always holds)
 */
export function maintains(predicate: Function | { raw: string }): any {
  return {
    type: "maintains",
    predicate: typeof predicate === "function" ? predicate.toString() : predicate.raw
  }
}

/**
 * Define a custom invariant with raw TLA+ code (escape hatch)
 */
export function defineInvariant(name: string, options: {
  description?: string
  raw: string
}): any {
  return {
    type: "custom",
    name,
    description: options.description,
    raw: options.raw
  }
}
