/**
 * Drive a real polly MessageBus from step definitions.
 *
 * `createBackground()` wires a MessageRouter whose request/response loopback
 * runs over ports — which don't exist in a single in-process world, so a
 * self-targeted `bus.send` would just time out. `handleMessage` is the exact
 * method the router calls for a background-targeted message
 * (`routeToSingleTarget` → `this.bus.handleMessage(message)`): it runs the
 * registered handler and returns its response. So we build the inbound
 * RoutedMessage a UI context would send and hand it to `handleMessage`.
 *
 * This crosses the real handler + state-signal path through the real,
 * factory-built bus. The only thing it does NOT exercise is cross-context port
 * transport — and that boundary is covered for real by the mesh e2e scenario,
 * not faked here. (The polly#57 lesson is about not letting a hand-wired bus
 * paper over a factory gap; here the factory built the bus and registered the
 * handlers, and we drive its own dispatch entry point.)
 */
import type { BusLike } from "./types.ts";

/**
 * Anything with the bus's dispatch entry point. Declared as a *method* (not an
 * arrow property) so its parameter is bivariant — a real
 * `MessageBus<TMessage>`, whose `handleMessage` takes the narrower
 * `RoutedMessage<TMessage>`, is assignable here.
 */
export interface DispatchBus {
  handleMessage(message: unknown): Promise<unknown>;
}

interface DriveOptions {
  /** The context the message appears to come from (a UI context → background). */
  source?: string;
  /** Default delivery target. */
  target?: string;
}

export function driveBus(bus: DispatchBus, driveOpts: DriveOptions = {}): BusLike {
  const source = driveOpts.source ?? "popup";
  const defaultTarget = driveOpts.target ?? "background";

  return {
    async send(payload, options) {
      const target = options?.target ?? defaultTarget;
      const targets = Array.isArray(target) ? target : [target];
      const message = {
        id: crypto.randomUUID(),
        source,
        targets,
        timestamp: Date.now(),
        payload,
        ...(options?.tabId === undefined ? {} : { tabId: options.tabId }),
      };
      const response = (await bus.handleMessage(message)) as
        | { success?: boolean; data?: unknown; error?: string }
        | undefined;
      // Return the handler's own return value (response.data); steps assert on it.
      return response?.data;
    },
  };
}
