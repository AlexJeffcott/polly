/**
 * TLC `-workers`: a count, or `"auto"` for one per core the container sees.
 *
 * A leaf module on purpose: the config types import it, and importing it from
 * `docker.ts` put that file in every program that type-checks a verification
 * config, where the adapters read its child-process event listeners as message
 * handlers. Keep this file free of listener-shaped text for the same reason:
 * adapter detection counts listener calls with a regex over every file.
 */
export type TLCWorkers = number | "auto";
