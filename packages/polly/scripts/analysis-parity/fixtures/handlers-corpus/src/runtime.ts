export interface Signal<T> {
  value: T;
}

export function $sharedState<T>(
  _key: string,
  initial: T,
  _options?: { verify?: boolean }
): Signal<T> {
  return { value: initial };
}

export function requires(_condition: boolean, _message?: string): void {}
export function ensures(_condition: boolean, _message?: string): void {}

export interface Bus {
  on(type: string, handler: (...args: never[]) => unknown): void;
}

export const bus: Bus = { on() {} };
