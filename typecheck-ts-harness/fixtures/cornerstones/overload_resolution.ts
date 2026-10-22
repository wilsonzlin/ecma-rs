// Cornerstone: overload selection
export function pick(x: string): string;
export function pick(x: number): number;
export function pick(x: string | number): string | number {
  return x;
}

export const s = pick("hi");
export const n = pick(1);
const bad = pick(true);
