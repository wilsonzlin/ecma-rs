export function pick<T>(left: T, right: T): T {
  return Math.random() > 0.5 ? left : right;
}

export function overload(value: string): string;
export function overload(value: number): number;
export function overload(value: string | number) {
  return value;
}

export function combine<A, B>(a: A[], b: B[]): Array<A | B> {
  return [...a, ...b];
}

// Exercise instantiation and overload selection with repeated calls so cache hit
// rates are visible in the benchmark output.
export const pickedA = pick(1, 2);
export const pickedB = pick(1, 2);
