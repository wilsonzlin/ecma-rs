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
