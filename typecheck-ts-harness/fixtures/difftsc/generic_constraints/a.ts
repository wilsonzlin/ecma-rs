export function f<T extends string>(x: T): T {
  return x as any;
}
