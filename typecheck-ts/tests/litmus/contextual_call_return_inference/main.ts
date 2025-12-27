declare function id<T>(x: T): T;
const n: number = id(1 as any);
// expect-def-type: n = number

declare function f(x: any): any;
declare function f(x: number): number;
const y: number = f(1 as any);
// expect-def-type: y = number
