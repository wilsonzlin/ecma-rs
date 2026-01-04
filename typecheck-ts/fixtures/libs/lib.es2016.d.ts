// Minimal ES2016 lib for tests
declare const console: {
  log(msg: string): void;
};

declare const Array: any[];
declare const Promise: any;

interface Array<T> {
  length: number;
  [n: number]: T;
}

interface Promise<T> {
  then(onfulfilled: (value: T) => T): Promise<T>;
}

type Uppercase<S extends string> = intrinsic;
type Lowercase<S extends string> = intrinsic;
type Capitalize<S extends string> = intrinsic;
type Uncapitalize<S extends string> = intrinsic;
type NoInfer<T> = intrinsic;
type BuiltinIteratorReturn = intrinsic;

declare const esVersion: "es2016";
