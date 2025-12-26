// Minimal ES2015 lib for tests
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

declare const esVersion: "es2015";
