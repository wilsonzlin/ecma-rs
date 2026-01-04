// Minimal ES2015 Promise lib for tests

declare const Promise: {
  resolve<T>(value: T): Promise<T>;
};

interface Promise<T> {
  then(onfulfilled: (value: T) => T): Promise<T>;
}

declare const esVersion: "es2015.promise";

