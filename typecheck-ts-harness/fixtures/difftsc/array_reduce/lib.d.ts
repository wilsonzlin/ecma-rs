export interface MyArray<T> {
  reduce(callback: (acc: T, cur: T) => T): T;
  reduce<U>(callback: (acc: U, cur: T) => U, init: U): U;
}

export const nums: MyArray<number>;
