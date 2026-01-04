// @target: ESNext

class D implements Disposable {
  value: number = 1;

  [Symbol.dispose](): void {}
}

using x = new D();
   // ^?

class Box implements Disposable {
  value: number = 123;

  [Symbol.dispose](): void {}
}

using { value } = new Box();
     // ^?

