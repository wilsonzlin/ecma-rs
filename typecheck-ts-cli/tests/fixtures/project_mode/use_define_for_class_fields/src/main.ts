class C {
  foo = this.bar;
  constructor(public bar: number) {}
}

class Base {
  x = 1;
}

class Derived extends Base {
  x: number;
}

export const value = (new C(1)).foo;
