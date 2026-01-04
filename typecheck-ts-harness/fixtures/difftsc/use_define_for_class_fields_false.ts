// @target: ESNext
// @useDefineForClassFields: false
class C {
  foo = this.bar;
  constructor(public bar: number) {}
}

class Base {
  x = 1;
}

class Derived extends Base {
  y = this.x;
  x = 2;
}

class StaticC {
  foo = StaticC.baz;
  static baz = 1;
}

class BaseOverwrite {
  x = 1;
}

class DerivedOverwrite extends BaseOverwrite {
  x: number;
}
