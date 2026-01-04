// @target: ESNext
// @useDefineForClassFields: false
class C {
  foo = this.bar;
  constructor(public bar: number) {}
}

