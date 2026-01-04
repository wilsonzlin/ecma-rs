// @target: ESNext
// @useDefineForClassFields: true
class C {
  foo = this.bar;
  constructor(public bar: number) {}
}

