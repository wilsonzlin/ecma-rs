// @lib: es5,dom
/// <reference lib="es2015.promise" />

const p: Promise<number> = Promise.resolve(1);
p.then((value) => value);
