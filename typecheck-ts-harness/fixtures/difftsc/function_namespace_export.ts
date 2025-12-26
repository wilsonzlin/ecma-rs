namespace foo {
  export const bar = 1;
}

export function foo() {
  return foo.bar;
}

export const value = foo();
