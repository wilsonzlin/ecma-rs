namespace foo {
  const bar = 1;
}

function foo() {
  return foo.bar;
}

export const value = foo();
