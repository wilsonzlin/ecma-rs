interface Animal {
  kind: "animal";
}

interface Dog extends Animal {
  bark(): void;
}

export interface Box<in out T> {
  readonly value: T;
}

export const dogBox: Box<Dog> = { value: { kind: "animal", bark() {} } };
             // ^?

// Diagnostic mismatch case: `in out` makes `Box<T>` invariant.
export const animalBox: Box<Animal> = dogBox;
