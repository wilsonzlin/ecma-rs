interface Producer<out T> {
  value: T;
}

interface Consumer<in T> {
  consume: (value: T) => void;
}

interface Invariant<in out T> {
  produce: () => T;
  consume: (value: T) => void;
}

type Box<out T> = {
  value: T;
};

declare class C<out T> {
  value: T;
}

interface BadOut<out T> {
  consume: (value: T) => void;
}

interface BadIn<in T> {
  value: T;
}
