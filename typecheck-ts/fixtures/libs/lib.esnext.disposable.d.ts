// Minimal ESNext disposable lib for tests (Explicit Resource Management)
//
// This intentionally contains only the surface needed to type-check `using` /
// `await using` declarations.

interface PromiseLike<T> {
  // Note: this is intentionally minimal. The real `lib.es5.d.ts` defines a
  // recursive `PromiseLike` that our checker is not yet robust enough to fully
  // evaluate without hitting recursion limits.
  then(
    onfulfilled?: ((value: T) => any) | undefined | null,
    onrejected?: ((reason: any) => any) | undefined | null,
  ): any;
}

interface SymbolConstructor {
  readonly dispose: unique symbol;
  readonly asyncDispose: unique symbol;
}

declare const Symbol: SymbolConstructor;

interface Disposable {
  [Symbol.dispose](): void;
}

interface AsyncDisposable {
  [Symbol.asyncDispose](): PromiseLike<void> | void;
}

interface SuppressedError {
  error: any;
  suppressed: any;
}

declare const SuppressedError: {
  new (error: any, suppressed: any, message?: string): SuppressedError;
};
