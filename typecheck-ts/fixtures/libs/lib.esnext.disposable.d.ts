// Minimal ESNext disposable lib for tests (Explicit Resource Management)
//
// This intentionally contains only the surface needed to type-check `using` /
// `await using` declarations.

// Note: this matches the recursive `PromiseLike` shape from the official
// TypeScript libs so that bundled lib checking exercises recursive structural
// types (and ensures `AsyncDisposable` is well-typed).
interface PromiseLike<T> {
  then<TResult1 = T, TResult2 = never>(
    onfulfilled?: ((value: T) => TResult1 | PromiseLike<TResult1>) | undefined | null,
    onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | undefined | null,
  ): PromiseLike<TResult1 | TResult2>;
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
