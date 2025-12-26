type Options = { a: number; b: string };
type ReadonlyPartial<T> = { readonly [K in keyof T]?: T[K] };

export const partial: ReadonlyPartial<Options> = { a: 1 };
             // ^?
