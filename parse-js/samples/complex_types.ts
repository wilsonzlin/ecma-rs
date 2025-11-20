// Complex TypeScript type constructs

// Conditional types
type IsString<T> = T extends string ? true : false;
type Unwrap<T> = T extends Promise<infer U> ? U : T;
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;

// Mapped types
type Readonly<T> = { readonly [P in keyof T]: T[P] };
type Partial<T> = { [P in keyof T]?: T[P] };
type Required<T> = { [P in keyof T]-?: T[P] };
type Nullable<T> = { [P in keyof T]: T[P] | null };

// Template literal types
type HTTPMethod = "GET" | "POST" | "PUT" | "DELETE";
type Endpoint = `/${string}`;
type Route = `${HTTPMethod} ${Endpoint}`;
type UppercaseHTTP = Uppercase<HTTPMethod>;
type LowercaseHTTP = Lowercase<HTTPMethod>;

// Recursive types
type JSONValue = string | number | boolean | null | JSONObject | JSONArray;
interface JSONObject {
  [key: string]: JSONValue;
}
interface JSONArray extends Array<JSONValue> {}

// Advanced conditional types
type Diff<T, U> = T extends U ? never : T;
type Filter<T, U> = T extends U ? T : never;
type NonNullable<T> = T extends null | undefined ? never : T;

// Distributive conditional types
type ToArray<T> = T extends any ? T[] : never;
type BoxedValue<T> = { value: T extends any ? T : never };

// Infer with nested conditionals
type UnpackArray<T> = T extends (infer U)[] ? U : T;
type UnpackPromise<T> = T extends Promise<infer U> ? U : T;
type DeepUnpack<T> = T extends Promise<infer U>
  ? DeepUnpack<U>
  : T extends (infer U)[]
    ? DeepUnpack<U>
    : T;

// Complex mapped types
type Getters<T> = {
  [K in keyof T as `get${Capitalize<string & K>}`]: () => T[K];
};

type Setters<T> = {
  [K in keyof T as `set${Capitalize<string & K>}`]: (value: T[K]) => void;
};

// Intersection types
type MixedType = { a: string } & { b: number } & { c: boolean };
type DeepMerge<T, U> = {
  [K in keyof T | keyof U]: K extends keyof T
    ? K extends keyof U
      ? T[K] | U[K]
      : T[K]
    : K extends keyof U
      ? U[K]
      : never;
};

// Variadic tuple types
type Concat<T extends any[], U extends any[]> = [...T, ...U];
type Tail<T extends any[]> = T extends [any, ...infer Rest] ? Rest : never;
type Head<T extends any[]> = T extends [infer First, ...any[]] ? First : never;

// Key remapping in mapped types
type EventHandlers<T> = {
  [K in keyof T as `on${Capitalize<string & K>}Change`]: (newValue: T[K]) => void;
};

// Conditional types with multiple infer
type ConstructorParams<T> = T extends new (...args: infer P) => any ? P : never;
type InstanceType<T> = T extends new (...args: any[]) => infer R ? R : any;

// Advanced template literal types
type CSSProperty = "width" | "height" | "color" | "backgroundColor";
type CSSValue = string | number;
type CSSProperties = {
  [K in CSSProperty]: CSSValue;
};

type DataAttribute = `data-${string}`;
type AriaAttribute = `aria-${string}`;

// Complex utility types
type DeepReadonly<T> = {
  readonly [P in keyof T]: T[P] extends object ? DeepReadonly<T[P]> : T[P];
};

type DeepPartial<T> = {
  [P in keyof T]?: T[P] extends object ? DeepPartial<T[P]> : T[P];
};

// Branded types
type Brand<K, T> = K & { __brand: T };
type USD = Brand<number, "USD">;
type EUR = Brand<number, "EUR">;

// Higher-order types
type Functor<F> = {
  map: <A, B>(f: (a: A) => B) => (fa: F) => F;
};

// Complex generic constraints
type KeysOfType<T, U> = {
  [K in keyof T]: T[K] extends U ? K : never;
}[keyof T];

type PickByType<T, U> = Pick<T, KeysOfType<T, U>>;
type OmitByType<T, U> = Omit<T, KeysOfType<T, U>>;

// Assertion functions
type AssertIsString<T> = T extends string ? T : never;
type AssertIsArray<T> = T extends any[] ? T : never;
