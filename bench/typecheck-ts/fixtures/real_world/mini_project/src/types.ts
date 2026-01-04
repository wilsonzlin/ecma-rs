export interface User {
  id: string;
  name: string;
  email?: string;
}

export interface Todo {
  id: string;
  title: string;
  completed: boolean;
  assignee?: User;
  tags: string[];
}

export type ApiError =
  | { kind: "network"; message: string }
  | { kind: "http"; status: number; body: string }
  | { kind: "decode"; message: string };

export type DeepReadonly<T> = T extends (...args: any[]) => any
  ? T
  : T extends readonly (infer U)[]
    ? ReadonlyArray<DeepReadonly<U>>
    : T extends object
      ? { readonly [K in keyof T]: DeepReadonly<T[K]> }
      : T;

