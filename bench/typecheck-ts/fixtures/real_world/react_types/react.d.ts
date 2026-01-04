// A trimmed-down React-like declaration file intended to stress `.d.ts` parsing
// and generic instantiation without pulling in the full @types/react package.

export type Key = string | number;

export interface Attributes {
  key?: Key | null;
}

export type ReactText = string | number;

export interface ReactElement<P = unknown> {
  type: unknown;
  props: P;
  key: Key | null;
}

export type ReactChild = ReactText | ReactElement;
export type ReactNode = ReactChild | boolean | null | undefined;

export interface FunctionComponent<P = {}> {
  (props: P): ReactElement<any> | null;
  defaultProps?: Partial<P>;
}

export type FC<P = {}> = FunctionComponent<P>;

export type PropsWithChildren<P> = P & { children?: ReactNode };

export type ElementType<P = any> = string | FunctionComponent<P>;

export type Exclude<T, U> = T extends U ? never : T;
export type Pick<T, K extends keyof T> = { [P in K]: T[P] };
export type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;

export type LibraryManagedAttributes<C, P> = C extends { defaultProps: infer D }
  ? Omit<P, keyof D> & Partial<D>
  : P;

export interface DOMAttributes<T> {
  children?: ReactNode;
  onClick?: (event: MouseEvent) => void;
}

export interface HTMLAttributes<T> extends DOMAttributes<T> {
  id?: string;
  className?: string;
  tabIndex?: number;
}

export interface ButtonHTMLAttributes<T> extends HTMLAttributes<T> {
  disabled?: boolean;
  type?: "button" | "submit" | "reset";
}

export interface InputHTMLAttributes<T> extends HTMLAttributes<T> {
  value?: string;
  onChange?: (value: string) => void;
}

export interface JSXIntrinsicElements {
  div: HTMLAttributes<HTMLDivElement>;
  span: HTMLAttributes<HTMLSpanElement>;
  button: ButtonHTMLAttributes<HTMLButtonElement>;
  input: InputHTMLAttributes<HTMLInputElement>;
  a: HTMLAttributes<HTMLAnchorElement> & { href?: string };
  ul: HTMLAttributes<HTMLUListElement>;
  li: HTMLAttributes<HTMLLIElement>;
}

export type ComponentProps<T extends ElementType> = T extends FunctionComponent<infer P>
  ? P
  : T extends keyof JSXIntrinsicElements
    ? JSXIntrinsicElements[T]
    : never;

export declare function createElement<T extends ElementType>(
  type: T,
  props: LibraryManagedAttributes<T, ComponentProps<T>> | null,
  ...children: ReactNode[]
): ReactElement<ComponentProps<T>>;

