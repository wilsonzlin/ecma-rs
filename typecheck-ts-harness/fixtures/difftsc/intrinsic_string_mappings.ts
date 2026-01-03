type Loud = Uppercase<"hello">;
type Quiet = Lowercase<"HELLO">;
type Capital = Capitalize<"hello">;
type Uncapital = Uncapitalize<"Hello">;

export const loud: Loud = "HELLO";
             // ^?
export const quiet: Quiet = "hello";
export const capital: Capital = "Hello";
export const uncapital: Uncapital = "hello";

// Diagnostic mismatch case: `Uppercase` should evaluate to `"HELLO"`.
export const mismatch: Loud = "hello";
