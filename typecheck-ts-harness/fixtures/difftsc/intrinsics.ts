export const upper: Uppercase<"hello"> = "HELLO";
             // ^?

export const lower: Lowercase<"HELLO"> = "hello";
             // ^?

export const capitalize: Capitalize<"hello"> = "Hello";
             // ^?

export const uncapitalize: Uncapitalize<"Hello"> = "hello";
             // ^?

export const union: Uppercase<"a" | "b"> = Math.random() > 0.5 ? "A" : "B";
             // ^?

export const template: Uppercase<`foo${string}bar`> = "FOOXBAR";
             // ^?

export const noInfer: NoInfer<"x"> = "x";
             // ^?
