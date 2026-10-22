// Cornerstone: distributive conditional types
type IsString<T> = T extends string ? true : false;

export const distYes: IsString<"a"> = true;
export const distNo: IsString<1> = false;

// Distributivity proved by inhabitance of both branches + rejection of string.
const distUnionTrue: IsString<"a" | 1> = true;
const distUnionFalse: IsString<"a" | 1> = false;
const distUnionBad: IsString<"a" | 1> = "no";

type ExtractStr<T> = T extends string ? T : never;
export const onlyA: ExtractStr<"a" | "b" | 1> = "a";
const badNum: ExtractStr<"a" | "b" | 1> = 1;

type Wrapped<T> = [T] extends [string] ? true : false;
export const wrapped: Wrapped<"a" | 1> = false;
