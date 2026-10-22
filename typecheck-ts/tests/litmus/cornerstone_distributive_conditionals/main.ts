// Cornerstone: distributive conditional types
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// Naked type-param check types distribute over unions; wrapped checks do not.

type IsString<T> = T extends string ? true : false;

const distYes: IsString<"a"> = true;
const distNo: IsString<1> = false;
// expect-def-type: distYes = true
// expect-def-type: distNo = false

// Distributive over union: both branches inhabit IsString<"a" | 1>
const distUnionTrue: IsString<"a" | 1> = true;
const distUnionFalse: IsString<"a" | 1> = false;
const distUnionBad: IsString<"a" | 1> = "no";
// expect-diagnostic: TS2322 "distUnionBad: IsString<"a" | 1> = \"no\""

// Non-distributive: whole union checked at once → false
type Wrapped<T> = [T] extends [string] ? true : false;
const wrapped: Wrapped<"a" | 1> = false;
// expect-def-type: wrapped = false

type ExtractStr<T> = T extends string ? T : never;
const onlyA: ExtractStr<"a" | "b" | 1> = "a";
const onlyB: ExtractStr<"a" | "b" | 1> = "b";
const badNum: ExtractStr<"a" | "b" | 1> = 1;
// expect-diagnostic: TS2322 "badNum: ExtractStr<"a" | "b" | 1> = 1"
