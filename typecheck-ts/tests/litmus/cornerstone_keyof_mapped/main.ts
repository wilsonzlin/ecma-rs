// Cornerstone: keyof duality + mapped types (modifiers / as-remapping)
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// keyof (A|B) = keyof A & keyof B; keyof (A&B) = keyof A | keyof B.
// Mapped types iterate keys and honor optional / `as` remapping.

type A = { a: number; shared: string };
type B = { b: boolean; shared: string };

// keyof (A|B) = common keys only
const keysUnion: keyof (A | B) = "shared";
const keysUnionBad: keyof (A | B) = "a";
// expect-diagnostic: TS2322 "keysUnionBad: keyof (A | B) = \"a\""

// keyof (A&B) = all keys
const keysInterA: keyof (A & B) = "a";
const keysInterB: keyof (A & B) = "b";
const keysInterShared: keyof (A & B) = "shared";
const keysInterBad: keyof (A & B) = "missing";
// expect-diagnostic: TS2322 "keysInterBad: keyof (A & B) = \"missing\""

// Mapped + optional + as-remapping
const partial: { [K in keyof A]?: A[K] } = { a: 1 };
// expect-def-type: partial = { a?: number; shared?: string }

const remapped: { [K in "a" | "b" as `${K}Id`]: number } = { aId: 1, bId: 2 };
// expect-def-type: remapped = { aId: number; bId: number }
