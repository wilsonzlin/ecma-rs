// @filename: alpha.ts
// @noLib: true
// @lib: es2020
// @types: example
// @moduleResolution: node16
// @useDefineForClassFields: false
// @noUncheckedIndexedAccess: true
// @declaration: true
export class Alpha {
  field = 1;
}

// @filename: node_modules/@types/example/index.d.ts
declare const example: string;

// @filename: beta.ts
// @target: ES2020
// @module: nodenext
export const beta = new Alpha();
export const value = example;
