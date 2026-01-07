# @minify-js/node

Node.js bindings for the Rust `minify-js` library.

## Install

```bash
npm i @minify-js/node
```

## Usage

```js
const {minify} = require('@minify-js/node');
// or: import {minify} from '@minify-js/node';

const src = Buffer.from('let x = 1;', 'utf-8');
const out = minify('global', src);
// out is a Buffer containing the minified source
```

`minify(topLevelType, src, options?)` accepts:

- `'global'` or `'module'` for `topLevelType`
- a `string` or `Buffer` of UTF-8 JavaScript/TypeScript for `src`
- an optional `options` object (see `index.d.ts`) controlling parsing and TypeScript lowering

It returns a `Buffer` containing the minified JavaScript output. Buffer inputs
must be valid UTF-8.

### Options

The optional third parameter can be used to control the parser dialect and TS
erasure semantics:

```js
const {minify} = require("@minify-js/node");

// Keep TypeScript const enums as runtime enums (instead of inlining/erasing).
const out = minify("module", "const enum E { A = 1 } export const x = E.A;", {
  dialect: "ts",
  preserveConstEnums: true,
});
```

If the input cannot be minified (e.g. due to syntax errors), an `Error` is
thrown containing rendered diagnostics for the input file. The error also has
an optional `diagnostics` property with structured diagnostics.
