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

`minify(topLevelType, src)` accepts `'global'` or `'module'` for `topLevelType` and a `Buffer` containing UTF-8 JavaScript for `src`, returning a `Buffer` with the minified output.
