# minify-js design doc

## Parse

Convert source JS into AST.

## Symbolize

Track and store definitions and usages of symbols (variables, classes, functions) in a tree of scopes (top level/module, function, block).

## Optimize

Convert to IR and perform optimizations.

IR is more regularized, and we can apply more optimizations in a safer simpler manner.

Our goal is minification. The belief is that IR optimization will achieve more than AST transformations.

Not all IR optimizations are done. Ones that improve performance but increase code size go against objective, so aren't done.

### Process

Subtrees within the AST, typically functions, are the unit for processing individually.

The tree is walked in execution order, emitting a flat list of IR statements like `goto`, `load`, and `binop`.

This is then split into basic blocks at jump points, forming a control flow graph.

It is converted into SSA form for simpler processing.

Several passes of optimizations are done until converged onto fixed point (i.e. optimization pass did not result in any changes).

It is converted back out of SSA form.

## Minification

This takes the low-level optimized IR and turns it into minifed JS.

### Reconstruction

Each CFG is transformed back into AST.

### Name minification

For the most optimal (i.e. short) naming of all symbols (variables, functions, classes), we can think of each unique name identified by a distinct integer. The goal is to minimize this set of unique integers needed to represent all symbols in the program. Then, it's possible to achieve minimal total bytes used by identifiers by assigning the shortest unique string to each integer, ideally by frequency of use. An additional constraint is that resulting identifiers must not break original code semantics due to clashing in scope.

Algorithm:

- All foreign vars should be allocated an integer first, sequentially from zero
- Then, for each function:
  - Map each symbol to the next available number, starting from zero, skipping over any number for a foreign var used in the function or any inner function (otherwise it will shadow).
- Then, map number to identifier. This is static and doesn't differ by function, context, usage, etc.
  - Skip over any reserved keywords and used global vars.

### Emitting

The AST is walked and JS is emitted in *minimal* form: reduce whitespace, semicolons, etc. as much as possible.
