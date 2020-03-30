> ⚠ **Warning!** This project is very much a work-in-progress and does not
> actually work yet! ⚠

# `peepmatic`

**`peepmatic` is a DSL and compiler for generating peephole optimizers for
[Cranelift][].**

![Rust](https://github.com/fitzgen/peepmatic/workflows/Rust/badge.svg)

The user writes a set of optimizations in the DSL, and then `peepmatic` compiles
the set of optimizations into an efficient peephole optimizer:

```
DSL ----peepmatic----> Peephole Optimizer
```

The generated peephole optimizer has all of its optimizations' left-hand sides
collapsed into a compact automata that makes matching candidate instruction
sequences fast.

The DSL's optimizations may be written by hand or discovered mechanically with a
superoptimizer like [Souper][]. Eventually, `peepmatic` should have a verifier
that ensures that the DSL's optimizations are sound, similar to what [Alive][]
does for LLVM optimizations.

Currently, `peepmatic` is targeting peephole optimizers that operate on
Cranelift's clif intermediate representation. The intended next target is
Cranelift's new backend's "vcode" intermediate representation. Supporting
non-Cranelift targets is not a goal.

[Cranelift]: https://github.com/bytecodealliance/wasmtime/tree/master/cranelift#readme
[Souper]: https://github.com/google/souper
[Alive]: https://github.com/AliveToolkit/alive2

## A DSL for Optimizations

A single peephole optimization has two parts:

1. A **left-hand side** that describes candidate instruction sequences that the
   optimization applies to.
2. A **right-hand side** that contains the new instruction sequence that
   replaces old instruction sequences that the left-hand side matched.

A left-hand side may bind sub-expressions to variables and the right-hand side
may contain those bound variables to reuse the sub-expressions. The operations
inside the left-hand and right-hand sides are a subset of clif operations.

Let's take a look at an example:

```lisp
(=> (imul $x 2)
    (ishl $x 1))
```

As you can see, the DSL uses S-expressions. (S-expressions are easy to parse and
we also have a bunch of nice parsing infrastructure for S-expressions already
for our [`wat`][wat] and [`wast`][wast] crates.)

[wat]: https://crates.io/crates/wat
[wast]: https://crates.io/crates/wast

The left-hand side of this optimization is `(imul $x 2)`. It matches integer
multiplication operations where a value is multiplied by the constant two. The
value multiplied by two is bound to the variable `$x`.

The right-hand side of this optimization is `(ishl $x 1)`. It reuses the `$x`
variable that was bound in the left-hand side.

This optimization replaces expressions of the form `x * 2` with `x << 1`. This
is sound because multiplication by two is the same as shifting left by one for
binary integers, and it is desirable because a shift-left instruction executes
in fewer cycles than a multiplication.

The general form of an optimization is:

```lisp
(=> <left-hand-side> <right-hand-side>)
```

### Variables

Variables begin with a dollar sign and are followed by lowercase letters,
numbers, hyphens, and underscores: `$x`, `$y`, `$my-var`, `$operand2`.

Left-hand side patterns may contain variables that match any kind of
sub-expression and give it a name so that it may be reused in the right-hand
side.

```lisp
;; Replace `x + 0` with simply `x`.
(=> (iadd $x 0)
    $x)
```

Within a pattern, every occurrence of a variable with the same name must match
the same value. That is `(iadd $x $x)` matches `(iadd 1 1)` but does not match
`(iadd 1 2)`. This lets us write optimizations such as this:

```lisp
;; Xor'ing a value with itself is always zero.
(=> (bxor $x $x)
    (iconst 0))
```

### Constants

We've already seen specific integer literals and wildcard variables in patterns,
but we can also match any constant. These are written similar to variables, but
use uppercase letters rather than lowercase: `$C`, `$MY-CONST`, and `$OPERAND2`.

For example, we can use constant patterns to combine an `iconst` and `iadd` into
a single `iadd_imm` instruction:

```lisp
(=> (iadd (iconst $C) $x)
    (iadd_imm $C $x))
```

### Nested Patterns

Patterns can also match nested operations with their own nesting:

```lisp
(=> (bor $x (bor $x $y))
    (bor $x $y))
```

### Preconditions and Unquoting

Let's reconsider our first example optimization:

```lisp
(=> (imul $x 2)
    (ishl $x 1))
```

This optimization is a little too specific. Here is another version of this
optimization that we'd like to support:

```lisp
(=> (imul $x 4)
    (ishl $x 2))
```

We don't want to have to write out all instances of this general class of
optimizations! That would be a lot of repetition and could also bloat the size
of our generated peephole optimizer's matching automata.

Instead, we can generalize this optimization by matching any multiplication by a
power of two constant `C` and replacing it with a shift left of `log2(C)`.

First, rather than match `2` directly, we want to match any constant variable `C`:

```lisp
(imul $x $C)
```

Note that variables begin with lowercase letters, while constants begin with
uppercase letters. Both the constant pattern `$C` and variable pattern `$x` will
match `5`, but only the variable pattern `$x` will match a whole sub-expression
like `(iadd 1 2)`. The constant pattern `$C` only matches constant values.

Next, we augment our left-hand side's pattern with a **precondition** that the
constant `$C` must be a power of two. Preconditions are introduced by wrapping
a pattern in the `when` form:

```lisp
;; Our new left-hand side, augmenting a pattern with a precondition!
(when
  ;; The pattern matching multiplication by a constant value.
  (imul $x $C)

  ;; The precondition that $C must be a power of two.
  (is-power-of-two $C))
 ```

In the right-hand side, we use **unquoting** to perform compile-time evaluation
of `log2($C)`. Unquoting is done with the `$(...)` form:

```lisp
;; Our new right-hand side, using unqouting to do compile-time evaluation of
;; constants that were matched and bound in the left-hand side!
(ishl $x $(log2 $C))
```

Finally, here is the general optimization putting our new left-hand and
right-hand sides together:

```lisp
(=> (when (imul $x $C)
          (is-power-of-two $C))
    (ishl $x $(log2 $C)))
```

### Bit Widths

Similar to how Cranelift's instructions are bit-width polymorphic, `peepmatic`
optimizations are also bit-width polymorphic. Unless otherwise specified, a
pattern will match expressions manipulating `i32`s just the same as expressions
manipulating `i64`s, etc... An optimization that doesn't constrain its pattern's
bit widths must be valid for all bit widths:

* 1
* 8
* 16
* 32
* 64
* 128

To constrain an optimization to only match `i32`s, for example, you can use the
`bit-width` precondition:

```lisp
(=> (when (iadd $x $y)
          (bit-width $x 32)
          (bit-width $y 32))
    ...)
```
