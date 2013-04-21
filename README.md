Some truly beautiful code. They are extremely short, yet extremely powerful.

* cps.ss - CPS transformer without administrative redexes, with
  treatment for conditionals and tail calls

* compiler.ss - an optimizing compiler from Scheme to X64 assembly

* meta-interp.ss - a meta-circular interpreter that can interpret
  itself to any level

* infer.ss - a Hindly-Milner style type inferencer for the lambda
  calculus that can infer infinite types (such as delta, omega, and
  the Y-combinator)

* bottom-up-typing.ss - a bottom-up type inference algorithm for
  Hindley-Milner system

* mk-c.ss - a modified implementation of the logic language miniKanren
  with a constraint-based negation operator

* interp-call-by-value.ss - a simple call-by-value interpreter

* interp-call-by-name.ss - a simple call-by-name interpreter

* interp-lazy.ss - an interpreter with lazy semantics similar to Haskell

* interp-delim.ss - a simple interpreter with delimited continuation
  operators (shift/reset/shift0/reset0)

* lazy-ski.ss - a compiler from lambda calculus to "lazy combinators"

* encoding.scm - encodings of various things in the lambda calculus,
  used by some other code (such as lazy-ski.ss)

* pmatch.scm - supporting macro for pattern matching, used by some
  other programs here
