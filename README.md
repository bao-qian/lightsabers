* cps.ss - CPS transformer without administrative redexes (10+ years of
  research, finished independently as a weekly homework)

* compiler.ss - optimizing compiler from Scheme to X64 assembly

* meta-interp.ss - meta-circular interpreter that can interpret itself
  to any level

* infer.ss - Hindly-Milner style type inferencer for lambda calculus
  (without polymorphic types)

* mk-c.ss - modified implementation of the logic language miniKanren
  with constraint-based negation operator

* interp-call-by-value.ss - simple call-by-value interpreter

* interp-call-by-name.ss - simple call-by-name interpreter

* interp-lazy.ss - interpreter with lazy semantics

* interp-delim.ss - simple interpreter with delimited continuation
  operators (shift/reset/shift0/reset0)

* lazy-ski.ss - compiler from lambda calculus to "lazy combinators"

* cek.ss - a "reversible" CEK abstract machine which can run forwards and
  backwards, and change directions any any time. This is one night's research.

* encoding.scm - "church encoding" of various things in the lambda
  calculus, used by some other code (e.g. lazy-ski.ss)

* pmatch.scm - supporting macro for pattern matching, used by some
  other programs here (compatible with most Scheme implementations)
