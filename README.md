# `pattern-matcher`

`pattern-matcher` is a library for compiling pattern matching to
efficient decision trees. The implementation is based on Luc
Maranget's papers [Compiling Pattern Matching to Good Decision
Trees][paper] and [Warning for pattern matching][warn-paper].

This library is organized to provide a generic interface to make it
suitable for all sorts of languages. In addition to generating a
decision tree, it also produces unmatched patterns, in the case of
non-exhaustive pattern matching and reports any redundant patterns, so
that it can be used to generate error or warning messages. Note that
guarded patterns are not properly supported.

The documentation contains an example on how to use the library. The
[test](test/) directory also contains an example for a very simple
language in [Calculus][calculus]. It uses
[QuickCheck](http://hackage.haskell.org/package/QuickCheck) to verify
the correctness of the pattern matching algorithm, by generating
random term of this language and verifying they evaluate to the same
result after compilation.

[test-dir]: test/
[calculus]: test/Calculus.hs
[paper]: http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf
[warn-paper]: http://www.journals.cambridge.org/abstract_S0956796807006223
[matcher]: src/Language/Pattern/Compiler.hs
