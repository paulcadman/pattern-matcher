# `pattern-matcher`

`pattern-matcher` is a library for compiling pattern matching to
efficient decision trees. The implementation is based on Luc
Maranget's paper « [Compiling Pattern Matching to Good Decision
Trees][paper] ».

The main module is [Language.Pattern.Matcher][matcher]. The user must
provide two functions for the algorithm to proceed: a deconstruction
function, taking a pattern, as represented in the user's source
language and deconstructing it into a more primitive representation;
and a heuristic function, in charge of selecting the optimal column to
match against when several are available. Some heuristics defined in
the paper are implemented in
[Language.Pattern.Heuristics][heuristics].

# Pattern skeleton

This algorithm works on *pattern skeletons*. A skeleton is either a
wild card pattern, eventually binding an identifier, for instance `_`
in OCaml; or a constructor skeleton, made of some tag and subpatterns,
for instance `[]` or `0 :: _`. In that last case, we would represent
`[]` by `Cons "[]" []` and `0 :: _` by `Cons "_::_" [Cons "0" [], Wild
Nothing]`

The algorithm is polymorphic in the type of `tag` used for
constructors, it only relies on them being instances comparable
through the `Ord` typeclass.

# Decision trees

# Heuristics

The [Language.Pattern.Heuristics][heuristics] module gives
implementation for some heuristics proposed and benchmarked in section
8 of [Maranget's paper][paper].

# Example and test

The [test](test/) directory contains an example of the use of this
library for a very simple language in [Calculus][calculus]. It uses
[QuickCheck](http://hackage.haskell.org/package/QuickCheck) to verify
the correctness of the pattern matching algorithm, by generating
random term of this language and verifying they evaluate to the same
result after compilation.

# Caveats

Here are some caveats when using this algorithm.

## Preserving sharing

The presence of or-patterns may duplicate leaves. Consider the
following:

```ocaml
match e with
| 0 | 1 -> x
| _ -> y
```

Compiled to C using `if` statements, we would get:
```c
switch (e) {
case 0: eval(x); break;
case 1: eval(x); break;
default: eval(y); break;
}
```

`x` is duplicated, which might be undesirable if it is a large
expression. To avoid the issue, it might be better to use labels
instead of expressions to present to the pattern matcher and then use
a form of `goto` to allow to preserve sharing of code to take
place. For instance, in C:

```c
switch(e) {
case 0: goto x_lab;
case 1: goto x_lab;
default: goto y_lab;
}

x_lab:
     eval(x);
     goto end_lab;

y_lab:
     eval(y);
     goto end_lab;

end_lab: ...
```

Note that this problem only arises when there are or-patterns in the
match, otherwise no code risks duplication.

## Bottom preservation

Consider an extension of OCaml where empty matches would be
allowed. The following code should throw an exception, because the
inner `match` can never succeed:

```ocaml
match (match [] with) with
| _ -> ()
```

However, if naively compiled, this would produce the tree that always
yield `()`, thus modifying the semantic

[test-dir]: test/
[calculus]: test/Calculus.hs
[paper]: http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf
[matcher]: src/Language/Pattern/Matcher.hs
[heuristics]: src/Language/Pattern/Heuristics.hs
