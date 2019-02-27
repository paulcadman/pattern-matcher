# `pattern-matcher`

`pattern-matcher` is a library for compiling pattern matching to
efficient decision trees. The implementation is based on Luc
Maranget's papers [Compiling Pattern Matching to Good Decision
Trees][paper] and [Warning for pattern matching][warn-paper].

This library is organized to provide a generic interface to make it
suitable for all sorts of languages. In addition to generating a
decision tree, it also produces unmatched patterns, in the case of
non-exhaustive pattern matching and reports any redundant patterns, so
that it can be used to generate error or warning messages.

# Decision trees

Decision trees can be thought of as cascading switches. Consider this
Haskell example:
```haskell
case e of
  ([], 0)    -> 0
  (_ : _, 1) -> 1
```

A simple compilation to a decision tree will give something like the following:
```
e +--- (,) ---> e.0 +---  [] ----> e.1 +---- 0 ----> 0
	                |                  |
					|				   \---- _ ----> FAIL
					|
					\--- _:_ ----> e.1 +---- 1 ----> 1
					                   |
									   \---- _ ----> FAIL
```

We can see that pattern matching is non-exhaustive (here the pattern
`(_, 2)` is not matched for instance) from the presence of `FAIL`
leaves.

Compiling to decision trees is not the only strategy for compiling
pattern-matching. See for instance, Augustsson's [Compiling pattern
matching](https://dl.acm.org/citation.cfm?id=5303) that uses
backtracking automata. Unlike backtracking automata, decision trees
have the advantage of testing any expression at most once, but do not
guarantee a linear code size.

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

Below is a detailed example of how to use the library for a similar
language.The language is typed and supports variables, integer and
lists, as such:
```math
\begin{aligned}
\tau &::= \mathrm{int}\ |\ \mathrm{list}\ \tau \\
\mathrm{pat}_\tau &::= v_\tau\ |\ c\ |\ \ []_{\mathrm{list}\ \tau}\ |\
\mathrm{pat}_{\tau} ::\ \mathrm{pat}_{\mathrm{list}\ \tau}\ |\
(\mathrm{pat}_\tau | \mathrm{pat}_\tau)
\end{aligned}
```

Represented in Haskell by:

```haskell
data Typ     = TInt
             | TList Typ
data Pattern = VarPat Typ  String
             | IntPat      Int
             | NilPat  Typ                  -- NilPat typ has type TList typ
             | ConsPat Typ Pattern Pattern  -- ConsPat typ _ _ has type TList typ
             | OrPat       Pattern Pattern
```

To convert `Pattern`s to `Skel`, we first need to define the type of `tag`s:
```haskell
data Tag = NilTag | ConsTag Typ | IntTag Int
```

and then convert by:
```haskell
toSkel                    :: Pattern -> [Skel String Tag]
toSkel (VarPat typ var)   = [WildSkel (rangeOfTyp typ) (Just var)]
toSkel (IntPat i)         = [ConsSkel (cons (IntTag i) [])]
toSkel (NilPat _)         = [ConsSkel (cons NilTag [])]
toSkel (ConsPat typ p ps) = [ ConsSkel (cons (ConsTag typ) [subp, subps])
                            | subp  <- toSkel p
                            , subps <- toSkel ps
                            ]
toSkel (OrPat p1 p2)      = toSkel p1 ++ toSkel p2
```

`rangeOf` returns the range of `tag`s a pattern of a certain type can
have:
```haskell
rangeOf :: Typ -> [Tag]
rangeOf TInt        = fmap IntTag [minBound .. maxBound]
rangeOf (TList typ) = [NilTag, ConsTag typ]
```

It is then easy to make `Tag` an instance of `IsTag`:
```haskell
instance IsTag Tag where
  tagRange NilTag     = [NilTag, ConsTag]
  tagRange ConsTag    = [NilTag, ConsTag]
  tagRange (IntTag j) = fmap IntTag [minBound..maxBound]

  subTags NilTag        = []
  subTags (ConsTag typ) = [rangeOf typ, rangeOf (TList typ)]
  subTags (IntTag _)    = []
```

We can then use either `match` or `anomalies` to compile or analyze a
set of patterns, choosing a heuristic. You may want to look at the
documentation for heuristics to decide which one to choose.

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
[warn-paper]: http://www.journals.cambridge.org/abstract_S0956796807006223
[matcher]: src/Language/Pattern/Matcher.hs
[heuristics]: src/Language/Pattern/Heuristics.hs
