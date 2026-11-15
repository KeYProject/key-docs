---
approved: mu 2026-06-19
author: Mattias Ulbrich
date: August 2011
valid_for: KeY since 2011
updated: KeY 2.12
---

# Embedding JavaDL expressions and functions into JML expressions

JML is the standard specification language for KeY (JML&starf; more
precisely). Though it is still possible to specify JavaDL-contracts in `.key`
files, the formalism with model fields, ghost state etc. is really centered on
JML.

The KeY implementation is a bit inert when it comes to extending the JML syntax.
However, often we want to quickly assess a new axiomatisation and want to use it
in the code directly.

An extension of the parser provides us with this possibility now.

## Escaping JavaDL function symbol names

In all JML specifications (also in set statements), function symbols known in
JavaDL can be used in JML if the name is prefixed with `\dl_`.

For instance, consider
```
   \functions {
      int foo(int);
      int bar;
   }
```

we can now refer to the term foo(5) from within JML using `\dl_foo(5)`. The term
`bar` must, however, for technical reasons be succeeded by (), i.e., `\dl_bar()`.
This works for predicate symbols, too.

If the first argument of the symbol is of type `Heap` and the number of actual
parameters is smaller than number of formal parameters, the program variable
"heap" (the current heap) is implicitly added as first parameter. Example:

In KeY:
```
\functions { Seq arr2seq(Heap, Object) }
```

In JML (e.g.):
```
//@ ensures \dl_arr2seq(arrayObject) == \emptySeq;
```
equivalent to

```
//@ ensures \dl_arr2seq(\dl_heap(), arrayObject) == \emptySeq;
```

## The weakest-precondition escape `\dl_wp_apply`

A predefined escape for the specification *inference* of lambda
expressions is `\dl_wp_apply` (Csiky, Ch. 5 and Sec. 6.2.5). It translates
to the JavaDL predicate `wp_apply(heap, f, a1, ..., an)` with the meaning

> *the functional method of the object `f` (bound to the lambda) called
> with the arguments `a1`, ..., `an` completes normally* — i.e., `f` is
> not null, the call throws no exception, and the call terminates.

It is intended for functional interfaces whose model methods give a
default specification: the interface can provide

```
/*@ public normal_behaviour
   @ requires \dl_wp_apply(this, arg);
   @ ensures \result == apply(arg);
   @ accessible \everything; */
public /*@ pure @*/ int apply(int arg);
```

so that a lambda desugared against this interface inherits a
weakest-precondition contract: during verification, KeY infers the actual
precondition piece by piece from the body of the lambda (the postcondition
is satisfied by definition of `apply`).

Like every `\dl_` escape, the first parameter of the underlying predicate
is the implicitly added heap (`\dl_wp_apply(this, x)` in JML becomes
`wp_apply(heap, this, x)` in JavaDL). The predicate is created lazily on
its first use, so no `\functions` declaration is needed to write
`\dl_wp_apply` in JML; it is currently the only escape with this on-demand
registration. Note that the signature `wp_apply(Heap, <arg sorts>)` is
derived from the *first* use — a model that uses `\dl_wp_apply` with
several different functional interface sorts is not supported.

The taclet rules that give `wp_apply` its semantics — `wp_def`, which
expands the predicate into the dynamic-logic formulation above, and
`wp_dep_contract`, a stability rule for the predicate under heap change
(a variant of `useDependencyContract` with an empty dependency set) — are
collected in `weiglLambda/keyForLambda.key` on the KeY classpath. This
file is *not* part of the default rule base: load it as additional rules
of the proof obligation, and make sure it is parsed *before* the JML
contracts of the project are translated (if a contract has already
registered `wp_apply` on demand, the `\predicates` declaration of the file
aborts with "Predicate 'wp_apply' is already defined!"). The `wp_def` rule
currently assumes that the functional interface of the project is named
`IntFunction`, as in the thesis; for a differently named interface, adapt
the schema variable types and the `varcond` of the rule.

See [Specifying lambda expressions](JMLGrammar.md#specifying-lambda-expressions)
for the explicit-specification counterpart.

## Limitations

* There is no sensible error message if a ill-typed term is used in a
set statement.
* The types supported in JML seem to be hardcoded, and cannot be
easily extended.
* Error messages might mislead and could potentially not point to the
right spot in the sources.
