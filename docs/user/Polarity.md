# Polarity triggers for rewrite taclets

*introduced oct 2012 by Christoph Scheben* 

## THE NEW FEATURE AND ITS MOTIVATION

Triggered by a soundness bug that I introduced last week (fixed again the day
afterwards), I introduced the ability to annotate rewrite-taclets with
a polarity (`\succedentPolarity` or `\antecedentPolarity`) in which the taclet may
be applied. Roughly speaking the polarity is the side of the sequent on which
a formula can be found (at most) if all surrounding junctors have been
decomposed by the corresponding rules. It gives the ability to generalise
rewrite-taclets like

```
wellFormedStoreObject {
    \schemaVar \term Heap h;
    \schemaVar \term Object o;
    \schemaVar \term Field f;
    \schemaVar \term deltaObject x;

       \find(==> wellFormed(store(h, o, f, x)))

        \varcond(\fieldType(f, alpha))

       \replacewith(wellFormed(h) & x = null | (boolean::select(h, x, java.lang.Object::<created>) = TRUE & alpha::instance(x) = TRUE))

       \heuristics(simplify_enlarging)
};
```


which match a formula top-level in the succedent or antecedent of a
sequent (for instance, as in this example, because the taclet is
overapproximating) such that it already can be applied before all
junctors have been decomposed. For instance if the rule above is
formulated as

```
wellFormedStoreObject {
    \schemaVar \term Heap h;
    \schemaVar \term Object o;
    \schemaVar \term Field f;
    \schemaVar \term deltaObject x;

       \find(wellFormed(store(h, o, f, x)))
       \succedentPolarity

       \varcond(\fieldType(f, alpha))

       \replacewith(wellFormed(h) & x = null | (boolean::select(h, x, java.lang.Object::<created>) = TRUE & alpha::instance(x) = TRUE))

       \heuristics(simplify_enlarging)
};
```

it is already applicable in the sequent

```
  wellFormed(h), x = null, (wellFormed(store(h, o, f, x)) -> p) ==>
```

(where p is a predicate) such that the application of the splitting
impLeft rule can be avoided. (Indeed I needed it for exactly this
case, but it is also helpful if for instance the wellformedness
predicate can be decomposed early in other situations.)


DEFINITION OF POLARITY:

A polarity is defined only in particular cases (see below). If the
polarity can not be deduced, then the corresponding taclet is not
applicable.

A polarity is defined only in the following cases:

1. The find-part of the taclet is of type Formula. (For terms in general there
seems to be no meaningful definition.)
2. Let F be the formula matching the find-part in some sequent.  F
may be only a direct or indirect subformula of junctors (AND, OR, NOT,
IMP) or a subformula of the second or third position of an
`\if-then-else` term. For instance the polarity of F in `AND(x, OR(y, NOT(F))) ==>`
would be defined whereas its polarity in
  `F <-> p ==>`
(where p is a predicate) or in
`NOT(\if(F)\then(TRUE)\else(FALSE)) ==>`
is undefined.

Let C(F) be a formula containing F and let C(L) be constructed from
C(F) by replacing F by some literal L .  F has positive polarity in
C(F) , iff (1) the polarity is defined and (2) L occurs at most
positive in the KNF of C(L) .  F has negative polarity in C(F) , iff
(1) the polarity is defined and (2) L occurs at most negative in the
KNF of C(L) . The polarity of F in ==> C(F) is succedent (antecedent)
iff (1) the polarity is defined and (2) F has positive (negative)
polarity in C(F) . The polarity of F in C(F) ==> is succedent
(antecedent) iff (1) the polarity is defined and (2) F has negative
(positive) polarity in C(F) .


## SOUNDNESS OF THE NEW TACLETS AND POSSIBLE APPLICATIONS

It is sound to replace any simple rewrite-taclet (without an add and
without creating or closing branches) which matches on a top-level
formula F in the succedent (antecedent) and replaces it by R by a
taclet which matches F in succedent polarity (antecedent polarity) and
replaces F by R . This is justified by the following proof-sketch: Let
us concentrate w.l.o.g. on the case where F has succedent polarity in
==> C(F) and that F occurs only once in the sequent (this is only for
presentation purposes). The calculus rules for the junctors and for
\if-\then-\else are equivalences. Hence they can be applied in both
directions. Thus if F matches with succedent polarity in a sequent S ,
then we can construct by application of the junctor and for
\if-\then-\else rules a set of sequents S_1, ..., S_n such that F
occurs at most top-level on the succedent of S_1, ..., S_n (by the
definition of succedent polarity). Now the application of the original
rewrite-taclet replaces all (top-level) occurrences of F by R
. Application of the rules which transformed S into S_1, ..., S_n in
the reverse order and in the reverse direction leads the sequent ==>
C(R) . Hence, the more liberal succedent poliarity taclet is sound iff
the corresponding simple rewrite-taclet is sound.

At the moment, only some wellformedness-taclets use the new
`\succedentPolarity` feature. (Sorry that they already went on the
master branch, but this was to fix the soundness problem I had
introduced.)

An other application would be skolemization: one could reformulate the
exLeft and allRight rules with `\antecedentPolarity` and
`\succedentPolarity`, respectively, such that in some cases
skolemization would be possible even if the quantifiers are not
top-level. I think this could helpful at least for the automatic proof
search strategy.

## PROVING CORRECTNESS

The new feature has been given a formal semantics in terms of a
meaning formula as in the paper "Ensuring the Correctness of
Lightweight Tactics for JavaCard Dynamic Logic" of Richard and
co-authors. Moreover, we provided the possibility to prove the
correctness of taclets with the new feature within KeY.
