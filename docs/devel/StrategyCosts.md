# Strategy Costs and the Cost-Band Ladder

*2026 — class names and values checked against the current sources
(`key.core` and `key.ncore.calculus`).*

!!! warning "Status: open pull request"
    The cost vocabulary described on this page (`CostBand`, `CombinationCost`,
    the theory-local cost holders) is **not yet merged** — it is introduced by
    an open pull request and this page is published together with it.
    *([pull request #3904](https://github.com/KeYProject/key/pull/3904))*

KeY's automated proof search is **cost-based**: for every applicable rule the
strategy computes an integer cost, and the
[rule-application pipeline](RuleApplicationPipeline.md) applies the cheapest
one. **The smaller the cost, the earlier the rule is applied.** Costs are a
search heuristic only; they never affect soundness.

The strategy is composed of **component strategies**, one per theory
(first-order logic, integer arithmetic, symbolic execution, strings,
heap/JavaDL). A component strategy assigns costs to **rule sets** — the groups
that taclets join with their `\heuristics(...)` clause. If several component
strategies assign a cost to the same rule application, the values are **added**.
All costs are therefore numbers on **one common scale**: which rule is applied
next is decided by comparing these numbers, no matter which theory they come
from — so a cost chosen in one theory always also competes with the rules of
every other theory.

This page explains the vocabulary in which those numbers are written, how to
choose a cost, and — only when necessary — how to extend the vocabulary. It is
background for [implementing strategies and macros](ExtendingKeY.md).

## The three layers

| Layer | Where | Holds |
|---|---|---|
| **`CostBand`** | `key.ncore.calculus`, `org.key_project.prover.strategy.costbased` | the shared cross-theory priority ladder |
| **`CombinationCost`** | `key.core`, `de.uka.ilkd.key.strategy` | costs whose meaning involves more than one theory |
| **theory-local holders** | `key.core`, `de.uka.ilkd.key.strategy` | the internal ordering of a single theory |

The theory-local holders are `FOLCost`, the integer-arithmetic holders
(`PolynomialCost`, `LinearEquationCost`, `LinearInequationCost`,
`NonlinearArithmeticCost`, `DivModCost`), `SymExCost`, `StringCost`,
`JavaCardDLCost` and `HeapSelectCost`. They are plain classes with
`static final long` constants. A strategy imports them statically (so call
sites read as bare names) and assigns them with
`bindRuleSet(dispatcher, "ruleSetName", cost)`, which gives the cost to all
taclets in that rule set.

## The band ladder

`CostBand` is an `enum` of named tiers, from most eager (smallest) to least.

| Band | Value | Meaning |
|---|---|---|
| `BLOCK_CONTRACT` | `Long.MIN_VALUE` | apply a block/loop contract instead of executing the block |
| `LOOP_INVARIANT` | −20000 | apply a loop invariant instead of unrolling |
| `CLOSE` | −15000 | close the goal (eager closure is completeness-neutral) |
| `REWRITE` | −11000 | one-step simplification and decidable ground rewrites (`concrete`) |
| `SUBST` | −10000 | force a pending substitution / eager equality (`try_apply_subst`) |
| `ELIMINATE` | −8000 | eliminate updates and literals |
| `DECOMPOSE` | −7000 | non-splitting sequent decomposition (alpha rules, update-apply-on-update) |
| `TYPE` | −6000 | type reasoning (delta rules, type hierarchy) |
| `NORMALIZE` | −5000 | canonicalize / order / commute terms |
| `SIMPLIFY` | −4500 | safe, size-reducing definitional simplification and SE steps |
| `EXECUTE` | −4000 | a symbolic-execution program step / state merge |
| `SOLVE` | −3000 | solve direct (in)equations; apply query axioms |
| `ENLARGE` | −2000 | useful but size-increasing simplification (e.g. comprehension / map unfolding) |
| `PREFER` | −500 | minor local structural preference |
| `DEFAULT` | 0 | no strategic bias — apply in due (age) order |
| `DEFER` | 500 | lazy definitional unfolding, applied only when needed |
| `DEFER_STRONG` | 10000 | strongly defer |
| `LAST_RESORT` | 1000000 | finite last resort — reachable, but only when nothing else applies |

Two entries deserve a closer look. **`DEFAULT` (0)** has the same effect as
assigning no cost at all — only rule sets that are given a cost contribute to a
rule's sum. Assigning `DEFAULT` is therefore a documented decision ("no
strategic bias — apply in due order"), not a technical necessity.
**`DEFER` / `DEFER_STRONG`** are positive: they *add* cost, so every cheaper
rule is applied first and the deferred rule — typically a lazy definitional
unfolding — fires only once nothing cheaper is applicable. Rules that must
never fire automatically are given infinite cost (`inftyConst()`), not a band.

## Choosing a rule's cost

Decide top-down: first the layer, then the exact value.

**1. Which layer?**

- **Cross-theory tier.** If the rule's *role* matches the documented meaning of
  a band — it closes the goal, it is a decidable rewrite, it lazily unfolds a
  definition — give its rule set that band's cost:
  `bindRuleSet(d, "ruleSet", CostBand.CLOSE.cost())`. Match by *meaning*, never
  because a value happens to equal a band: two unrelated rules may cost the same
  number and still belong to different layers. (For example, a modal-tautology
  closure and a substitution both cost −10000, but only the latter is `SUBST`.)
- **Theory-internal ordering.** If the cost only orders rules *within one
  theory* — which normalisation step runs before which — add a named constant to
  that theory's holder. Name it for *what it achieves*, not after the rule-set
  string. If it builds on a sibling constant, write the arithmetic
  (`MERGE_POINT_SKIP = MERGE_RULE - 1000`) so the relationship cannot silently
  drift apart.
- **Shared between theories.** If the value's *meaning* involves several
  theories, it belongs in `CombinationCost` — see
  [when a cost is shared between theories](#when-a-cost-is-shared-between-theories).

**2. Fine placement.**

Within a band, fine ordering is a small delta on the tier:

```java
CostBand.NORMALIZE.cost()      // the band's cost (-5000)
CostBand.PREFER.at(300)        // band + delta = -200: same tier, ordered
                               // against its in-band neighbours
```

Both return the cost as a constant strategy feature, ready to use in
`bindRuleSet` and inside feature terms; the raw number is available as
`value()`. A delta keeps the rule in the same tier; a larger step belongs in a
different band, not in a delta. Theory-local holders need no `at(..)`: a holder is a
plain list of constants, so a finer step is simply one more named constant (or
arithmetic on a sibling, as above).

### How the layers relate

Every cost is a number on the one common scale, so the layers differ only in
what a value *means*: a `CostBand` names a coarse tier that has the same
meaning across all theories; a theory-local constant is an absolute value that
orders one theory's steps among each other. Theory-local constants are
deliberately **not** written relative to a band: this way, retuning a band
moves exactly those rules that were placed on it — and nothing inside the
theories. The flip side is that the cross-theory priority of a theory-local
value is decided by its numeric value alone. When picking one, look at the
ladder to see between which tiers it falls: that determines which other
theories' rules it runs before.

## When a cost is shared between theories

`CombinationCost` holds the costs that no single theory owns. A cost belongs
there in two situations:

1. **More than one strategy assigns a cost to the same rule set.** For such
   rule sets `ModularJavaDLStrategy` picks which strategy's cost applies,
   depending on the term the rule is applied to — for `apply_equations`, for
   example, integer terms get the integer strategy's cost, all others the FOL
   strategy's. The two values are two halves of one decision and must agree, so
   the constant lives here (`ORDERED_REWRITING`). If two strategies assign
   costs to the same rule set without such a registered resolution, strategy
   construction fails immediately — the decision has to be made consciously.
2. **One taclet belongs to rule sets of different strategies.** The costs are
   then added, so the quantity that was actually tuned is the sum, not either
   part. For example, the `applyEq` taclet is both in `apply_equations` and in
   the heap rule set `apply_select_eq`; the heap-side constant is derived from
   the tuned sum (`APPLY_SELECT_EQ_EFFECTIVE`).

A theory-local rule may also reference a `CombinationCost` constant when
sharing that level is intended — retuning the shared level then moves the
coupled rule with it.

## Extending — only when necessary

- **Add a theory-local constant** — the common case, and cheap: a new named
  `static final long` in the theory's holder. No cross-theory impact; verifying
  with [runAllProofs](Testing/RunAllProves.md) suffices.
- **Add or relate a `CombinationCost` constant** — only when a value is
  genuinely cross-theory in one of the two ways above. Keep both sides
  connected through the shared constant.
- **Add or change a `CostBand` tier** — rare and high-impact. A new tier is
  only justified if the level matters *across* theories; ordering inside a
  single theory belongs in that theory. Changing a band's value, or its order
  relative to other bands, shifts the search of **all** proofs.

!!! warning "Verifying a cost change"
    Cost changes never affect soundness, but they change which proof is found
    and how fast. Verify every change with a full
    [runAllProofs](Testing/RunAllProves.md); after a `CostBand` or
    `CombinationCost` change, additionally compare representative proofs node
    for node against the previous costs. Respect the ordering constraints noted
    on the bands — in particular `BLOCK_CONTRACT` must stay cheaper than
    `REWRITE` and all symbolic-execution rules, otherwise a block starts
    executing instead of being contracted.
