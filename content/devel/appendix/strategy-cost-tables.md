# Appendix: Strategy Cost Tables

*2026 — values checked against the current sources (`key.core` and
`key.ncore.calculus`).*

This appendix collects every cost constant for reference. See
[Strategy Costs and the Cost-Band Ladder](StrategyCosts.md) for what the layers
mean and how to choose a cost.

## Cost bands

The shared cross-theory ladder (`CostBand`, `key.ncore.calculus`):

--8<-- "includes/costband-table.md"

## Combination costs

Costs whose meaning involves more than one theory (`CombinationCost`,
`key.core`):

| Constant | Value | Meaning |
|---|---|---|
| `ORDERED_REWRITING` | −4000 | demodulation — apply an oriented equation as a rewrite (`apply_equations`); shared by the FOL and integer strategies |
| `CNF_CONVERSION` | −150 | priority of CNF conversion (`apply_equations_andOr`, and FOL's `conjNormalForm`) |
| `APPLY_SELECT_EQ_EFFECTIVE` | −5700 | tuned effective cost of the `applyEq` taclet (`apply_equations` + heap `apply_select_eq`, summed) |

## Theory-local costs

Each component strategy keeps its internal ordering in one or more holders.

### First-order logic — `FOLStrategy`

`FOLCost`:

| Constant | Value | Meaning |
|---|---|---|
| `QUANTIFIER_DISTRIBUTION` | −300 | `distrQuantifier`, `swapQuantifiers` |
| `CNF_RESTRUCTURE` | −35 | CNF associativity / distribution (`cnf_orAssoc`, `cnf_andAssoc`, `cnf_dist`) |
| `REPLACE_KNOWN_UNDER_CONNECTIVE` | 100 | defer `replace_known_right` under an implication/equivalence |
| `CUT_DIRECT_STANDARD` | 100 | standard cost of a direct cut |
| `PULL_OUT_QUANTIFIER` | −20 | preferred direction of the `pullOutQuantifier*` rules |
| `PULL_OUT_QUANTIFIER_REVERSE` | −40 | dispreferred direction of the `pullOutQuantifier*` rules |

### Integer arithmetic — `IntegerStrategy`

Split into sub-holders that anticipate a future split of the integer strategy
into separate sub-strategies.

`PolynomialCost` — polynomial normal-form canonicalisation:

| Constant | Value | Meaning |
|---|---|---|
| `EXPAND` | −120 | `elimSubNeg`, `homo`, `pullOutFactor`, `elimOneLeft/Right` |
| `MUL_ORDER` | −100 | multiplication ordering |
| `MUL_ASSOC` | −80 | multiplication associativity |
| `ADD_ORDER` | −60 | addition ordering |
| `ADD_ASSOC` | −10 | addition associativity |
| `DISTRIBUTE` | −35 | `polySimp_dist` (the `distLeft` sub-case is `DISTRIBUTE + 20`) |
| `PULLOUT_GCD` | −2250 | pull out the gcd of a polynomial |

`LinearEquationCost` — polynomial equation solving:

| Constant | Value | Meaning |
|---|---|---|
| `BALANCE` | −30 | `polySimp_balance`, `polySimp_normalise` |
| `APPLY_EQ_MONOMIAL_TIEBREAK` | 1 | tie-break rider on `ORDERED_REWRITING` for `polySimp_applyEq`; the rigid variant is `+ 1` |

`LinearInequationCost` — Omega / Fourier-Motzkin inequation solving:

| Constant | Value | Meaning |
|---|---|---|
| `PROPAGATION` | −2400 | propagate inequations |
| `PULLOUT_GCD_CONFLUENT` | −2150 | general gcd normalisation — confluent, applied eagerly |
| `SATURATE` | −1900 | saturate the inequation set |
| `FOR_NORMALISATION` | −1100 | bring an inequation into normal form |
| `MOVE_LEFT` | −90 | move a summand to the left |
| `MAKE_NON_STRICT` | −80 | turn a strict inequation non-strict |
| `CONTRAD` | −60 | detect a contradiction |
| `COMMUTE` | −40 | commute |
| `STRENGTHEN` | −30 | strengthen |
| `ANTISYMM` | −20 | antisymmetry |
| `PULLOUT_GCD_ANTEC_NONCONFLUENT` | −10 | antecedent-specialised gcd pull-out — not confluent, applied opportunistically |

`NonlinearArithmeticCost` — cross-multiplication and case distinctions:

| Constant | Value | Meaning |
|---|---|---|
| `MULTIPLY` | 1000 | cross-multiplication base (`inEqSimp_nonLin`); case-distinction offsets are `MULTIPLY + n` |
| `DIVIDE_INEQUATION` | −1400 | divide an inequation by a bounded factor (the inverse of cross-multiplication) |
| `SPLIT_EQ` | −100 | split an equation into two inequations |

`DivModCost` — division / modulo and DefOps expansion:

| Constant | Value | Meaning |
|---|---|---|
| `EXPAND_RANGES` | −8000 | expand integer range predicates |
| `MOD_HOMO_EQ` | −5000 | modulo homomorphism on an equation |
| `INLINE` | −5000 | inline `jdiv`/`jmod` for a literal numerator (eager, concrete) |
| `MOD` | −4000 | literal-only division / modulo |
| `MOD_EXPAND` | −3500 | modulo expansion for a polynomial modulus |
| `POLY_DIVISION` | −2250 | polynomial division |
| `EXPAND_MODULO` | −600 | expand a modulo term |
| `EXPAND_NUMERIC_OP` | −500 | expand a defined numeric operator |
| `BELOW_MODALITY` | 200 | extra cost for `defOps_div`/`jdiv` below a modality |

### Symbolic execution — `SymExStrategy`

`SymExCost`:

| Constant | Value | Meaning |
|---|---|---|
| `MODAL_TAUTOLOGY` | −10000 | close a modal tautology |
| `MERGE_RULE` | −4000 | apply the merge rule |
| `MERGE_POINT_SKIP` | −5000 | delete a merge point in skip mode (`MERGE_RULE − 1000`) |
| `BOX_DIAMOND_CONV` | −1000 | convert a box/diamond towards the antecedent-polarity program |
| `PROGRAM_STEP` | −100 | a cheap concrete program step |
| `METHOD_CONTRACT_PREFERENCE` | −20 | preference for the method-contract feature |
| `LOOP_CONTRACT_INTERNAL_TIEBREAK` | 42 | prefer the external loop contract over the internal one |
| `SPLIT_IF` | 50 | mildly defer `split_if` |
| `METHOD_EXPAND` | 100 | expand a method body (in expand mode) |
| `PROGRAM_STEP_BELOW_QUANTIFIER` | 200 | a program step underneath a quantifier |
| `THROWING_PROGRAM_STEP` | 500 | a program step that would raise a tracked exception |
| `LOOP_SCOPE_EXPAND` | 1000 | expand a loop scope (in the loop-scope-expand treatment) |
| `METHOD_EXPAND_REPRESSED` | 2000 | expand a method body when contracts are preferred |

### Strings — `StringStrategy`

`StringCost` (negative = eager normalisation, positive = deferred unfolding; the
unfolding ladder itself uses `CostBand.DEFER.at(..)`):

| Constant | Value | Meaning |
|---|---|---|
| `INTEGER_TO_STRING` | −10000 | translate an integer to its string representation |
| `REPLACE_INLINE` | −2500 | inline a `replace` when all arguments are literals |
| `CHAR_TO_INT_LITERAL` | −100 | convert a char literal to an int literal |
| `BELOW_MODALITY` | 500 | penalty for unfolding a string definition below a modality |

### Heap / JavaDL — `JavaCardDLStrategy`

`JavaCardDLCost` — axiom / observer / comprehension / induction reasoning:

| Constant | Value | Meaning |
|---|---|---|
| `AUTO_INDUCTION` | −6500 | apply auto-induction (like a delta rule) |
| `JAVA_INTEGER_SEMANTICS` | −5000 | insert the java integer operator definitions |
| `AUTO_INDUCTION_LEMMA` | −300 | apply an auto-induction lemma |
| `CLASS_AXIOM` | −250 | apply a class axiom |
| `LIMIT_OBSERVER` | −200 | limit an observer symbol (must beat `CLASS_AXIOM`) |
| `USER_TACLET_HIGH_PRIORITY` | −50 | user taclet set to high priority |
| `COMPREHENSION` | −50 | ordinary comprehension handling |
| `IN_REACHABLE_STATE` | 100 | `inReachableState` implication |
| `DEPENDENCY_CONTRACT` | 250 | apply a dependency contract |
| `COMPREHENSION_ENLARGE` | 10000 | expensive comprehension application |
| `USER_TACLET_LOW_PRIORITY` | 10000 | user taclet set to low priority |
| `LOCSET_CNF_COMMUTE` | −800 | loc-set CNF commutation |
| `COMPREHENSION_SIMPLIFY` | −5000 | cheap comprehension application |

`HeapSelectCost` — the pull-out-select simplification pipeline (a candidate for
a future heap/select sub-strategy):

| Constant | Value | Meaning |
|---|---|---|
| `PULL_OUT_SELECT_BELOW_UPDATE` | −4200 | pull out a select below an update |
| `PULL_OUT_SELECT` | −1900 | pull out a select otherwise |
| `APPLY_SELECT_EQ` | −1700 | replace a select by its skolem constant (`APPLY_SELECT_EQ_EFFECTIVE − ORDERED_REWRITING`) |
| `SIMPLIFY_SELECT` | −5600 | simplify the select term in the pulled-out equation |
| `APPLY_AUXILIARY_EQ` | −5500 | replace the skolem constant by its computed value |
| `HIDE_AUXILIARY_EQ` | −5400 | hide the auxiliary equation after replacement |
| `HIDE_AUXILIARY_EQ_CONST` | −500 | hide the auxiliary equation, constant case |
