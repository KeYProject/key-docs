# Proof Reordering

-- *Author: Arne Keller*, June 2023 valid for KeY-2.12.0

-- WIP

!!! abstract

    This note describes the new *Proof Reordering/Regrouping* functionality in KeY 2.12.
    It allows reordering and regrouping the steps in a proof.

Both functions are available in the toolbar.

## Reordering

Steps are reordered based on the data gathered in the dependency graph.
The algorithm tries to build long chains of steps working on a single formula, starting with the first formula on the sequent.
Newly created formulas are added to a queue and processed later.
The last (splitting) step in a branch is never moved, to avoid losing earlier proof steps.

## Grouping

### Default settings

1. Propositional expansion: `alpha`, `delta`
2. Normal forms: `negationNormalForm`, `conjNormalForm`
3. Polynomials and inequations: `polySimp_*`, `inEqSimp_*`, simplify_literals
4. Simplifications: `simplify`, `simplify_enlarging`, `simplify_select`

Modifiable by the user in the settings UI.
