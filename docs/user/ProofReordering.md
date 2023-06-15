# Proof Reordering

-- *Author: Arne Keller*, June 2023 valid for KeY-2.12.0

-- WIP

!!! abstract

    This note describes the new *Proof Reordering/Regrouping* functionality in KeY 2.12.
    It allows reordering and regrouping the steps in a proof.

## Grouping

### Default settings

1. Propositional expansion: `alpha`, `delta`
2. Normal forms: `negationNormalForm`, `conjNormalForm`
3. Polynomials and inequations: `polySimp_*`, `inEqSimp_*`, simplify_literals
4. Simplifications: `simplify`, `simplify_enlarging`, `simplify_select`

Planned to be modifiable by user.
