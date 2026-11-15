# Macros

Proof macros bundle strategy invocations and rule applications into
higher-level proof steps. They can be applied from the GUI (context menu
*Strategy macros* or toolbar) and from proof scripts via the `macro`
command, e.g. `macro autopilot;`.

The list below covers the macros shipped with KeY (defined in package
`de.uka.ilkd.key.macros` of `key.core`).

## Auto pilot

### Full Auto Pilot (`autopilot`)

1. Finish symbolic execution
2. Separate proof obligations
3. Expand invariant definitions
4. Try to close all proof obligations

### Auto pilot, preparation only (`autopilot-prep`)

1. Finish symbolic execution
2. Separate proof obligations
3. Expand invariant definitions

### Finish symbolic execution (`symbex`)

Continue automatic strategy application until no more modality is on the
sequent.

### Flexible automation (`auto-macro`)

Macro with multiple options for flexible automation. With default options it
behaves like `symbex`.

### Close provable goals below (`tryclose`)

Closes closable goals, leaves the rest untouched (see setting *AutoPrune*).
Applies only to goals beneath the selected node.

## Propositional

### Propositional expansion with splits (`split-prop`)

Apply rules to decompose propositional toplevel formulas; splits the goal if
necessary.

### Propositional expansion without splits (`nosplit-prop`)

Apply rules to decompose propositional toplevel formulas; does not split the
goal.

## Simplification

### One single proof step (`onestep`)

One single proof step is applied.

### Heap simplification (`simp-heap`)

Performs simplification of heap and location-set (`LocSet`) terms. It applies
simplification rules (including the "unoptimized" select rules), One Step
Simplification, alpha, and delta rules.

### Integer simplification (`simp-int`)

Performs simplification of integers and terms with integers. Applies only
non-splitting simplification rules.

### Update simplification only (`simp-upd`)

Applies only update simplification rules.

## Other

### Full Information Flow Auto Pilot (`infflow-autopilot`)

For information-flow proofs (module `key.core.infflow`):

1. Search exhaustively for an applicable position, then
2. start auxiliary computation,
3. finish symbolic execution,
4. try to close as many goals as possible,
5. apply the macro recursively,
6. finish the auxiliary computation,
7. use information flow contracts, and
8. try to close as many goals as possible.

### Transcendental floats (`transcendental`)

Axiomatizes transcendental float functions (such as `sin`) for SMT
translation.
