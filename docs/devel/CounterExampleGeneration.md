# Counterexample generation

*Expanded 2026; class names and module locations checked against the
sources.*

KeY can search for counterexamples to an (unprovable) goal by translating
the sequent to SMT and asking Z3 for a model. The functionality is spread
over several modules:

- `keyext.ui.testgen` — the GUI action (`CounterExampleAction`)
- `key.core.testgen` — the generator logic
  (`de.uka.ilkd.key.testgen.smt.counterexample.AbstractCounterExampleGenerator`)
  and the `SemanticsBlastingMacro`
- `key.core` — the SMT infrastructure (`de.uka.ilkd.key.smt`:
  `SolverLauncher`, `communication.Z3CESocket`, `ModelExtractor`)
- `key.ui` — the result display (`de.uka.ilkd.key.gui.smt.InformationWindow`)

## High-level flow

1. The user clicks the *Counterexample* button in the toolbar; this triggers
   `CounterExampleAction` (in `keyext.ui.testgen`).
2. The action constructs and starts a `CEWorker` (a `SwingWorker`), so the
   search runs off the event thread and can be interrupted.
3. `AbstractCounterExampleGenerator#searchCounterExample` copies the sequent
   into a hidden *side proof* and prepares it by applying the
   `SemanticsBlastingMacro`, which rewrites the sequent into a form suitable
   for SMT model finding (expanding the heap/JavaDL semantics).
4. `SolverLauncher` starts Z3 in counterexample mode; `Z3CESocket` handles
   the solver communication and awaits its output.
5. If Z3 reports *sat*, `Z3CESocket` queries the model and passes it to the
   `ModelExtractor`, which reconstructs heap/object values from the SMT
   model.
6. `InformationWindow#initModel` displays the counterexample to the user.

## See also

- [SMT translation](../SMTTranslation/) — how sequents are translated to
  SMT-LIB.
- [Adding SMT solvers](../AddingSMTSolvers/) — how solvers are configured
  and launched.
- Test case generation (`key.core.testgen`) reuses the same
  model-extraction machinery to derive test inputs.
