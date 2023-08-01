# Counterexample generation

This is the high-level flow for generating counterexamples using Z3.

1. User clicks on Counterexample button in toolbar.
2. `CEWorker` is constructed and started in `CounterExampleAction`.
3. `AbstractCounterExampleGenerator#searchCounterExample` prepares the sequent by applying the `SemanticsBlastingMacro`.
4. `SolverLauncher`, `Z3CESocket` and other classes launch Z3 and await its output.
5. `Z3CESocket` gets the model and passes it to the `ModelExtractor`.
6. `InformationWindow#initModel` displays the counterexample.