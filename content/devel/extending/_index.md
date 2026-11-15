# Extending KeY

*2026*

This page is the entry point for developers who want to add functionality to
KeY. It gives an overview of the available extension mechanisms and links to
the detailed guides. For orientation in the code base, read the
[Architecture Overview](../Architecture/) first.

!!! tip "Step-by-step recipes"
    Compiled, verified walkthroughs for the most common tasks are in the
    [Developer How-Tos](../howto/): adding an
    [extension module](../howto/AddExtension/), a
    [menu entry](../howto/AddMenuEntry/), a
    [toolbar](../howto/AddToolbarAction/), and
    [taclets](../howto/AddTaclets/).

## Which mechanism do I need?

| You want to … | Mechanism | Detailed guide |
|---|---|---|
| Add a new prover rule expressible schematically | **Taclet** in a `.key` rule file | [How to add taclets](../howto/AddTaclets/), [How to write new taclets](../HowToTaclet/) |
| Add a prover rule that needs arbitrary Java code | **Built-in rule** | below |
| Add panels, menu/toolbar entries, settings pages, tooltips, … to the GUI | **GUI extension** (`KeYGuiExtension`) | [How to add an extension](../howto/AddExtension/), [GUI extensions](../GUIExtensions/) |
| Add a new proof script command | **`ProofScriptCommand`** service | [How to add a script command](../howto/AddScriptCommand/), [reference](../ScriptCommands/) |
| Add a high-level proof step usable from GUI *and* scripts | **`ProofMacro`** service | [How to add a proof macro](../howto/AddProofMacro/) |
| Connect another SMT solver | **Solver definition** (JSON) / `SolverType` | [Adding SMT solvers](../AddingSMTSolvers/) |
| React to events (rule applications, selection, proof changes, …) | **Listeners** | [Event listeners](../Listeners/) |
| Use KeY from your own application | **KeY as a library** | [External projects](../ExternalProject/) |

## The `ServiceLoader` pattern

Almost all extension points are discovered via Java's
[`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html).
The recipe is always the same:

1. Implement the service interface (e.g. `ProofScriptCommand`,
   `ProofMacro`, `KeYGuiExtension`).
2. Register the fully qualified name of your class in a file
   `src/main/resources/META-INF/services/<fully-qualified-interface-name>`
   of your module (one class name per line).
3. Put your module (jar) on the classpath. KeY picks the implementation up
   at startup — no central registry needs to be modified.

For a self-contained extension, create a new Gradle module `keyext.<name>`
(add it to `settings.gradle`; depend on `key.core` and — for UI parts —
`key.ui`) and put it on the runtime classpath by adding
`runtimeOnly project(":keyext.<name>")` to the `dependencies` block of
`key.ui/build.gradle`. The existing `keyext.*` modules (`keyext.slicing`,
`keyext.caching`, `keyext.exploration`, …) are good templates.

## Adding a proof macro

A *proof macro* bundles strategy invocations into one user-visible proof
step (see the [user documentation of macros](../../user/ProofScripts/macros/)).

1. Implement `de.uka.ilkd.key.macros.ProofMacro`; usually you extend one of
   the abstract helpers in the same package, e.g.
   `AbstractProofMacro`, `SequentialProofMacro` (run several macros in
   sequence), or `StrategyProofMacro` (run the automated strategy with a
   modified strategy).
2. Provide `getName()`, `getCategory()`, `getDescription()`, and
   `getScriptCommandName()` — the latter makes the macro available in proof
   scripts as `macro <name>;`.
3. Register the class in
   `META-INF/services/de.uka.ilkd.key.macros.ProofMacro`.

Example to mimic: `FullAutoPilotProofMacro` (a `SequentialProofMacro`) in
`key.core`.

## Adding a built-in rule

Taclets cannot express everything (e.g. rules that need to inspect or
generate arbitrary proof obligations). For those cases KeY has *built-in
rules*, implemented in Java:

1. Implement `de.uka.ilkd.key.rule.BuiltInRule` (look at e.g.
   `UseOperationContractRule`, `LoopScopeInvariantRule`, or the merge rules
   in `de.uka.ilkd.key.rule.merge` for reference). The two essential methods
   are `isApplicable(Goal, PosInOccurrence)` and `apply(...)` which returns
   the resulting goals.
2. Register the rule in the active *profile*: profiles
   (`de.uka.ilkd.key.proof.init.Profile`, standard implementation
   `JavaProfile`) determine the set of available rules. For experimentation
   you can subclass `JavaProfile` and override
   `initBuiltInRules()`.

Prefer taclets whenever the rule is schematically expressible — they are
declarative, easier to review, and their soundness can be
[verified mechanically](../Testing/ProveRules/).

## Adding a new proof obligation type

Implement `de.uka.ilkd.key.proof.init.POExtension` and a
`de.uka.ilkd.key.proof.init.loader.ProofObligationLoader` (so that proofs
for your obligation can be reloaded), and register both via
`META-INF/services`. See `FunctionalOperationContractPO` and the existing
loaders in `de.uka.ilkd.key.proof.init.loader` for reference.

## Checklist before contributing

- Follow the [coding conventions](../CodingConventions/) and run
  [Spotless](../SpotlessAutomaticFormatting/) (`./gradlew spotlessApply`).
- Add tests — see the [testing infrastructure](../Testing/).
- New taclets need soundness justification
  ([proved rules](../Testing/ProveRules/)).
- See `CONTRIBUTING.md` in the repository root for the pull-request
  workflow.
