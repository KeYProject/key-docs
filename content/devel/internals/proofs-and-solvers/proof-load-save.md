# Proof loading / saving

*Expanded 2026; class names checked against `key.core`
(`de.uka.ilkd.key.proof.io`).*

## Loading

Loading of problem files (`.key`, `.java`) and proof files (`.proof`,
`.zproof` bundles) is driven by an `AbstractProblemLoader`
(package `de.uka.ilkd.key.proof.io`):

1. A `ProblemLoader` is created — by the GUI (e.g. *File → Load*, recent
   files, command line arguments) via the user interface control, or
   programmatically through `KeYEnvironment.load(...)` when KeY is
   [used as a library](../ExternalProject/).
2. `AbstractProblemLoader#load()` sets up the environment: creating a
   directory for Java source files, unzipping proof bundles, parsing the
   input file, and reading taclet definitions. The result is an
   `InitConfig` with all rules, sorts, and functions available for the
   proof.
3. `#createProofObligationContainer()` determines and instantiates the
   proof obligation described by the input (for reloaded proofs, via the
   registered `ProofObligationLoader` services — extension point
   `de.uka.ilkd.key.proof.init.loader.ProofObligationLoader`).
4. `#createProof()` creates a `ProofAggregate` based on the obligation and
   registers it in the environment.
5. For proof files, `#loadSelectedProof()` replays the stored proof steps
   using `IntermediateProofReplayer`: the saved rule applications are parsed
   into an intermediate representation and re-applied one by one to the new
   proof. Replay failures (e.g. due to changed rules) leave the proof open
   at the failing step and are reported to the user.

## Saving

Saving is done by `OutputStreamProofSaver` (subclass `ProofSaver` adds
file handling and user notification). It writes the proof header (settings,
classpath, included files) followed by a textual representation of the proof
tree: one s-expression-like entry per rule application, including rule name,
position information, instantiations, and built-in rule data (contracts,
merge information, …).

Related classes:

- `ProofSaver` / `OutputStreamProofSaver` — `.proof` format
- `ProofBundleSaver` — `.zproof` *proof bundles* which package the proof
  together with all source and classpath files needed to reload it
- `de.uka.ilkd.key.settings.ProofSettings` — the settings serialized into
  the proof header

## See also

- [Proof caching](../../user/ProofCaching/) reuses saved/closed proofs to
  close new goals.
- The [proof script](../../user/ProofScripts/) mechanism is an alternative,
  more change-resilient way to persist interactive proof steps.
