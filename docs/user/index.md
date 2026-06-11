# KeY User Guide

Welcome to the **KeY user documentation**. This guide covers everything you
need to *use* KeY for the deductive verification of Java programs — from
installation to advanced proof scripting. (Information on extending or
contributing to KeY lives in the [Developer Guide](../devel/).)

## How this guide is organized

The chapters are arranged so that they can be read front to back:

1. **[Getting Started](../quicktour/)** — install KeY, load a
   JML-annotated Java program, and run your first proofs. Start here if
   you are new to KeY.
2. **[Working with the Prover](UiFeatures/)** — day-to-day interactive
   proving: [excluding goals from automation](Interactive/),
   [proof exploration](Exploration/), [node diffs](NodeDiff/), the
   [linearized proof tree](ProofTreeLinearMode/),
   [proof caching](ProofCaching/), and [proof slicing](ProofSlicing/).
3. **Structuring Verification Projects** — the
   [classpath directive](Classpath/), dealing with
   [generics](RemoveGenerics/), [user-defined data types](ADTs/), and
   [JavaDL escapes in JML](JavaDLinJML/).
4. **[Proof Scripts](ProofScripts/)** — make interactive proofs
   persistent, resilient, and reapplicable with KeY's scripting language.
5. **SMT Solvers** — how to
   [add and configure SMT solvers](SMT/AddingSMTSolvers/).
6. **Bridges to Other Tools** — exporting proof obligations to
   [Isabelle](IsabelleTranslation/).
7. **Language Reference** — the grammars of [JML](JMLGrammar/), the
   [KeY input language](KeyGrammar/), and KeY's
   [Java extensions](JavaGrammar/).
8. **[FAQ](FAQ/)** — answers to common problems.

The **[Release Notes](../changelog/)** list what changed in each KeY
release.

## Learn more

Additional information is available on the
[KeY Project homepage](https://key-project.org) or on our
[GitHub repository](https://github.com/KeYProject/key/), where you can find
the source code, development updates, and contribute to the project.

Happy proving!

## Disclaimer

Some content of these pages has been co-produced by AI agents, mainly as
summaries of other pages, publications or other sources.
