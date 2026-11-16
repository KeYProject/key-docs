---
title: "User Guide"
weight: 10
---

Welcome to the **KeY user documentation**. This guide covers everything you
need to *use* KeY for the deductive verification of Java programs — from
installation to advanced proof scripting. (Information on extending or
contributing to KeY lives in the [Developer Guide](../devel/).)

## How this guide is organized

The chapters are arranged so that they can be read front to back:

1. **[Getting Started](getting-started/quicktour/)** — install KeY, load a
   JML-annotated Java program, and run your first proofs. Start here if
   you are new to KeY.
2. **[Working with the Prover](proving/)** — day-to-day interactive
   proving: [excluding goals from automation](proving/interactive/),
   [proof exploration](proving/exploration/), [node diffs](proving/node-diff/), the
   [linearized proof tree](proving/proof-tree-linear-mode/),
   [proof caching](proving/proof-caching/), and [proof slicing](proving/proof-slicing/).
3. **Structuring Verification Projects** — the
   [classpath directive](projects/classpath/), dealing with
   [generics](projects/generics/), [user-defined data types](projects/adts/), and
   [JavaDL escapes in JML](projects/javadi-in-jml/).
4. **[Proof Scripts](proof-scripts/)** — make interactive proofs
   persistent, resilient, and reapplicable with KeY's scripting language.
5. **SMT Solvers** — how to
   [add and configure SMT solvers](smt/adding-smt-solvers/).
6. **Bridges to Other Tools** — exporting proof obligations to
   [Isabelle](bridges/isabelle/).
7. **Language Reference** — the grammars of [JML](language/jml-grammar/), the
   [KeY input language](language/key-grammar/), and KeY's
   [Java extensions](language/java-grammar/).
8. **Supported Language Features** — which Java features KeY can verify:
   the [Java coverage table](features/java-coverage/).
9. **[FAQ](faq/)** — answers to common problems.

The **[Migrating from KeY 2 to KeY 3](migration-key-3/)** guide explains how to
carry existing proofs and specifications over to KeY 3. The
**[Release Notes](release-notes/)** list what changed in each KeY release.

## Learn more

Additional information is available on the
[KeY Project homepage](https://key-project.org) or on our
[GitHub repository](https://github.com/KeYProject/key/), where you can find
the source code, development updates, and contribute to the project.

Happy proving!

## Disclaimer

Some content of these pages has been co-produced by AI agents, mainly as
summaries of other pages, publications or other sources.
