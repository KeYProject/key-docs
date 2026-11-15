---
title: "Developer Guide"
weight: 20
---

This guide is for developers who want to work *on* KeY or build *on top
of* it. (If you want to *use* KeY to verify programs, see the
[User Guide](../user/) instead.)

## How this guide is organized

1. **[Architecture](architecture/)** — how the code base is organized into
   Gradle modules and where the important packages live. Read this first.
2. **[Building KeY](building/)** — checking out, building, running, and
   testing KeY with Gradle.
3. **Working on the Code** — [coding conventions](working-on-code/coding-conventions/),
   [automatic formatting with Spotless](working-on-code/spotless/), and
   [logging](working-on-code/logging/); see also `CONTRIBUTING.md` in the repository.
4. **[Extending KeY](extending/)** — the central chapter for adding
   functionality. It starts with a decision table ("I want to add …") and
   contains compiled, verified **[How-Tos](extending/howto/)** for the most common
   tasks: a new [extension module](extending/howto/add-extension/), a
   [menu entry](extending/howto/add-menu-entry/), a [toolbar](extending/howto/add-toolbar/),
   [taclets](extending/howto/add-taclets/), a [proof macro](extending/howto/add-proof-macro/),
   and a [script command](extending/howto/add-script-command/). In-depth references:
   [writing taclets](extending/how-to-write-taclets/),
   [polarity triggers](extending/polarity/),
   [GUI extension points](extending/gui-extensions/),
   [script commands](extending/script-commands/),
   [SMT solvers](extending/adding-smt-solvers/), and
   [event listeners](extending/listeners/).
5. **Using KeY as a Library** —
   [KeY in external projects](library/external-project/) and the
   [JSON-RPC interface](library/rpc/).
6. **Internals** — background on selected subsystems: the
   [rule application pipeline](internals/proof-search/rule-application-pipeline/) (taclet matching →
   strategy evaluation → application),
   [taclet matching](internals/proof-search/taclet-matching/) (the match-plan framework and its
   two back-ends),
   [proof loading/saving](internals/proofs-and-solvers/proof-load-save/), [the KeY parser](internals/terms-and-parsing/new-key-parser/),
   [SMT translation](internals/proofs-and-solvers/smt-translation/), and
   [counterexample generation](internals/proofs-and-solvers/counterexample-generation/).
7. **[Testing](testing/)** — unit tests, `RunAllProofs`,
   [proved rules](testing/prove-rules/), CI.
8. **[Writing Documentation](writing-documentation/)** — how to contribute to this
   site.

## Dependencies worth knowing

- [JavaParser](https://javaparser.org/) — parsing of Java sources
  (`de.uka.ilkd.key.java.JavaService`)
- [ANTLR 4](https://www.antlr.org/) — parsing of `.key` files and JML
- [Docking Frames](https://docking-frames.org/) — UI layout of the main
  window
- [SLF4J/Logback](https://www.slf4j.org/) — logging
