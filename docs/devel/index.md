# Developer Guide

This guide is for developers who want to work *on* KeY or build *on top
of* it. (If you want to *use* KeY to verify programs, see the
[User Guide](../user/) instead.)

## How this guide is organized

1. **[Architecture](Architecture/)** — how the code base is organized into
   Gradle modules and where the important packages live. Read this first.
2. **[Building KeY](Gradle/)** — checking out, building, running, and
   testing KeY with Gradle.
3. **Working on the Code** — [coding conventions](CodingConventions/),
   [automatic formatting with Spotless](SpotlessAutomaticFormatting/), and
   [logging](Logging/); see also `CONTRIBUTING.md` in the repository.
4. **[Extending KeY](ExtendingKeY/)** — the central chapter for adding
   functionality. It starts with a decision table ("I want to add …") and
   contains compiled, verified **[How-Tos](howto/)** for the most common
   tasks: a new [extension module](howto/AddExtension/), a
   [menu entry](howto/AddMenuEntry/), a [toolbar](howto/AddToolbarAction/),
   [taclets](howto/AddTaclets/), a [proof macro](howto/AddProofMacro/),
   and a [script command](howto/AddScriptCommand/). In-depth references:
   [writing taclets](HowToTaclet/),
   [polarity triggers](../user/Polarity/),
   [GUI extension points](GUIExtensions/),
   [script commands](ScriptCommands/),
   [SMT solvers](AddingSMTSolvers/), and
   [event listeners](Listeners/).
5. **Using KeY as a Library** —
   [KeY in external projects](ExternalProject/) and the
   [JSON-RPC interface](rpc/).
6. **Internals** — background on selected subsystems: the
   [rule application pipeline](RuleApplicationPipeline/) (taclet matching →
   strategy evaluation → application),
   [proof loading/saving](ProofLoadSave/), [the KeY parser](NewKeyParser/),
   [SMT translation](SMTTranslation/), and
   [counterexample generation](CounterExampleGeneration/).
7. **[Testing](Testing/)** — unit tests, `RunAllProofs`,
   [proved rules](Testing/ProveRules/), CI.
8. **[Writing Documentation](howtodoc/)** — how to contribute to this
   site.

## Dependencies worth knowing

- [JavaParser](https://javaparser.org/) — parsing of Java sources
  (`de.uka.ilkd.key.java.JavaService`)
- [ANTLR 4](https://www.antlr.org/) — parsing of `.key` files and JML
- [Docking Frames](https://docking-frames.org/) — UI layout of the main
  window
- [SLF4J/Logback](https://www.slf4j.org/) — logging
