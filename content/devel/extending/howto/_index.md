---
title: "How-Tos (verified recipes)"
weight: 10
---

Step-by-step recipes for common extension tasks. Each how-to was checked
against the KeY sources, and the code shown was compiled (and, for the
taclet example, executed) against the current code base in June 2026.

- **[How to add an extension](add-extension/)** — create a new
  `keyext.<name>` Gradle module that plugs into the KeY GUI, including all
  build-file wiring. The other GUI how-tos build on this.
- **[How to add a main menu entry](add-menu-entry/)** — contribute actions
  to KeY's main menu.
- **[How to add a toolbar](add-toolbar/)** — contribute a toolbar to
  the main window.
- **[How to add taclets](add-taclets/)** — add calculus rules, either
  locally to one verification project or to KeY's standard rule base.
- **[How to add a proof macro](add-proof-macro/)** — bundle strategy steps
  into one proof step, usable from the GUI and from scripts.
- **[How to add a proof script command](add-script-command/)** — extend the
  proof script language with a new command.
- **[How to add a term label](add-term-label/)** — annotate term
  occurrences with non-soundness-relevant bookkeeping information and
  keep the annotation alive across rule applications.

For the conceptual overview of all extension mechanisms (script commands,
macros, built-in rules, SMT solvers, …), see
[Extending KeY](../).
