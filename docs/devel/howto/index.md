# Developer How-Tos

Step-by-step recipes for common extension tasks. Each how-to was checked
against the KeY sources, and the code shown was compiled (and, for the
taclet example, executed) against the current code base in June 2026.

- **[How to add an extension](AddExtension/)** — create a new
  `keyext.<name>` Gradle module that plugs into the KeY GUI, including all
  build-file wiring. The other GUI how-tos build on this.
- **[How to add a main menu entry](AddMenuEntry/)** — contribute actions
  to KeY's main menu.
- **[How to add a toolbar](AddToolbarAction/)** — contribute a toolbar to
  the main window.
- **[How to add taclets](AddTaclets/)** — add calculus rules, either
  locally to one verification project or to KeY's standard rule base.
- **[How to add a proof macro](AddProofMacro/)** — bundle strategy steps
  into one proof step, usable from the GUI and from scripts.
- **[How to add a proof script command](AddScriptCommand/)** — extend the
  proof script language with a new command.
- **[How to add a term label](AddTermLabel/)** — annotate term
  occurrences with non-soundness-relevant bookkeeping information and
  keep the annotation alive across rule applications.

For the conceptual overview of all extension mechanisms (script commands,
macros, built-in rules, SMT solvers, …), see
[Extending KeY](../ExtendingKeY/).
