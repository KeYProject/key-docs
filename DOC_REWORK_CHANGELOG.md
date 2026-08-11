# Documentation Rework — Changelog

Work log for the reorganization and completion of the KeY documentation
(`key-docs`), checked against the implementation in `key-src`.

## 2026-07-12 — Thread Safety and Determinism page

- NEW `devel/ThreadSafety.md` (Developer Guide → Working on the Code): bachelor-level
  guide to writing prover code that stays correct under the multi-core prover.
  Mental model (per-goal vs shared objects), four rules with worked examples from
  real KeY code (ModalityCache vs introduction-time cache; ThreadLocal vs
  volatile-snapshot memo designs; LinkedHashSet iteration-order fix; goal-local
  fresh names), and a guide to the CI detectors (SharedStateLintTest,
  ScDeterminismTest, RunSmallProofsMt2w/4w) with the allowlist etiquette.
  Companion to the in-repo `key.core/.../prover/README.md` (concise version the
  CI failure messages link to). Extended same day with an opt-out section: the
  four mechanisms for restricting a feature to the single-core prover (profile
  capability, macro allowParallel(), rule applicability guard, strategy
  companion cost) with the real code examples, plus the linter-allowlist
  walkthrough.

## Milestone plan

- **M1 — Reorganization**: restructure the mkdocs navigation, keep the
  user/developer split, fix broken nav entries, remove duplicates,
  re-enable orphaned pages (quicktour, proof-script pages, LLM, Isabelle).
- **M2 — Outdated content**: update pages that no longer match the
  implementation (Recoder → JavaParser migration, script command package,
  broken `macros.md` export, stale warnings).
- **M3 — Missing content**: expand stub pages (`ProofLoadSave`,
  `CounterExampleGeneration`, `UiFeatures`, `devel/index`), add an
  architecture overview, and add a developer guide on **how to extend KeY**
  (GUI extensions, taclets, built-in rules, proof script commands, macros,
  SMT solvers).
- **M4 — QA**: link check over the nav, final consistency pass.

## Changes

### M1 — Reorganization

- `mkdocs.yml`: renamed site from "KeY Developer Documentation" to
  "KeY Documentation" (the site covers users *and* developers).
- **User Guide** restructured:
  - Re-enabled the **Quicktour** (was fully commented out) as
    "Getting Started (Quicktour)" — first entry of the User Guide.
  - New grouping: Getting Started → Core Concepts → Languages →
    UI Features → Proof Scripts → SMT Solvers → Bridges → FAQ → Changelog.
  - Moved `JavaGrammar.md` from "Topics" to "Languages" where it belongs.
  - Re-enabled previously orphaned pages: `ProofScripts/language.md`,
    `ProofScripts/variables.md`, `user/SMT/AddingSMTSolvers.md`,
    `user/IsabelleTranslation/`, `user/LLM/`.
  - Ordered Proof Scripts pages didactically (intro → language →
    commands → variables → macros → linear scripts → JML → historical).
- **Development** section restructured:
  - New grouping: Start → Architecture → Basics → **Extending KeY** →
    Internals → Testing → Write Documentation.
  - Removed broken nav entry `devel/ProveRules.md` (file never existed;
    correct file is `devel/Testing/ProveRules.md`).
  - Moved `How2ExtRecoder.md` (obsolete), `SMTTranslation.md`,
    `CounterExampleGeneration.md` under "Internals"; `rpc/index.md` and
    `Testing/TestingInfrastructure.md` were orphaned and are now in the nav.
  - Nav placeholders added for new pages written in M3:
    `devel/Architecture.md`, `devel/ExtendingKeY.md`, `devel/ScriptCommands.md`.
- Moved `docs/workbench/` to `disabled/workbench/` — it duplicated
  `eclipse/CrossProject/index.md` and was not in the nav.
- Rewrote landing pages to match the new structure: `docs/index.md`
  (fixed broken `user/quicktour/` link, added Developer Guide pointers),
  `docs/user/index.md` (real section overview with links), and
  `docs/user/UiFeatures/index.md` (was a bare 5-line link list).

### M2 — Outdated content

- `quicktour/install.md`: required Java version 11 → **21**
  (`sourceCompatibility = 21` in `key-src/build.gradle`).
- `devel/How2ExtRecoder.md`: warning updated — Recoder is no longer
  "planned to be removed", it **has been removed**; KeY now uses
  JavaParser (`JavaService`, `KeYJPMapping` in `de.uka.ilkd.key.java`).
  Page kept as historical reference.
- `user/ProofScripts/macros.md`: was a broken auto-generated export
  (literal `${new Date()}`, raw `<html>` fragments). Rewritten cleanly and
  checked against `de.uka.ilkd.key.macros`: added missing macros
  `auto-macro`, `simp-int`, `transcendental`; grouped by category; added
  note on invoking macros from scripts via `macro <name>;`.
- `devel/GUIExtensions.md`: checked against
  `de.uka.ilkd.key.gui.extension.api.KeYGuiExtension`. Fixed `TermInfo`
  description (it documents the status-line term info; the hover tooltip is
  the separate `Tooltip` extension point, which was missing). Filled the
  previously empty `MainMenu`, `StatusLine`, `KeyboardShortcuts` sections;
  added pointers to the `keyext.*` modules as example extensions.
- Verified as still accurate (no change needed): `devel/Listeners.md`,
  `user/ProofScripts/commands.md` (auto-generated 2025-10-06 from the
  current `de.uka.ilkd.key.scripts` package).

### M3 — Missing content

- **New page `devel/Architecture.md`**: module map of the Gradle build
  (foundations / core / UI / `keyext.*` extensions, from `settings.gradle`),
  important `key.core` packages, and a list of the `ServiceLoader`-based
  extension points found in `META-INF/services` of `key.core`.
- **New page `devel/ExtendingKeY.md`** (developer guide on how to extend
  the system): decision table mapping goals to mechanisms; the
  `ServiceLoader` registration recipe; how to add a **proof macro**
  (`ProofMacro`, `SequentialProofMacro`/`StrategyProofMacro`), a
  **built-in rule** (`BuiltInRule`, profile registration via
  `JavaProfile#initBuiltInRules`), and a **proof obligation type**
  (`POExtension` + `ProofObligationLoader`); contribution checklist.
  All cited classes verified to exist in `key-src`.
- **New page `devel/ScriptCommands.md`**: how to add a proof script
  command — `ProofScriptCommand` interface, `ServiceLoader` registration,
  `AbstractCommand` + parameter classes with `@Argument`/`@Option`/`@Flag`
  injection (example modeled on the real `CutCommand`), error handling,
  testing pointers.
- `devel/ProofLoadSave.md`: expanded from a 12-line stub — full load
  pipeline (`AbstractProblemLoader`, `InitConfig`, `ProofObligationLoader`,
  `IntermediateProofReplayer`), save side (`OutputStreamProofSaver`,
  `ProofBundleSaver`, `.zproof` bundles), cross-links.
- `devel/CounterExampleGeneration.md`: expanded from a 9-line stub — which
  module each class lives in (the flow spans `keyext.ui.testgen`,
  `key.core.testgen`, `key.core`, `key.ui`), step-by-step flow incl. the
  hidden side proof and `SemanticsBlastingMacro`, cross-links to SMT pages.
- `devel/index.md`: rewritten from a bare link list into a structured
  Developer Guide landing page (start here → extending → internals →
  testing → dependencies).

### M4 — QA

- All nav entries in `mkdocs.yml` verified to resolve to existing files.
- Relative links in all new/edited pages checked (mkdocs
  directory-URL convention, matching the existing pages).
- All class/package names cited in new developer pages verified against
  `key-src` (e.g. `AbstractCommand` is non-generic and uses
  `@Argument`/`@Option` injection via `ValueInjector`; the CE flow spans
  four modules; `Tooltip` vs. `TermInfo` extension points).

### Post-QA fixes

- `devel/SMTTranslation.md`: the sequence diagram was written in `seqdiag`
  syntax (not even fenced), which the site cannot render — converted to a
  Mermaid `sequenceDiagram` (the mermaid2 plugin is enabled in `mkdocs.yml`).
- `devel/howtodoc/index.md`: removed the blockdiag/seqdiag examples (the
  `markdown-blockdiag` extension is no longer enabled) and added a warning
  pointing authors to Mermaid instead.

### M5 — Final quality pass

- Site now **builds with `mkdocs build` without any broken-link warnings**
  (verified; only cosmetic warnings from the bibtex plugin scanning `@word`
  tokens in code remain — output is unaffected).
- `devel/howtodoc/index.md`: fixed 13 dead links that had been copied from
  the Material-for-MkDocs documentation (now point to the official
  `squidfunk.github.io` pages; the `local-doc.html` example now points to a
  real page).
- **SMT solver configuration pages corrected against
  `SolverPropertiesLoader`** (they contradicted each other):
  - `user/SMT/AddingSMTSolvers.md`: classpath resource is
    `…/smt-solvers.json`, not `solvers.key.json` (the page had copied a
    stale javadoc); system property syntax `-Dkey.smt_solvers=…`; removed
    the obsolete `.props`/`solvers.txt` workflow (pre-PR-3597) and linked
    the developer page for the JSON schema.
  - `devel/AddingSMTSolvers.md`: fixed the garbled list numbering
    (1, 3, 2, 1), clarified that later files overwrite earlier ones, and
    cleaned up grammar in the intro.
- `devel/Testing/TestingInfrastructure.md`: fixed title typos
  ("Infracture of Continous" → "Infrastructure of Continuous"), added a
  historical-content warning (current CI is GitHub Actions
  `.github/workflows/*` + GitLab CI; the page describes the old
  Travis/Jenkins setup), de-linked dead `/admin/runners` links.
- `eclipse/`: added a "Legacy content" warning to the section index (the
  plugins target Eclipse Indigo/Luna); fixed dead `../../download/` links
  in the SED and MonKeY pages (→ key-project.org/download); the SED
  tutorial link now points to the tutorial section within the page; the
  two evaluation links whose targets no longer exist were de-linked.
- `user/LLM/index.md` turned out to be an **empty skeleton** (headings
  only, no corresponding feature in `key-src`) — removed from the nav and
  from the user index until it has content.
- `docs/changelog.md` (release changelog) stopped at 2.12.2 although a
  **2.12.3 release (2024-09-08)** exists — added a curated entry
  summarizing the GitHub release notes (ADTs, `seqUpd`, JML `\TYPE`,
  proof-caching dependency graph, heap indicator, Java 21 testing, …).
- `devel/Architecture.md`: Mermaid module diagram rewritten with explicit
  node IDs (dotted names are fragile in Mermaid); the "extension module"
  recipe in `devel/ExtendingKeY.md` now names the concrete
  `runtimeOnly project(":keyext.<name>")` wiring verified in
  `key.ui/build.gradle`.
- Sitewide link audit with mkdocs URL semantics over **all** pages
  (including directory-style links the builder does not validate): no
  remaining broken internal links.

### M6 — Developer how-tos (verified against a real build)

New section **Development → Extending KeY → How-Tos** (`devel/howto/`):

- `AddExtension.md` — full walkthrough for a new `keyext.demo` module:
  directory layout, **all three build files** (`keyext.demo/build.gradle`,
  `include` in `settings.gradle`, `runtimeOnly project(":keyext.demo")` in
  `key.ui/build.gradle`), the `@KeYGuiExtension.Info` metadata, and the
  `META-INF/services` registration; table of real `keyext.*` modules to
  learn from.
- `AddMenuEntry.md` — `MainWindowAction`/`KeyAction` recipe; documented the
  `setMenuPath` semantics from `KeYGuiExtensionFacade` (no path →
  *Extensions* menu, dotted paths create submenus, `CHECKBOX` property,
  `PRIORITY` ordering).
- `AddToolbarAction.md` — `KeYGuiExtension.Toolbar`, icons via
  `IconFactory` + `MainWindow.TOOLBAR_ICON_SIZE`, toggle buttons and
  stateful buttons with pointers into `keyext.caching`/`keyext.slicing`.
- `AddTaclets.md` — two scenarios: project-local taclets in a `.key` file
  (`\rules` + `\heuristics`) and extending the standard rule base
  (`proof/rules/`, `\include` order in `standardRules.key`,
  `ruleSetsDeclarations.key`, soundness via taclet proofs, which test
  suites to run). No build-file changes needed for taclets (resources).
- Nav, `ExtendingKeY.md` (tip box + decision table) and `devel/index.md`
  link the new how-tos.

**Verification performed** (this is why the pages say "compiled/verified"):

- Implemented the demo extension in `key-src` exactly as documented;
  `./gradlew :keyext.demo:compileJava` and `:key.ui:compileJava` both
  succeed; the service file is correctly packaged
  (`unzip -p keyext.demo.jar META-INF/services/…` shows the class).
- Ran the taclet example end-to-end:
  `./gradlew :key.ui:run --args='--auto demoTaclet.key'` loads the custom
  taclet and closes the proof ("Number of goals remaining open: 0 —
  Proved").
- The scratch module and build-file edits were reverted afterwards;
  `key-src` is back to a clean checkout. The complete code lives in the
  how-to pages.
- Bug found while writing: `HowToTaclet.md` referenced
  `ruleSetDeclarations.key`; the actual file is
  **`ruleSetsDeclarations.key`** — fixed there and used correctly in the
  new page.
- Docs site rebuilt: no broken-link warnings; link audit over the new
  pages passes.

### M7 — How-tos: proof macros and proof script commands (verified)

- **New page `devel/howto/AddProofMacro.md`**: where macro code lives
  (incl. build wiring via the extension-module skeleton), base-class
  decision table (`SequentialProofMacro` / `StrategyProofMacro` /
  `AbstractProofMacro`), full compiling example (`DemoMacro` wrapping
  `TryCloseMacro`), `ServiceLoader` registration
  (`META-INF/services/de.uka.ilkd.key.macros.ProofMacro`), GUI and
  headless verification recipe, parameter support via
  `hasParameter`/`setParameter` (checked against `MacroCommand`).
- **New page `devel/howto/AddScriptCommand.md`**: full compiling example
  (`GreetCommand` with `@Option` injection, `EchoMessage` output following
  `EchoCommand`), registration
  (`META-INF/services/de.uka.ilkd.key.scripts.ProofScriptCommand`),
  headless verification via `\proofScript` in a `.key` file, error-handling
  conventions. Positioned as the hands-on companion of the
  `devel/ScriptCommands.md` reference.
- **Verification performed**: recreated the scratch `keyext.demo` module
  with both classes; `./gradlew :keyext.demo:compileJava` passes; a problem
  file with `\proofScript { greet name:"world"; macro "demo-close"; }`
  run via `--auto` closes ("Proved") — proving that both the command and
  the macro resolve through `ServiceLoader` and execute. Scratch code and
  build-file edits reverted afterwards; `key-src` is clean.
- Pitfall discovered during verification and documented in both pages:
  hyphenated macro names must be **quoted** in scripts
  (`macro "demo-close";`) — a bare `demo-close` is a parse error
  (`proofScriptExpression` only allows plain identifiers).
- Nav, `devel/howto/index.md`, and the `ExtendingKeY.md` decision table
  link the new pages.

### M8 — Eclipse plugins moved to a Historical section

- Nav: top-level tab **KeYclipse** replaced by **Historical → Eclipse
  plugins (unsupported)**; all nine pages keep their URLs (no file moves,
  so external links stay intact).
- `eclipse/index.md`: warning strengthened — the integrations are **no
  longer supported or maintained**; pointer to the standalone KeY
  application for current tooling.
- All nine `eclipse/*/index.md` subpages now carry an "Unsupported
  historical content" admonition directly under their title.
- Checked: no other documentation page links into the Eclipse section, so
  no further text updates were required.

### M9 — Final pass

- `mkdocs build`: no broken-link warnings.
- Sitewide link audit (both `.md`-style and directory-style links, all
  pages): **0 broken links**.
- Orphan check: every page is in the nav except the intentionally
  disabled `user/LLM/index.md` and `disabled/`.
- Verified the historical admonition renders correctly on pages with
  frontmatter (`eclipse/SED/index.md`).

### M10 — Book-like table of contents + final polish

**Navigation restructured into numbered chapters** with a front-to-back
reading order and explicit ToC labels for every page (page URLs unchanged):

- *User Guide*: Welcome → **1.** Getting Started (Quicktour) →
  **2.** Working with the Prover (all interactive/UI features, now one
  chapter) → **3.** Structuring Verification Projects → **4.** Proof
  Scripts → **5.** SMT Solvers → **6.** Bridges to Other Tools →
  **7.** Language Reference (the three grammars) → **8.** FAQ →
  Release Notes.
- *Developer Guide* (tab renamed from "Development"): Welcome →
  **1.** Architecture → **2.** Building KeY → **3.** Working on the Code →
  **4.** Extending KeY (overview, verified How-Tos, in-depth references) →
  **5.** Using KeY as a Library (External Projects + JSON-RPC, previously
  scattered) → **6.** Internals → **7.** Testing →
  **8.** Writing Documentation.
- *Historical* tab moved after the Developer Guide.
- `user/Polarity.md` moved (nav-only) into Developer Guide →
  Extending KeY: it documents a taclet-language feature for rule authors,
  not end users.
- Obsolete/outdated pages are labeled as such in the ToC
  ("Extending Recoder (obsolete)", "Deterministic Test Order (outdated)",
  "Historical Notes (2015)").

**Polish:**

- Added missing `#` page titles: the four quicktour chapters used `##` as
  their top heading; `user/Interactive.md` had no title at all (now
  "Excluding Goals from Automation").
- `user/index.md` and `devel/index.md` rewritten as chapter-mirrored
  tables of contents; `user/UiFeatures/index.md` is now the overview page
  of chapter 2 (including the Interactive page, which it previously
  omitted).
- `user/Polarity.md`: 2012 mailing-list shouting headings
  ("THE NEW FEATURE AND ITS MOTIVATION") converted to sentence case, with
  a provenance note.
- `user/Classpath.md`: removed "(TODO)" from the "Combining" heading and
  fixed the outdated claim that KeY "does not YET support external .jml
  files" — `JavaService` in `key.core` collects `.jml` files alongside
  `.java` since the JavaParser migration.
- Checked the old `git.key-project.org` GitLab links in FAQ, Spotless, and
  NewKeyParser pages: instance is still online (HTTP 200), links kept.

**QA:** `mkdocs build` clean (no broken-link warnings), sitewide link
audit: 0 broken links, orphan check: every page in the nav (except the
intentionally parked LLM stub and `disabled/`).

### M11 — Uniform sidebar styling + rule application pipeline

- `docs/extra.css`: new rule making **all chapter-level entries in the
  left sidebar bold** — previously only entries with subsections (rendered
  as section labels) were bold, while plain chapter pages
  ("1. Architecture", "8. FAQ") were not. The selector targets
  `nav[data-md-level="1"]` (verified against the generated HTML), so
  deeper levels keep their normal weight.
- **New page `devel/RuleApplicationPipeline.md`** (Internals, first
  entry): how a rule application comes about, in three stages —
  1. *Matching*: per-taclet `VMTacletMatcher` (compiled matching
     instructions), `RuleAppIndex`/`TacletIndex`/`TermTacletAppIndex`
     caching partial `TacletApp`s per term position, recomputed only for
     changed formulas;
  2. *Strategy evaluation*: `QueueRuleApplicationManager` priority queue
     fed via `NewRuleListener`, costs from `Strategy.computeCost`
     (feature terms, `TopRuleAppCost`), lazy `\assumes` matching and
     schema-variable instantiation (`createFurtherApps`,
     `Strategy.instantiateApp`), final filtering in `completeRuleApp`
     (still-applicable check, `isApprovedApp`, `tryToInstantiate`);
  3. *Application*: `DefaultProver#applyAutomaticRule` loop with
     `GoalChooser` and `StopCondition`, `Goal.apply` →
     `TacletExecutor`, index update closing the cycle.
  All class names and the control flow verified by reading the
  implementation (`key.core`, `key.ncore.calculus`); includes a Mermaid
  overview diagram, the interactive-application path, and a
  "where to hook in" table. Cross-linked from `devel/index.md` and
  `HowToTaclet.md`.
- QA: build clean, CSS confirmed in the built site, sitewide link audit
  0 broken links (caught and fixed four missing `../` prefixes in the new
  page before shipping).

### M12 — Architecture diagram redesign

- `devel/Architecture.md`: replaced the simple six-node dependency graph
  with a **layered stack diagram** (flowchart with four subgraph layers):
  User interface (`key.ui` + `keyext.*` with a "plug into" edge) →
  Specialized APIs (symbolic execution, testgen, infflow, wd,
  proof_references) → Core prover (`key.core` with its responsibilities) →
  Language-independent foundations (`key.ncore.calculus` → `key.ncore` →
  `key.util`). Arrows read "builds on"; a caption notes the
  simplifications.
- Rendering verified with the site's exact Mermaid version (10.4.0) via a
  live browser preview. This caught a real layout bug: Mermaid ignores a
  subgraph's `direction` when layers are connected, so the five API
  modules stacked vertically — fixed with invisible `~~~` links that force
  the horizontal row.

### M13 — Per-page review status ("approved" field)

- New MkDocs hook `hooks/approval.py` (wired via `hooks:` in
  `mkdocs.yml`): every page can carry an `approved:` front matter field
  with the reviewer's initials.
  - `approved: <initials>` → green badge "✓ checked by <initials>"
  - field missing → amber badge "⚠ not yet verified"
  - `approved: none` → no badge (for generated pages)
- Badge styling (top-right pill, light/dark variants) in
  `docs/extra.css`.
- `approved: none` set on the two generated pages (`changelog.md`,
  `user/ProofScripts/commands.md`); all other pages currently show
  "not yet verified" until someone signs them off.
- Convention documented in *How to write documentation* (new section
  "Review status of pages").
- Verified by building and inspecting the HTML for all three states, and
  visually in a browser preview (badge position/colors, no layout
  breakage with title, ToC, and Mermaid diagram).

### M13b — Verified badge moves to the footer, with date

- `hooks/approval.py` reworked: **approved pages** now render the badge as
  a full-width green note at the **end of the page** ("✓ This page was
  checked by ⟨initials⟩ on ⟨date⟩."), keeping the prominent amber top
  badge only for unverified pages (call to action).
- The verification date comes from the front matter: either a separate
  `approved-on: 2026-06-11` field or the shorthand
  `approved: rb 2026-06-11`; without a date only the initials are shown.
  (YAML date values and plain-meta string values both handled.)
- New `.approval--footer` style in `docs/extra.css` (left-bordered note
  instead of a floating pill).
- `devel/Architecture.md` (signed off by rb) got `approved-on: 2026-06-11`
  added to the fresh sign-off.
- Convention documentation in *How to write documentation* updated.
- Verified by building (footer badge with date on Architecture, top badge
  on unverified pages, generated pages still suppressed) and by checking
  the computed styles in the browser (block at end of content, green
  left-border note).

### M14 — Detailed section on the taclet matching VM

- `devel/RuleApplicationPipeline.md`: new subsection
  "Inside `VMTacletMatcher`: the matching VM", based on a close reading of
  `VMTacletMatcher`, `SyntaxElementMatchProgramGenerator`,
  `VMProgramInterpreter`, and the instruction classes:
  - compile-once/execute-often design: per-taclet instruction array from a
    pre-order walk of the `\find` pattern (plus one program per `\assumes`
    formula); instruction kinds (SV match + skip-subtree, node-kind check,
    operator identity, bind/unbind for quantifiers, modality/update
    special cases);
  - execution model: pooled depth-first cursor over the candidate term
    (operator node first, then subterms), lockstep traversal, no
    backtracking, first failing instruction aborts with `null`;
  - **worked example**: the compiled 8-instruction program for the real
    `eqSymm` taclet (`\find(commEqLeft = commEqRight)`,
    `classicalLogic/firstOrderRules.key`) with a step-by-step execution
    trace against `f(c) = g(d)` (success, resulting `MatchConditions`)
    and `p & q` (failure at the operator-identity instruction);
  - repeated schema variables check consistency instead of overwriting;
    surrounding concerns in `matchFind` (update-prefix stripping into the
    update context, `checkConditions` for `\varcond`/`\notFreeIn`).

### M15 — Badge colors from the site palette

- `docs/extra.css`: the review badges no longer use hard-coded
  Material-Design hex colors (greens/ambers); they now use the theme's
  local CSS variables — verified badge in the site's accent color
  (`--md-accent-fg-color`: teal in light mode, orange in dark mode),
  "not yet verified" in the neutral foreground tones
  (`--md-default-fg-color--light/--lighter`), both on
  `--md-code-bg-color`. The explicit dark-mode overrides became
  unnecessary and were removed; the badges now follow palette changes in
  `mkdocs.yml` automatically.

### M16 — Orange "not yet verified" badge; squidfunk links localized

- `docs/extra.css`: the "not yet verified" badge is now orange (dark
  orange in light mode, lighter orange in dark mode for contrast); the
  verified footer note keeps the site accent color.
- `devel/howtodoc/index.md`: removed all 12 `squidfunk.github.io` content
  links (introduced earlier when fixing the page's dead relative links):
  - icons/emoji/admonition references now point to the **local sections
    of the same page** (`#icons-emojis`, `#admonitions`; anchors verified
    in the built HTML);
  - markdown-extension references (Emoji, Attribute Lists, Markdown in
    HTML) now point to the canonical extension documentation
    (pymdown-extensions / python-markdown) instead of Material's mirror;
  - "primary/accent color", "additional JavaScript", and "additional
    style sheet" references were de-linked and now name the local
    configuration directly (`mkdocs.yml` palette, `extra_javascript`,
    `docs/extra.css`).
  - Follow-up: the five remaining `github.com/squidfunk` /
    `raw.githubusercontent.com` links were removed as well — the Material
    release-notes badge link was de-linked, the `.icons` reference now
    names the directory inside the installed `mkdocs-material` package,
    and the three example-icon links became plain code paths (the
    rendered shortcodes next to them already display the icons).
    The only remaining mention is the theme-generated footer credit
    ("Made with Material for MkDocs").

### M17 — Quicktour appendix: actual toolbar icons

- The shortcut/toolbar table in `quicktour/appendix.md` showed outdated
  PNG screenshots of the old KeY icons. The current GUI draws its toolbar
  icons from FontAwesome via `IconFactory`
  (`de.uka.ilkd.key.gui.fonticons`); the table now renders exactly those
  glyphs via the theme's bundled FontAwesome shortcodes, mapped from the
  `IconFactory` constants: Load = `FOLDER_OPEN`, Reload = `REDO_ALT`
  (FA6: rotate-right), Save = `SAVE` (floppy-disk), Proof Management =
  `TASKS` (list-check), Edit = `EDIT` (pen-to-square), Start strategy =
  `PLAY_CIRCLE` in green, Undo = `BACKSPACE` (delete-left), Prune = `CUT`
  (scissors).
- The SMT entry is a text drop-down button in the current GUI (solver
  selection), not an icon — described as such.
- The one-step simplifier icon is still a PNG in the sources; the actual
  file was copied from
  `key.ui/.../gui/images/toolbar/oneStepSimplifier.png` over the outdated
  one in `docs/quicktour/figures/`.
- Verified in the built HTML: all shortcodes render as inline SVGs, no
  literal `:fontawesome-…:` text remains, green styling applied.
- Pruned `docs/quicktour/figures/`: deleted 24 unreferenced files (the
  replaced icon PNGs, old LaTeX-era `.eps` figures, and stale
  screenshots), after also replacing the last inline use of the old
  proof-management icon in `quicktour/proving.md` with the current
  glyph. Remaining: `errorDialogUnknownType.png`,
  `oneStepSimplifier.png`, `proverWithLoadedPO.png` — all referenced.
- Added `devel/PerformanceOptimizations.md` (Developer Guide → 6. Internals,
  after the Rule Application Pipeline): a conceptual overview of the 3.1
  performance series — the compiled taclet matcher (experimental,
  [#3831](https://github.com/KeYProject/key/pull/3831)) plus the default-on
  cost reuse + age ([#3837](https://github.com/KeYProject/key/pull/3837)),
  assumes-parking ([#3838](https://github.com/KeYProject/key/pull/3838)),
  prefix-walk skip ([#3836](https://github.com/KeYProject/key/pull/3836)) and
  allocation reductions ([#3835](https://github.com/KeYProject/key/pull/3835)),
  with a combined 1.82× automode result (all five PRs incl. the matcher) ([#3839](https://github.com/KeYProject/key/pull/3839)).
  Each section follows previous-design / problem / chosen-solution with a
  mermaid diagram; added to the nav.

### M18 — Term labels: internals page and how-to

- New Internals page `devel/TermLabels.md`: why term labels exist
  (non-soundness-relevant per-occurrence annotations that must travel
  with the term), the shipped label inventory with attachers, and the
  design after the 2026 term-label rework — labels directly on
  `TermImpl` (no `LabeledTermImpl` subclass anymore), the three equality
  modes (plain `equals` ignores **all** labels;
  `IRRELEVANT_TERM_LABELS_PROPERTY` keeps proof-relevant ones;
  `equalsIncludingLabels`/`labeledHashCode` strict for interning),
  label-sensitive interning via `StrictTermKey`, and the
  `TermLabelManager` hook taxonomy (Factory / Policy / Update /
  Refactoring / Merger) including the fixed execution order and why the
  Policy/Update split is intentional.
- New verified how-to `devel/howto/AddTermLabel.md`: decision guidance,
  label + factory definition, profile registration, attachment from
  taclets (`<<demo>>`) and from `TermBuilder`, a maintenance-hook
  ladder ordered by runtime cost, and testing pointers.
- Both added to the nav (Internals; How-Tos) and to the how-to overview.
- **Note:** these pages document the state of the `termlabel-cleanup`
  branch (label-agnostic equality); merge together with that PR.

### M11 — Internals restructuring (port from the queue branch)

- "6. Internals" regrouped into subsections: Proof search / Terms and
  parsing / Proofs and external solvers / Legacy (ported from the
  `queue-docs` branch).
- Removed `devel/PerformanceOptimizations.md` (+ nav entry + reference in
  `Multithreading.md`): the documented "3.1" performance series is merged
  into `main`.
- **Not** ported (stays on `queue-docs` until the eager queue lands): the
  `EagerRuleApplicationQueue.md` appendix, the lazy/eager manager section
  in `RuleApplicationPipeline.md`, and the "9. Appendices" nav group.

### M12 — Strategy costs

- New page `devel/StrategyCosts.md` — "Strategy Costs and the Cost-Band
  Ladder": how-to for extending/modifying the automated strategies. The
  three cost layers (`CostBand` ladder / `CombinationCost` / theory-local
  holders), the band table with semantics (`DEFAULT`, `DEFER`,
  `BLOCK_CONTRACT` ordering constraint), choosing a cost top-down (layer,
  then fine placement), why theory-local constants are deliberately not
  anchored to bands, the two situations that make a cost combination-shared,
  and the verification required per layer.
- Added to the nav under Internals → Proof search, next to the
  rule-application pipeline.
- **Note:** documents the state of the `bubel/strategy-cost-cleanup`
  branch (CostBand vocabulary); merge together with that PR.
- Follow-up: `cost()`/`at(delta)` return the cost as a constant strategy
  feature (call sites lose the `longConst(...)` wrapper); raw number via
  `value()`. Snippet updated accordingly.
- New appendix page `devel/StrategyCostTables.md` ("9. Appendices" →
  "Strategy Cost Tables"): reference tables for every cost constant — the cost
  bands (shared with the main page via a `--8<--` snippet include,
  `includes/costband-table.md`, so they stay consistent), the combination
  costs, and the theory-local costs grouped by component strategy. Linked from
  the main page; all 96 values cross-checked against the sources.

## Known issues / suggestions for follow-up

- `key-src` `README.md` states "Java 17 or newer" while the build sets
  `sourceCompatibility = 21` — the README should be updated upstream.
- The Javadoc of `ProofScriptCommand` still references the old service path
  `META-INF/service/de.uka.ilkd.key.macros.scripts.ProofScriptCommand`
  (package was renamed to `de.uka.ilkd.key.scripts`).
- `devel/Testing/deterministicTestOrder.md` is explicitly flagged as
  pre-JUnit-5; kept with its warning.
- `user/LLM/index.md` is an empty stub — write content (or delete) once
  the corresponding feature lands; then re-add it to the nav.
- A `KEY-3.0.0-JP-rc` prerelease exists on GitHub (2026-03); the release
  changelog should get an entry when 3.0.0 is final.
- The javadoc of `SolverPropertiesLoader` (key-src) still names the
  classpath resource `solvers.key.json` although the code loads
  `smt-solvers.json` — fix upstream.
- `TranscendentalFloatSMTMacro.getDescription()` returns `"<html>TODO"` in
  the source.
