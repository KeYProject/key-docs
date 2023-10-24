# Changelog

## [2.12.1](https://github.com/KeYProject/key/releases/tag/KEY-2.12.1) (2023-10-13)

### Bug fixes

- SMT solvers are properly terminated on timeout
- Proof Macro statistics are kept visible and only count the newly applied rules
- Stop button is disabled after use, re-enabled after stop completes (this is to avoid double activation)
- Fully disable origin tracking if it is disabled
- Proof slicing works even if a cut introduced no new formulas in any branch
- When marking goal(s) as interactive/automatic, proof tree no longer loses expansion state
- Fix proof tree behaviour when toggling goals
- Fix branch selection in caching
- Fix gradle detection of git branch
- Fix unit test
- Fix environments not disposed in tests, keep strategy info visible after applying
- Proof macro: record statistics correctly
- Fix: KeY files with errors cannot be edited

## [2.12.0](https://github.com/KeYProject/key/releases/tag/KeY-2.12.0) (2023-08-18)

### Breaking changes
* [The minimum required JDK version is set to 11.](https://git.key-project.org/key/key/-/merge_requests/380)
- This release contains breaking changes for the reloading of older proofs:
    - Integers in specifications are now considered as unbounded (i.e. `\bigint`, math mode specifiers can be used to deviate from the default).
    - The list of rule sets used by the One-Step-Simplifier has changed.
    - JML assertions are handled as a standalone construct and not as a block contract anymore.

### Highlights

* [Support for floating points](https://git.key-project.org/key/key/-/merge_requests/403)
* [Support for JML asserts/assumes as standalone construct (instead of transforming into blockcontracts)](https://git.key-project.org/key/key/-/merge_requests/494), [Support of \old() in JML asserts](https://git.key-project.org/key/key/-/merge_requests/533)
* [Support for JML math mode specifiers (and changed default semantics to spec_bigint_math)](https://github.com/KeYProject/key/pull/3014)
* [Proof Slicing](user/ProofSlicing.md) system ([#3026](https://github.com/KeYProject/key/pull/3026))
* [Proof Caching](user/ProofCaching.md) system
* [Run the Javac compiler when loading Java code](https://git.key-project.org/key/key/-/merge_requests/581)
* Migration to GitHub
    * [Files for Github Actions](https://git.key-project.org/key/key/-/merge_requests/634)
    * [Add `merge_group` event to checks](https://github.com/KeYProject/key/pull/3060)
    * Artiweb: [#3047](https://github.com/KeYProject/key/pull/3047), [#3097](https://github.com/KeYProject/key/pull/3097), [#3098](https://github.com/KeYProject/key/pull/3098), [#3101](https://github.com/KeYProject/key/pull/3101), [#3102](https://github.com/KeYProject/key/pull/3102), [#3103](https://github.com/KeYProject/key/pull/3103)
    * [Upload HTML test report](https://github.com/KeYProject/key/pull/3010)
    * [Dependabot](https://github.com/KeYProject/key/pull/3002)

### Features

* [Enable JavaDL data types in ghost and model fields](https://git.key-project.org/key/key/-/merge_requests/469)
* [Change SwitchToIf to create a if-else cascade](https://git.key-project.org/key/key/-/merge_requests/444)
* [More proof script commands: hide and unhide](https://git.key-project.org/key/key/-/merge_requests/486)
* [Logging via slf4j](https://git.key-project.org/key/key/-/merge_requests/240) 
* [Suggested automation for seqPerm](https://git.key-project.org/key/key/-/merge_requests/531)
* [More descriptive names for result variables](https://git.key-project.org/key/key/-/merge_requests/542) 
* [Implement some features of the jml assert wishlist](https://git.key-project.org/key/key/-/merge_requests/532)
* [ChoiceExpr: En-/Disabling taclets/goal templates using boolean expression](https://git.key-project.org/key/key/-/merge_requests/574) 
* [New rules from the sorting case study](https://git.key-project.org/key/key/-/merge_requests/567)
* [Overflow checking](https://github.com/KeYProject/key/pull/3027)
* [Bring INVISMT to KeY; Refactors SolverTypes](https://git.key-project.org/key/key/-/merge_requests/406)
* [Redux additions](https://git.key-project.org/key/key/-/merge_requests/588) 

### UI/UX Improvements
* [Selection history (back + forward button)](https://github.com/KeYProject/key/pull/3006)
* [Generic undo button for user actions](https://github.com/KeYProject/key/pull/3009)
* [Expand oss nodes](https://github.com/KeYProject/key/pull/3061)
* [Allow user to select any installed LaF](https://github.com/KeYProject/key/pull/3038)
* [Un-clutter the context menus in the proof tree view](https://git.key-project.org/key/key/-/merge_requests/611) 
* [Close more dialogs on escape press](https://git.key-project.org/key/key/-/merge_requests/571) 
* [Replay progress display](https://git.key-project.org/key/key/-/merge_requests/560) 
* [Improved taclet error reporting](https://git.key-project.org/key/key/-/merge_requests/603) 
* [Immediately resize proof tree font](https://git.key-project.org/key/key/-/merge_requests/624)
* [Tooltip for the exloration status label](https://git.key-project.org/key/key/-/merge_requests/592)
* [Update log button, use Desktop.open instead of edit, fix an exception and log format on windows](https://git.key-project.org/key/key/-/merge_requests/610)
* [Report location on error in constant evaluation](https://github.com/KeYProject/key/pull/3025)
* [Report better error for missing model method]( https://github.com/KeYProject/key/pull/3041)
* [Proof tree view: Multiple small changes for readability](https://github.com/KeYProject/key/pull/3012)
* [Disable exploration tree updates when disabled](https://git.key-project.org/key/key/-/merge_requests/569)
* [Focus first cell in the taclet instantiation dialog on open](https://git.key-project.org/key/key/-/merge_requests/572)
* [Clipboard: Replace nbsp from html document selection with normal spaces](https://git.key-project.org/key/key/-/merge_requests/480)
* [Improve naming in recently used files dropdown](https://git.key-project.org/key/key/-/merge_requests/622)
### 🛠 Maintenance/Internal Changes

* Logging 
    * [Logging cleanup](https://github.com/KeYProject/key/pull/3093)
    * [Housekeeping: Logging](https://git.key-project.org/key/key/-/merge_requests/540)

* Code formatting with spotless 
    * [Check formatting  with Spotless](https://git.key-project.org/key/key/-/merge_requests/497)
    * [Formatted rules](https://git.key-project.org/key/key/-/merge_requests/597)
    * [Set an import order for Java code](https://github.com/KeYProject/key/pull/3094)
    * [Apply Spotless to code base: Source code reformatting (no license headers)](https://git.key-project.org/key/key/-/merge_requests/584)
    * [Spotless: Don't join manually split lines](https://git.key-project.org/key/key/-/merge_requests/586)

* Code-Clean-Ups and Refactoring:
    * [Replace the hardcoded SolverType classes by .props files](https://git.key-project.org/key/key/-/merge_requests/514)
    * [Position information overhaul](https://github.com/KeYProject/key/pull/3049)
    * [Remove ServiceLoaderUtil](https://git.key-project.org/key/key/-/merge_requests/470)
    * [Remove last Eclipse files](https://git.key-project.org/key/key/-/merge_requests/471)
    * [Code cleanup](https://github.com/KeYProject/key/pull/3064)
    * [Miscellaneous cleanups (unused classes removed etc.)](https://github.com/KeYProject/key/pull/3044)
    * [Removal of the Eclipse Plugins](https://git.key-project.org/key/key/-/merge_requests/390) 
    * [Remove sonarqube from readme](https://github.com/KeYProject/key/pull/3077)
    * [Cleanup: Remove extension of CreatingASTVisitor by MergeRuleUtils.CollectLocationVariablesVisitor](https://git.key-project.org/key/key/-/merge_requests/529) 
    * [Some code cleanup](https://git.key-project.org/key/key/-/merge_requests/619) 
    * [Refactor Java formatter used in the sequent view](https://github.com/KeYProject/key/pull/3034)
    * [Overhaul of the Configuration](https://github.com/KeYProject/key/pull/3031)
    * [Add possibility to check for unsupported properties keys to SettingsConverter and clean up the class](https://git.key-project.org/key/key/-/merge_requests/638) 
    * [Removal of the Proof Collection Parser](https://github.com/KeYProject/key/pull/3030)

* Dependencies
    * [Recoder became part of this repo (Version 0.84 incl. KeY extensions)](https://git.key-project.org/key/key/-/merge_requests/424)
    * [Update dependencies](https://git.key-project.org/key/key/-/merge_requests/467) 
    * [No dependencies as local jar files](https://git.key-project.org/key/key/-/merge_requests/484)
    * [JUnit 5](https://git.key-project.org/key/key/-/merge_requests/489) 
    * [Update Checkstyle configuration to latest Checkstyle version](https://git.key-project.org/key/key/-/merge_requests/631) 
    * [Externalization of Interaction Logging](https://git.key-project.org/key/key/-/merge_requests/500) 
    * [Prepare build.gradle scripts for Gradle 8.0](https://git.key-project.org/key/key/-/merge_requests/620)

* Performance
    * [Performance when switching nodes](https://git.key-project.org/key/key/-/merge_requests/482)
    * [Autopilot Performance: hasModality](https://git.key-project.org/key/key/-/merge_requests/508)
    * [Performance: pause tree updates while executing "Set All Goals Below to XX"](https://git.key-project.org/key/key/-/merge_requests/528)
    * [Avoid creating proof obligations in ProofManagementDialog](https://git.key-project.org/key/key/-/merge_requests/554)

* Tests
    * [JUnit XML files for optional-tests](https://github.com/KeYProject/key/pull/3096)
    * [Add documentation for TestTacletEquality and update oracle](https://git.key-project.org/key/key/-/merge_requests/473)
    * [Restore Information FlowTests](https://git.key-project.org/key/key/-/merge_requests/553) 
    * [Split `testRunAllProofs` into two tasks](https://git.key-project.org/key/key/-/merge_requests/559)
    * [Disable proof_references + symbolic_execution](https://git.key-project.org/key/key/-/merge_requests/589) 

* Misc
    * [Small tweaks to proof script engine](https://github.com/KeYProject/key/pull/3020)
    * [Reducing the binary filesize by only including the necessary example files](https://git.key-project.org/key/key/-/merge_requests/626) 
    * [Improve smt solver checking on windows](https://git.key-project.org/key/key/-/merge_requests/609)
    * [Translating DL contracts to JML](https://git.key-project.org/key/key/-/merge_requests/375) 
    * [Read `\profile` and `\settings` once](https://github.com/KeYProject/key/pull/3007)
    * [Stop the message about java_profile.jfr](https://git.key-project.org/key/key/-/merge_requests/590)
    * [Suppress logback message before configuration](https://git.key-project.org/key/key/-/merge_requests/591)
    * [Support for jdiv and jmod in SMT translation via definitions](https://git.key-project.org/key/key/-/merge_requests/547)
    * [Add gen folder to gitignore](https://git.key-project.org/key/key/-/merge_requests/598)
    * [Add Task runWithProfiler to execute key.ui with the  Java Flight Recoder](https://git.key-project.org/key/key/-/merge_requests/504)
    * [Load some (old) proofs with wrong/missing instantiations of \assumes in taclet app](https://git.key-project.org/key/key/-/merge_requests/516) 
    * [Specialized version of RuleContext::getText in TextualJMLAssertStatement::getClauseText](https://git.key-project.org/key/key/-/merge_requests/479)
    * [Multiplication for rule costs](https://git.key-project.org/key/key/-/merge_requests/541)

### 🐛 Bug Fixes

* [Bug fixes from the IdentityHashMap case study](https://git.key-project.org/key/key/-/merge_requests/499)
* [Remove highlighting artifacts in SequentView with Unicode symbols enabled](https://git.key-project.org/key/key/-/merge_requests/595)
* [Avoid tooltip NPE for incomplete proof nodes](https://github.com/KeYProject/key/pull/3037)
* [Always load correct example on double click](https://git.key-project.org/key/key/-/merge_requests/632) 
* [TokenMgrErr in issue dialogs](https://git.key-project.org/key/key/-/merge_requests/633)
* [Fix exception when parsing unknown source name in BuildingException](https://git.key-project.org/key/key/-/merge_requests/570)
* [Solve missing plugin in shadowJar by adding `mergeServiceFiles()`](https://git.key-project.org/key/key/-/merge_requests/545)
* [Fix Z3 counterexample generation](https://git.key-project.org/key/key/-/merge_requests/623)
* [Fix three memory leaks](https://git.key-project.org/key/key/-/merge_requests/573)
* [Keep original PositionInfo in ForToWhileTransformation](https://git.key-project.org/key/key/-/merge_requests/628)
* [Check for correct polarity when applying taclets](https://git.key-project.org/key/key/-/merge_requests/616)
* [Add triggers to textual representations of taclets](https://git.key-project.org/key/key/-/merge_requests/600)
* [Allow declaration of function symbols in custom key file and to use them in JML via \dl](https://git.key-project.org/key/key/-/merge_requests/602)
* [Fix leftover files that are not formatted properly](https://git.key-project.org/key/key/-/merge_requests/604)
* [Fix loop in strategy](https://git.key-project.org/key/key/-/merge_requests/129)
* [Fix PosInProgram](https://git.key-project.org/key/key/-/merge_requests/621)
* [Fix file filter for .proof.gz files](https://git.key-project.org/key/key/-/merge_requests/536)
* [Fixed rule "wellFormedStoreObjectEQ"](https://git.key-project.org/key/key/-/merge_requests/526)
* [Resolve "Taclet leaves a broken tree after failing to apply"](https://git.key-project.org/key/key/-/merge_requests/492)
* [Fix potential stack overflow in ExplorationStepsList](https://git.key-project.org/key/key/-/merge_requests/510)
* [Show message of the chained cause of the exception in IssueDialog](https://git.key-project.org/key/key/-/merge_requests/515)
* [Ensure that the condition of a JML assert statement is always a formula](https://git.key-project.org/key/key/-/merge_requests/530)
* [Fix widening casts and boxing of extension primitive types like bigint](https://git.key-project.org/key/key/-/merge_requests/583)
* [Fix construction of Javac issue dialog](https://github.com/KeYProject/key/pull/3008)
* [Fix handling of multiline log messages]( https://github.com/KeYProject/key/pull/3033)
* [Fix javacc deprecation warning]( https://github.com/KeYProject/key/pull/3016)
* [Fix ProofTreeView NPE](https://github.com/KeYProject/key/pull/3070)
* [Fix program element printing in proof saver](https://github.com/KeYProject/key/pull/3073)
* [Fix some positions being offset](https://github.com/KeYProject/key/pull/3084)
* [Fix type of `Long.MIN_VALUE` and `Long.MAX_VALUE`](https://github.com/KeYProject/key/pull/3100)
* [Activate Z3 if no other SMT solver is configured](https://github.com/KeYProject/key/pull/3048)
* [Register modifier when parsing JML spec](https://github.com/KeYProject/key/pull/3040)
* [Fix set statements (allow expressions on lhs, e.g. for array and field access)](https://git.key-project.org/key/key/-/merge_requests/566)
* [Fix IllegalArgumentException being thrown from IssueDialog](https://git.key-project.org/key/key/-/merge_requests/485)
* [Insert JML assume and assert statements in the right order](https://git.key-project.org/key/key/-/merge_requests/476) 
* [Make AbbrevMap::getTerm fulfill its contract and prevent a NPE](https://git.key-project.org/key/key/-/merge_requests/481)
* [A collection for some (straight forward) of the SonarQube reliability bugs](https://git.key-project.org/key/key/-/merge_requests/618)
* [Remove space from taclet proof save file name](https://git.key-project.org/key/key/-/merge_requests/568)
* [Resolve "Parsing exception: undeclared variable in an assignable declaration"](https://git.key-project.org/key/key/-/merge_requests/506) 
* [Fix for heap/permissions/threads example](https://git.key-project.org/key/key/-/merge_requests/527) 
* [Repairing JML interpretation of equality on floats and doubles.](https://git.key-project.org/key/key/-/merge_requests/524) 

* Further bug fixes: [#1664](https://git.key-project.org/key/key/-/merge_requests/474), [#1658](https://git.key-project.org/key/key/-/merge_requests/491), [#1652](https://git.key-project.org/key/key/-/merge_requests/495), [#1679](https://git.key-project.org/key/key/-/merge_requests/503), [#1681, #1682](https://git.key-project.org/key/key/-/merge_requests/507), [#1678](https://git.key-project.org/key/key/-/merge_requests/521), [#1685](https://git.key-project.org/key/key/-/merge_requests/512), [#1690](https://git.key-project.org/key/key/-/merge_requests/517), [#1706](https://git.key-project.org/key/key/-/merge_requests/538), [#1709](https://git.key-project.org/key/key/-/merge_requests/539), [#1684](https://git.key-project.org/key/key/-/merge_requests/511), [#1711](https://git.key-project.org/key/key/-/merge_requests/549), [#1707](https://git.key-project.org/key/key/-/merge_requests/601), [#1723](https://git.key-project.org/key/key/-/merge_requests/587), [#1598](https://git.key-project.org/key/key/-/merge_requests/513), [#3035](https://github.com/KeYProject/key/pull/3045) 

--- 
We like to thank our contributors for this release, namely: 

Alicia Appelhagen, Richard Bubel, Lukas Grätz, Christian Hein, Arne Keller, Michael Kirsten, Florian Lanzinger, Wolfram Pfeifer, Mike Schwörer, Benjamin Takacs, Samuel Teuber, Mattias Ulbrich, Alexander Weigl, Julian Wiesler

## 2.10.0 (2021-12-23)

### Core
* IMP: New SMT translation (!312), rework of the SMT communication (!381), and smaller fixes (!394)
* IMP: Renovating the KeY parser (!278)
* IMP: Rewrite of the JML parser in ANTLR (!306) with better exception message (!376)
* IMP: JML-Extension: Assert/Assume and *_free for block contracts (!342)
* FIX: Comment attachment in recoder (!399, !401)
* FIX: Collision of auxiliary contract (!396)
* FIX: Path handling of key files (!395)
* FIX: Pruning in closed branches looses rules (!388, #1480)
* FIX: Repaired file information if a directory is opened in KeY (!386, #1530)
* FIX: Proof loading in the CLI (!385)
* FIX: Invalid URLs under Windows (#1504, !264)
* FIX: lost error messages due to MalformedURLException (!290, #1529)
* FIX: catch headless to make key --auto runnable again (!382)
* FIX: `\singleton` of a non-location (e.g., `\singleton(3)`) now raises an error (!377)
* FIX: Completeness gap for array types (!367, #1566)
* FIX: add loop scope unwind (!326)


### UI 

* IMP: A better dialog for warnings (!374)
* IMP: Performance tuning and fixes for ProofTree (!391)
* IMP: Enables selection of proof in Proof Differences view (!256)
* IMP: Better SourceView Tooltip (!379)
* IMP: Add setting to disable load examples dialog window (!368)
* IMP: Enable syntax highlighting for JML starting with annotation markers (!325)
* FIX: make proof to load from bundle selectable (!237)
* FIX: Escaping comma when saving bookmarked filenames of KeYFileChooser (!387, #1551)
* FIX: make exception dialog able to show files in Jar files (!383)
* FIX: Resolve "SMT Option GUI throws NPE on startup" (!373)

### Development

* Enabling of SonarQube in Merge Requests (!323, !378)
* Dependency fixes for Gradle 7 (!372)

<!--
* NEW: *Proof Exploration* allows you to answer *What-If* questions on sequents.

### Scripts 

* NEW: Documentation support for proof scripts (!15)
* NEW: KeY Proof Scripts are ported from the Key Proof Script Debugger 
        (https://formal.iti.kit.edu/psdbg)
-->

*We like to thank all the contributor to this release:*

Alexander Weigl, 
Alicia Appelhagen,
Benjamin Takacs,
Florian Lanzinger, 
Jonas Schiffl, 
Julian Wiesler,
Lukas Grätz, 
Mattias Ulbrich, 
Michael Kirsten,
Richard Bubel, 
Wolfram Pfeifer

## 2.8.0 (2020-12-01)

### Logic

  * NEW: bsum taclets (!96)
  * NEW: Taclets for more flexible handling of observer depency (!177) 
  * NEW: Loop contracts improvements (!188)
  * NEW: Loop scopes: a new rule for proving loop invaraints (!313, !326)
  * NEW: Support for Annotation Marker in JML (!308)
  * NEW: created new file intDiv.key for newly added taclets concerning 
         (!182, !171, !180, !157, !152, !144, !141, !135, !98) 
  * NEW: SMT preparation macro (!165)
  * NEW: Completion Scopes (!305)
  * FIX: Bugfixing handling of program variables of type "any" and parsing (!133)
  * NEW: `\infinite_uniton(int x; x >= 0; this[x])` is now available in binder syntax:
         `(\infinite_uniton int x; x >= 0; this[x])`. 
         Old form is deprecated and will be removed in later versions. (!132)
  * NEW: Adding "System.arraycopy" with contract to JavaRedux (!137)
  * NEW: Explizit excption for nested updates (allowed in the KeY book, unsupported by implementation) (!319)
  * FIX: Speed up in saving proofs (!120)
  * FIX: Incompleteness issue when rewite taclet was applied and the goaltemplate… (!119)
  * NEW: Loop contract (!?, !73)
  * NEW: Loading and Storing proofs with compression (gzip) (!12)
  * NEW: Saving of proofs (incl. dependening resources) into one file (zip) called "proof bundle" (!237)
  * FIX: Fix of inner blocks (!82)
  * FIX: KeY read files character-wise, now the file content is cached (!XXX)
  * More jml synonyms (!85)
  * FIX: user-provided notes are saved within the proof file (!304)
  * FIX: Origin labels for user interactions could not be parsed
  * FIX: Method signature resolve in JML expressions (!309)


### UI

 * NEW: Unifying and polishing the user interface (!123): 
   - KeY uses a docking framework, including storable/loadable layouts (!189)
   - The settings are concentrated inside one dialog (!189, !266)
   - Adaptable colors and key strokes (!189, !236, !254)
   - Adaptable clutter rules (!7)
   - Key based navigation within the proof tree view (!198)
   - FIX: Handling of regex in search (!199)
   - NEW: Icons !227
 * NEW: Heatmaps: Coloring formulae on the sequent based on their change activity (!38, !140)
 * NEW: Saving of proof bundles (!148, !310)
 * NEW: View of the current source code marking executed parts. (!99, !260, !263, !267, !325)
 * NEW: GUI Extension inferface: You can easily plugin new GUI elements. 
 * NEW: Origin labels tracks the origin of formulae within a sequence (!122, !248)
 * NEW: Intraction logging (HacKeYthon'18) brings logging of user interaction 
        with exports to Proof Scripts (!84)
 * NEW: Proof exploration
 * NEW: Favourites in file dialogs (!252)
 * NEW: License dialog (!253)
 * NEW: View for proof differences based on formula distance matching (!255)
 * NEW: Schiffl's search filter (!4)
 * NEW: Pre-select previous selected contract in ProofManagementDialog (!287)
 * FIX: Parsing of char, integer and long literals (!9, #1446, !214, !196)
 * FIX: Collision of heatmap and search colors (!178)
 * FIX: Slightly less confusing presentation of SMT solver results (!160)
 * FIX: Cluttering with the status line (!244)
 * NEW: Allow macro application via keyboard shortcut from tree (!268)
 * NEW: Open Java files without considering a classpath (!243)
 
### Scripts 
  * NEW: Rewrite command (!51)
  * FIX: Several fixes and breaking changes: (!153, !146, !145)
  * NEW: Improvements to the proof scripts (!314)

### Environment 

 * NEW: Gradle became build tool  (!179, !205, !208, !209, !280)
   - Changes to the test infrastructure (!196)
   - Export of maven dependecies
   - New distribution formats: either a FatJar or zip file
 * NEW: Quality assessment via sonarqube and sonarcloud (!323)
 * Java 11 ready (!47)
   - remove of JavaFX dependencies (!95)
 * Integrate tests for well-definedness checks (!87 )

### Eclipse

  * Support of Eclipse PHOTON (!74)


### Seveal small and large bug fixes: 

(!331, !297, !296, !293,!290, !288, !286, !284, !277, !276, !273, !272, !271, !270, !265, !264, !234, !228, !227, !225, !224, !222, !219, !213, !212, 
!209, !208, !205, !203, !201, !200, !199, !192, !190, !173, !170, !167, !163, !162, !158, !156, 
!154, !153,  !151, !146, !145, !139, !136, !133, !131, !119, !117, 
!108, !99, !92, !83, !82, !81, !78, !77, !75, !73, !71, !70, !69, !68, 
!67, !66, !65, !58, !52, !47, !46, !45, !40, !39, !37, !33, !31, !30, !24,
!23, !22, !14, !13, !10, !9, !8, !7, !3, !2)


*We like to thank all the contributor to this release:*

Alexander Weigl, Carsten Csiky, Dominic Steinhöfel, Florian Lanzinger, Hans-Dieter Hiep, Jelle
Kübler, Jonas Schiffl, Lukas Grätz, Lulu Luong, Mattias Ulbrich, Michael Kirsten, Mihai
Herda, Peter Schmitt, Richard Bubel, Sarah Grebing, Wolfram Pfeifer



## 2.6.3 (2017-10-11)

## 2.6.2 (2017-04-13)

## 2.6.1 (2017-01-31)

## 2.6.0 (2016-12-22)

## 2.4.1 (2015-02-18)

## 2.4.0 (2015-02-17)

* Information flow reasoning
* Full support for symbolic execution with bitwise operations
* Improved test case generation
* Improved user interface
* Support for CVC4 SMT solver backend

## 2.2.3 (2014-10-06)

* Fix concurrency issue introduced in 2.2.2

## 2.2.2 (2014-07-11)

* Support for CVC3 version 2.4.1 SMT backend
* Bug fixes

## 2.2.1 (2014-05-27)

* Test case generation using bounded SMT (requires Z3, OpenJML)
* Bug fixes

## 2.2.0 (2014-04-29)

* Counter example generation using bounded SMT (requires Z3)
* Increased JML support / JML extensions
  * block contracts (extension) / assert statements
  * \min and \max numerical quantifiers
  * changed default semantics of signals_only to include unchecked exceptions
  * model methods (new implementation)
  * old clause (variable binder in contract)
  * nearly everything parseable
* Verification of a large class of recursive methods
  * generalized variants to all ordered sets
* Proof obligations for specification well-definedness
* Term labels
* Rule triggers (extended taclet syntax)
* More efficient handling of heap disjointness and heap selects
* Improved reasoning about bounded sums/products
* User Interfaces
  * rule focus for inner nodes
  * improved search
  * detailed proof statistics
  * auto save and quick save features
  * keyboard shortcuts
* Reduced memory footprint
* A lot of bug fixes
* Java 8 compatibility
* Re-implemented .key parser

##  2.0.2 (2013-09-19)

* Support for latest versions of Z3 and CVC3
* Windows 8 compatibility
* Fix a soundness issue with types and heap access
* Various bug fixes
 
##  2.0.1 (2013-06-19)
 
* Bug fixes
  * Incompleteness with Java integer arithmetics
  * Command line mode fixes
  * various other

##  2.0.0 (2013-04-18)
 
* New explicit heap modeling
  * Data types for location sets and heaps
  * The heap is now a special (local) variable
  * Dynamic frames
  * JML extension for dynamic frame specification
  * Re-implementation of JavaCard transactions
* Verification of (primitive) recursive methods
* Sequence ADT
* Nearly complete JML support
  * model fields and methods
  * initially clauses and class axioms
  * measured_by clauses
  * accessible clauses
  * sum and product comprehension
  * the \bigint type, mixed integer semantics
  * weak purity by default
  * reachability predicate
  * \index and \values keywords for enhanced for-loops
* Escape to dynamic logic from within JML
* MonKeY batch mode
* GUI changes
  * new dialog to enter invariants interactively
  * search in sequents and proof trees
  * logical symbols in Unicode
* Runnable from command line without windowing system
* Improved integration of SMT solvers
  * SMT-LIB 2.0 backend interface
  * possible to run multiple solvers in parallel
  * support for integer division (Z3 only)
* > 150 bug fixes
* Discontinued features
  * RTSJ support
  * Test case generation
  * OCL
  * Proof reuse

##  1.6.5 (2013-01-23)

* Minor bugfixes
* Java 7 compatibility

##  1.6.0 (2010-10-06)

* Support for Strings
* Enhanced JML support
* Improved integration of external SMT solvers
* Improved "verification-based testing" mechanism
* Real Time Java (RTSJ) calculus
* GUI improvements
* Various bugfixes


##  1.4.0 (2009-03-25)

* Unified proof obligation framework
  * sharing of proof obligations across different specification languages
  * unified API for adding new proof obligations
  * same GUI elements used for all specification languages
  * more elegant translation of \old, @pre-like constructs
* Improved JavaCard DL Specification interface
  * specification of DL invariants
* Rewrite of JML front-end
  * ghost variables/fields and JML set statement
  * non_null by default
  * \old in loop invariants supported
  * \object_creation(type) in JML assignable clauses
* New standalone OCL front-end
  * discontinued support for Borland Together integration
* Java language support enhancements:
  * enum types (partially)
  * inner and anonymous classes
  * enhanced for loop
  * variable method arguments
  * covariant method signature
* Generation of JML specifications
* Strictly pure queries can be pushed directly into an update
* Stable proof loading and saving
* Classpath directive
* various bugfixes


## 1.2.0 (2007-11-30)

* significantly improved proof strategies wrt. quantifier treatment
   and arithmetics
* improved proof tree view, i.e.
  * hiding of closed subtrees
  * hiding of intermediate proof steps
  * search in proof tree
* improved proof saving and loading
* includes _alpha_ version of the visual debugger
* various bugfixes

##  1.0.1:

* fixed an installation problem when KeY had not been installed before

##  1.0.0:


* KeY-Book examples are based on this version
  (except Schorr-Waite, which provides a developer version on
  the book example site)
* new proof-obligation generation framework
  * used currently only by the OCL translation;
    adaption of JML translation is underway
* new method lemma rule
* considerable improvements concerning arithmetics
* lots of bugfixes and improved stability

##  1.0pre1a:

* bug fixes and improvements
* polynomial integer simplification

##  1.0pre1:

* pre-release of upcoming 1.0
* several improvements and fixes


## 0.99.2 (?)

* fixed: Initialisation procedure of the KeY prover
  (KeY did not work properly if installed on a fresh system
  without a working KeY configuration file)
* fixed: Source Code Distribution 0.99.1 was way too big

##  0.99.1 (?)

* bug fixes concerning JML front-end

## 0.99 (?)

* first version with the JML front-end
* support of loop invariants
* lots of new stuff
  
[!616]: https://git.key-project.org/key/key/-/merge_requests/616
[!618]: https://git.key-project.org/key/key/-/merge_requests/618
[!619]: https://git.key-project.org/key/key/-/merge_requests/619
[!623]: https://git.key-project.org/key/key/-/merge_requests/623