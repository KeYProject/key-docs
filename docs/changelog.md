# Changelog

## Upcoming: 2.12.0 (2023-08-02)

### Core

* **BREAK:** Minimum required Java version is 11. (!380)
* NEW: [Proof Slicing](user/ProofSlicing.md) system
* NEW: [Proof Caching](user/ProofCaching.md) system
* IMP: Removal of the Eclipse Plugins. Eclipse support is now shipped in [keyclipse repository](https://git.key-project.org/key/keyclipse) (!390)
* IMP: Removal of `System.out/err` in favor for logging with SLF4J (!240)
* IMP: Translation of the last DL contracts to JML contracts. (!375)
* ?? IMP: Logical Infrastructure for final values independent from the heap
* ?? IMP: Subscripts in SequentView
* Bring INVISMT to KeY; Refactors SolverTypes (!406)
* Performance: Switching sequents (!482)
* No dependencies as local jar files (!484)
* change SwitchToIf to create a if-else cascade (!444)
* More proof script commands: hide and unhide. (!486)
* Enables JavaDL data types in ghost and model fields (!469)
* insert jml assume and assert statements in the right order (!476)
* Fix comment attachment in recoder (!399)
* Restore RECODER-0.84 (!424)
* Update dependencies (!467)

### UI
* IMP: More functionality in statistics dialog

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
  
