# ChangeLog

## 2.8.0 (2019-XX-XX)

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
