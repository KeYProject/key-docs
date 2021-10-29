# SMT Translation

##### Abstract
> This document is aimed at Developers who wish to contribute to the KeY-SMT integration,
> particularly the translation from KeY sequents to SMTLIB.

## Overview
The main class for SMT translation, `ModularSMTLib2Translator`, is instantiated in the `SolverType`
class. It is responsible for extracting high-level information from the sequent to be translated
(such as the type hierarchy), and for writing the translation result back to KeY. The actual
translation is orchestrated by a `MasterHandler`, which has access to a set of handlers for specific
terms. All of these implement the `SMTHandler` interface. The `MasterHandler` schedules a term for
translation and delegates it to a handler that reports it can handle terms of the given type. If the
term contains subterms, the `MasterHandler` is called again recursively to translate these. The
result of the translation is an SMTLIB S-Expression.

seqdiag {
    ModularSMTLib2Translator -> MasterHandler [label = "Term"]
    MasterHandler -> SMTHandler [label = "canHandle(Term)"];
    MasterHandler <-- SMTHandler [label = "Capability"];
    MasterHandler -> SMTHandler [label = "handle(MasterHandler, Term)"];
    MasterHandler <- SMTHandler [label = "translate(Term)"];
    MasterHandler -> MasterHandler [label = "recursion"]
    MasterHandler --> SMTHandler [dotted, label = "handle(MasterHandler, Term)"];
    MasterHandler <-- SMTHandler [label = "SExpr"];
    ModularSMTLib2Translator <- MasterHandler [label = "SExpr"]
}

## Adding a new Handler

A handler is responsible for KeY terms of a certain type (e.g., boolean connectors, integer
arithmetic, quantifiers, ...). Adding a new handler requires taking the following steps:
1. Create the new Handler in the `de.uka.ilkd.key.smt.newsmt2` package and make it extend the
   `SMTHandler` interface
2. Implement the `canHandle()`, `handle()`, and `init()` methods
3. Add the name of the new class to the
   `/key/key.core/src/main/resources/META-INF/services/de.uka.ilkd.key.smt.newsmt2.SMTHandler` file
4. If your handler needs needs axioms or function declarations, add a file to the
   key/key.core/src/main/resources/de/uka/ilkd/key/smt/newsmt2 folder. The filename should be the
   same as the Java class, but the file extension should be `.preamble.xml`. Axioms and declarations
   are added as SMTLIB within XML `entry` tags. The axioms and declarations will be loaded on
   demand, if a term of the corresponding handler type is found on the sequent.
   
   Example (from `BooleanConnectiveHandler.preamble.xml`):
   
   ``` xml
   <entry key="bool.decls">
(declare-fun u2b (U) Bool)
(declare-fun b2u (Bool) U)
(declare-const sort_boolean T)
    </entry>

    <entry key="bool.axioms">
(assert (instanceof (b2u true) sort_boolean))
(assert (instanceof (b2u false) sort_boolean))
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))
    </entry>
   ```
