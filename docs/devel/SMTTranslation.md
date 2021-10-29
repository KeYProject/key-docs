# SMT Translation

##### Abstract
> This document is aimed at Developers who wish to contribute to the KeY-SMT integration,
> particularly the translation from KeY sequents to SMTLIB.

## Overview
The main class for SMT translation, `ModularSMTLib2Translator`, is instantiated in the `SolverType`
class. It is responsible for extracting high-level information from the sequent to be translated
(such as the type hierarchy), and for writing the translation result back to KeY. The actual
translation is orchestrated by a `MasterHandler`, which has access to a set of handlers for specific
terms. All of these implement the `SMTHandler` interface. The `MasterHandler` schedules a Term for
translation and delegates it to a handler that reports it can handle terms of the given type. If the
term contains subterms, the `MasterHandler` is called again recursively to translate these. The
result of the translation is an SMTLIB S-Expression.

seqdiag {
    -> MasterHandler [label = "Term"]
    MasterHandler -> SMTHandler [label = "canHandle(Term)"];
    MasterHandler <-- SMTHandler [label = "Capability"];
    MasterHandler -> SMTHandler [label = "handle(MasterHandler, Term)"];
    MasterHandler <- SMTHandler [label = "translate(Term)"];
    MasterHandler -> MasterHandler [label = "recursion"]
    MasterHandler --> SMTHandler [dotted, label = "handle(MasterHandler, Term)"];
    MasterHandler <-- SMTHandler [label = "SExpr"];
    <- MasterHandler [label = "SExpr"]
}
