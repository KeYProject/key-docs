# Grammar

In KeY, there are multiple formal languages for reading specification and
logical constructs. 

On the specification we have `JML*` -- a dialect of the Java Modeling Language
-- which comes within the Java files. JML specification are parsed and
interpreted into `JavaDL` expression. `JavaDL` are represented by the `Term`
class hierarchy. They can be pretty-printed with the `LogicPrinter` and read by
facade of the `KeyParser`. Also the `KeyParser` is used to read declarations of
logical constructs: i.e. *sorts*, *predicates*, *functions*, *taclets*,
*transformers*, *taclet choices*, and problem options and definitions.

In the following we dive into the `KeyParser`, the term hierarchy and operators
hierarchy and the expression and declaration syntax.

Internally, every expression is a tree of `Term`s, whereas the `Term` class
defines a homomorph *Abstract Syntax Tree* (AST). Each `Term` has an operator,
which defines its meaning, and a list of sub-terms. The internal representation
of term is its prefix form, in which the term is printed as a tree of function
application.

This format is not intuitive for humans, hence we defined an syntax that also
uses infix and postfix notions.

## Expression Syntax 

Precedence:

1. Label on functions (`term «label»`)
1. Parallel (`||`) *updates only*
1. Assignment (`term := term`) *updates only*
2. Equivalence (`<->`)
3. Implication (`->`)
4. Disunction (`|`)
5. Conjunction (`&`)
6. Equalities (`=`, `!=`), Negation (`! term`), Quantifier , Modality 
7. Comparison (`<, <=, >=, >`) 
8. Arithmetik (`+,-`)
9. Multiplicaiton (`*`)
10. Division (`/` and Modulo (`%`)
11. Unary minus (`- term`)
12. Cast (`(sort) term`)
13. Bracket suffixes, (`term[i]`, `term[1,5]`, `term[*]`, `term[a:=2]`) 
14. Final primitives: 
  * Parens (`( term )`)
  * Location set, Location term
  * Substitution `{\subst x; y} f(x)`
  * If-then-else and Ifex-then-else (`\if (a) TRUE \else b`) 
  * Abbreviaton (`@name`)
  * Function names and application (`T.(U::a)`, `t.query()`, `a.b@heap2`)
  * Literals


## Declaration Syntax and Keywords

## Reference 

### SORTS {: #Token-SORTS}

#### GENERIC {: #Token-GENERIC}

#### PROXY {: #Token-PROXY}

#### EXTENDS {: #Token-EXTENDS}

#### ONEOF {: #Token-ONEOF}

#### ABSTRACT {: #Token-ABSTRACT}

## SCHEMAVARIABLES {: #Token-SCHEMAVARIABLES}

### SCHEMAVAR {: #Token-SCHEMAVAR}

## MODALOPERATOR {: #Token-MODALOPERATOR}

### PROGRAM {: #Token-PROGRAM}

### FORMULA {: #Token-FORMULA}

### TERM {: #Token-TERM}

### UPDATE {: #Token-UPDATE}

## VARIABLES {: #Token-VARIABLES}

## VARIABLE {: #Token-VARIABLE}

## HEURISTICSDECL {: #Token-HEURISTICSDECL}

# Definition of Taclets

## General definition

## Goals 
### CLOSEGOAL {: #Token-CLOSEGOAL}
## REPLACEWITH {: #Token-REPLACEWITH}
## ADDRULES {: #Token-ADDRULES}
## ADDPROGVARS {: #Token-ADDPROGVARS}

## Attributes 

### NONINTERACTIVE {: #Token-NONINTERACTIVE}
### DISPLAYNAME {: #Token-DISPLAYNAME}
### HELPTEXT {: #Token-HELPTEXT}
### HEURISTICS {: #Token-HEURISTICS}

## FIND {: #Token-FIND}

## ADD {: #Token-ADD}

## ASSUMES {: #Token-ASSUMES}


## Variable Conditions

Variable conditions are additionally conditions that can be added to taclets
with the help of the `\varcond(...)` construct. Consider the example:

```
rules {
  xyz {
    \find(...)
    
    \varcond(\new(#boolv, boolean))
    
    \replacewidth(...)
  
  }
}
```

Internally, variable conditions correspond the `MatchCondition` class. With the
new parser creating and adding variable conditions will be simplified.

### `\sameObserver` (SAME_OBSERVER {:#Token-SAMEOBSERVER}

A variable condition that is satisfied if the two arguments are schema
variables, their instantiations are terms of observer functions, with the same
function, which as exactly one heap argument and has got a dependency contract,

*Limitations:* Currently, this and
`de.uka.ilkd.key.rule.metaconstruct.ObserverEqualityMetaConstruct` only support
observers with a single heap argument, that should be generalised.


### `\skolemTerm` (SKOLEMTERM) {: #Token-SKOLEMTERM}

### `\applyUpdateOnRigid`

### `\simplifyIfThenElseUpdate` 

### `\skolemFormula` SKOLEMFORMULA {: #Token-SKOLEMFORMULA}

### `\termLabel` TERMLABEL {: #Token-TERMLABEL}

### `\modifies` MODIFIES {: #Token-MODIFIES}

### PROGRAMVARIABLES {: #Token-PROGRAMVARIABLES}

### SAME_OBSERVER {: #Token-SAME_OBSERVER}

### VARCOND {: #Token-VARCOND}

### APPLY_UPDATE_ON_RIGID {: #Token-APPLY_UPDATE_ON_RIGID}

### DEPENDINGON {: #Token-DEPENDINGON}

### DISJOINTMODULONULL {: #Token-DISJOINTMODULONULL}

### DROP_EFFECTLESS_ELEMENTARIES {: #Token-DROP_EFFECTLESS_ELEMENTARIES}

### DROP_EFFECTLESS_STORES {: #Token-DROP_EFFECTLESS_STORES}

### SIMPLIFY_IF_THEN_ELSE_UPDATE {: #Token-SIMPLIFY_IF_THEN_ELSE_UPDATE}

### ENUM_CONST {: #Token-ENUM_CONST}

### FREELABELIN {: #Token-FREELABELIN}

### `\hasSort` (HASSORT) {: #Token-HASSORT}

### `\fieldType` FIELDTYPE {: #Token-FIELDTYPE}

### FINAL {: #Token-FINAL}

### ELEMSORT {: #Token-ELEMSORT}

### HASLABEL {: #Token-HASLABEL}

### HASSUBFORMULAS {: #Token-HASSUBFORMULAS}

### ISARRAY {: #Token-ISARRAY}

### ISARRAYLENGTH {: #Token-ISARRAYLENGTH}

### ISCONSTANT {: #Token-ISCONSTANT}

### ISENUMTYPE {: #Token-ISENUMTYPE}


### ISINDUCTVAR {: #Token-ISINDUCTVAR}

### ISLOCALVARIABLE {: #Token-ISLOCALVARIABLE}

### ISOBSERVER {: #Token-ISOBSERVER}

### DIFFERENT {: #Token-DIFFERENT}

### METADISJOINT {: #Token-METADISJOINT}

### ISTHISREFERENCE {: #Token-ISTHISREFERENCE}

### DIFFERENTFIELDS {: #Token-DIFFERENTFIELDS}


### ISREFERENCE {: #Token-ISREFERENCE}

### ISREFERENCEARRAY {: #Token-ISREFERENCEARRAY}

### ISSTATICFIELD {: #Token-ISSTATICFIELD}

### ISSUBTYPE {: #Token-ISSUBTYPE}

### EQUAL_UNIQUE {: #Token-EQUAL_UNIQUE}

### NEW {: #Token-NEW}

### NEW_TYPE_OF {: #Token-NEW_TYPE_OF}

### NEW_DEPENDING_ON {: #Token-NEW_DEPENDING_ON}

### HAS_ELEMENTARY_SORT {: #Token-HAS_ELEMENTARY_SORT}

### NEWLABEL {: #Token-NEWLABEL}

### CONTAINS_ASSIGNMENT {: #Token-CONTAINS_ASSIGNMENT}

### NOT_ {: #Token-NOT_}

### NOTFREEIN {: #Token-NOTFREEIN}

### SAME {: #Token-SAME}

### STATIC {: #Token-STATIC}

### STATICMETHODREFERENCE {: #Token-STATICMETHODREFERENCE}

### MAXEXPANDMETHOD {: #Token-MAXEXPANDMETHOD}

### STRICT {: #Token-STRICT}

### TYPEOF {: #Token-TYPEOF}

### INSTANTIATE_GENERIC {: #Token-INSTANTIATE_GENERIC}

### SUBST {: #Token-SUBST}

# Term constructs 


## if-then-else {: #Token-IF} {: #Token-THEN} {: #Token-ELSE}

## A binding if-then-else  {: #Token-IFEX}


# File constructs

## INCLUDE {: #Token-INCLUDE}

## INCLUDELDTS {: #Token-INCLUDELDTS}

## CLASSPATH {: #Token-CLASSPATH}

## BOOTCLASSPATH {: #Token-BOOTCLASSPATH}

## NODEFAULTCLASSES {: #Token-NODEFAULTCLASSES}

## JAVASOURCE {: #Token-JAVASOURCE}

## WITHOPTIONS {: #Token-WITHOPTIONS}

## OPTIONSDECL {: #Token-OPTIONSDECL}

## KEYSETTINGS {: #Token-KEYSETTINGS}

## PROFILE {: #Token-PROFILE}

## TRUE {: #Token-TRUE}

## FALSE {: #Token-FALSE}

## SAMEUPDATELEVEL {: #Token-SAMEUPDATELEVEL}

## INSEQUENTSTATE {: #Token-INSEQUENTSTATE}

## ANTECEDENTPOLARITY {: #Token-ANTECEDENTPOLARITY}

## SUCCEDENTPOLARITY {: #Token-SUCCEDENTPOLARITY}



## TRIGGER {: #Token-TRIGGER}

## AVOID {: #Token-AVOID}

## PREDICATES {: #Token-PREDICATES}

## FUNCTIONS {: #Token-FUNCTIONS}

## TRANSFORMERS {: #Token-TRANSFORMERS}

## UNIQUE {: #Token-UNIQUE}

## RULES {: #Token-RULES}

## AXIOMS {: #Token-AXIOMS}

## PROBLEM {: #Token-PROBLEM}

## CHOOSECONTRACT {: #Token-CHOOSECONTRACT}

## PROOFOBLIGATION {: #Token-PROOFOBLIGATION}

## PROOF {: #Token-PROOF}

## PROOFSCRIPT {: #Token-PROOFSCRIPT}

## CONTRACTS {: #Token-CONTRACTS}

## INVARIANTS {: #Token-INVARIANTS}

## LEMMA {: #Token-LEMMA}

## IN_TYPE {: #Token-IN_TYPE}

## IS_ABSTRACT_OR_INTERFACE {: #Token-IS_ABSTRACT_OR_INTERFACE}

## CONTAINERTYPE {: #Token-CONTAINERTYPE}

## LOCSET {: #Token-LOCSET}

## SEQ {: #Token-SEQ}

## BIGINT {: #Token-BIGINT}

## UTF_PRECEDES {: #Token-UTF_PRECEDES}

## UTF_IN {: #Token-UTF_IN}

## UTF_EMPTY {: #Token-UTF_EMPTY}

## UTF_UNION {: #Token-UTF_UNION}

## UTF_INTERSECT {: #Token-UTF_INTERSECT}

## UTF_SUBSET {: #Token-UTF_SUBSET}

## UTF_SETMINUS {: #Token-UTF_SETMINUS}

## SEMI {: #Token-SEMI}

## SLASH {: #Token-SLASH}

## COLON {: #Token-COLON}

## DOUBLECOLON {: #Token-DOUBLECOLON}

## ASSIGN {: #Token-ASSIGN}

## DOT {: #Token-DOT}

## COMMA {: #Token-COMMA}

## LPAREN {: #Token-LPAREN}

## RPAREN {: #Token-RPAREN}

## LBRACE {: #Token-LBRACE}

## RBRACE {: #Token-RBRACE}

## LBRACKET {: #Token-LBRACKET}

## RBRACKET {: #Token-RBRACKET}

## AT {: #Token-AT}

## EQUALS {: #Token-EQUALS}

## EXP {: #Token-EXP}

## TILDE {: #Token-TILDE}

## PERCENT {: #Token-PERCENT}

## STAR {: #Token-STAR}

## MINUS {: #Token-MINUS}

## PLUS {: #Token-PLUS}

## GREATER {: #Token-GREATER}

## LESS {: #Token-LESS}

## DOC_COMMENT {: #Token-DOC_COMMENT}

## ML_COMMENT {: #Token-ML_COMMENT}

## MODALITYD {: #Token-MODALITYD}

## MODALITYB {: #Token-MODALITYB}

## MODALITYBB {: #Token-MODALITYBB}

## MODAILITYGENERIC1 {: #Token-MODAILITYGENERIC1}

## MODAILITYGENERIC2 {: #Token-MODAILITYGENERIC2}

## MODAILITYGENERIC3 {: #Token-MODAILITYGENERIC3}

## MODAILITYGENERIC4 {: #Token-MODAILITYGENERIC4}

## MODAILITYGENERIC5 {: #Token-MODAILITYGENERIC5}

## MODAILITYGENERIC6 {: #Token-MODAILITYGENERIC6}

## MODAILITYGENERIC7 {: #Token-MODAILITYGENERIC7}

## MODALITYD_END {: #Token-MODALITYD_END}

## MODALITYG_END {: #Token-MODALITYG_END}

## MODALITYB_END {: #Token-MODALITYB_END}

## MODALITYBB_END {: #Token-MODALITYBB_END}

