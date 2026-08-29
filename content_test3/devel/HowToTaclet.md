---
approved: True
approved_by: dd
approved_date: 2026-08-11
title: How to write new taclets
weight: 100
---

# How to write new taclets

New prover rules in KeY can be added in form of built-in rules[^1] written in plain
Java code and as so-called "taclets" ("schematic theory-specific rules").
Taclets permit for an easy-readable definition of rules; when a taclet is
applied during a proof, the taclet itself as well as the instantiation of its
schematic parts are displayed to the user, making the rule application more
transparent. Almost all rules implemented for KeY are defined as taclets (with
the exception of special rules like method contract application, loop invariant
application (so far) and one-step-simplification). For information about
taclets, please consult the [book chapter "Proof Search with Taclets"](https://link.springer.com/chapter/10.1007/978-3-319-49812-6_4) of the
2nd KeY book.

This article covers the necessary basics for adding new taclets to the KeY
system. In particular, the following topics are discussed:


##  How to add a taclet

The standard location for `.key` files containing taclets is in the `key.core`
project, location `resources/de/uka/ilkd/key/proof/rules` (*note*: unless stated
otherwise, all locations in this article are relative to the main source root of `key.core`).
The file `standardRules.key` lists all the taclet files that are are loaded as defaults
when starting KeY with the Java profile. New taclets can be added to either of
the existing files listed there (if they fit into the scope), or can be added to
a new file which is then referred to in `standardRules.key`.

The standard rule file can be obtained from a profile
(`de.uka.ilkd.key.proof.init.Profile`) via the method `getStandardRules()`. The
class `de.uka.ilkd.key.proof.init.JavaProfile`, for example, sets the standard
rules to the aforementioned `standardRules.key`. If one wishes to add taclets
that are unrelated to Java, that taclet should be referred to from the standard
rules collection of an appropriate profile.

Taclets can be added to "rule sets" which are used, e.g., by strategy
heuristics. Default rule sets are defined in the file
`resources/de/uka/ilkd/key/proof/rules/ruleSetsDeclarations.key`.
How taclets are matched against sequents and selected for automatic
application is described in
[The Rule Application Pipeline](../RuleApplicationPipeline/).

### Quick example

Consider the definition of `cut_direct` below (part of `propRule.key`).

```
\schemaVariables {
  \formula cutFormula;
}

\rules {
  cut_direct {
    \find(cutFormula)
    \sameUpdateLevel
    "CUT: #cutFormula TRUE" [main]:
        \replacewith(true) \add(cutFormula ==>);
    "CUT: #cutFormula FALSE":
        \replacewith(false) \add( ==> cutFormula)
    \heuristics(cut_direct)
  };
}
```

First, we need to define the variables we want to use in the taclet.
This is the `\schemaVariables` block at the start of the `.key` file.
We only require a single `\formula` type schema variable called `cutFormula`.

Then, we define the actual taclets in this file by creating a `\rules` block.
For the purposes of this example, we limit ourselves to the cut_direct taclet.
`propRule.key` contains many more taclets.
The `\rules` block contains the taclet definitions, each of which begins with the name of the taclet
("cut_direct"), creating a new block defined by curly brackets and a semicolon at the end.

Since the `\find(...)` part of the taclet definition does not contain a `==>`, the `cut_direct` taclet finds (matches) a sub-term anywhere in a sequent formula.
The application restriction flag `\sameUpdateLevel` ensures that the `\find(...)` and `\add(...)` parts are
under the same update application (or none). 

!!! info

  Since KeY 3.0, `\sameUpdateLevel` is the default for all (relevant) taclets
  and does not need to be added manually. Use `\ignoreUpdateLevel` to switch
  it off.

The taclet creates two new branches, which are defined directly afterwards.
The first branch is labeled "CUT: #cutFormula TRUE".
In this branch, the found sub-term is replaced with true (`\replacewith(true)`), and the found sub-term is added as a new sequent formula to the antecedent: `\add(cutFormula ==>)`.

A particular branch of the taclet can be tagged by enclosing the tag in brackets.
This tag must be written after the branch label.
The first branch in this example is tagged with "main".
This particular value causes the branch to be visually continued on the parent branch if [the linearized Proof Tree mode](../../user/ProofTreeLinearMode/) is active.

The second branch of the taclet is labeled "CUT: #cutFormula FALSE".
In this branch, the found sub-term is replaced with false (`\replacewith(false)`), and the found sub-term is added as a new sequent formula to the succedent: `\add( ==> cutFormula)`.

Finally, the taclet is added to the `cut_direct` heuristics group.

## Automatically Generating Additional Taclets

KeY 3.1 allows for automatic generation of "derived" taclets. This is
especially helpful for "EQ" taclets, which are commonly used to achieve more
performant automation. Assume a taclet like `elementOfUnion`:

```key
elementOfUnion {
  \schemaVar \term Object o;
  \schemaVar \term Field f;
  \schemaVar \term LocSet s, s2;

  \find(elementOf(o, f, union(s, s2)))

  \replacewith(elementOf(o, f, s) | elementOf(o, f, s2))

  \heuristics(simplify_enlarging)
  \generate(\EQ(union(s, s2)))
};
```

This taclet can only be applied when `union(s, s2)` is directly in the
`elementOf` function. But a common situation is a sequent such as
```
s1 = union(s, s2),
==>
elementOf(o, f, s1)
```
where `union(s, s2)` has been "pulled out" into `s1`.

We can use _taclet generators_ to deal with this case easily. The
`\generate(\EQ(...))` generates the following taclet automatically:

```key
elementOfUnionEQ {
  \schemaVar \term Object o;
  \schemaVar \term Field f;
  \schemaVar \term LocSet s, s2;
  \schemaVar \term LocSet EQ;

  \assumes(union(s, s2) = EQ ==>)
  \find(elementOf(o, f, EQ))

  \replacewith(elementOf(o, f, s) | elementOf(o, f, s2))

  \heuristics(simplify_enlarging)
};
```

Note that an `\assumes(...)` part with an equation is added and how the term
given to `\EQ(...)` is replaced in `\find(...)`. The `\find` parts of any rules
in `\addrules` are also altered the same way. Rule sets are copied from the
original taclet but can be altered by `\EQ(union(s, s2) : concrete)`.

At the moment, `\EQ` is the only supported generator.

## How to extend the taclet language

{{% alert type="danger" %}}
This section does not reflect recent KeY developments. [The parser was recently rewritten](../../devel/NewKeyParser/).
{{% /alert %}}

Sometimes, especially when one wants to introduce new symbolic execution
concepts, the existing taclet language is not expressive enough and has to be
extended. There are four things one might have to extend to support new taclet
features: (1) The taclet parsers; this includes the parser for the taclet
language itself (which usually will not have to be changed) and the parser for
new program constructs, (2) for matching different classes of statements,
corresponding model classes will have to be added to the system, which are then
referred to in factory classes and the parser(s), (3) whenever the standard
find-replace pattern of taclets is not sufficient, one can add "transformers"
performing more complex actions during taclet execution, and (4) when taclets
depend on additional input such as specifications, one can define (automatic or
interactive) completions for the taclet. We'll discuss all those points in the
following.

It might be helpful to learn about the process by examples. To
get started, an example for a new program statement used for matching is
`merge_point`, the keyword for a merge point statement. A simpler one is
`ForLoop`, a schema variable matching for loops. If you search for those
identifiers in all files in the project, you'll find the entry points
needed for extensions. Note that merge points are also used in JML
specifications, which is a different topic (therefore, you might want to ignore
the corresponding parser files `KeYJMLPre{Lexer, Parser}.g`, basically everything
in the `(...)/speclang/jml` directory). An example for a transformer is the
`#for-to-while` construct which accepts a for loop as input and transforms it to
a while loop. Your friends here are the eclipse functionalities `Search -> File`
(use `*.*` as a pattern here, and only search in the key.core project), `Ctrl+T`
for finding types, and `Ctrl+R` for finding resources.

### Parsing

There are several relevant parsers you might need to know. The "main KeY
parser," `src/main/antlr4/JavaKeY{Lexer, Parser}.g4` is an ANTLR4 parser
which covers KeY's language for sorts, terms, formulas etc., taclets, and proof
files. For most extensions, this file does not need to be touched. It extends
the more general, largely Java-independent parser in `key.ncore/main/antlr/`.

We use an [extension of the JavaParser project](https://github.com/jmltoolkit/jmltk)
to parse Java and the KeY's
extentions for Java, such as schema variables or KeY specific constructs.
In its JavaCC file, you find definitions for `#for-to-while` and
`merge_point`.

So, if for your taclet the basic taclet language has to be changed, adapt
`(Java)KeYParser.g4` accordingly and for creating new transformers or language
extensions, the JavaParser
is the relevant parser. The best
advice here is to have a look at the existing definitions to see how to add
a new one. Note that at the same time when extending the parser by new
transformers or statement types, you will also have to add new Java classes and
extend factories. We cover this in the next section.

### New Program Statement / Expression Types

There are two categories of extensions: (1) New program schema variable sorts,
which match existing programming language fragments, and (2) extensions to the
language, e.g. by artificial constructs needed for a proof / symbolic
execution technique.

A new "matcher sort" for taclets is added quite easily. As an example, take the
"loop init" clause of a for loop. A corresponding schema variable for the use in
taclets can be declared as `\program LoopInit #loopInit;`. After that,
`#loopInit` can be used in a taclet to match a loop init clause. It suffices to
declare a new "program schema variable sort" in
`de.uka.ilkd.key.logic.sort.ProgramSVSort` (for instance `LoopInitSort` in the
example) which calls the constructor of `ProgramSVSort` with the identifier by
which it later should be referred to in taclet definitions.

A language extension like the merge points has to be added to several parts in the system: 

1. A parser model extension is added in [JML ToolKit](https://github.com/jmltoolkit/jmltk)
(see `MergePointStatement.java` for an example).
2. A mirror of the parser extension for the logic side of KeY is added to
`de/uka/ilkd/key/java/statement/` (also here, there's a `MergePointStatement.java`).
3. A converter for the parser model extension to the logic representation in
`de/uka/ilkd/key/java/loader/JP2KeYConverter.java`. Look what's done for the
`MergePointStatement`.
4. Extension of Java visitor classes: Classes `Visitor.java`,
`JavaASTVisitor.java`, `CreatingASTVisitor.java`, and `ProgVarReplaceVisitor.java`
in directory `de/uka/ilkd/key/java/visitor/`. Note that not all of these might 
apply to you, e.g. if your new statement does not contain program variables that
might have to be substituted in a proof.
5. Extension of the pretty printer to nicely render your extension in sequents:
`de/uka/ilkd/key/java/PrettyPrinter.java`.


### New Meta Constructs / Transformers

Meta constructs give additional powers to taclets. By them, it is even possible
to create taclets which are actually built-in rules since all the work (maybe
except for some matcher preprocessing) is deferred to a powerful transformer.
Note that we discourage from using that style; meta constructs should be used at
a very small scope. If that's not possible, directly using built-in rules is
a more "honest" and better maintainable approach.

Our running example here is the `#for-to-while` construct (actually an example
for the bad style of delegating everything to a transformer). For adding
transformers this to the system, follow these steps:

1. Add a model class to the directory `src/de/uka/ilkd/key/rule/metaconstruct/`
(see e.g. `ForToWhile.java`). The class should extend `ProgramTransformer` and
pass the keyword to be used to the super class, here `#for-to-while`.
2. Extend the `visit(MetaConstruct, Void)` method in `src/de/uka/ilkd/key/java/JP2KeYConverter` 
to return the new class when appropriate. See what's done for `#for-to-while`.
3. Add the construct to [the parser](https://github.com/jmltoolkit/jmltk).

### Completions

Sometimes the input to a taclet depends on other information than that available
from a current proof situation (i.e., a sequent). In that case, the rule has to
be completed before it is applied. A good example is the rule "cut"
(`resources/de/uka/ilkd/key/proof/rules/classicalLogic/propRule.key`) defined as follows:

```key
\schemaVariables {
  \formula cutFormula;
}
cut { "CUT: #cutFormula TRUE":\add (cutFormula ==>);
      "CUT: #cutFormula FALSE":\add (==> cutFormula)
      \heuristics(cut) };
```

The formula `cutFormula` is not obtained from the sequent, it's left as a "hole"
in the definition. When applying the rule in KeY, a standard dialog will pop up
asking for an instantiation of "curFormula".

For certain situations, special completions are required. A classic example are
rules depending on specification, like loop invariant or method contract rule
applications. To this end, custom completions implementing
`/key.ui/src/de/uka/ilkd/key/gui/InteractiveRuleApplicationCompletion.java`
(note: this class is the first not residing in the key.core project) can be
added and registered in
`/key.ui/src/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java`.

{{% alert type="warning" %}}
Obviously, interactive rule application completions are currently
only designed to handle BuiltInRules. So for taclets, this will have to be
adapted!
{{% /alert %}}

Alternatively to the implementation of an interactive completion, additional
information, like for instance a specification, could be retrieved by special
meta constructs. Specifications are stored in
`de.uka.ilkd.key.proof.mgt.SpecificationRepository` and can be retrieved via
a call like `services.getSpecificationRepository().getLoopSpec(loop)`. If the
specification repository already contains the means to store that specification,
this should be quite straightforward to accomplish.


---

## Variable Conditions

### `\alwaysAbnormallyTerminates`

This is a variable condition, that checks if a given variable binds new variables.

**Signatures**

* `\alwaysAbnormallyTerminates(VARIABLE)`
* `\not\alwaysAbnormallyTerminates(VARIABLE)`




### `\applyUpdateOnRigid`

This variable condition can be used to check whether an update can be performed on a formula or
term.
That is the case if the top-level operator is rigid and of arity greater than 0.

**Signatures**

* `\applyUpdateOnRigid(VARIABLE, VARIABLE, VARIABLE)`




### `\containsAssignment`

This variable condition can be used to check whether an assignment expression occurs as a
subexpression of a schemavariable instantiation,

**Signatures**

* `\containsAssignment(VARIABLE)`
* `\not\containsAssignment(VARIABLE)`




### `\different`



**Signatures**

* `\different(VARIABLE, VARIABLE)`




### `\differentFields`

This variable condition checks if given two terms s, t both terms have a different unique symbol
as top level operator

**Signatures**

* `\differentFields(VARIABLE, VARIABLE)`




### `\disjointModuloNull`

General varcond for checking relationships between types of schema variables.

**Signatures**

* `\disjointModuloNull(TYPE_RESOLVER, TYPE_RESOLVER)`




### `\dropEffectlessElementaries`



**Signatures**

* `\dropEffectlessElementaries(VARIABLE, VARIABLE, VARIABLE)`




### `\dropEffectlessStores`



**Signatures**

* `\dropEffectlessStores(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`




### `\equalUnique`



**Signatures**

* `\equalUnique(VARIABLE, VARIABLE, VARIABLE)`




### `\fieldType`

Variable condition that enforces a given generic sort to be instantiated with the type of a field
constant.

The condition can only be fulfilled if the given field term is constant of which the referred
type is known.

**Signatures**

* `\fieldType(VARIABLE, SORT)`




### `\final`

ensures that the given instantiation for the schema variable denotes a final field

**Signatures**

* `\final(VARIABLE)`
* `\not\final(VARIABLE)`




### `\freeLabelIn`



**Signatures**

* `\freeLabelIn(VARIABLE, VARIABLE)`
* `\not\freeLabelIn(VARIABLE, VARIABLE)`




### `\getFreeInvariant`

Extracts the free loop invariants for the given loop term. Free invariants are only assumed, but
not proven (like an axiom).

**Signatures**

* `\getFreeInvariant(VARIABLE, VARIABLE, VARIABLE)`




### `\getInvariant`

Extracts the loop invariants for a loop term (for all applicable heap contexts).

**Signatures**

* `\getInvariant(VARIABLE, VARIABLE, VARIABLE)`




### `\getVariant`

Extracts the variant for a loop term.

**Signatures**

* `\getVariant(VARIABLE, VARIABLE)`




### `\hasElementarySort`

Variable condition that enforces a given generic sort to be instantiated with the sort of a
program expression a schema variable is instantiated with

**Signatures**

* `\hasElementarySort(VARIABLE, SORT)`




### `\hasInvariant`

Checks whether a loop has an invariant (either normal or "free").

**Signatures**

* `\hasInvariant(VARIABLE, VARIABLE)`




### `\hasLabel`

This variable condition checks if an instantiation for term labels contains a specific term
label.

**Signatures**

* `\hasLabel(VARIABLE, STRING)`
* `\not\hasLabel(VARIABLE, STRING)`




### `\hasSort`

Variable condition that enforces a given generic sort to be instantiated with the sort of a
program expression a schema variable is instantiated with

**Signatures**

* `\hasSort(VARIABLE, SORT)`




### `\hasSubFormulas`

This variable condition checks if an instantiation for a formula has sub formulas which are
formulas. It returns false for an arity equal to zero or no sub formulas. This is needed to
simplify distinguishing between different well-definedness operators in taclets, since the
difference exists only for formulas.

**Signatures**

* `\hasSubFormulas(VARIABLE)`
* `\not\hasSubFormulas(VARIABLE)`




### `\isAbstractOrInterface`

This variable condition checks if a given type denotes an abstract class or interface type.

**Signatures**

* `\isAbstractOrInterface(tr: TYPE_RESOLVER)`
* `\not\isAbstractOrInterface(tr: TYPE_RESOLVER)`




### `\isArray`

This variable condition checks if an instantiation is an array.

**Signatures**

* `\isArray(VARIABLE)`
* `\not\isArray(VARIABLE)`




### `\isArrayLength`



**Signatures**

* `\isArrayLength(VARIABLE)`
* `\not\isArrayLength(VARIABLE)`




### `\isBindingExpr`

This is a variable condition, that checks if a given variable binds new variables.

**Signatures**

* `\isBindingExpr(VARIABLE, VARIABLE, VARIABLE)`
* `\not\isBindingExpr(VARIABLE, VARIABLE, VARIABLE)`


* `\isBindingExpr(VARIABLE)`
* `\not\isBindingExpr(VARIABLE)`




### `\isConstant`

This variable condition checks if an instantiation is a constant formula or term, i.e. its arity
is equal to zero.

**Signatures**

* `\isConstant(VARIABLE)`
* `\not\isConstant(VARIABLE)`




### `\isEnumConst`

ensures that the given instantiation for the schemavariable denotes a constant of an enum type.

**Signatures**

* `\isEnumConst(VARIABLE)`




### `\isFinal`

This variable condition checks if a given type denotes a final type.

Final types are either primitive types or classes that are declared final or arrays of final
types.

**Signatures**

* `\isFinal(tr: TYPE_RESOLVER)`
* `\not\isFinal(tr: TYPE_RESOLVER)`




### `\isInStrictFp`

This variable condition checks if a context is affected by the strictfp modifier

**Signatures**

* `\isInStrictFp()`
* `\not\isInStrictFp()`




### `\isLabeled`

Checks whether the given statement is labeled, i.e., actual a LabeledStatement. This information
is obtained from the program prefix.

**Signatures**

* `\isLabeled(VARIABLE)`
* `\not\isLabeled(VARIABLE)`




### `\isLocalVariable`

Ensures the given ProgramElement denotes a local variable

**Signatures**

* `\isLocalVariable(VARIABLE)`
* `\not\isLocalVariable(VARIABLE)`




### `\isModelField`

This variable condition checks if the instantiation of a schemavariable (of
type Field) refers to a Java field declared as "model".

The negated condition is true if the instantiation refers to an instance
or static or ghost field.

**Signatures**

* `\isModelField(VARIABLE)`
* `\not\isModelField(VARIABLE)`




### `\isObserver`



**Signatures**

* `\isObserver(VARIABLE, VARIABLE)`




### `\isReference`

This variable condition checks if a schemavariable is instantiated with a reference or primitive
type

**Signatures**

* `\isReference(TYPE_RESOLVER)`
* `\not\isReference(TYPE_RESOLVER)`




### `\isReferenceArray`

This variable condition checks if an array component is of reference type

**Signatures**

* `\isReferenceArray(VARIABLE)`
* `\not\isReferenceArray(VARIABLE)`




### `\isStaticField`

This variable condition checks if the instantiation of a schemavariable (of type Field) refers to
a Java field declared as "static".

The negated condition is true if the instantiation refers to an instance (non-static) field.

Inspired by ` FieldTypeToSortCondition`.

**Signatures**

* `\isStaticField(VARIABLE)`
* `\not\isStaticField(VARIABLE)`




### `\isThisReference`

This variable condition checks if a given type denotes an abstract class or interface type.

**Signatures**

* `\isThisReference(var: VARIABLE)`
* `\not\isThisReference(var: VARIABLE)`




### `\mayExpandMethod`

ensures that the given instantiation for the schemavariable denotes a method whose body may be
expanded. For determining the method the callee and the arguments of the method are needed as
arguments.


A method may be inlinded if:

* the method is private, or
* the method is static, or
* the method is final, or
* the receiver class is final, or
* the corresponding taclet option is set to relaxed inlining.



**Signatures**

* `\mayExpandMethod(VARIABLE, VARIABLE, VARIABLE)`
* `\not\mayExpandMethod(VARIABLE, VARIABLE, VARIABLE)`


* `\mayExpandMethod(VARIABLE, VARIABLE)`
* `\not\mayExpandMethod(VARIABLE, VARIABLE)`



### `\metaDisjoint`



**Signatures**

* `\metaDisjoint(VARIABLE, VARIABLE)`




### `\new`

variable condition used if a new variable is introduced

**Signatures**

* `\new(VARIABLE, JAVA_TYPE)`


* `\new(VARIABLE, SORT)`




### `\newDependingOn`



**Signatures**

* `\newDependingOn(VARIABLE, VARIABLE)`




### `\newLabel`

This variable condition ensures that no other label of the same name exists in the context
program or one of the schemavariable instantiations.

**Signatures**

* `\newLabel(VARIABLE)`


### `\newLocalVars`

For the loop scope rule, if a local program variable that may be altered by the loop body appears
in the frame condition,
it is necessary to use the value *before* the loop first executes in the frame condition.


To achieve this, this condition generates 

1. the "before" version of each variable that may be written to by the loop `
MiscTools#getLocalOuts(ProgramElement, Services)`;

2. an update storing the value of each such PV in its "before" version,i.e.,
`{...||i_before := i||...}`;

3. the reverse of the update, to be applied to the frame condition, i.e.,
`{...||i := i_before||...}`.

**Signatures**

* `\newLocalVars(VARIABLE, VARIABLE, VARIABLE, VARIABLE)`




### `\newTypeOf`

variable condition used if a new variable is introduced

**Signatures**

* `\newTypeOf(VARIABLE, VARIABLE)`




### `\notFreeIn`



**Signatures**

* `\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`
* `\not\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`


* `\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`
* `\not\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`


* `\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE)`
* `\not\notFreeIn(VARIABLE, VARIABLE, VARIABLE, VARIABLE)`


* `\notFreeIn(VARIABLE, VARIABLE, VARIABLE)`
* `\not\notFreeIn(VARIABLE, VARIABLE, VARIABLE)`


* `\notFreeIn(VARIABLE, VARIABLE)`
* `\not\notFreeIn(VARIABLE, VARIABLE)`




### `\reference`

This variable condition checks if a type is an enum type.

**Signatures**

* `\reference(VARIABLE, VARIABLE, VARIABLE)`
* `\not\reference(VARIABLE, VARIABLE, VARIABLE)`




### `\same`

General varcond for checking relationships between types of schema variables.

**Signatures**

* `\same(TYPE_RESOLVER, TYPE_RESOLVER)`
* `\not\same(TYPE_RESOLVER, TYPE_RESOLVER)`




### `\sameObserver`

A variable condition that is satisfied if the two arguments are


* schema variables,
* their instantiations are terms of observer functions,
* with the same function,
* which as exactly one heap argument
* and has got a dependency contract

#### Limitations

Currently, this and
`de.uka.ilkd.key.rule.metaconstruct.ObserverEqualityMetaConstruct` only support
observers with a single heap argument, that should be generalised.

**Signatures**

* `\sameObserver(schema1: VARIABLE, schema2: VARIABLE)`

   Create a new condition
   * `schema1` @param schema1 first argument, must be schema variable
   * `schema2` @param schema2 2nd argument, must be schema variable
   
### `\scrictSub`

General varcond for checking relationships between types of schema variables.

**Signatures**

* `\scrictSub(TYPE_RESOLVER, TYPE_RESOLVER)`




### `\simplifyIfThenElseUpdate`



**Signatures**

* `\simplifyIfThenElseUpdate(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`
* `\simplifyIfThenElseUpdate(VARIABLE, VARIABLE, VARIABLE, VARIABLE, VARIABLE)`




### `\static`

ensures that the given instantiation for the schemavariable denotes a static field

**Signatures**

* `\static(VARIABLE)`
* `\not\static(VARIABLE)`




### `\staticMethodReference`

ensures that the given instantiation for the schemavariable denotes a static method. For
determining the method the callee and the arguments of the method are needed as arguments.

**Signatures**

* `\staticMethodReference(VARIABLE, VARIABLE, VARIABLE)`
* `\not\staticMethodReference(VARIABLE, VARIABLE, VARIABLE)`




### `\storeStmtIn`

Stores the given ` Statement`, after substitution of ` SchemaVariable`s, into
the given ` ProgramSV` for later use in other conditions and transformers. The
arguments are a ` ProgramSV` and a ` JTerm`, where the ` JTerm` must contain a `
JavaBlock` with a ` StatementBlock` containing *a single statement* (that works,
e.g., when passing an expression like `\modality{#allmodal`{ while (#e) #body
`\endmodality(post)`); this statement is then stored (in the example the while
statement).

**Signatures**

* `\storeStmtIn(VARIABLE, TERM)`




### `\storeTermIn`

Stores the given ` JTerm`, after substitution of ` SchemaVariable`s, into the given
` SchemaVariable` for later use in other conditions and transformers.

**Signatures**

* `\storeTermIn(VARIABLE, TERM)`




### `\sub`

General varcond for checking relationships between types of schema variables.

**Signatures**

* `\sub(TYPE_RESOLVER, TYPE_RESOLVER)`
* `\not\sub(TYPE_RESOLVER, TYPE_RESOLVER)`




### `\subFormulas`

This variable condition checks if an instantiation for a formula has sub formulas which are
formulas. It returns false for an arity equal to zero or no sub formulas. This is needed to
simplify distinguishing between different well-definedness operators in taclets, since the
difference exists only for formulas.

**Signatures**

* `\subFormulas(VARIABLE)`
* `\not\subFormulas(VARIABLE)`



---

[^1]: Built-in rules reside in the directory `src/de/uka/ilkd/key/rule/` and
implement the interface `BuiltInRule`. This simple interface defines three
methods only; however, when implementing built-in rules, there are quite some
things to consider, which are not in the scope of this article. New BuiltInRules
have to be registered in the `Profile` they belong to, see
`src/de/uka/ilkd/key/proof/init/JavaProfile.java`, method `initBuiltInRules()`
for the place where BuiltInRules are registered in the default Java profile.
