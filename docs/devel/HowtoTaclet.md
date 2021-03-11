# Writing Taclets

New prover rules in KeY can be added in form of built-in rules<a
href="#fn1" id="fnref1" name="fnref1"><sup>1</sup></a> written in
plain Java code and as so-called "taclets" ("schematic theory-specific
rules"). Taclets permit for an easy-readable definition of rules; when
a taclet is applied during a proof, the taclet itself as well as the
instantiation of its schematic parts are displayed to the user, making
the rule application more transparent. Almost all rules implemented
for KeY are defined as taclets (with the exception of special rules
like method contract application, loop invariant application (so far)
and one-step-simplification). For information about taclets, please
consult the [book chapter "Proof Search with
Taclets"](https://link.springer.com/chapter/10.1007/978-3-319-49812-6_4)
of the 2nd KeY book.

This article covers the necessary basics for adding new taclets to the
KeY system. In particular, the following topics are discussed:


###  How to add new taclets

The standard location for `.key` files containing taclets is in the
`key.core` project, location `resources/de/uka/ilkd/key/proof/rules`
(*note*: unless stated otherwise, all locations in this article are
relative to `key.core`). The file `standardRules.key` lists all the
taclet files that are are loaded as defaults when starting KeY with
the Java profile. New taclets can be added to either of the existing
files listed there (if they fit into the scope), or can be added to a
new file which is then referred to in `standardRules.key`.

The standard rule file can be obtained from a profile
(`de.uka.ilkd.key.proof.init.Profile`) via the method
`getStandardRules()`. The class
`de.uka.ilkd.key.proof.init.JavaProfile`, for example, sets the
standard rules to the aforementioned `standardRules.key`. If one
wishes to add taclets that are unrelated to Java, that taclet should
be referred to from the standard rules collection of an appropriate
profile.

Taclets can be added to "rule sets" which are used, e.g., by strategy
heuristics. Default rule sets are defined in the file
`resources/de/uka/ilkd/key/proof/rules/ruleSetDeclarations.key`.

### How to extend the taclet language

Sometimes, especially when one wants to introduce new symbolic
execution concepts, the existing taclet language is not expressive
enough and has to be extended. There are four things one might have to
extend to support new taclet features: (1) The taclet parsers; this
includes the parser for the taclet language itself (which usually will
not have to be changed) and the parser for new program constructs, (2)
for matching different classes of statements, corresponding model
classes will have to be added to the system, which are then referred
to in factory classes and the parser(s), (3) whenever the standard
find-replace pattern of taclets is not sufficient, one can add
"transformers" performing more complex actions during taclet
execution, and (4) when taclets depend on additional input such as
specifications, one can define (automatic or interactive) completions
for the taclet. We'll discuss all those points in the following.

It might be helpful to (additionally?) learn about the process by
examples. To get started, an example for a new program statement used
for matching is "merge_point", the keyword for a merge point
statement. A simpler one is "ForLoop", a schema variable matching for
loops. If you search for those identifiers in all files in the
"key.core" project, you'll find the entry points needed for
extensions. Note that merge points are also used in JML
specifications, which is a different topic (therefore, you might want
to ignore the corresponding parser files "KeYJMLPre{Lexer, Parser}.g,
basically everything in the `(...)/speclang/jml` directory.). An
example for a transformer is the "#for-to-while" construct which
accepts a for loop as input and transforms it to a while loop. Your
friends here are the eclipse functionalities `Search -> File` (use
`*.*` as a pattern here, and only search in the key.core project),
`Ctrl+T` for finding types, and `Ctrl+R` for finding resources.

#### Parsing

There are several relevant parsers you might need to know. The "main
KeY parser", `src/de/uka/ilkd/key/parser/KeY{Lexer, Parser}.g` is an
ANTLR3 parser which covers KeY's language for sorts, terms, formulas
etc., taclets, and proof files. For most extensions, this file does
not need to be touched.

The parsers for Java extensions in taclets and proof files are
`src/de/uka/ilkd/key/parser/schemajava/SchemaJavaParser.jj` and
`src/de/uka/ilkd/key/parser/schemajava/ProofJavaParser.jj`, which are
JavaCC parsers. In the former, you also find definitions for
`#for-to-while` and `merge_point`; in the latter, only `merge_point`
occurs since it is an extension of Java and not a transformer like
`#for-to-while` which is only needed in taclets, but will never occur
in a Java program.

So, if for your taclet the basic taclet language has to be changed,
adapt `KeYParser.g` accordingly; for creating new transformers,
`SchemaJavaParser.jj` is the relevant parser, and for additions to the
Java language accepted by KeY, `SchemaJavaParser.jj` and
`ProofJavaParser.jj` will have to be changed. The best advice here is
to have a look at the existing definitions to see how to add a new
one. Note that at the same time when extending the parser by new
transformers or statement types, you will also have to add new Java
classes and extend factories. We cover this in the next section.

#### New Program Statement / Expression Types

There are two categories of extensions: (1) New program schema
variable sorts, which match existing programming language fragments,
and (2) extensions to the language, e.g. by artificial constructs
needed for a proof / symbolic execution technique.

A new "matcher sort" for taclets is added quite easily. As an example,
take the "loop init" clause of a for loop. A corresponding schema
variable for the use in taclets can be declared as `\program LoopInit #loopInit;`.
After that, `#loopInit` can be used in a taclet to match
a loop init clause. It suffices to (1) declare a new "program schema
variable sort" in `de.uka.ilkd.key.logic.sort.ProgramSVSort` (for
instance `LoopInitSort` in the example) which calls the constructor of
`ProgramSVSort` with the identifier by which it later should be
referred to in taclet definitions, and (2) to use that sort in
`SchemaJavaParser.jj`. Have a look how `ForInit` is used there to get
a feeling.

A language extension like the merge points has to be added to several parts in the system:

1. A parser model extension is added in
   `src/de/uka/ilkd/key/java/recoderext/` (see
   `MergePointStatement.java` for an example).
2. The factories
   `de/uka/ilkd/key/java/recoderext/SchemaJavaProgramFactory.java` and
   `(...)/ProofJavaProgramFactory.java` are extended by corresponding
   factory methods.
3. A mirror of the parser extension for the logic side of KeY is added
   to `de/uka/ilkd/key/java/statement/` (also here, there's a
   `MergePointStatement.java`).
5. A converter for the parser model extension to the logic
   representation in `de/uka/ilkd/key/java/Recoder2KeYConverter.java`.
   Look what's done for the `MergePointStatement`. The methods there
   are called by reflection, so the name of the new method has to be
   `convert`, and it has to accept the parser model extension as only
   argument.
6. Extension of Java visitor classes: Classes `Visitor.java`,
   `JavaASTVisitor.java`, `CreatingASTVisitor.java`, and
   `ProgVarReplaceVisitor.java` in directory
   `de/uka/ilkd/key/java/visitor/`. Note that now all of these might
   apply to you, e.g. if your new statement does not contain program
   variables that might have to be substituted in a proof.
7. Extension of the pretty printer to nicely render your extension in
   sequents: `de/uka/ilkd/key/java/PrettyPrinter.java`.

The factory methods and parser model classes can then be used in
`{Schema, Proof}JavaParser.jj`.

#### New Meta Constructs / Transformers

Meta constructs give additional powers to taclets. By them, it is even
possible to create taclets which are actually built-in rules since all
the work (maybe except for some matcher preprocessing) is deferred to
a powerful transformer. Note that we discourage from using that style;
meta constructs should be used at a very small scope. If that's not
possible, directly using built-in rules is a more "honest" and better
maintainable approach.

Our running example here is the `#for-to-while` construct (actually an
example for the bad style of delegating everything to a transformer).
For adding transformers this to the system, follow these steps:

1. Add a model class to the directory
   `src/de/uka/ilkd/key/rule/metaconstruct/` (see e.g.
   `ForToWhile.java). The class should extend `ProgramTransformer` and
   pass the keyword to be used to the super class, here
   "#for-to-while".
2. Extend the class
   `src/de/uka/ilkd/key/java/SchemaRecoder2KeYConverter` to return the
   new class when appropriate. Look for `convert(RKeYMetaConstruct)`
   to see what's done for `#for-to-while`.
3. Add the construct to the parser (`SchemaJavaParser.jj`).

#### Completions

Sometimes the input to a taclet depends on other information than that
available from a current proof situation (i.e., a sequent). In that
case, the rule has to be completed before it is applied. A good
example is the rule "cut"
(`resources/de/uka/ilkd/key/proof/rules/propRule.key`) defined as
follows:

```
\schemaVariables {
  \formula cutFormula;
}
cut { "CUT: #cutFormula TRUE":\add (cutFormula ==>);
      "CUT: #cutFormula FALSE":\add (==> cutFormula)
      \heuristics(cut) };
```

The formula `cutFormula` is not obtained from the sequent, it's left
as a "hole" in the definition. When applying the rule in KeY, a
standard dialog will pop up asking for an instantiation of
"curFormula".

For certain situations, special completions are required. A classic
example are rules depending on specification, like loop invariant or
method contract rule applications. To this end, custom completions
implementing
`/key.ui/src/de/uka/ilkd/key/gui/InteractiveRuleApplicationCompletion.java`
(note: this class is the first not residing in the key.core project)
can be added and registered in
`/key.ui/src/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java`.

**NOTE/WARNING**: Obviously, interactive rule application completions
are currently only designed to handle BuiltInRules. So for taclets,
this will have to be adapted!

Alternatively to the implementation of an interactive completion,
additional information, like for instance a specification, could be
retrieved by special meta constructs. Specifications are stored in
`de.uka.ilkd.key.proof.mgt.SpecificationRepository` and can be
retrieved via a call like
`services.getSpecificationRepository().getLoopSpec(loop)`. If the
specification repository already contains the means to store that
specification, this should be quite straightforward to accomplish.

---

<ol dir="auto"> <li> <p><a id="fn1" name="fn1"> </a>Built-in rules
reside in the directory <code>src/de/uka/ilkd/key/rule/</code> and
implement the interface <code>BuiltInRule</code>. This simple
interface defines three methods only; however, when implementing
built-in rules, there are quite some things to consider, which are not
in the scope of this article. New BuiltInRules have to be registered
in the <code>Profile</code> they belong to, see
<code>src/de/uka/ilkd/key/proof/init/JavaProfile.java</code>, method
<code>initBuiltInRules()</code> for the place where BuiltInRules are
registered in the default Java profile. <a href="#fnref1"><gl-emoji
title="leftwards arrow with hook"
data-name="leftwards_arrow_with_hook"
data-unicode-version="1.1">↩</gl-emoji></a></p> </li> </ol>
