# Rewrite of the KeYParser 

*weigl, 2021-03-12*

!!! abstract

    This note explains the rewrite of the KeyParser and KeyLexer to ANTLR4. It explains the background, the architecture
    and shows how to deal breaking changes. 
    

## Background

With the MR !278, a new lexer and parser for the KeY language is introduced. The KeY language is used to parse the `*.key` and `*.proof`, and is also used as the input language for entering terms in the user interface. 

In general, this parser was hard to maintain and extend over the years.
The old parser was a traditional ANTLR3 parser, where the grammar and the source code are mixed up. It also some lookahead were required.  KeY files are interpreted on different levels: The first level are the basic notions (e.g. sorts and choice options), second level are the functions, predicates and transformers, and the third level are the axioms, contracts and rules. These parsing level are required due to the dependencies between these logical entities, e.g. a rule requires certain functions and sorts during its interpretation. In the old KeY-Parser, each file is parsed (and read) on a specific level. Hence, to interpret a KeY file, multiple parse passes are required. 

The new parser is written in ANTLR4 and has a clear separation of concern. The parser is completly free of Java code, and the lexer is reduced to minimum. Therefore, a KeY file is parsed once, and the AST is interpreted on the different levels. 
This also allows a more flexible interpretation of the AST, e.g. the taclet condition (`varcond`) can now easily be added or removed. Also new facades enforce a separation of the application logic from the parser. In normal usage scenarios, you are not able to access on the AST directly (but of course, there is a possibility to do so). 

Also the new facilities provide a better user feedback for ill-formed inputs. 
The `TermCreationException` is enriched with errornous parse tree node and position info (file, line, char). Every taclet has an origin information (`file:line`). This information is also visible in the taclet information in the `InfoView`.
Every term, which is created by the parser, has given an origin information (`file:line`).
Better feedback whether the ill-formedness is due to syntax or semantic is possible, and will later be provided.

* The grammar is already a bit simplified:
  - No distinguishing between problem and declaration file. 
  - Some rules were slightly rewritten to decrease the ambiguities 
  - Requirement of flag orders reduce



## API (Facades)

Two new facade provide access to the parser. Of cource it is possible to access the lexer or the parser directly, but this should be avoided. 

### High-level Access

The class `KeyIO` provides a high-level facade for parsing and evaluation of KeY files, 
and Strings. First, this class is stateful as it operates on a supplied `Services` and `NamespaceSet` object. Everything interpreted entity, especially the KeY files, has a potential effect on these objects. `KeYIO` is construction a `Services` and `NamespaceSet` object, and provide the following functions:

* `parseExpression(in : String | CharStreams) : Term`
   
   Parsing the given input to a `Term`.

* `parseSequent(in : CharStreams) : Sequent`

   Parsing the given input to a `Sequent`.

* `findTaclets(in : KeyAst.File) : List<Taclet>`

  Given a `KeyAst` object return a list of declared taclets.

* `evalDeclarations(in : KeYAST.File) : void`

  Given a `KeyAst` object interpret basic (level one) declarations.

* `evalFuncAndPred(in : KeYAST.File)`

  Given a `KeyAst` object interpret the functions, predicates and transformers.

* `load(in : Path|CharStream|URL|String) : Loader`

   Given a file location, return a `Loader` instance. A `Loader` provides a simple API to fully read and interpret a KeY file. This also includes the transitive parsing of included KeY files. This facililty does not handle Java. Therefore, types which are translated from the Recoder are not available and lead to an failure. Nonetheless, 
   `Loader` is able to bootstrap the basic definition. 

   The currently used loading logic is in `ProblemInitializer`.
    
In general, `KeyIO` delivers KeY objects (Term, Sequent, Taclet, etc. ) for given inputs. 

# Low-level Parsing

Sometimes we need to go beyond the interpretation of AST nodes (e.g. syntax checks, highlighting, Finding used symbols). For these scenario, `ParsingFacade` provides 
a thin above the new parser. This facades abstracts the building of `KeYLexer` and `KeYParser`, e.g. it sets an exception throwing error handling. As a result, 
`KeYAst` objects are returned. These objects carries the internal `ParsingRuleContext` of the ANTLR4, but hide it from the from the developer. With such an `KeyAst` object can be used on the `KeyIO` facade to create a KeY object. For hardcore users, `ParsingFacade` provides a method for unwrapping the internal AST. 

For normal use cases, the `ParsingFacade` and the new parser and lexer or visitor classes
and the visitor classes should not be used directly.

* `createParser(in) : KeYParser` and `createLexer(in) : KeYLexer`

   Create a new parser or lexer for the given input. 

* `getChoices(files : List<File>) : ChoiceInformation`

   Given a set of files, this function finds all defined choices and options.

* `getParseRuleContext(ast : KeyAst) : ParserRuleContext`

   Unwrap the provided AST.

* `parseExpression(in) : KeYAst.Expression`, `parseSequent: KeYAst.Expression`, and  `parseFile(in) : KeYAst.File`

  Parse the given input to an expression, sequent or file AST. 
  

## Behind the facades

The new parser facility consists of:

* the grammar file `KeyParser.g4`
* the lexer file `KeyLexer.g4`
* the facades 
* and visitors for interpretation 

ANTLR4 generates for the grammar file the parser, the AST classes and also an AST visitor. We implement this visitor for the different interpretation levels. In detail, there are 

* `DefaultBuilder` -- basic functions (e.g. throwing errors or adding warnings)
  * `ExpressionBuilder` -- construction of expression (`Term`) 
    * `ContractsAndInvariantsFinder` -- evaluation of contracts and invariants
    * `ProblemFinder` -- evaluation of commands for `KeYProblemFile`, in particular providing the `\problem` term. 
    * `TacletPBuilder` -- construction of taclets 
  * `DeclarationBuilder` -- evaluation of basic declarations  (sorts, choices, etc.)
  * `FunctionPredicateBuilder` -- evaluation of functions etc.

Note that these visitors are last classes in a long and too complicated loading 
architecture in KeY. For details look into `ProblemInitializer`, `KeyFile` and `KeYProblemFile`. 

## Questions and Answers

### What are the breaking changes?

Note that the classes `KeyParserF` and `KeyLexerF` are not generated anymore. 
Please rewrite your code and use `KeyIO` instead. * `DefaultTermParser` is deprecated in favor for KeyIO.

There was a few bugs in Key files that were not recognise by the old parser due to choice option which were never selected. This hasn't an effect on the KeY regression test, but might affect your proofs. 

In general, choices are handled correctly now. This may break some of your proofs, too. 
In particular,  `sort.key`in quicksort was not provable anymore (due to missing taclet)
and required a `\withOption moreSeqRules:on` entry in the KeY problem file. 

Note that changes were required in the syntax of variable conditions (see below).


### Why does the lexer required some pieces of Java code?

The exception is the handling of `NUM_LITERAL` followed by an LPAREN '`(`' needed for function decls like `numbers 0 (numbers);`. Normally, a `123` is a number and lexed as a number literal (`NUM_LITERAL`). But if you write `1(2(3(#)))` each digit becomes and identifier. 

The second case is handling of the keyword `\proof`. This keyword introduce an S-expr with the taclet applications to reconstruct a proof. The new lexer emits two tokens when `\proof` is hit, the first token is `PROOF`, and the second is `EOF`. The second token stops the parsing. 


### Where are the grammar rules for the sexpr of proofs?

Proofs are not handled by the parser anymore. This avoids the construction of large AST for several hundreds of megabyte input files.  The handling of proofs are as follows:

* You parse the `*.proof` as a normal KeY problem file. 
* If `\proof` is hit, the lexer and parser stops, resulting into a valid AST without nodes for the stored proof. 
* By checking for the AST node of `\proof`, you can determine that a proof exists. 
* In the next step, you reopen the file, and seek to the position after `\proof`, and lex again.
* Using the token stream you can reconstruct the proof easily, without much memory consumption.

This is already implemented in `ProofReplayer`.

### How can I add a new variable condition?

A taclet holds a list of *variable conditions*. These are conditions on the values of the  declared (schema) variables in a taclet. These conditions were a fixed set defined by the grammar in the old parser.  In the new parser, the grammar is (nearly) independent of the particular existing conditions.

In particular, to define a new variable condition you should apply the following steps:

* Define the class for your variable condition as an subclass of `VariableCondition`
* In `TacletBuilderManipulators`, you need to define instance(s) of `ConditionBuilder`. These are the factory methods for your variable conditon. 
* Register `ConditionBuilder` in `TacletBuilderManipulators`, either by adding a call to `TacletBuilderManipulators#register()` or using the `ServiceLoader`.
* Define a token in the `KeyLexer.g4`, and add the token to the list of `varcondId` in `KeyParser.g4`.
  (This is step is only required, as the `varcondId` are currently a list of allowed identifier for variable conditions. 
  In the future, we generalize `varcondId` to an arbitrary identifier, then this step can be omitted.)

Note that changes were required in the syntax of variable conditions. In particular, combinations with `\hasSort` and `\new` 
are unfolded. Namely, 

- `\new` is split into `\new`, `\newDependingOn`, `\newTypeOf`.
- `\hasSort` is split into `\hasSort` and `\hasElementarySort`.

In the old parser, you write `\new(\typeOf(x))` in the new parser you write `\newTypeOf(x)`. 

