# JML Grammar

!!! abstract
    
    Cheat sheet and definition for JML*, the JML-dialect of KeY.
  
    Currently under construction.   


## Introduction 

Java Modelling Language (JML) is a specification for Java software and currently the only supported specification language in KeY.
JML is itself an extension and also a restriction of Java, e.g., an Java expression is a valid JML expression and thus it can be used 
inside ensures clauses, but for well-definedness reason this expression has to side-effect free.

KeY supports a subset of JML, as defined in its [own reference manual](http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman.html), 
and has also added extension to this subset. The KeY-supported dialect is called JML*.

In this document, we give rather technical, reference like overview of the grammar and tweaks of JML*.

## JML* the top level view

JML* specification are defined within Java comments, which starts with an `@` sign. 
Valid JML* comments are:

```
//@ public instance invariant true;
/*@
    public model int x = 0;
 */
```

In contrast to the JML reference, KeY currently *does not* support comment tags. Therefore `//+KeY@` 
is currently not a legal.


!!! note
    
    A common beginners mistakes is a white space between  `//` and `@` sign, like `// @`.
    These commons are not considers as JML comments. 

    This is also a nice trick to disable JML comments.

JML comments can be placed in any valid position where also a Java comment can be placed. But in practise, 
you should keep strict policy:

* Comments with invariants, method and field declaration are part of the class, 
  and should be placed where the member variables are declared.
* There are also JML comments, which contains only additional modifier. 
  These comments should be placed along the Java modifiers.
* Method contracts should be place for a the associated method, like loop contracts should directly placed 
  before a Java loop statement and block contracts for Java code blocks.
* The last category are JML comments that are used as Java statements. These should be placed as Java statements.

In the following, we go through each JML detail.

## Model methods

In JML, you can declare and define methods in JML annotation comments
which can then (only) be used in specifications. They are treated
specially as declarations and definitions of logical functions. This
has two consequences:
1. The syntax supported in model methods is restricted (since it must
   be translatable directly to a logical formula.
2. All model methods must always terminate.

Termination is not optional, as non-termination compromises soundness
of the approach. Unfortunately, termination proofs are not fully
implemented yet.

Regarding the restricted syntax in model methods, their bodies can be
be nested `if` statements around `return` statements. Local variable
declarations (using `var`) are allowed. More concretely, the
(simplified) part of the JML syntax for model method bodies is

```
method_declaration : typespec IDENT param_list (method_body=mbody_block | ';')

mbody_block : '{' mbody_var* mbody_statement '}'

mbody_statement :
    'return' expression ';'
  | 'if' '(' expression ')' (mbody_statement | mbody_block) 'else' (mbody_statement | mbody_block)

mbody_var : 'var' IDENT '=' expression ';'
```

## Specifying lambda expressions

KeY supports lambda expressions and method references by *transformation*:
the Java frontend desugars them into plain Java before any JML processing,
following the transformation-based approach of Carsten Csiky's bachelor
thesis *Specification and Deductive Verification of Java Programs with Lambda
Expressions* (KIT, 2019). A lambda expression `x -> ...` is desugared into a
class implementing its functional interface, and the JML specification
written in the lambda body is converted into *model methods* (see above) on
that generated class.

A complete, verifiable example is bundled in the Examples dialog as
**Lambda Expressions** (`Java/Lambdas`): its proof obligation proves the
contract of a desugared lambda and closes in auto mode without interaction.

### Syntax

The specification is written as JML comment(s) that form the *leading
statement(s)* of the block body of the lambda. The clause kinds of method
contracts are available:

```
i -> {
    //@ requires i >= 0;
    //@ ensures \result <= cap;
    //@ invariant \result >= 0;
    //@ assignable \nothing;
    //@ accessible cap;
    return i < cap ? i : cap;
}
```

* `//@ ...` and `/*@ ... @*/` comments are both possible; inside a block
  body, `//@` is the natural choice.
* The clauses must come *first* in the block body, before any plain
  statement; JML comments after the first plain statement are not part of
  the contract. The leading JML comment(s) are always interpreted as the
  lambda's contract — not as a JML *block* contract of a nested block.
* A lambda with an expression body (`x -> x + 1`) cannot carry a
  specification.
* Free variables of the clauses may refer to the enclosing scope (here
  `cap`, the enclosing field); they are resolved to the fields of the
  desugared class like any other captured value.
* `modifies` is accepted as an alias of `assignable`.

### What the clauses mean

The clauses are the method contract of the functional method of the
desugared class, i.e., of one call of the lambda:

| clause       | meaning for the lambda                                                             |
|--------------|------------------------------------------------------------------------------------|
| `requires`   | a precondition of a call of the lambda                                             |
| `ensures`    | a postcondition; `\old(...)` is the state before the call, `\result` the return value |
| `invariant`  | a two-state property that shall hold both before and after *every* call (see the note below) |
| `assignable` | the locations the lambda may modify (its footprint)                                |
| `accessible` | the locations the lambda must have access to                                       |

### How the specification is realized

The transformation happens in pipeline steps that run before the JML
processing:

**1. Desugaring.** The lambda expression is replaced by the instance
creation of a local class implementing the functional interface. The lambda
parameters bind (by name) to the parameters of the functional method, and
`this`/`super` in the body are escaped so that they keep referring to the
enclosing instance. A method reference (`expr::m`, `T::m`, `T::new`) is
normalized into an equivalent lambda first and desugared like any other
lambda.

**2. Hoisting.** The local class is moved into the enclosing class as a
unique `private static final` nested class that captures its closure
explicitly:

```java
// before
class Clamp {
    int cap;

    IntFunction clamp() {
        int min = 5;
        IntFunction f = x -> {
            //@ requires x >= min;
            //@ ensures \result <= cap;
            return x < cap ? x : min + x;
        };
        return f;
    }
}
```

```java
// after (abridged; the contract conversion is shown below)
class Clamp {
    int cap;

    IntFunction clamp() {
        int min = 5;
        return new IntFunction__1(min, this);
    }

    private static final class IntFunction__1 implements IntFunction {
        public int apply(int x) {
            return x < outer_this.cap ? x : this._outer_final_min + x;
        }

        private final int _outer_final_min;
        private final Clamp outer_this;

        public IntFunction__1(int min, Clamp outer_this) {
            this._outer_final_min = min;
            this.outer_this = outer_this;
        }
    }
}
```

* Captured local variables and parameters become `private final` fields
  `_outer_final_<name>`, passed through a public constructor at every
  instantiation site.
* The enclosing instance is stored in a `private final` field
  `outer_this` (and `outer_super`, if the body uses `super`); references to
  its fields and methods are rewritten to `outer_this.<field>` and
  `outer_this.<method>(...)`.
* Nested lambdas are desugared innermost first, so a closure chain of nested
  lambdas needs no special case.
* The step is written generically and also hoists user-written local
  classes.

**3. Contract conversion.** The JML clauses extracted from the lambda body
are converted into JML *model method definitions* (and, for the frame
clauses, optionally model fields) on the generated class. The shape of the
generated model methods — their return type and their `two_state` modifier —
is taken from the declaration of the functional interface, which must
therefore declare the model method (or model field) for every clause used:

| clause       | model method           | alternative model field |
|--------------|------------------------|-------------------------|
| `requires`   | `preCondition(...)`    | —                       |
| `ensures`    | `postCondition(...)`   | —                       |
| `invariant`  | `invariantMethod(...)` | —                       |
| `assignable` | `frameCondition(...)`  | `footprint`             |
| `accessible` | `accessibleMethod(...)`| `accessibleFields`      |

The parameters of the model methods are the parameters of the functional
method; `postCondition` and `invariantMethod` receive an additional
parameter `__result` of the return type of the functional method, and
occurrences of `\result` in the clause are rewritten to `__result`. The
remaining identifiers of the clause body are rewritten to the members of the
generated class: `this`/`super` of the enclosing scope become
`outer_this`/`outer_super`, captured locals become the `_outer_final_*`
fields, and fields of the enclosing instance become `outer_this.<field>`;
other JML escapes such as `\old` pass through unchanged. A clause referring
to a variable that is none of these is reported as an error.

For example, with these declarations on the functional interface

```
interface IntFunction {
    //@ model boolean preCondition(int i);
    //@ model two_state boolean postCondition(int i, int __result);
    //@ model \locset frameCondition(int i);
    int apply(int i);
}
```

the lambda

```
IntFunction f = i -> {
    //@ requires i >= 0;
    //@ ensures \result <= 7;
    //@ assignable \nothing;
    return i < 7 ? i : 7;
};
```

is converted into the following members of the generated class:

```
//@ model boolean preCondition(int i) { return i >= 0; }
//@ model two_state boolean postCondition(int i, int __result) { return __result <= 7; }
//@ model \locset frameCondition(int i) { return \locset(\nothing); }
```

For `assignable` and `accessible`, the frame may alternatively be declared
as a model *field* (`footprint`/`accessibleFields`) on the functional
interface. The model field route produces a `model` field and a `represents`
clause on the generated class (e.g., `represents footprint <- <frame>;`)
and requires that the frame expression does not depend on the arguments of
the functional method. If both the model method and the model field are
declared, the model method is chosen.

### Specifying against a functional interface

The model methods are the interface through which *clients* of the
functional interface talk about the behaviour of a lambda without knowing
its implementation: the functional interface specifies its functional method
*against* the model methods,

```
interface IntFunction {
    //@ model boolean preCondition(int i);
    //@ model two_state boolean postCondition(int i, int __result);
    //@ model \locset frameCondition(int i);
    /*@ requires preCondition(x);
       @ ensures postCondition(x, \result);
       @ assignable frameCondition(x); @*/
    int apply(int x);
}
```

and every implementation — in particular every desugared lambda — is
verified against this contract. The API designer may additionally attach
requirements to the abstract model methods themselves (KeY checks them), or
provide default *implementations* of the model methods, e.g., a
weakest-precondition default (see
[the `\dl_wp_apply` escape](JavaDLinJML.md#the-weakest-precondition-escape-dl_wp_apply)).

!!! note "Side-effectful lambdas"

    A side-effectful lambda (one that modifies locations) is specified with
    an `invariant` clause and a frame via `footprint`/`accessibleFields` or
    `frameCondition` (Csiky, Sec. 6.4): the `invariant` is a property that
    shall hold both before and after *every call* of the lambda. The
    functional interface ties it in by making it both a precondition and a
    postcondition of the functional method (`requires invariantMethod(...)`
    and `ensures invariantMethod(x, \result)`). Note that a `two_state`
    model method may only be referenced from post-state contexts (e.g.,
    `ensures`); a precondition tie-in therefore requires a non-`two_state`
    declaration of `invariantMethod`. The thesis' ghost field tracking the
    sequence of calls is not part of the current implementation.

### Method references

A method reference is normalized into an equivalent lambda and desugared
like any other lambda. If the target method (or constructor) carries a JML
contract, the contract is *copied onto the synthetic lambda* and converted
like an explicitly written contract; the parameter names of the target are
renamed to the parameter names of the synthetic lambda:

* bound or static reference (`expr::m`, `this::m`, `T::staticM`) — the
  clauses of the target apply to the call of `m`;
* unbound instance reference (`T::m`) — the receiver `this` of the target's
  contract becomes the first parameter of the synthetic lambda (the
  receiver);
* constructor reference (`T::new`) — `this` of the constructor contract (the
  object under construction) becomes the result of the synthetic lambda,
  i.e., the `__result` parameter of `postCondition`/`invariantMethod`.

### Limitations

* The target (functional interface) type of a lambda or method reference
  must be resolvable from its context. Lambdas in field initializers and
  other contexts without an enclosing statement, and lambdas inside
  anonymous classes, are not supported yet.
* Method references inside a conditional expression (`cond ? a::m : b::n`)
  are not supported by the current parser fork.
* The specification must be the leading statement(s) of the lambda's block
  body (see [Syntax](#syntax)).
* The conversion is deliberately strict: an unknown free variable in a
  clause, or a clause for which the functional interface declares no model
  method or field, is reported as an error instead of a silent fallback.

### A note on "nested" JML comments

When inspecting KeY's intermediate representation of a source file (e.g.,
the pipeline snapshots in the test suite), JML comments are re-serialized
with their original markers preserved, so a JML line comment may appear as
a doubled line comment:

```
//@ //@ model boolean preCondition(int i);
```

This is a display artifact of the re-printed JML comment, not a nested
specification construct: source written by the user always uses a single JML
comment marker (`//@` or `/*@ ... @*/`).


## Entity names

In a recent update of the JMLref, JML entities can carry a name. KeY
currently supports names upon following entities:

* class invariants, axioms, intitially
* loop invariants, decreasing
* clauses: ensures, requires, maesured_by, captures, diverges, duration, when, signals, breaks, continues, returns, signals\_only, readable\_if, writeable\_if, monitors\_for, history\_contraint, 
* statement: set, assume and assert
* contracts 
* On JML terms via `\lbl(*name*, term)` function

These labels do not carry semantics. These are just names which can be
exploited.

!!! note 
    
	You can use the feature flag `JML_ENTITY_NAMES_AS_TERMLABEL` to activate the transfer of the JML entity names into KeY's term label (label `named(X)` for entity name "X"). This can be used for further analysis.

For example: 

```java
class Test {
    //@ public invariant MY_SUPER_INVARIANT: CONST == 42;
    public final int CONST = 42;
	
    /*@ requires Z: this != null;
      @ ensures A: \result == 42;
      @ ensures B: \result >= 0;
      @ ensures C: \result != 0; */
    public int foo() {return CONST;}
}
```



## JML Method Contracts

```
jmlContract     : [JML_START](#JML_START)
                  [methodContracts](#methodContracts) mod* 
                  [JML_END](#JML_END) ;

methodContracts : ALSO? methodContract ( ALSO methodContract )*
;
```



```
methodContract  : (PACKAGE | PRIVATE | PROTECTED | PUBLIC)?
                  ( BEHAVIOR | NORMAL_BEHAVIOR | EXCEPTIONAL_BEHAVIOR)?
                  (clause |
                    NESTED_CONTRACT_START
                    methodContracts
                    NESTED_CONTRACT_END
                  )*
                ;

clause      : (   requires
                | ensures
                | signals
                | signalsOnly
                | diverges
                | determs
                | assign
                | acc
                | mby )
	          ';'
            ;
```

## Modifiers

* `pure`
* `strictly_pure`
* `model`
* `helper`
* `nullable_by_default`
* `public`
* `private`
* `protected`
* `package`
* `non_null`
* `nullable`

## JML statements

### `set <ghost_var> = <>;`

### `assert <expr>`

### `assume <expr>`


```
requires    : REQUIRES heap* expr  ;
ensures     : ENSURES heap* expr   ;
signals     : SIGNALS LPAREN typeType id? RPAREN expr;
signalsOnly : SIGNALS_ONLY
                typeType (COMMA typeType )*
	        ;

diverges    : DIVERGES expr
            ;

determs     :   DETERMINES exprs
	            BY exprs
	            ( DECLASSIFIES exprs  | ERASES exprs )?
	            ( NEW_OBJECTS exprs )?
	        ;

jmlClassElem    : JML_START classElem JML_END
                ;

jmlModifier     : JML_START  mod (COMMA? mod)* JML_END
                ;

jmlBlockCntr    : JML_START blockContracts JML_END
                ;

/**

*/
classElem       : classSpec+  |  modelMethod
                ;
/**

*/
classSpec   : visibility? (classInv | fieldDecl | represents | accessible ) SEMI_TOPLEVEL;

/**

*/
classInv    :   (STATIC | INSTANCE)?
                (INVARIANT | CONSTRAINT | INITIALLY | AXIOM)
                expr
            ;

/**

*/
fieldDecl   :  (INSTANCE|STATIC)? ( GHOST | MODEL ) (INSTANCE|STATIC)? typeType id (COMMA id)*
            ;

/**

*/
represents  :  REPRESENTS
                ( expr | id ASSIGN expr | id SUCH_THAT expr)
                (COMMA ( expr | id ASSIGN expr | id SUCH_THAT expr) )*
            ;

/**

*/
accessible  : ACCESSIBLE id COLON expr (COMMA expr)* mby?
            ;
/**

*/
modelMethod : (visibility? MODEL_BEHAVIOR methodContracts)?
              visibility? ( NO_STATE | TWO_STATE | HELPER | STATIC)*
               MODEL
              ( NO_STATE | TWO_STATE | HELPER | STATIC)*
              visibility? STATIC? typeType IDENTIFIER ('(' params? ')')?
              ( LBRACE RETURN expr SEMI RBRACE
              | SEMI_TOPLEVEL
              )
            ;

params      : jmlTypeType id ( COMMA jmlTypeType id )*
            ;

/**
A heap specification is an identifier enclosed with angle brackets.

Examples:

* <javacard>
* <first>
*/
heap        : (LT IDENTIFIER GT)
            ;


/**

*/
assign      : (ASSIGNABLE |  MODIFIABLE | MODIFIES ) heap* expr (COMMA expr )*
            ;

acc         : ACCESSIBLE heap* expr (COMMA expr )* mby?
            ;

/**
Measures_by

*/
mby         : MEASURED_BY exprs
            ;

/**

*/
mod         : PURE | STRICTLY_PURE | MODEL | HELPER | NULLABLE_BY_DEFAULT
            | PUBLIC | PRIVATE | PROTECTED | PACKAGE | NON_NULL | NULLABLE
		    ;

/**
An annotation is a JML construct that can disappear
within a sequence of statements.

*/
annot       : setStm SEMI_TOPLEVEL
            | assert_ SEMI_TOPLEVEL
            | fieldDecl SEMI_TOPLEVEL
            | UNREACHABLE
            | loopInv
            | blockContracts
            ;
/**
Entry point for annotations.
*/
jmlAnnotation   : JML_START annot+ JML_END
                ;
/**

*/
loopInv     :   (
                    ( loopInvclause
                    | variantclause
                    | assign
                    | determs
                    )
                    SEMI_TOPLEVEL
                )+
            ;
/**
The loop_invariant clause.

Loop_invariants are allowed to be specified for a list of <heap>s
 and only takes one expression.

Examples:

* loop_invariant<h1> (\forall int i; i < j; f(i))
*/
loopInvclause   : LOOP_INVARIANT  heap* expr
                ;

/**

*/
variantclause   : DECREASES exprs
                ;
/**

*/
blockContracts  : ALSO? blockContract (ALSO blockContract)*
	            ;

blockContract   : visibility? bbehavior? bclause+
                ;

/**
Enumeration of behaviours for block contracts:

We support the british and american english keywords.

Example:
* behavior
* normal_behaviour
* exceptional_behaviour
* break_behavior
* continue_behavior
* return_behavior
*/
bbehavior       : BEHAVIOR
                | NORMAL_BEHAVIOR
                | EXCEPTIONAL_BEHAVIOR
                | BREAK_BEHAVIOR
                | CONTINUE_BEHAVIOR
                | RETURN_BEHAVIOR
                ;

/**
Clause in a block contract.

A block contract can either be a
* breaks
* continues
* returns
* or a clauses of a method contract (cf. <clause>).
*/
bclause         :
                ( breaks SEMI_TOPLEVEL
                | returns_ SEMI_TOPLEVEL
                | clause
                )
                ;

/**
A breaks non-terminal describes the irregular control within a loop.

Examples:

* breaks () true
* breaks (a) a==2
* continues (abc) a&2!=1
 */
breaks          : (BREAKS | CONTINUES)
                  LPAREN id? RPAREN expr
		        ;

returns_        : RETURNS expr
                ;

setStm          : SET location=expr ASSIGN value=expr
                ;

assert_         : ASSERT_ expr
                ;


/**

*/
exprs           :  (expr COMMA)* expr
                ;

/**
https://docs.oracle.com/javase/tutorial/java/nutsandbolts/operators.html

| Operators             | Precedence                    |
| postfix               | expr++ expr--                 |
| unary	                | ++expr --expr +expr -expr ~ ! |
| multiplicative        |  * / %                        |
| additive	            | + -                           |
| shift	                | << >> >>>                     |
| relational        	|  < > <= >= instanceof         |
| equality	            |  ==  !=                       |
| bitwise AND           | `&`                           |
| bitwise exclusive OR	|`^`                            |
| bitwise inclusive OR	|`|`                            |
| logical AND           |`&&`                           |
| logical OR            | `||`                          |
| ternary	            | ? :                           |
| assignment	        | = += -= *= /= %= &= ^= |= <<= >>= >>>= |

*/
expr  :
    // We start with the base cases, that have no degrees of freedom for selection to achieve a fast parser
      jmlPrimary                                                                                            #exprLiteral
    | quantifiedExpr                                                                                  #exprComprehension
    | LPAREN (LBLPOS | LBLNEG) IDENTIFIER expr RPAREN                                                       #labeledExpr
    | LPAREN expr RPAREN                                                                                     #exprParens
    //| (expr DOT ) id                                                                                  #exprFieldAccess
    |  expr LBRACK expr RBRACK                                                                          #exprArrayAccess
    |  expr LBRACK expr DOTDOT expr RBRACK                                                               #exprArryLocSet
    |  expr LBRACK MUL RBRACK                                                                           #exprArrayAccess
    //  cascade from the highest to the lowest precedence
    | LPAREN typeType RPAREN expr                                                                              #exprCast
    | SUB expr                                                                                           #exprUnaryMinus
    | BANG expr                                                                                       #exprLogicalNegate
    | TILDE expr                                                                                       #exprBinaryNegate
    | NEW (id DOT)* id                                                                                          #exprNew
    | expr bop=DOT id                                                                                            #access
    | expr bop=DOT MUL                                                                                           #locAll

    //arithmetic
    | expr MUL expr                                                                                  #exprMultiplication
    | <assoc=right> expr op=(MOD|DIV) expr                                                                #exprDivisions
    | expr op=(SUB|ADD) expr                                                                          #exprLineOperators

    | expr (LT LT | GT GT GT | GT GT) expr                                                                   #exprShifts

    | expr op=(LE|GE|GT|LT|INSTANCEOF|ST) expr                                                           #exprRelational

    // ST is for type comparison
    | expr op=(EQUAL|NOTEQUAL) expr                                                                      #exprEqualities

    | expr op=BITAND expr                                                                                 #exprBinaryAnd
    | expr op=CARET expr                                                                                  #exprBinaryXor
    | expr op=BITOR expr                                                                                   #exprBinaryOr
    | expr op=AND expr                                                                                   #exprLogicalAnd
    | expr op=OR expr                                                                                     #exprLogicalOr

	| expr LBRACK expr DOTDOT expr RBRACK                                                               #exprSubSequence
    | expr QUESTION expr COLON expr                                                                         #exprTernary
    // end of java hierarchy

    | expr op=IMPLIES expr                                                                         #exprImplicationRight
    | expr op=IMPLIESBACKWARD expr                                                                  #exprImplicationLeft
    | expr op=EQUIVALENCE expr                                                                          #exprEquivalence
    | expr op=ANTIVALENCE expr                                                                          #exprAntivalence
    | expr LPAREN exprs? RPAREN                                                                            #exprFunction
    | id LPAREN exprs? RPAREN                                                                              #exprFunction
    | THIS #exprThis
    | SUPER #exprSuper
    ;

jmlPrimary
    : LPAREN expr RPAREN
    | THIS
    | SUPER
    | literal
    | IDENTIFIER
    | typeTypeOrVoid DOT CLASS
    | nonWildcardTypeArguments (explicitGenericInvocationSuffix | THIS arguments)
    | methodReference // Java 8
    | jmlTypeType
    ;

/**
A comprehension is a variable binder with a list of expression

Examples:
* (\forall int x; x > 0 && x < a.length; p(x) )
* (\sum int x; x>= 0 && x < 10; x+1)
* (\product int x; x>= 0 && x < 10; y)
* (\max int x; x>= 0 && x < 10; f(x))

Currently following comprehension are defined:
    \sum, \product, \max, \min, \num_of, \exists, \foreach, \infinite_union

*/
quantifiedExpr
    :
        LPAREN
            op=(FORALL|EXISTS|IDENTIFIER)
            typeType id (COMMA id)* SEMI
            (expr SEMI)*
            expr
        RPAREN
    ;

		    //  LPAREN '\\lblneg' id expr RPAREN
            //   LPAREN '\\lblpos' id expr RPAREN


/**
Identifier in JML are

* normal java identifier or
* symbols that begin with a backslash '\'


We try to minimize the specific usage of specific DL keywords,
and catch false usage later.
*/
id:     IDENTIFIER | THIS | SUPER;

/**
Types are just normal identifiers, e.g.

* boolean
* byte
* char
* short
* int
* long
* \bigintv
* \seq
* \locset
* nullMod? id ('[]')
*/
jmlTypeType:  (NULLABLE | NON_NULL)? typeType
            ;
```            
