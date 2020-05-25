# JML Grammar

!!! abstract
    
    Cheat sheet for JML*, the JML-dialect of KeY.
  

!!! note

    The name of tokens are written in uppercase, e.g. `JML_START` 
    describes either `/*@` or `//@` -- both introduce a JML 
    specification.


## JML Method Contracts

<pre>
jmlContract     : [JML_START](#JML_START)
                  [methodContracts](#methodContracts) mod* 
                  [JML_END](#JML_END) ;

methodContracts : ALSO? methodContract ( ALSO methodContract )*
;
</pre>


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
