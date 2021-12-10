# KeY's Extension to Java

*weigl, 2021* 

## Proof Java

The first extension is *Proof Java* (PJava) which brings new proof-
and JML-related construct into Java. 

New constructs:

* JML-support:
  * escaped identifiers `\map`, `\set`
  * new modifiers: `ghost` and `model`
  * New top-level 
  * simplified function calls
* KeY-support:
  * New statements: `method-frame`, `loop-frame`, `merge_point`,
    symbolic execution.

### General escape expression

An escape expression is a primary expression which captures the use of
escaped identifier. An escaped identifier (`<escapedId>`) is a regular
Java identifier which starts with an escape char `\`, e.g., `\abc`,
`\dl_map`. Following is invalid: `\1` or `\2a`.

An escape expression is a variable access or function application with an escaped identifier:

* `<escapedId>`
* `<escapedId>( <expr> )`
* `<escapedId>( <expr>,<expr> )`
* `<escapedId>( <expr>,<expr>, ... )`


### Implicit Identifiers 

KeY uses a third identifier kind, the implicit identifiers. These are
Java identifiers enclosed by angular brackets `<...>`.


!!! note weigl
   
   We should change this into something unambigous. Normally,
   synthetic fields or classes uses the dollar sign `$`.

### IndexRange

* `<expr> .. <expr>`

An artefact from an old time? --- defined but unused currently.

### MethodCallStatement

* `method-frame ( [ result-> <name> ,] source = <method-signature>@<type> [, this = <expr>] ) : <block>`

### MethodBodyStatement

* `<expr> @ <type>;`
* `<name> = <expr> @ <type>;`


### TransactionStatement

* `#beginJavaCardTransaction ;`
* `#commitJavaCardTransaction ;`
* `#finishJavaCardTransaction ;`
* `#abortJavaCardTransaction ;`

### MergePointStatement

* `merge_point ( <expr> );`
### LoopScope

* `loop-scope ( <expr> ) <block>`


### CatchAllStatement

### ExecStatement

```
exec <block>
[ ccatch ( \Return ) <block> ]
(ccatch( \Return <type> <id> ))*
[ ccatch( \\Break ) <block>]
(  ccatch (  "\\Break" <id> ) <block> )*
[ ccatch ( \Break * ) <block> ]
[ ccatch ( \Continue ) <block> ]
( ccatch ( \Continue name ) <block> )*
[ ccatch ( \Continue * ) <block> ]
( ccatch ( <parameter> )<block>
```





## Schema Java

The second extension is *Schema Java* (SJava) for the specification of
patterns. SJava has new construct, which are translated into
placeholder AST, also known as Schemavariables (SV). Beside of these
placeholder, where are some meta-construct for the term rewriting.

In particular, the extension has following 


### Schema Variables

Schema variables are the new main feature of SJava. A schema variable
is a regular Java identifier but it start with an hash `#`, e.g.,
`#se`, `#a`, `#averlongvariable123`. A schema variable is not allowed
to start with a number, e.g., `#1`, `#2a`.

A schema variable can occur at every position where a normal
identifier can occur. In some cases it has a refined meaning:

* `#a + #b`
* `(#T) (#b - #q)`
* `class #NAME { }`
* `#var + 2 - obj.abc()`
* `#obj.#field1.#field2.#method(#arg1, #arg2);`

Schema variables also be combined with the constructs of PJava.

Refined meaning occurs when a schema identifier occurs in certain
spots, i.e., as a *type*, as a *statement*, ...

### Passive Expression

`@ ( <expr> )`

I do not know.

### Contextual Block Statement (Start Block)

A block with context information

* ` { . <method-signature>@<type>(<expr>)  .. <statements>  ... }`
* ` { . <exec>  .. <statements>  ... }`
* ` { .. <statements>  ... }`
* ` { <statements> }`

### StaticEvaluate

* `#evaluate(<expr>)`

### IsStaticMC

### MetaConstructStatement

* `#unwind-loop( <label> , <label>, <loopStatement>);`
* `#unwind-loop-bounded(<label>, <label>, <loopStatement>);`
* `#FORINITUNFOLDTRANSFORMER(ForInit);`
* `#LOOPSCOPEINVARIANTTRANSFORMER(<whileStatement>);`
* `#unpack(<forStatement>);`
* `#for-to-while(<label>, <label>, <statement>);`
* `#switchof(<statement>)`
* `#do-break(<labeledStatement>);`
* `#evaluate-arguments(<expression);`
* `#replace(<statement>, <variable>);`
* `#method-call([<variable>,] [<variable>,], <primaryExpression>);`
* `#expand-method-body(<statement>[, <variable>]);`
* `#constructor-call(<variable>, <variable>);`
* `#special-constructor-call(<variable>);`
* `"#post-work" ( consRef = ExpressionSV() ) ";"`
* `"#static-initialisation" ( activeAccess = PrimaryExpression() ) ";"`
* `"#resolve-multiple-var-decl" ( stat = Statement() ) ";"`
* `"#array-post-declaration" ( stat = Statement() ) ";"`
* `"#init-array-creation" ( sv = VariableSV() "," consRef = ExpressionSV() ) ";"`
* `"#init-array-creation-transient" ( sv = VariableSV() "," consRef = ExpressionSV() ) ";"`
* `"#init-array-assignments" ( sv = VariableSV() "," consRef = ExpressionSV() ) ";"`
* `"#enhancedfor-elim" ( loopStat=ForStatement() ) ";"`
* `<REATTACHLOOPINVARIANT> ( loopStat = WhileStatement() ) ";"`

### Schema Statement

### Schema Type

* `<schemaId>`
* `#typeof(<expr>)`
