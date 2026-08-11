# Language Constructs

Proof scripts are textual representations of rule applications, settings changes
and strategy invocations (in the case of KeY as underlying verification 
system also referred to as macros).


## Variables and Types

We need to distinguish between: logic, program, and script variables.

* **logic variable**: Occur on sequents, bounded by a quantifier or in an update

* **program variable**: declared and used in Java programs. They are constants
  on the sequent.

* **script variable**: declared and assignable within a script

Proof Script Language has script variables.

A script variable has a name, a type and a value.
Variables are declared by

```
var0 : type;
var1 : type :=  value;
var2 :=  value;
```

Both statements declare a variable, in the latter  case (`var1` and `var2`) we directly assign a value, in
the first form `var0` receives a default value.

### Types and Literals

We have following types: `INT`, `TERM<Sort>`, `String`.

* `INT` represents integer of arbitrary size.
    ```
    42
    -134
    ```


* `TERM<S>` represents a term of sort `S` in KeY.
  `S` can be any sort given by KeY. If the sort is ommitied, then `S=Any`.

  ```
  `f(x)`
  `g(a)`
  `imp(p,q)`
  ```


* `STRING`

  ```
  "i am a string"
  ```

### Special Variables

To expose settings of the underlying prover to the user we include special variables:

* `MAX_STEPS` : amount denotes the maximum number of proof steps the underlying prover is allowed to perform



## Proof Commands

Proof commands start with an identifier followed by optional arguments:

```
command argName="argument" "positional argument" ;
```

Every command is terminated with a semicolon. There are named arguments in the
form argName="argument" and unnamed argument without name. Single `'...'` and
double quotes `"..."` can both be used.

Single-line comments are start with `//`.

## KeY Rules/Taclets

All KeY rules can be used as proof command. The following command structure is
used to apply single KeY rules onto the sequent of a selected goal node. If no
argument is following the proof command the taclet corresponding to this command
has to match at most once on the sequent.

If more terms or formulas to which a proof command is applicable exist,
arguments have to be given that indicate the where to apply the rule to.

A rule command has the following syntax:


```
RULENAME [on=TERM]?
         [formula=TERM]
         [occ=INT]
         [inst_*=TERM]
```

with:

* `TERM` specific sub-term
* `TOP_LEVEL_FORMULA`: specific top level formula
* `OCCURENCE_IN_SEQUENT`: Number of occurence in the sequent
* `maxSteps` the number of steps KEY should at most use until it terminateds teh proof search

If a rule has schema variables which must be instantiated manually,
such instantiations can be provided as arguments. A schema variable
named sv can be instantiated by setting the argument sv="..." or by
setting inst_sv="..." (the latter works also for conflict cases like
inst_occ="...").


### Examples

* `andRight;`

   Applicable iff there is only one matching spot on the sequent

* `eqSymm formula="a=b";`

    This command changes the sequent `a=b ==> c=d` to `b=a ==> c=d` Using only
    `eqSymm;` alone would have been ambiguous.

* `eqSymm formula="a=b->c=d" occ=2;`

    This command changes sequent `a=b->c=d ==>` to `a=b->d=c ==>`. The
    occurrence number is needed since there are two possible applications on the
    formula

* `eqSymm formula="a=b->c=d" on="c=d";`

    This command changes the sequent "a=b->c=d ==>" to "a=b->d=c ==>".
    It is simialr to the example above, but here the option to specify a
    subterm instead of an occurrence number is used.

* `cut cutFormula="x > y";`

   This command is almost the same as `cut \`x>y\``


### Macro-Commands

In the KeY system macro commands are proof strategies tailored to specific proof tasks.
The available macro commands can be found using the command help.
Using them in a script is similar to using rule commands:

```MACRONAME (PARAMETERS)?```

Often used macro commands are:

<ul>
    <li>symbex : performs symbolic execution</li>
    <li>auto: invokes the automatic strategy of key</li>
    <li>heap_simp: performs heap simplification</li>
    <li>autopilot: full autopilot</li>
    <li>autopilot_prep: preparation only autopilot</li>
    <li>split_prop: propositional expansion w/ splits</li>
    <li>nosplit_prop: propositional expansion w/o splits</li>
    <li>simp_upd: update simplification</li>
    <li>simp_heap: heap simplification</li>

</ul>

Example:

auto;
<h2>Selectors</h2>
As nited before proof commands are implemented as single goal statements.
Some proof commands split a proof into more than one goal.
To allow to apply proof commands in proof state with more than one proof goal, the language allows for
a selector statement <em>cases</em>. Such a <em>cases</em>-statement has the following structure:
<br>
cases { <br>
case MATCHER: <br>
STATEMENTS <br>
[default: <br>
STATEMENTS]?<br>
}

<h2>Control Flow Statements</h2>
The script language allows different statements for control-flow.
Control-Flow statements define blocks, therefor it is neccessary to use curly braces after a control-flow statement.
<ul>
    <li>foreach {STATEMENTS}</li>
    <li>theOnly {STATEMENTS}</li>
    <li>repeat {STATEMENTS}</li>

</ul>


<!--



Commands in scripts
-------------------

This list of available script commands is subject to change and to
extension. If you write your own script commands (s. below), please
add an explanation to this list here. The list is sorted alphabetically.

-- auto ------------------

Apply the automatic KeY strategy on the current goal. Optinally you
can specify the number of steps to run.

Examples:
auto steps=30000;
# run at most 30000 steps automatically.

-- cut -------------------

Performs a cut and thus splits the sequent into two goals. The unnamed
argument is the formula to cut with

Examples:
cut "value1 = value2";

-- exit ------------------

Terminate the script prematurely at that point. Used mainly for debug
purposes.

Examples:
exit;

-- instantiate -----------

Quantifier instantiation is a task that often occurs. Instead of
specifying the entire formula, it suffices here to name the variable
that is to be instantiated. If that is not unique, the number of the
occurrence of that quantified variable can be specified as well.

Examples:
instantiate var="x" occ="3" with="42"
# Instantiate the third instantiateable formula whose bound
# variable is called "x" with the value 42

instantiate formula="\forall int x; f(x) = 42" with="23"
# The quantified formula can also be specified if wanted.
# This here for the antecedent.

instantiate formula="\exists int x; f(x) = 42" with="23"
# Existentially quantified variables can be instantiated if they
# occur on the succedent side.

instantiate hide var=x value="x_0"
# instantiate x and hide the quantified formula

-- leave -----------------

Mark the currently active goal as non-interactive (the orange hand
symbol in the GUI). It is then excluded from further analysis by
scripts. This is good for debugging unfinished proof scripts.

-- macro -----------------

Invoke a macro on the current goal. The names of available macros
include:

autopilot      full autopilot
autopilot-prep preparation only autopilot
split-prop     propositional expansion w/ splits
nosplit-prop   propositional expansion w/o splits
simp-upd       update simplification
simp-heap      heap simplification

Examples:
macro autopilot-prep;

(Future version may drop the macro keyword and allow macro invocations
directly.)

-- rule ------------------

Apply a single rule onto the current sequent. As unnamed argument add
the name of the taclet to be applied. If the taclet matches only once
on the entire sequent, the rule is applied. If it matches more than
once you need to specify more. In that case you can first specify the
sequence formula and then the number of the occurrence in the formula
or the specific subterm via the 'on' keyword.
If a rule has schema variables which must be instantiated manually,
such instantiations can be provided as arguments. A schema variable
named sv can be instantiated by setting the argument sv="..." or by
setting inst_sv="..." (the latter works also for conflict cases like
inst_occ="...").

Examples:
rule andRight;
# if there is only one matching spot on the sequent

rule eqSymm formula="a=b";
# changes sequent "a=b ==> c=d" to "b=a ==> c=d"
# "rule eqSymm;" alone would have been ambiguous.

rule eqSymm formula="a=b->c=d" occ=2;
# changes sequent "a=b->c=d ==>" to "a=b->d=c ==>".
# occurrence number needed since there are
# two possible applications on the formula

rule eqSymm formula="a=b->c=d" on="c=d";
# changes sequent "a=b->c=d ==>" to "a=b->d=c ==>".
# same as above, but using the option to specify a
# subterm instead of an occurrence number.

rule cut cutFormula="x > y";
# almost the same as 'cut "x>y"'

-- script ----------------

Invoke another script which resides in an external file.

Example:
script '/path/to/other/file.script';

-- select ----------------

Unlike most other commands, this command does not change the proof but
chooses the goal on which the next step operates. Currently you can
specify a formula. The goal is chosen such that the formula appears
(toplevel) on the sequent (antecedent or succedent). You can limit the
search to antecedent or succedent.

Examples:
select formula="{ x:=1 }y < x";
# search for the formula anywhere
select succedent formula="wellFormed(someHeap)";
# search only the succedent for the formula

-- smt -------------------

Invoke an external SMT solver. That solver must be adequately
configured outside the script mechanism. By default, Z3 is invoked,
but that can be chosen.

Examples:
smt;
# invoke Z3
smt solver="Z3,yices";
# a comma separated list of solvers can be specified.

-- tryclose --------------

Unlike other commands this command operates on ALL open goals and
effectively applies the "try provable goals below" macro to all of
them. A number of steps can optionally be given.

Examples:
tryclose;
tryclose steps=2000;
# spend 2000 steps on each open goal


Write your on proof commands
----------------------------

to be done.
Contact Mattias, if you are interested.
-->
</body>
</html>
