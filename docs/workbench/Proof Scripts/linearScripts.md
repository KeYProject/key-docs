# Making interactive persistent using proof scripts

*Mattias Ulbrich <ulbrich@kit.edu>, 2015*

Experimental feature: Proof scripts are currently only visible in the GUI if KeY
is launched with the `--experimental` option. Concrete syntax is subject to
change.

Every KeY user knows the pain of manually redoing an interactive proof over and
over again even though only a tiny bit of the program or specification have
changed. NOW you can use proof scripts which will alleviate your worries with
repeating proofs.

Proof scripts are textual representations of rule applications, settings changes
and macro invocations. They are notated in linear order. The target of a script
command is usually the first open goal in the proof tree, i.e., the first
reached when traversing the proof tree (not necessarily the first in the *Goal*
pane in the GUI).


## Syntax of proof scripts

Proof commands start with an identifier followed by optional arguments:

```
command argName="argument" "argument without name" ;
```

Every command is terminated with a semicolon. There are named arguments in the
form `argName="argument"` and unnamed argument without name. Single `'...'` and
double quotes `"..."` can both be used. If `"argument"` is an identifier itself,
the quotes can optionally be dropped, like in

```
rule andRight ;
```


The character # begins a comment which extends to the end of the line.
Currently, there are no multi-line comments in proof scripts. Proof scripts are
case sensitive.


## How can scripts be loaded

1. In the GUI:
Open a proof obligation. Currently proof scripts work only reliably if
applied to the root of a fresh proof obligation (no rule applications,
prune steps). The open the context menu (sequent or proof tree),
choose "Strategy macros" and then "Run proof script ...". In the file
dialog that appears, choose the script file to load. The script is
automatically applied. You can follow the process in a logging window.

2. From within key input files:
At the very end of key files *INSTEAD* of a \proof object, you can now
attach a proof script directly in double quotes following the keyword
\proofScript. An very simple example reads:

```
\predicates {a; b;}
\problem { a & b -> a }

\proofScript "
   rule 'impRight';
   rule 'andLeft';
   rule 'close';"
```

Since the script is no enclosed in `"..."`, only single quotes `'...'` can
be used in the script. You can also load a script from an external
file by writing

```
\proofScript "script 'some_filename.script';"
```


## Commands in scripts

This list of available script commands is subject to change and to extension. If
you write your own script commands (s. below), please add an explanation to this
list here. The list is sorted alphabetically.

* `auto`

  Apply the automatic KeY strategy on the current goal. Optinally you can
  specify the number of steps to run.

  ```
  auto steps=30000; # run at most 30000 steps automatically.
  ```

* `cut`

  Performs a cut and thus splits the sequent into two goals. The unnamed
  argument is the formula to cut with

  ```
  cut "value1 = value2";
  ```

* exit 

  Terminate the script prematurely at that point. Used mainly for debug purposes.

  ```
  exit;
  ```

* `instantiate`

     Quantifier instantiation is a task that often occurs. Instead of specifying
     the entire formula, it suffices here to name the variable that is to be
     instantiated. If that is not unique, the number of the occurrence of that
     quantified variable can be specified as well.

     Instantiate the third instantiateable formula whose bound variable is called
     `x` with the value `42`
     ```
     instantiate var="x" occ="3" with="42"
     ```
     The quantified formula can also be specified if wanted.
     This here for the antecedent.
     ```
     instantiate formula="\forall int x; f(x) = 42" with="23"
     ```
     Existentially quantified variables can be instantiated if they occur on the
     succedent side.
     ```
     instantiate formula="\exists int x; f(x) = 42" with="23"
     ```
     Instantiate x and hide the quantified formula: 
     ```
     instantiate hide var=x value="x_0"
     ```
* `leave`

    Mark the currently active goal as non-interactive (the orange hand symbol in
the GUI). It is then excluded from further analysis by scripts. This is good for
debugging unfinished proof scripts.

* `macro`

    Invoke a macro on the current goal. The names of available macros include:
    
    * `autopilot`      -- full autopilot
    * `autopilot-prep` -- preparation only autopilot
    * `split-prop`     -- propositional expansion w/ splits
    * `nosplit-prop`   -- propositional expansion w/o splits
    * `simp-upd`       -- update simplification
    * `simp-heap`      -- heap simplification

   
    ```
    macro autopilot-prep;
    ```

    !!! note 
        Future version may drop the macro keyword and allow macro
        invocations directly.

* `rule`

     Apply a single rule onto the current sequent. As unnamed argument add the
     name of the taclet to be applied. If the taclet matches only once on the entire
     sequent, the rule is applied. If it matches more than once you need to specify
     more. In that case you can first specify the sequence formula and then the
     number of the occurrence in the formula or the specific subterm via the 'on'
     keyword. If a rule has schema variables which must be instantiated manually,
     such instantiations can be provided as arguments. A schema variable named sv can
     be instantiated by setting the argument `sv="..."` or by setting `inst_sv="..."`
     (the latter works also for conflict cases like `inst_occ="..."`).

     If there is only one matching spot on the sequent
     ``` 
     rule andRight;
     ``` 
     Changes sequent `a=b ==> c=d` to `b=a ==> c=d`.
     `rule eqSymm;` alone would have been ambiguous.
     ```
     rule eqSymm formula="a=b";
     ```
     Changes sequent `a=b->c=d ==>" to "a=b->d=c ==>`.
     The occurrence number is needed since there are two possible applications on the formula.
     ```
     rule eqSymm formula="a=b->c=d" occ=2;
     ```
     
     changes sequent "a=b->c=d ==>" to "a=b->d=c ==>".
     same as above, but using the option to specify a 
     subterm instead of an occurrence number.
     ```
     rule eqSymm formula="a=b->c=d" on="c=d";
     ```
     
     Almost the same as `cut "x>y"`:
     ```
     rule cut cutFormula="x > y";
     ```
     
* `script`

    Invoke another script which resides in an external file.
    ```
    script '/path/to/other/file.script';
    ```

* `select`

     Unlike most other commands, this command does not change the proof but
     chooses the goal on which the next step operates. Currently you can specify
     a formula. The goal is chosen such that the formula appears (toplevel) on the
     sequent (antecedent or succedent). You can limit the search to antecedent or
     succedent.
     
     Search for the formula anywhere
     ```
     select formula="{ x:=1 }y < x";
     ```
     
     Search only the succedent for the formula: 
     ```
     select succedent formula="wellFormed(someHeap)";
     ```
     
* `smt`

    Invoke an external SMT solver. That solver must be adequately
    configured outside the script mechanism. By default, Z3 is invoked,
    but that can be chosen.
    
    Invoke Z3

    ```
    smt;
    ```
    
    A comma separated list of solvers can be specified.
    ```
    smt solver="Z3,yices";
    ```
    
* `tryclose`

    Unlike other commands this command operates on ALL open goals and
    effectively applies the "try provable goals below" macro to all of
    them. A number of steps can optionally be given.

    ```
    tryclose;
    ```
    
    Spend 2000 steps on each open goal
    ```
    tryclose steps=2000;
    ```
    


## Write your on proof script commands

to be done.
Contact Mattias, if you are interested.
