<style>
  nav.md-nav--secondary li.md-nav__item li.md-nav__item li.md-nav__item { display: none; }
</style>
# Proof Script Commands

This document lists all proof script commands available in the KeY system.
The general ideas of scripts, their syntax, and control flow are described
in the general documentation files on proof scripts.

Field | Value
----- | -----
Generated on: | Fri Oct 03 19:00:08 CEST 2025
Branch: | jmlScripts
Version: | 2.12.4-dev
Commit: | 382f4ce88f33ee3eb90e34b05e23451863271d4c

The commands are organised into categories. Each command may have multiple aliases
under which it can be invoked. The first alias listed is the primary name of the command.
There *named* and *positional* arguments. Named arguments need to be prefixed by their name
and a colon. Positional arguments are given in the order defined by the command.
Optional arguments are enclosed in square brackets.

## Category *Control*

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/ActivateCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `activate`</span>


Reactivates the first open (not necessarily enabled) goal.
This can be useful after a 'leave' command to continue
working on a complicated proof where 'tryclose' should not
apply on certain branches temporarily, but where one still
wants to finish the proof.



<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/AssertOpenGoalsCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `assertOpenGoals`</span>


The assert command checks if the number of open and enabled goals is equal to the given number.
If not, the script is halted with an error message.

Note: This command was called "assert" originally.


#### Usage: 
`assertOpenGoals goals:⟨Integer⟩`

#### Parameters:


* `goals` *(named option, type Integer)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/AssumeCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `assume`</span>


The assume command is an **unsound** taclet rule and adds a formula to the antecedent of the current goal
Can be used for debug and proof exploration purposes.


#### Usage: 
`assume ⟨JTerm (formula)⟩`

#### Parameters:


* `formula` *(1st positional argument, type JTerm)*:<br>The formula to be assumed.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/AxiomCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `axiom`</span>


**Caution! This proof script command is deprecated, and may be removed soon!**

This command is deprecated and should not be used in new scripts.
Use the equivalent `assume` command instead.


The assume command is an **unsound** taclet rule and adds a formula to the antecedent of the current goal
Can be used for debug and proof exploration purposes.


#### Usage: 
`axiom ⟨JTerm (formula)⟩`

#### Parameters:


* `formula` *(1st positional argument, type JTerm)*:<br>The formula to be assumed.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/EchoCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `echo`</span>


A simple "print" command for giving progress feedback to the
human verfier during lengthy executions.


#### Usage: 
`echo ⟨String (message)⟩`

#### Parameters:


* `message` *(1st positional argument, type String)*:<br>The message to be printed.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/ExitCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `exit`</span>


Exits the currently running script context unconditionally.
(In the future, there may try-catch blocks to react to this).




<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SetFailOnClosedCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `failonclosed`</span>


**Caution! This proof script command is deprecated, and may be removed soon!**



#### Usage: 
`failonclosed ⟨String (command)⟩`

#### Parameters:


* `command` *(1st positional argument, type String)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/HideCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `hide`</span>


The hide command hides all formulas of the current proof goal that are in the given sequent.
The formulas in the given sequent are hidden using the taclets hide_left and hide_right.


#### Usage: 
`hide ⟨Sequent (sequent)⟩`

#### Parameters:


* `sequent` *(1st positional argument, type Sequent)*:<br>The sequent containing the formulas to hide. Placeholders are allowed.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/LeaveCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `leave`</span>


Marks the current goal to be ignored by the macros.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/AllCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `onAll`</span>


Executes a given block of script commands on all open goals.
The current goal is set to each open goal in turn while executing the block.
It expects exactly one positional argument, which is the block to be executed on each goal.

#### Examples:
* `onAll { smt solver="z3"; }`
* `onAll { auto; }`




<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/ScriptCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `script`</span>


Includes and runs another script file.

#### Usage: 
`script ⟨String (filename)⟩`

#### Parameters:


* `filename` *(1st positional argument, type String)*:<br>The filename of the script to include. May be relative to the current script.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SelectCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `select`</span>


The select command selects a goal in the current proof.
Exactly one of the parameters must be given.
The next command will then continue on the selected goal.

#### Examples:
- `select formula: (x > 0)`
- `select number: -2`
- `select branch: "Loop Invariant"`


#### Usage: 
`select [branch:⟨String⟩] [formula:⟨JTerm⟩] [number:⟨Integer⟩]`

#### Parameters:


* `branch` *(optional named option, type String)*:<br>The name of the branch to select. If there are multiple branches with the same name, the first one is selected.

* `formula` *(optional named option, type JTerm)*:<br>A formula defining the goal to select. May contain placeholder symbols. If there is a formula matching the given formula in multiple goals, the first one is selected.

* `number` *(optional named option, type Integer)*:<br>The number of the goal to select, starts with 0. Negative indices are also allowed: -1 is the last goal, -2 the second-to-last, etc.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SkipCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `skip`</span>


Does exactly nothing.



<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/UnhideCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `unhide`</span>


The unhide command re-inserts formulas that have been hidden earlier in the proof using the hide command.
It takes a sequent as parameter and re-inserts all formulas in this sequent that have been hidden earlier.


#### Usage: 
`unhide ⟨Sequent (sequent)⟩`

#### Parameters:


* `sequent` *(1st positional argument, type Sequent)*:<br>The sequent containing the formulas to be re-inserted. Placeholders are allowed.


## Category *Fundamental*

<hr>

### <span style="color: var(--md-primary-fg-color);"> Command `assert`</span>

Alias for command [→ `cut`](#command-cut)

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/AutoCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `auto`</span>


The AutoCommand invokes the automatic strategy "Auto" of KeY (which is also launched by
when clicking the "Auto" button in the GUI).
It can be used to try to automatically prove the current goal.
Use with care, as this command may leave the proof in a incomprehensible state
with many open goals.

Use the command with "close" to make sure the command succeeds for fails without
changes.

#### Usage: 
`auto [all] [classAxioms] [dependencies] [expandQueries] [modelsearch] [add:⟨String⟩] [breakpoint:⟨String⟩] [matches:⟨String⟩] [steps:⟨int⟩]`

#### Parameters:


* `all` *(flag)*:<br>*Deprecated*. Apply the strategy on all open goals. There is a better syntax for that now.

* `classAxioms` *(flag)*:<br>Enable automatic and eager expansion of symbols. This expands class invariants, model methods and
fields and invariants quite eagerly. May be an enabler (if a few definitions need to expanded),
may be a showstopper (if expansion increases the complexity on the sequent too much).

* `dependencies` *(flag)*:<br>Enable dependency reasoning. In modular reasoning, the value of symbols may stay the same, without that its definition is known. May be an enabler, may be a showstopper.

* `expandQueries` *(flag)*:<br>Automatically expand occurrences of query symbols using additional modalities on the sequent.

* `modelsearch` *(flag)*:<br>Enable model search. Better for some (types of) arithmetic problems. Sometimes a lot worse.

* `add` *(optional named option, type String)*:<br>Additional rules to be used by the auto strategy. The rules have to be given as a
comma-separated list of rule names and rule set names. Each entry can be assigned to a priority
(high, low, medium or a natural number) using an equals sign.


* `breakpoint` *(optional named option, type String)*:<br>When doing symbolic execution by auto, this option can be used to set a Java statement at which symbolic execution has to stop.

* `matches` *(optional named option, type String)*:<br>Run on the formula matching the given regex.

* `steps` *(optional named option, type int)*:<br>The maximum number of proof steps to be performed.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/CutCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `cut`</span>


The cut command makes a case distinction (a cut) on a formula on the current proof goal.
From within JML scripts, the alias 'assert' is more common than using 'cut'.
If followed by a `\by proof` suffix in JML, it refers the sequent where
the cut formula is introduced to the succedent (i.e. where it is to be established).


#### Usage: 
`cut ⟨JTerm (formula)⟩`

#### Parameters:


* `formula` *(1st positional argument, type JTerm)*:<br>The formula to make the case distinction on.

#### Aliases:
cut, assert

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/DependencyContractCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `dependency`</span>


The dependency command applies a dependency contract to a specified term in the current goal.
Dependency contracts allow you to do modular reasoning. If for a heap-dependent function symbol,
no changes occur inside the dependency set of this function, the result remains the same.
This can be applied to model methods, model fields or invariants.


#### Usage: 
`dependency on:⟨JTerm⟩ [heap:⟨JTerm⟩]`

#### Parameters:


* `on` *(named option, type JTerm)*:<br>The term to which the dependency contract should be applied. This term must occur in the current goal. And it must be the invocation of a heap-dependent observer function symbol.

* `heap` *(optional named option, type JTerm)*:<br>The heap term to be compared against. If not given, the default heap is used.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/FocusCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `focus`</span>


The command "focus" allows you to select formulas from the current sequent
to focus verification on. This means that all other formulas are discarded
(i.e. hidden using `hide_right`, `hide_left`).

Benefits are: The automation is guided into focussing on a relevant set of
formulas.

The selected set of sequent formulas can be regarded as an equivalent to a
believed "unsat core" of the sequent.

#### Examples:
- `focus x > 2 ==> x > 1` only keeps the mentioned to formulas in the current goal
  removing all other formulas that could distract the automation.


#### Usage: 
`focus ⟨Sequent (toKeep)⟩`

#### Parameters:


* `toKeep` *(1st positional argument, type Sequent)*:<br>The sequent containing the formulas to keep. It may contain placeholder symbols.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/InstantiateCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `instantiate`</span>


Instantiate a universally quantified formula (in the antecedent;
or an existentially quantified formula in succedent) by a term.
One of `var` or `formula` must be specified. If `var` is given, the formula is determined by looking for
a particular occurrence of a quantifier over that variable name.
If `formula` is given, that quantified formula is used directly.
`with` must be specified.

#### Examples:

* `instantiate var:a occ:2 with:a_8 hide`
* `instantiate formula:"\forall int a; phi(a)" with="a_8"`


#### Usage: 
`instantiate [hide] with:⟨JTerm⟩ [formula:⟨JTerm⟩] [occ:⟨int⟩] [var:⟨String⟩]`

#### Parameters:


* `hide` *(flag)*:<br>If given, the rule used for instantiation is the one that hides the instantiated formula to prevent it from being used for further automatic proof steps.

* `with` *(named option, type JTerm)*:<br>The term to instantiate the bound variable with. Must be given.

* `formula` *(optional named option, type JTerm)*:<br>The toplevel quantified formula to instantiate. Placeholder matching symbols can be used.

* `occ` *(optional named option, type int)*:<br>The occurrence number of the quantifier over 'var' in the sequent starting at 1. Default is 1.

* `var` *(optional named option, type String)*:<br>The name of the bound variable to instantiate.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/MacroCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `macro`</span>


The MacroCommand invokes one of KeY's macros. The macro must be registered to KeY's services.

The command takes the name of the macro as first argument, followed by optional
parameters to configure the macro.

The macro is applied to the first open automatic goal in the proof.

#### Examples:
* `macro "prop-split"`
* `macro "auto-pilot"`


#### Usage: 
`macro ⟨String (macroName)⟩ instantiations... [matches:⟨String⟩] [occ:⟨Integer⟩]`

#### Parameters:


* `macroName` *(1st positional argument, type String)*:<br>Macro name

* `instantiations...`: *(options prefixed by `arg_`, type String)*:<br>Macro parameters, given as varargs with prefix 'arg_'. E.g. arg_param1=value1

* `matches` *(optional named option, type String)*:<br>Run on formula matching the given regex

* `occ` *(optional named option, type Integer)*:<br>Run on formula number "occ" parameter

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/OneStepSimplifierCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `oss`</span>


The oss command applies the *one step simplifier* on the current proof goal.
This simplifier applies a set of built-in simplification rules to the formulas in the sequent.
It can be configured to apply the one step simplifier only on the antecedent or succedent.
By default, it is applied on both sides of the sequent.


#### Usage: 
`oss [antecedent:⟨Boolean⟩] [succedent:⟨Boolean⟩]`

#### Parameters:


* `antecedent` *(optional named option, type Boolean)*:<br>Application of the one step simplifier can be forbidden on the antecedent side by setting this option to false. Default is true.

* `succedent` *(optional named option, type Boolean)*:<br>Application of the one step simplifier can be forbidden on the succedent side by setting this option to false. Default is true.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/RuleCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `rule`</span>


This command can be used to apply a calculus rule to the currently active open goal.

#### Examples:
- `rule cut inst_cutFormula: (a > 0)` applies the cut rule on the formula `a > 0` like the cut command.
- `rule and_right on=(__ & __)` applies the rule `and_right` to the second occurrence
    of a conjunction in the succedent.
- `rule my_rule on=(f(x)) formula="f\(.*search.*\)"` applies the rule `my_rule` to the term
    `f(x)` in a formula matching the regular expression.


#### Usage: 
`rule ⟨String (rulename)⟩ instantiations... [formula:⟨JTerm⟩] [matches:⟨String⟩] [occ:⟨Integer⟩] [on:⟨JTerm⟩]`

#### Parameters:


* `rulename` *(1st positional argument, type String)*:<br>Name of the rule to be applied.

* `instantiations...`: *(options prefixed by `inst_`, type JTerm)*:<br>Instantiations for term schema variables used in the rule.

* `formula` *(optional named option, type JTerm)*:<br>Top-level formula in which the term appears. This may contain placeholders.

* `matches` *(optional named option, type String)*:<br>Instead of giving the toplevl formula completely, a regular expression can be specified to match the toplevel formula.

* `occ` *(optional named option, type Integer)*:<br>Occurrence number if more than one occurrence matches. The first occurrence is 1. If ommitted, there must be exactly one occurrence.

* `on` *(optional named option, type JTerm)*:<br>Term on which the rule should be applied to (matching the 'find' clause of the rule). This may contain placeholders.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SMTCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `smt`</span>


The smt command invokes an SMT solver on the current goal(s).
By default, it uses the Z3 solver on the first open automatic goal.
If the option 'all' is given, it runs on all open goals.
If the option 'solver' is given, it uses the specified solver(s) instead of Z3.
Multiple solvers can be specified by separating their names with commas.
The available solvers depend on your system: KeY supports at least z3, cvc5.


#### Usage: 
`smt [all] solver:⟨String⟩ timeout:⟨int⟩`

#### Parameters:


* `all` *(flag)*:<br>*Deprecated!* Apply the command on all open goals instead of only the first open automatic goal.

* `solver` *(named option, type String)*:<br>

* `timeout` *(named option, type int)*:<br>


## Category *Internal*

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SetEchoCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `@echo`</span>


**Caution! This proof script command is deprecated, and may be removed soon!**

An internal command to switch on/off echoing of executed commands.


#### Usage: 
`@echo ⟨String (command)⟩`

#### Parameters:


* `command` *(1st positional argument, type String)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/CheatCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `cheat`</span>


Use this to close a goal unconditionally. This is unsound and should only
be used for testing and proof debugging purposes. It is similar to 'sorry'
in Isabelle or 'admit' in Rocq.




<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/JavascriptCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `javascript`</span>


This command allows to execute arbitrary JavaScript code. The code is executed in a context where
the current selected goal is available as `goal` and a function `setVar(v,t)` is
available to set an abbreviation (where `v` is the name of the variable including the
leading `@` and `t` is either a term or a string that can be parsed as a term).

#### Example:
```
javascript {
  var x = goal.getAntecedent().get(0).getFormula();
  setVar("@myVar", x);
}
```

This command is powerful but should be used with care, as it can easily lead to unsound proofs if
used incorrectly.


#### Usage: 
`javascript ⟨String (script)⟩`

#### Parameters:


* `script` *(1st positional argument, type String)*:<br>The JavaScript code to execute.

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SaveInstCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `saveInst`</span>




<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SaveNewNameCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `saveNewName`</span>


Special "Let" usually to be applied immediately after a manual rule application. Saves a new name
introduced by the last rule which matches certain criteria into an abbreviation for
later use. A nice use case is a manual loop invariant rule application, where the newly
introduced anonymizing Skolem constants can be saved for later interactive instantiations. As for
the let command, it is not allowed to call this command multiple times with the same name
argument (all names used for remembering instantiations are "final").


#### Usage: 
`saveNewName ⟨String (abbreviation)⟩ matches:⟨String⟩`

#### Parameters:


* `abbreviation` *(1st positional argument, type String)*:<br>The abbreviation to store the new name under, must start with @

* `matches` *(named option, type String)*:<br>A regular expression to match the new name against, must match exactly one name

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SchemaVarCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `schemaVar`</span>


**Caution! This proof script command is deprecated, and may be removed soon!**

Defines a schema variable that can be used in subsequent commands.


#### Usage: 
`schemaVar ⟨String (type)⟩ ⟨String (var)⟩`

#### Parameters:


* `type` *(1st positional argument, type String)*:<br>

* `var` *(2nd positional argument, type String)*:<br>


## Category *JML*

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/ObtainCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `__obtain`</span>


Command that introduces a fresh variable with a given name and sort.
Exactly one of `such_that`, `equals`, or `from_goal` must be given.

The command should not be called directly, but is used internally by
the JML script support within KeY.


#### Usage: 
`__obtain var:⟨String⟩ [equals:⟨JTerm⟩] [from_goal:⟨boolean⟩] [such_that:⟨JTerm⟩]`

#### Parameters:


* `var` *(named option, type String)*:<br>Name of the variable to be instantiated.

* `equals` *(optional named option, type JTerm)*:<br>Represented term for which this is an abbreviation.

* `from_goal` *(optional named option, type boolean)*:<br>Top-level formula in which the term appears.

* `such_that` *(optional named option, type JTerm)*:<br>Condition that is to be established for the fresh variable.


## Category *Uncategorized*

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/BranchesCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `branches`</span>


#### Usage: 
`branches ⟨String (mode)⟩ [branch:⟨String⟩] [child:⟨Integer⟩]`

#### Parameters:


* `mode` *(1st positional argument, type String)*:<br>

* `branch` *(optional named option, type String)*:<br>

* `child` *(optional named option, type Integer)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/ExpandDefCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `expand`</span>


#### Usage: 
`expand [formula:⟨JTerm⟩] [occ:⟨Integer⟩] [on:⟨JTerm⟩]`

#### Parameters:


* `formula` *(optional named option, type JTerm)*:<br>

* `occ` *(optional named option, type Integer)*:<br>

* `on` *(optional named option, type JTerm)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/LetCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `let`</span>




#### Aliases:
let, letf

<hr>

### <span style="color: var(--md-primary-fg-color);"> Command `letf`</span>

Alias for command [→ `let`](#command-let)

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/RewriteCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `rewrite`</span>


#### Usage: 
`rewrite find:⟨JTerm⟩ replace:⟨JTerm⟩ [formula:⟨JTerm⟩]`

#### Parameters:


* `find` *(named option, type JTerm)*:<br>

* `replace` *(named option, type JTerm)*:<br>

* `formula` *(optional named option, type JTerm)*:<br>

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/SetCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `set`</span>


#### Usage: 
`set settings... [oss:⟨Boolean⟩] [stack:⟨String⟩] [steps:⟨Integer⟩] [userData:⟨String⟩]`

#### Parameters:


* `settings...`: *(options prefixed by ``, type String)*:<br>key-value pairs to set

* `oss` *(optional named option, type Boolean)*:<br>Enable/disable one-step simplification

* `stack` *(optional named option, type String)*:<br>Push or pop the current settings to/from a stack of settings (mostly used internally)

* `steps` *(optional named option, type Integer)*:<br>Maximum number of proof steps

* `userData` *(optional named option, type String)*:<br>Set user-defined key-value pair (Syntax: userData:"key:value")

<hr>

### <span style="float:right;">[Source](https://github.com/KeYProject/key/blob/382f4ce88f33ee3eb90e34b05e23451863271d4c/key.core/src/main/java/de/uka/ilkd/key/scripts/TryCloseCommand.java)</span><span style="color: var(--md-primary-fg-color);"> Command `tryclose`</span>


#### Usage: 
`tryclose [⟨String (branch)⟩] [assertClosed] [steps:⟨Integer⟩]`

#### Parameters:


* `branch` *(optional 1st positional argument, type String)*:<br>

* `assertClosed` *(flag)*:<br>

* `steps` *(optional named option, type Integer)*:<br>

