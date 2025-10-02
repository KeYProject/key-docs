# Linear Proof Scripts

!!! note
    This covers linear scripts. Scripts can also be attached to [JML assertions with scripts](../jml).

Every KeY user knows the pain of manually redoing an interactive proof
over and over again even though only a tiny bit of the program or
specification have changed. One can use proof scripts which will
alleviate worries with repeating proofs.

Proof scripts are textual representations of rule applications, settings changes
and macro invocations. They are notated in linear order. The target of a script
command is usually the first open goal in the proof tree, i.e., the first
reached when traversing the proof tree (not necessarily the first in the *Goal*
pane in the GUI).

## Syntax of proof scripts

A proof script is a finite sequence of proof commands with arguments.

Proof commands start with an identifier followed by optional arguments:

```
command argName:"argument" "positinoal argument without name" ;
```

Every command is terminated with a semicolon. There are named
arguments in the form `argName="argument"` and positional argument
without name. Double quotes `"..."` can be used to denote strings.  If
`"argument"` is an identifier itself, the quotes can optionally be
dropped, like in

```
rule andRight ;
```

Besides strings, *terms* and *sequents* can also be given as arguments
to proof script commands, for instance

```
cut x > 0 ;
```

makes a case distinction over `x > 0` splitting the goal into two new
goals.

Proof scripts are case sensitive. Comments can be added like in Java
using `/* ... */` or `//`.


## How can scripts be loaded

From within key input files. At the very end of key files *INSTEAD* of
a `\proof` object, you can attach a proof script in braces directly
following the keyword \proofScript. An very simple example reads:

```
\predicates {a; b;}
\problem { a & b -> a }

\proofScript {
   rule impRight;
   rule andLeft;
   rule close;
}
```

You can also load a script from an external file by writing

```
\proofScript { script"'some_filename.script"; }
```

## Available commands for linear scripts

The [list of available script commands](../commands) is subject to
change and to extension.

## Linearity of scripts

Linear scripts are (linear) sequences of proof script commands, but
proofs are organised as trees.  For the linearisation, the script
always applies to **topmost open proof goal** in the proof tree.
While this brings a certain order into the proof process, it is 1)
difficult to follow the structure of the (tree-shaped) proof without
seeing the proof tree and 2) if there are many proof goals, the
topmost may not be the one to operate on.

Hence, there is the [`select` command](../commands/#command-select)
that allows you target the next proof steps to a different goal than
the topmost open goal.

Sometimes it makes sense to abandom linearity: The
[`auto`](../commands/#command-auto) and [`tryclose`
command](../commands/#command-tryclose)s have a parameter that allows
them to be applied not to the active goal but to all open goals.

Example:

```
// Apply the autopilot
macro "autopilot-prep";
// and try to close all goals
tryclose all steps: 10000;

// Let's assume two goals remain open.

// Work on goal 1:
select formula: x = TRUE;
rule specialRule;
auto;

// Work on goal 2:
macro "special-macro";
```

## Example linear proof script application:

in the KeY repository:

* https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/quicksort/split.key
* https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/quicksort/sort.key
* https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/quicksort/sort.script

