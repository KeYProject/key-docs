# Scripting Interactive Proofs

To persist interactions performed during proof contsruction in KeY and to replay these
interactions, KeY allows users to use proof scripts.

In this documentation the scripts that allow for branching statements are eplained. (see [Explanation
of linear scripts](./linearScripts.md) for the other version of scripts in KeY)

The three main building blocks of the scripting language are mutators, control-flow
structures, and selectors for proof goals. We describe the general concepts in the
following. 

##Mutators. 
Mutators are the most basic building blocks of the proof
script. When executed a mutator may change the proof script state by changing
variables and the underlying proof state by adding nodes to the proof tree.
