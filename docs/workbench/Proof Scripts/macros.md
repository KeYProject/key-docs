# Macros

!!! warning
    This page was automatically created. There seems to have been issues with the export format apparently.

Generated on: ${new Date()} by `gendoc.groovy`.

Covering the macros of [KeY](http://key-project.org).

## Full Auto Pilot (`autopilot`) 

Auto Pilot

<html><ol><li>Finish symbolic execution<li>Separate proof obligations<li>Expand invariant definitions<li>Try to close all proof obligations</ol>



## Auto pilot (preparation only) (`autopilot-prep`) 

Auto Pilot

<html><ol><li>Finish symbolic execution<li>Separate proof obligations<li>Expand invariant definitions</ol>



## Full Information Flow Auto Pilot (`infflow-autopilot`) 

Information Flow

<html><ol><li>Search exhaustively for applicable position, then<li>Start auxiliary computation<li>Finish symbolic execution<li>Try to close as many goals as possible<li>Apply macro recursively<li>Finish auxiliary computation<li>Use information flow contracts<li>Try to close as many goals as possible</ol>



## Propositional expansion (w/o splits) (`nosplit-prop`) 

Propositional

Apply rules to decompose propositional toplevel formulas; does not split the goal.



## One Single Proof Step (`onestep`) 

Simplification

One single proof step is applied



## Heap Simplification (`simp-heap`) 

Simplification

This macro performs simplification of Heap and LocSet terms.
It applies simplification rules (including the "unoptimized" select rules), One Step Simplification, alpha, and delta rules.



## Update Simplification Only (`simp-upd`) 

Simplification

Applies only update simplification rules



## Propositional expansion (w/ splits) (`split-prop`) 

Propositional

Apply rules to decompose propositional toplevel formulas; splits the goal if necessary



## Finish symbolic execution (`symbex`) 

Auto Pilot

Continue automatic strategy application until no more modality is on the sequent.



## Close provable goals below (`tryclose`) 

null

Closes closable goals, leave rest untouched (see settings AutoPrune). Applies only to goals beneath the selected node.

