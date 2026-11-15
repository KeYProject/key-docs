---
approved: mu 2026-06-19
---
# Excluding Goals from Automation

Often enough one deals with proofs in KeY with a considerable number of open
goals which can be divided into two categories: interesting and uninteresting
ones.

*Scenario 1:*
We assume the unteresting ones to be closed soon by automatic rule application,
and want to concentrate on the interesting ones. They should be left untouched
by automatic rule application.

*Scenario 2:* 
We have many branches and want to deal with them separately and want
to focus on one after the other.

This is what we can tell KeY to do in the UI:

## Interactive vs. Automatic

Both in the "Proof" and the "Goals" view on the left hand side one can
now open a context popup menu which contains new items to mark open
goals as 
* automatic ("OPEN GOAL", green, key icon) 
  or
* interactiv ("INTERACTIVE GOAL", orange, key icon with hand)

Pressing the Start/Stop Button on top will trigger rule application
only on automatic goals.  The "Apply Strategy" Menu Item from the
context menu however will also work on interactive goals. So does the
"shift+left mouse click" mechanism on a selected goal.

All goals which are derived from an interactive goal are marked
interactive also.
