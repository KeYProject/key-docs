## Excluding goals from automatic rule application

Often enough one deals with proofs in KeY with a considerable number of open
goals which can be divided into two categories: interesting and uninteresting
ones.

We assume the unteresting ones to be closed soon by automatic rule application,
and want to concentrate on the interesting ones. They should be left untouched
by automatic rule application.

This is what we can tell KeY to do, now.

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
