# Proof Caching

-- *Author: Arne Keller*, May 2023 valid for KeY-2.12.0

!!! abstract

    This note describes the new *Proof Caching* functionality in KeY 2.12.
    It allows reusing parts of earlier proofs when performing another proof.
   

## Overview

The *Proof Caching* functionality allows reusing previous proofs when creating a new proof.
More precisely, it allows you to close a branch of the proof by "reference" to an already closed branch in another proof.
These conditions have to be met:

![tree with cached goals](./ProofCachingTree.png)

### Required conditions for caching to work

To close a branch with sequent S in proof P using another branch with sequent S' in proof P', the following conditions have to bet:

1. Choice settings (handling of integer overflows etc.) of P and P' need to be equal
2. Antecedent(S') ⊆ Antecedent(S) and Succedent(S') ⊆ Succedent(S)
3. Neither branch uses state merging
4. S' may not contain query terms (would constitute an external influence)
5. S' may not contain symbolic execution terms (would constitute an external influence)

### Activating the extension

In KeY's settings dialog, enable the Proof Caching extension.
You can toggle the automatic search for references in the "Proof Caching" section (on by default).

### Automated reference search

When running the auto pilot or a strategy macro, KeY will automatically search for references
whenever the proof is branched.
This search considers all closed branches in other proofs and compares the current sequent to the
first node in the closed branch.

### Manual reference search

Right-click on an open goal in the proof tree and select "close by reference".
If a matching branch is found, the goal will be closed.
Otherwise, a dialog with an error message will open.

### Copying referenced proof steps

In the status line, a button indicates whether cached goals are present:

![button in status line](./ProofCachingStatusLine.png)

Clicking on the button opens a dialog with additional details where the referenced proof
may be copied into the new proof.

![dialog](./ProofCachingDialog.png)

### Toolbar buttons

Two new buttons are added to the toolbar.

![buttons](./ProofCachingToolbar.png)

The first button copies all referenced steps into the current proof.
The second button jumps to the referenced proof step, if the currently selected node is a cached goal.

### Saving the full proof

When saving a proof that references other proofs, those proof steps are first copied into the new proof.
This ensures that the proof is reloadable and self-contained.
When a referenced proof is closed, the proof steps required in other proofs are first copied over.

### Possible future extensions

Not implemented yet.

- caching proof information across KeY runs: so far, only currently opened proofs are considered
- checking for references right after finishing symbolic execution: so far, only if the proof is split afterwards
- allowing for "compatible" differences in choice settings (difficult)