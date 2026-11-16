---
title: "2. Working with the Prover"
weight: 20
---

This chapter covers KeY's user interface features for day-to-day
interactive proving:

- **[The Taclet Match Dialog](taclet-match-dialog/)** — complete and apply a
  taclet interactively: see how it matched the sequent, instantiate the
  remaining schema variables, and preview the result before you apply.
- **[Excluding Goals from Automation](interactive/)** — mark open goals
  as *interactive* so the automated strategy leaves them alone while you
  work on the interesting ones.
- **[Proof Exploration](exploration/)** — try out "what if" changes to a
  sequent (adding/editing formulas) without compromising the soundness of
  your proof.
- **[Comparing Proof Nodes](node-diff/)** — diff a proof node with its
  parent to see what a rule application changed.
- **[Linearized Proof Tree](proof-tree-linear-mode/)** — an alternative,
  linear rendering of the proof tree.
- **[Proof Caching](proof-caching/)** — automatically close goals by
  reusing previously completed proofs.
- **[Proof Slicing](proof-slicing/)** — analyze which proof steps were
  actually necessary and derive a smaller proof.

Most of these features are implemented as *GUI extensions*; developers can
add their own — see [GUI extensions](../../devel/extending/gui-extensions/) in the
Developer Guide.
