# Working with the Prover

This chapter covers KeY's user interface features for day-to-day
interactive proving:

- **[Excluding Goals from Automation](../Interactive/)** — mark open goals
  as *interactive* so the automated strategy leaves them alone while you
  work on the interesting ones.
- **[Proof Exploration](../Exploration/)** — try out "what if" changes to a
  sequent (adding/editing formulas) without compromising the soundness of
  your proof.
- **[Comparing Proof Nodes](../NodeDiff/)** — diff a proof node with its
  parent to see what a rule application changed.
- **[Linearized Proof Tree](../ProofTreeLinearMode/)** — an alternative,
  linear rendering of the proof tree.
- **[Proof Caching](../ProofCaching/)** — automatically close goals by
  reusing previously completed proofs.
- **[Proof Slicing](../ProofSlicing/)** — analyze which proof steps were
  actually necessary and derive a smaller proof.

Most of these features are implemented as *GUI extensions*; developers can
add their own — see [GUI extensions](../../devel/GUIExtensions/) in the
Developer Guide.
