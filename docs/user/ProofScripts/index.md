# Scripting Interactive Proofs


### Motivation for Proof Scripts in KeY

Formal verification in KeY often requires revisiting and refining
intermediate specifications like loop invariants through a highly
iterative process. However, even small adjustments to the program or
its specification can invalidate entire proofs, necessitating complete
reconstruction. Although KeY's current mechanism can replay proofs
from fine-grained rule applications, it is brittle and vulnerable to
minor changes. Especially in low-automation contexts, where many steps
are performed manually, repeating those steps is time-consuming and
error-prone.

**Proof scripts offer a solution** by capturing the essential and complex reasoning steps, while delegating routine proof search tasks to the automatic engine. This significantly improves maintainability and usability of proofs as code or specifications evolve.

### Benefits of Proof Scripts in KeY

-  **Robustness to Changes**: Scripts focus on core proof decisions rather than low-level steps, making them resilient to small changes in the code or specification.
-  **Increases Comprehensibility**: Proof scripts can convey the high-level proof ideas that allow users to understand the reasoning.
-  **Maintains Manual Effort**: Records manual proof actions (e.g., quantifier instantiations or definition expansions) so that they don't need to be repeated after specification changes.
-  **Improved Automation Synergy**: Proof scripts guide the prover through the difficult parts while letting the automated search handle simpler steps.
-  **Scalability to Complex Proofs**: Handles proof branching more effectively, applying scripts only where user interaction is needed.
-  **Better Usability over Previous Scripting**: Avoids complex top-level goal selection required in earlier global script mechanisms.
-  **Facilitates Proof Reuse**: Allows key insights and strategies to persist across code revisions, supporting iterative verification workflows.

Proof scripts are textual representations of rule applications,
settings changes and macro invocations. They are notated in linear
order. The target of a script command is usually the first open goal
in the proof tree, i.e., the first reached when traversing the proof
tree (not necessarily the first in the Goal pane in the GUI).

## Proof Script Languages

There are two flavours of proof script languages. One more low-level
for the interaction on the level of JavaDL and one for more high-level
interaction on the level of JML annotated to Java code.

### Linear Proof Scripts[^1]

[Documentation of Linear Proof Scripts](linearScripts)

Linear scripts are added to entire JavaDL proof obligations. They can
be loaded interactively or stored in `.key` files.

### JML Proof Scripts

[Documentation of JML Proof Scripts](jml)

JML scripts are added to individual assertions of a Java method. They
are annotated as JML comments in `.java` files.

[^1]: That is a working title name – might be subject to change.
