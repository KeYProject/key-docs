# Event listeners

To monitor different parts of the KeY system, you may register specific event listeners.
This list gives an overview grouped by the object you need to register the listener at.
Some extremely obscure listeners (e.g. ISideProofStoreListener, NodeInfoVisualizerListener) are omitted.

## KeYMediator

### GUIListener

Accepts events for the opening and closing of modal dialogs.
Receives a notification when KeY is about to be closed.

### InterruptedListener

Receives an event when the user clicks on the stop button.

### KeYSelectionListener

Monitor the currently selected proof, node, goal, ...

### UserActionListener

Get notified when the user does certain actions (starting a macro, loading a proof, ...).

### enableWhenProofLoaded

Pass an action to this method to enable it only when a proof is loaded.

## AbstractMediatorUserInterfaceControl

Aquire via `mediator.getUI()`.

### ProverTaskListener

Listener for longer tasks, which may be run in a separate worker thread. Examples: proof loading, macros.

## AbstractProofControl

Aquire via `mediator.getUI().getProofControl()`.

### AutoModeListener

Receives an event when "auto mode" is activated or deactivated.
This mode is used for several functions (proof macros, ...).
When in "auto mode", the KeY interface (except for the stop button) will not respond to user interaction and the UI will not update.

### InteractionListener

Listener for interactions done by the user: settings changed, macro started, rule applied, proof pruned, ...

## Proof

### ProofTreeListener

Monitor changes to the proof (new nodes, prune events, ...).

### ProofDisposedListener

Gets notified when a proof is about to be disposed and when a proof has been successfully disposed.

### RuleAppListener

Receives an event for each rule applied on the proof.

## Goal

### GoalListener

Monitor the state of a goal (sequent, node, automatic state).

## ProblemInitializer

### ProblemInitializerListener

Notified about everything related to loading a proof (progress indications, status messages, ...).

## Config

### ConfigChangeListener

Notified about changes to the font configuration.

## DelayedCutProcessor

### DelayedCutListener

Related to the 'delayed cut' functionality.

## TacletAppIndex

### NewRuleListener

Receives an event when a new taclet is added by a rule application.

## Lookup

### LookupListener

Receives an event whenever a value in the Lookup instance changes.

## MergeRuleBuiltInRuleApp

### MergeRuleProgressListener

When applying a merge rule, this listener will be notified for each merged branch.
