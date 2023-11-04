# Proof Slicing

-- *Author: Arne Keller*, December 2022 valid for KeY-2.12.0 (last updated: November 2023)

!!! abstract

    This note describes the new *Proof Slicing* extension in KeY 2.12.
    It allows reducing the size of finished proofs by
    removing proof steps that are not necessary to close the proof.

    This feature is available if the extension is activated in the settings.
   

## Overview

The *Proof Slicing* extension aggregates several features:
automatic construction of the dependency graph (an alternative view on the proof),
two analysis algorithms to identify proof steps to remove,
and the proof slicing algorithm that constructs a new (smaller) proof slice given the analysis results.

![Image of side panel](./ProofSlicing.png)

## Dependency Graph

Each sequent formula in the proof is stored as a node in the dependency graph.
Proof steps are represented by a hyperedge starting at the new sequent formulas introduced.
If the step required some formulas to be present beforehand, the hyperedge points to these nodes.
(For technical reasons, this hyperedge is stored as a collection of regular edges from each input to each output.)
Proof steps that close a proof branch start at a special kind of node: a "closed goal" node.
See the last section below for all types of graph nodes.

The extension automatically constructs the dependency graph when loading or constructing a proof.
The number of nodes and edges is displayed in the sidebar.
You may inspect the dependency graph by clicking on "Show rendering of graph".
This requires an installation of [Graphviz](https://www.graphviz.org/) on your system (more specifically, `dot` or `dot.exe` needs to be in your `$PATH`).
Installation instructions are available [at graphviz.org](https://www.graphviz.org/download/).

You may also export the dependency graph in DOT format ("Export as DOT" button) and visualize it using any other tool of your choice.

<figure markdown>
  ![Dependency graph example](./ProofSlicingDependencyGraph.png)
  <figcaption>Dependency Graph of a simple proof (top node: proof obligation)</figcaption>
</figure>

!!! attention

    It is not advisable to render the dependency graph of large proofs: the render process may consume excessive amounts of memory and/or CPU time.

### Chain Shortening

When inspecting the dependency graph, you might want to see only the "big picture" of the proof.
If you don't care about the hundreds of intermediate steps it takes to normalize a polynomial (for example),
you may enable the "Shorten long chains" option before rendering the graph.
When enabled, all nodes with input and output degree equal to one are collapsed into the output edge.

<figure markdown>
  ![Side-by-side comparison of chain shortening](./ProofSlicingShortenedChains.png)
  <figcaption>Left graph: default settings. Right graph: chain shortening enabled.</figcaption>
</figure>

## Proof Analysis

The extension offers two analysis algorithms.
The first algorithm ("Dependency Analysis") uses the dependency graph to find proof steps that do not "contribute" to a closed goal.
If none of the sequent formulas introduced by a proof step are used in further steps to close a proof branch, the proof step
may be omitted.
The second algorithm ("De-duplicate rule applications") identifies identical proof steps in different proof branches which can be performed earlier in the proof.

After running the analysis algorithms, you may also inspect which proof steps will be removed.
They are marked with an 'X' in the proof tree panel (see last figure on this page).

!!! info

    Both algorithms may be combined.

<figure markdown>
  ![Dependency graph example](./ProofSlicingDependencyGraphAnalyzed.png)
  <figcaption>Dependency Graph: edges highlighted in red will be omitted in the proof slice</figcaption>
</figure>

## Proof Slicing

The last section of the sidebar allows you to slice the proof.
The "Slice proof" button runs the analysis algorithms (if not already done), constructs a proof slice, and loads the resulting proof.
It may be possible to slice the proof again to remove more proof steps.
The "Slice proof to fixed point" button repeatedly executes the analysis and slicing algorithms until no more size reductions are possible.

<figure markdown>
  ![Proof slicing applied](./ProofSlicingNewProof.png)
  <figcaption>Running the proof slicer creates a new proof</figcaption>
</figure>

## Dependency Graph node types

All nodes store the branch location of the proof step that created them.
In case of splitting proof steps, the branch of the new node is stored.

### Tracked Formula

Simply a formula on the sequent. If the same formula is created by two different steps, it is represented by different graph nodes.

### Closed Goal

Indicates a finished branch.

### Pseudo Input / Output

Used if a proof step has no inputs / outputs to ensure that the outputs / inputs of the proof step are connected to an edge.

### Variable

Specified as an output if the proof step creates a new skolem constant.
Specified as an input if the proof steps uses the variable to instantiate a schema variable.
(Not implemented yet.)

### Taclet

Dynamically added rule.
Specified as output if the proof step defines the rule.
Specified as an input if the proof step uses this rule.