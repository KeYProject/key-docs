# Proof loading / saving

## Loading

1. (various ways a ProblemLoader gets created)
2. `AbstractProblemLoader#load()` sets up the environment (creating a directory for Java source files, unzipping the proof, reading taclet definitions, ...)
3. `#createProofObligationContainer()` creates the proof obligation
4. `#createProof()` creates a `ProofAggregate` object based on the obligation
5. `#loadSelectedProof()` replays the proof steps using `IntermediateProofReplayer`

## Saving

Is done in `OutputStreamProofSaver`.