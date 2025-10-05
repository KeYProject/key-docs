# Proof Scripts in JML 

!!! note
    This describes proof scripts from JML as opposed to [linear scripts](../linearScripts)
    that are written in KeY files in JavaDL.
    
The KeY verification system supports **proof scripts** to make interactive proofs **repeatable, robust, and easier to manage**.
Instead of manually clicking through proof steps in the GUI for each verification run, users can persist important proof interactions directly in the source code via **JML assertions**.

Scripts make proofs more **resilient to small changes** in code or specifications, while still leaving routine steps to KeY’s automatic proof search.

[Linear proof scripts] can be used to compose scripts for entire JavaDL proof obligations. The challenge there is that symbolic execution may produce a lot of open proof goals and identifying and navigating to the right open goal in order to apply proof steps can be unnecessarily challenging.

Now, you can attach proof scripts to JML assertions directly in the Java sources such that no navigation is needed.

## Attaching Scripts to Assertions

Proof scripts can be attached directly to JML assertions using the `\by { ... }` construction.

When KeY encounters an assertion with `\by`:

1. The proof splits into two branches:
   * One where the assertion must be proven.
   * One where the assertion is assumed.

2. If the assertion has a script, the script is executed to prove that branch.

**Example** (from a case study):

```java
/*@ assert \seqPerm(\array2seq(values),
                 \old(\array2seq(values))) \by {
        oss;   // one-step simplification
        assert "seqDef{int u;}(0, values.length, values[u])
              = seqDef{int j;}(0, values.length, values[j]@heapAfter_Storage)"
            \by { auto; }
        auto;  // automatic proof search
} @*/
```

This proof of the JML assertion introduces an intermediate assertion as a stepstone towards the ultimate goal. The two arising goals can be verified using KeY's automation.


## Basic Commands

A script consists of a list of commands. The most important ones include:

* **`auto`**
  Runs KeY’s automatic proof search. Options can restrict steps or strategies.

* **`macro "name"`** Runs a predefined tactic. Examples:
    * `macro "simp-heap"` – Simplify heap expressions.
    * `macro "split-prop"` – Expand propositional formulas.

* **`rule <name>`**
  Apply a single sequent calculus rule.
  Example:

  ```java
  rule impRight on="a->b";
  ```

* **`assert "formula" \by { ... }`**
  Creates a case split.
  The nested block can contain its own script.
  
The documentation also contains [a full list of all proof script commands](../commands).

## Structuring Scripts

Scripts for JML assertions can be **nested** inside assertions.
This makes them more structured and robust than the older linear script format.

Scripts do **not** support loops or conditionals. Repetition is handled by automation (`auto`, macros).

## Debugging and Special Commands

* **`leave`**
  Stop the script and leave the current goal open for interactive continuation.

* **`assume`**
  Add a formula as an assumption without proving it (for quick what-if analysis).
  
* **`cheat`**
  Closes a goal unconditionally (like `assume false`).

## Advanced Features

### Abbreviations (`let`)

Define short names for long terms.

```java
let @middle="begin + bucket_starts[bucket]";
rule seqDef_split on="seqDef{int j;}(begin, end, values[j])"
                  inst_idx="@middle";
```

### Term Matching

Scripts allow placeholders (`_`) for terms and formulas.
Example:

```
f(_) = _ ∧ _
```

matches any conjunction where the first part is an equality of the form `f(t) = s`.

### Named Witnesses

Control the naming of Skolem constants during quantifier instantiation:

```java
witness "\forall int b; (0 <= b & b < num_buckets -> _)" as="b_0";
rule allLeft on="\forall int b; (b < num_buckets & b >= 0 & b != bucket -> _)"
              inst_t="b_0";
```

## Examples

Here are some examples of proof scripts in JML:

### Heap Simplification and Rule Application

```java
/*@ assert \assignable(\old(\heap()), values[*]) \by {
    oss;
    rule assignableDefinition;
    macro "simp-heap";
    auto;
} @*/
```

### Using Abbreviations and Nested Assertions

```java
/*@ assert sample2: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), before_sort) \by {
    oss;
    let @numSamplesFinal="int::final(self, de.wiesler.SampleParameters::$num_samples)";
    assert "seqPerm(seqDef{int j;}(begin + @numSamplesFinal, end, ...),
                    seqDef{int j;}(begin + @numSamplesFinal, end, ...))" \by {
        auto;
    }
    auto;
} @*/
```

### Proof of Boyer-More using JML proof scripts

see https://github.com/KeYProject/key/blob/96a6a98328bb9dbaadfb5b54e11b29230e77dfe9/key.ui/examples/heap/BoyerMoore/src/BoyerMoore.java

### Proof of Quicksort using JML proof scripts

see https://github.com/KeYProject/key/blob/4579ddf083e76927db5c2ffb40268962482aa9e3/key.ui/examples/heap/quicksort/Quicksort.java

### Proof of the [IPS4O sorting algorithm](https://doi.org/10.1007/978-3-031-57246-3_15) (partially) using scripts

see https://github.com/KeYProject/ips4o-verify/blob/pfeifer/STTT/src/main/java/de/wiesler/Sorter.java
