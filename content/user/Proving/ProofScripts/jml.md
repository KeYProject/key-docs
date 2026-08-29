---
title: "Proof Scripts in JML"
weight: 29
---

# Proof Scripts in JML 

{{% alert type="info" %}}
This describes proof scripts from JML as opposed to [linear scripts](../linearScripts)
that are written in KeY files in JavaDL.

{{% /alert %}}
The KeY verification system supports **proof scripts** to make interactive proofs **repeatable, robust, and easier to manage**.
Instead of manually clicking through proof steps in the GUI for each verification run, users can persist important proof interactions directly in the source code via **JML assertions**.

Scripts make proofs more **resilient to small changes** in code or specifications, while still leaving routine steps to KeY’s automatic proof search.

[Linear proof scripts](../linearScripts) can be used to compose scripts for entire JavaDL proof obligations. The challenge there is that symbolic execution may produce a lot of open proof goals and identifying and navigating to the right open goal in order to apply proof steps can be unnecessarily challenging.

Now, you can attach proof scripts to JML assertions directly in the Java sources such that no navigation is needed.

## Attaching Scripts to Assertions in Methods

When KeY encounters an JML assertion during symbolic execution, it splits the proof into two branches: One where the assertion must be proven and one where the assertion is assumed. Traditionally (and when no proof is annotated), the first goal is subject to KeY's usual automatic strategy.

**The novelty** is that you can add a proof script annotation to any JML assertion with `\by` keyword
Two forms are supported:

- *single command* as in `/*@ assert P \by auto; */` or
- *block* as in `/*@ assert P \by { oss; auto; } */`.

**Example** (from a case study):

```java
/*@ assert \dl_seqPerm(seq3, seq0) \by {
  @   assert \dl_seqPerm(seq1, seq0) \by auto; // intermediate goals
  @   assert \dl_seqPerm(seq2, seq0) \by auto; // intermediate goals
  @   auto; // automatic proof search
  @} */
```

??? note "`auto` required"

    Currently,  every assertion **inside** a JML proof script needs to have a trailing `\by auto;` to be submitted to KeY's automation.
    Toplevel JML assertions need not be thus annotated. A toplevel assertion without \by-clause will be subjected to `auto` automatically.

This proof of the JML assertion introduces intermediate assertions as stepstones towards the ultimate goal. The two arising goals can be verified using KeY's automation.

**A pattern:** Normalise the proof state, apply a rule very precisely and leave the remainder to automation, like:

```java
/*@ assert A ==> B \by {
    oss;             // basic simplifications
    rule "impRight"; // explicit rule application
    auto;            // let automation finish
} @*/
```

For very simple cases, a single command suffices, here by calling an SMT solver:

```java
/*@ assert A ==> B \by smt; @*/
```

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
  rule "impRight" on: "a->b";
  ```

* **`assert "formula" \by { ... }`**
  Creates a case split.
  The nested block can contain its own script.
  
The documentation also contains [a full list of all proof script commands](../commands).

## Matching and Disambiguation

When applying rules or macros, you may need to disambiguate where they apply:

- `on:` a term pattern to select the subterm (placeholders allowed where supported)
- `formula:` a top-level formula where the term occurs
- `occ:` which occurrence to choose if multiple matches exist

Example (target a specific subterm and occurrence):

```java
rule "bsum_positive1" occ: 0 on: (\num_of int i; lo <= i < a.length; a[i] >= lo);
```

See the [rule command](../commands/#command-rule) for details.

## Structuring Scripts

Scripts for JML assertions can be **nested** inside assertions.
This makes them more structured and robust than the older linear script format.

Scripts do **not** support loops. Repetition is handled by automation (`auto`, macros).

### Case Handling inside `by { ... }`

Within a block, you can react to subgoals created by a preceding command using labeled cases:

```java
rule "andRight" \by {
  case "Case 1":
    auto;
  case "Case 2":
    instantiate hide:true var:"x" with: t;
    auto;
  // optional
  default:
    auto;
}
```

{{% alert title="Cases are labels" type="info" %}}
Cases select among the generated subgoals; they are not general conditionals on program state.
The labels that can be used depend on the applied command. Many rules merely produces labels like the "Case 1" and "Case 2" above. Other commands have more speaking names. Check the commands reference for more information.
{{% /alert %}}

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

For top-level formula selection, regular expressions can be used with `matches:` in supported commands (see the reference).

### Introducing Witnesses (`obtain`)

Introduce a fresh variable and either bind it to a term, constrain it, or obtain it from the current goal:

```java
obtain int x = someTerm;                 // direct binding
obtain int y such_that P(y) \by { ... }  // prove a condition for y
obtain int z \from_goal;                 // pick from current goal
```

### Named Witnesses

Control the naming of Skolem constants during quantifier instantiation:

```java
witness "\forall int b; (0 <= b & b < num_buckets -> _)" as="b_0";
rule allLeft on="\forall int b; (b < num_buckets & b >= 0 & b != bucket -> _)"
              inst_t="b_0";
```

## Examples

Here are some examples of proof scripts in JML.
See also the curated [Examples](Examples) page with verbatim snippets and links.


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

see https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/BoyerMoore/src/BoyerMoore.java

### Proof of Quicksort using JML proof scripts

see https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/quicksort/Quicksort.java

### VerifyThis 2026 — h-index using JML proof scripts

see https://github.com/KeYProject/key/blob/main/key.ui/examples/heap/verifyThis26_01_hIndex/src/HIndex.java

### Proof of Red-Black-Trees using JML proof scripts

see https://github.com/KeYProject/rbtree-verification/blob/main/src/Tree.java

### Proof of the [IPS4O sorting algorithm](https://doi.org/10.1007/978-3-031-57246-3_15) (partially) using scripts

see https://github.com/KeYProject/ips4o-verify/blob/pfeifer/STTT/src/main/java/de/wiesler/Sorter.java
