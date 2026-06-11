# How to add taclets

*2026 — the project-local example below was executed against the current
KeY sources: the file loads, the custom rule applies, and the proof
closes (`./gradlew :key.ui:run --args='--auto demoTaclet.key'` reports
"Proved").*

Taclets are KeY's schematic calculus rules. This how-to covers *where to
put* new taclets; for *how to write* them (the taclet language itself,
schema variables, rule sets) read
[How to write new taclets](../../HowToTaclet/).

There are two scenarios: taclets for **one verification project**, and
taclets for **KeY's standard rule base**.

## Scenario A: project-local taclets

Any `.key` file may declare its own sorts, functions, predicates, and
rules. They exist only for proofs started from that file — no rebuild of
KeY needed. Minimal, runnable example (`demoTaclet.key`):

```
\predicates {
    magic;
}

\rules {
    magicHolds {
        \find(==> magic)
        \closegoal
        \heuristics(closure)
    };
}

\problem {
    magic
}
```

Load the file in KeY (or run
`./gradlew :key.ui:run --args='--auto demoTaclet.key'` for a batch check);
the automated strategy closes the goal using `magicHolds`, because
`\heuristics(closure)` assigns the taclet to a rule set the strategy
applies automatically. Without a `\heuristics` clause the taclet is only
available interactively.

For larger self-contained theories, follow the examples in
`key.ui/examples/theories/` (e.g. `set.key`, `binaryTree.key`): declare
`\sorts`, `\functions`, `\schemaVariables`, and `\rules`, and pull the
theory into a problem file with `\include`.

!!! warning "Soundness"
    KeY does not check that your taclets are sound — a wrong rule lets you
    "prove" wrong statements. Treat project-local taclets as axioms of
    your verification project, and keep them few and reviewable. Derived
    rules can be justified with taclet proofs (see Scenario B, step 4).

## Scenario B: extending KeY's standard rule base

The standard rules live in `key.core` under

```
key.core/src/main/resources/de/uka/ilkd/key/proof/rules/
```

organized by theory (`integer/`, `float/`, `classicalLogic/`, `heap.key`,
`seq.key`, …). The file `standardRules.key` in the same directory includes
them all and is referenced by `JavaProfile` — this is what every standard
proof loads.

Steps:

1. **Pick or create a rule file.** Add your taclet to the thematically
   fitting file, or create a new `myTheory.key` next to the others.
2. **Include it** (only for new files): add an
   `\include myTheory;` line at the appropriate position in
   `standardRules.key`. *The order of includes matters*: for the soundness
   proofs of derived taclets you may only use taclets that appear before
   the one being proved (see the comment at the top of
   `standardRules.key`).
3. **Rule sets**: if your taclet should participate in automation, assign
   it with `\heuristics(...)` to one of the rule sets declared in
   `ruleSetsDeclarations.key` (new rule sets are declared there, and their
   costs are assigned in the strategy implementation, package
   `de.uka.ilkd.key.strategy`).
4. **Justify soundness**: derived (non-axiomatic) taclets should be proved
   sound. Add a corresponding entry to the taclet-proof regression suite —
   see [Regression tests for proved rules](../../Testing/ProveRules/).
5. **Run the tests**: at minimum the parser/prover smoke tests,
   `./gradlew :key.core:test`, and ideally the
   [RunAllProofs](../../Testing/RunAllProves/) suite, since new automated
   rules can change proof search behavior globally.

No build-file changes are needed in either scenario — rule files are
resources of `key.core` and are picked up automatically.

## Built-in rules

If your rule cannot be expressed schematically as a taclet (it needs
arbitrary Java code), you need a *built-in rule* instead — see
[Extending KeY](../../ExtendingKeY/#adding-a-built-in-rule).
