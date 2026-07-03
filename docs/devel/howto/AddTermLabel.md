# How to add a term label

*2026 — the code below was compiled against the term-label rework branch;
the registration/attachment pattern is the one exercised by
`TestTermLabelManager` and the shipped labels.*

A *term label* annotates a term occurrence with bookkeeping information
that is **not soundness-relevant** — erasing all labels must never make a
proof wrong. Labels travel with their term through rule applications.
Read [Term Labels](../../TermLabels/) first for the concept and the
architecture; this page is the recipe.

## 0. Do you actually need a new label?

A label is the right tool if you need to *mark a term occurrence* and
find the mark again later (in a strategy feature, a rule, or the GUI).
It is the wrong tool if the information is per-proof (use proof
metadata), per-formula-position (use `PosInOccurrence` bookkeeping), or
soundness-relevant (then it must be part of the logic, not a label).

## 1. Define the label

**Without parameters** — add two constants to
`de.uka.ilkd.key.logic.label.ParameterlessTermLabel`:

```java
public static final Name DEMO_LABEL_NAME = new Name("demo");

public static final TermLabel DEMO_LABEL =
    new ParameterlessTermLabel(DEMO_LABEL_NAME);
```

**With parameters** — write a class implementing `TermLabel`. Keep it
immutable, implement `equals`/`hashCode` (label-set comparison relies on
them), and expose the parameters via `getTLChild(int)` /
`getTLChildCount()`. `SymbolicExecutionTermLabel` (one `int` id) is a
compact template. Parameters are printed as strings and must be parsable
back (step 2).

If the label should be invisible to proof-relevant comparisons — it is
purely cosmetic, like `origin` — override `isProofRelevant()` to return
`false`. Leave the default (`true`) otherwise.

## 2. Provide a factory

The factory parses the label when a proof file or taclet mentions it.

- Parameterless: reuse `SingletonLabelFactory`, no code needed (step 3).
- Parameterized: implement `TermLabelFactory<YourLabel>`; its
  `parseInstance(List<String> parameters, TermServices services)` gets the
  parameter strings. See `SymbolicExecutionTermLabelFactory` for
  validation and error reporting via `TermLabelException`.

## 3. Register in the profile

Labels are part of a profile's vocabulary. For a standard label, extend
`JavaProfile.computeTermLabelConfiguration()`:

```java
result = result.prepend(new TermLabelConfiguration(
    ParameterlessTermLabel.DEMO_LABEL_NAME,
    new SingletonLabelFactory<>(ParameterlessTermLabel.DEMO_LABEL)));
```

For an experimental or module-local label, subclass the profile and
override `computeTermLabelConfiguration()` instead (the symbolic
execution API does exactly this, see
`SymbolicExecutionJavaProfile`). An unregistered label name is a parse
error, so nothing outside your profile can create the label from text.

The two-argument `TermLabelConfiguration` shown above is the common
case: factory only, no maintenance hooks. The full constructor
additionally takes application-term policies, modality-term policies,
updates, refactorings, and a merger — see step 5.

## 4. Attach the label

**From a taclet** (the normal way): write the label after the term in
the rule file —

```
demoIntro {
    \find (f(x))
    \replacewith (f(x)<<demo>>)
    \heuristics (simplify)
};
```

Labels written in a taclet's `\replacewith`/`\add` are attached
automatically when the rule fires; no Java code runs.

**From Java code** (rules, macros, PO generation):

```java
JTerm labeled = services.getTermBuilder().label(term,
    ParameterlessTermLabel.DEMO_LABEL);
// or keep existing labels and add one:
JTerm added = services.getTermBuilder().addLabel(term,
    ParameterlessTermLabel.DEMO_LABEL);
```

**Reading it back**, e.g. in a strategy feature:

```java
if (term.containsLabel(ParameterlessTermLabel.DEMO_LABEL)) { ... }
// or, when only the subtree matters:
if (term.containsLabelsRecursive()) { ... }
```

Remember the equality contract: `equals` ignores labels. If you keep
terms in a map and your values depend on the key's labels, key the map
with `StrictTermKey`.

## 5. Decide how the label survives rule applications

Work through this ladder top-down and stop at the first rung that
covers your label — each further rung costs performance on every rule
application:

1. **Nothing.** The label sits on a term that rules never rewrite (or
   it is fine that a rewrite drops it), or every occurrence is created
   by taclets that write the label explicitly. Most shipped labels live
   here.
2. **`TermLabelPolicy`.** The rewritten term should *keep* the label the
   original had: register an application-term policy (label sits on the
   rewritten term itself) or a modality-term policy (label sits on the
   modality below the updates). `StayOnOperatorTermLabelPolicy` keeps a
   label as long as the top operator stays the same.
3. **`TermLabelUpdate`.** You need to add/remove/replace labels
   depending on the rule being applied (can be restricted to specific
   rules via `getSupportedRuleNames()`). Runs after the policies and
   sees the label set they produced.
4. **`TermLabelRefactoring`.** You need to change labels on terms *other*
   than the one being created — up to the whole sequent. Scopes:
   below-updates, application subtree (optionally including parents),
   whole sequent. This is the expensive rung; the whole-sequent scope
   rewrites every formula after every application of the supported
   rules.
5. **`TermLabelMerger`.** Your label must survive when its formula is
   rejected as a duplicate of an equal-modulo-labels formula already in
   the sequent (`FormulaTermLabelMerger` is the only shipped example).

All hooks are registered through the same `TermLabelConfiguration` from
step 3. The execution order (policies before updates) is fixed; do not
design a label that needs an update to run before a policy.

## 6. Test it

- Unit level: build terms with `TermBuilder.label(...)` and assert on
  `getLabels()`/`containsLabel(...)`; see `LabeledTermImplTest`.
- Framework level: `TestTermLabelManager` shows how to register
  policies/updates/refactorings against a throwaway profile.
- Proof level: replay a proof that exercises your taclet and check the
  label appears where expected — `TermLabelEquivalenceDumpTest`
  (key.core tests) dumps every sequent of replayed proofs including all
  labels and is the template for label-coverage regression checks.
