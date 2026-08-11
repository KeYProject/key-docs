# Term Labels

!!! warning "Status: open pull request"
    The term-label rework described on this page is **not yet merged** — it is
    an open pull request. This page documents the proposed design (in particular
    the label-agnostic term equality); details may still change during review of
    the pull request, so this page will be updated accordingly.
    *([pull request #3884](https://github.com/KeYProject/key/pull/3884))*

Term labels are annotations attached to terms: `heap<<anonHeapFunction>>`,
`x + 1<<origin(...)>>`. They carry bookkeeping information *about* a term
occurrence without changing what the term means. This page explains why
they exist (concept), how they are realized (design), and where the
extension points are. For the concrete recipe see
[How to add a term label](howto/AddTermLabel/).

## Concept: why term labels?

KeY's calculus works on terms. Several features need to attach
information to a *particular occurrence* of a term that

1. is **not soundness-relevant** — proofs must stay correct if all labels
   are erased (this is a hard contract, stated on the `TermLabel`
   interface), and
2. must **travel with the term** through rule applications — when a rule
   rewrites, copies, or splits a formula, the annotation should end up in
   the right place in the result.

Requirement 2 is what rules out any side-table keyed by term value: the
same term value (`x = 0`) can occur many times with different
annotations, and rule applications rebuild terms wholesale. The label has
to ride on the term occurrence itself.

The labels shipped with KeY, and who attaches them:

| Label | Attached by | Purpose |
|---|---|---|
| `origin(...)` | JML translation, maintained during proof | provenance: which spec clause a formula came from (user-facing; the only label with `isProofRelevant() == false`) |
| `anonHeapFunction` | loop/method contract rules (via taclets) | marks anonymization heap symbols; strategy features test for it |
| `selectSK` | pull-out-select taclets | marks select-Skolem constants for controlled simplification |
| `impl` | JML translation | marks implicit (tool-generated) specification parts |
| `SC` | translation of `&&`/`||` | short-circuit evaluation marker |
| `loopScopeIndex` | loop-scope taclets | connects loop-scope machinery across rule applications |
| `Trigger` | SMT translation only | quantifier trigger hint for SMT solvers |
| `postCondition`, `undef`, `selfComposedExecution` | information-flow module (`key.core.infflow`) | self-composition bookkeeping |
| `SE`, `LB`, `LoopInvariantNormalBehavior`, `BC`, `F` | symbolic-execution API (`key.core.symbolic_execution`, own profile) | symbolic execution tree / truth-value tracing |

The first six are what you will meet in ordinary verification; a plain
`JavaProfile` proof only ever attaches those.

## Design

### Representation

A term (`TermImpl`, the only implementation of `JTerm`) carries its
labels directly:

- `getLabels()` returns an `ImmutableArray<TermLabel>`; unlabeled terms
  share one empty array. There is no separate class for labeled terms.
- `hasLabels()`, `getLabel(Name)`, `containsLabel(label)` are cheap
  accessors.
- `containsLabelsRecursive()` answers "is there a label anywhere in this
  subtree?" — cached per term (one lazily computed two-bit flag in a
  packed word, like `containsJavaBlockRecursive()`), so label-aware code
  can skip label-free subtrees in O(1).

Labels themselves implement `TermLabel` (`Named`; parameters via
`getTLChild(i)`/`getTLChildCount()`). Parameterless labels are instances
of `ParameterlessTermLabel`; parameterized ones (e.g. `origin`,
`SE(id)`) are own classes. Labels should be immutable, and their
`equals` is what label-set comparison uses.

### Equality: three modes

The central design decision (2026 rework): **plain term equality ignores
all term labels.**

| Mode | Use | Where |
|---|---|---|
| `t1.equals(t2)` / `hashCode` | *logical* identity: same formula, labels are noise | default everywhere |
| `t1.equalsModProperty(t2, IRRELEVANT_TERM_LABELS_PROPERTY)` | like `equals`, but labels with `isProofRelevant() == true` still count; only cosmetic labels (origin) are ignored | comparisons that must distinguish, say, an `anonHeapFunction`-labeled heap from an unlabeled one |
| `t1.equalsIncludingLabels(t2)` + `t1.labeledHashCode()` | strict identity including all labels (compared as sets, per subterm) | interning and caches whose *values* depend on labels |

Why ignore-all is the default: sequent redundancy elimination has always
ignored labels (a formula differing only in labels is rejected as
already present), so the default now agrees with the calculus' own
notion of "same formula"; and the sites needing strictness turned out to
be a handful of infrastructure caches, while under the old strict
default *dozens* of call sites had to opt out of labels explicitly.

Two rules of thumb fall out of this:

- **Label-opaque operations belong on the term.**
  `equalsIncludingLabels` treats labels as opaque sets — it knows nothing
  about specific labels — so it lives on `TermImpl`.
- **Label-kind-aware operations belong in a `Property`.**
  `IrrelevantTermLabelsProperty` consults `isProofRelevant()`; that
  knowledge must not leak into the term implementation.

Consequences to be aware of when writing code:

- A `HashMap<JTerm, …>`/`HashSet<JTerm>` now conflates label variants.
  That is usually what you want (it is why the old code was littered
  with "ignore labels" comparisons). If your map's *values* depend on
  the labels of the key, wrap keys in `StrictTermKey` (label-sensitive
  `equals`/`hashCode` via `equalsIncludingLabels`/`labeledHashCode`).
- Labels are never *lost* through the term factory: its intern cache is
  keyed with `StrictTermKey`, so label variants are interned separately
  and `==` sharing works for labeled terms exactly as for unlabeled
  ones. The taclet-app index cache is label-sensitive too (taclet
  matching may test labels).

### Maintenance during proof: `TermLabelManager` and its hooks

Placing a label is easy; the real work is keeping it in the right place
as the proof runs. Rules do **not** edit terms in place — when a rule
fires it *builds new terms* to replace the old ones. So the label a user
sees on `x + 1<<l>>` before a step sits on an object the step discards;
unless something re-attaches `l`, it is simply gone. Deciding the labels
of the freshly built terms is the job of `TermLabelManager`
(`de.uka.ilkd.key.logic.label`), which the rule engine calls at every
rewrite.

A little vocabulary first, because the hooks are phrased in it:

- The rule is applied at one position of the sequent; the subterm there
  is the **application term** (the redex the rule rewrites), and the rule
  produces the **new term** that replaces it.
- For rules that drive a program the label of interest often sits not on
  the application term but *inside* it. A symbolic-execution formula
  looks like `{u1 || u2 || …} ⟨p⟩ φ` — a block of *updates* wrapped
  around a *modality* `⟨p⟩ φ` — and a step that advances the program
  rewrites the updates while the modality carries the label. So the
  manager also computes the **modality term**, the modality reached by
  skipping the leading updates (`TermBuilder.goBelowUpdates`), and lets a
  label look at *its* labels too.

All hooks receive this information bundled in a `TermLabelContext` (the
rule, rule application, goal, application term, modality term, …) and add
their own payload (the term being built or refactored, the label set).

The five hook kinds are five answers to the question *"how does my label
end up on the new term — or survive elsewhere?"*, from the cheapest and
most common case to the rarest:

- **Nothing at all.** If the taclet writes the label itself —
  `\replacewith (f(x)<<l>>)` in the rule file — the engine copies it onto
  the new term automatically; and a label on a term that rules never
  rewrite just rides along. *Almost every label lives here.*
- **`TermLabelPolicy` — "the new term should keep a label the old term
  had."** The policy is asked, per label of the application term (or of
  the modality term), whether to re-attach it to the new term, and may
  return a modified label. Example: `StayOnOperatorTermLabelPolicy`
  keeps a label as long as the top operator is unchanged. Policies are
  declarative — registered under the label's name, consulted only for it.
- **`TermLabelUpdate` — "I need to compute the label set
  programmatically."** An update receives the whole *mutable* set of
  labels destined for the new term and may add, drop or rewrite entries,
  optionally only for specific rules. This is the escape hatch when
  "keep an existing label" is not enough — e.g. the symbolic-execution
  updates mint a fresh node id and attach a new `SE` label here.
- **`TermLabelRefactoring` — "I need to fix up labels on *other* terms,
  after the fact."** The hooks above only shape the one new term; a
  refactoring runs *after* the step and may rewrite labels on surrounding
  terms. How far it reaches is its **scope**: only the modality below the
  updates, the subtree under the application term (optionally including
  its parent chain up to the formula), or — the sledgehammer — every
  formula in the sequent. Wider scope means more terms rebuilt on every
  application of that rule, so choose the narrowest that works. Example:
  origin labels are recomputed over the application subtree so a parent's
  recorded origin stays consistent with its children's.
- **`TermLabelMerger` — "my formula was dropped as a duplicate; save its
  labels."** A sequent side is a set, and membership ignores labels (see
  [Equality](#equality-three-modes)), so adding a formula that already
  exists *modulo labels* is rejected. The merger is handed the rejected
  copy and the surviving one and can carry labels across so they are not
  lost.

A profile bundles one label's hooks into a `TermLabelConfiguration`. The
same content as a quick reference:

| Hook | What it decides | When it runs |
|---|---|---|
| `TermLabelFactory` | how to parse the label from text | proof loading / taclet parsing |
| `TermLabelPolicy` | keep (possibly transform) or drop one existing label of the application/modality term | while building the new term |
| `TermLabelUpdate` | free edit of the new term's whole label set | after the policies |
| `TermLabelRefactoring` | relabel *other* terms, within a chosen scope | after the rule application |
| `TermLabelMerger` | rescue labels of a formula rejected as a duplicate | at sequent insertion |

**The order is fixed and part of the contract.** Building one term runs:
taclet-provided labels → application-term policies → modality-term
policies → rule-specific updates → rule-independent updates. Policies run
*before* updates deliberately: a policy decides which existing labels
survive, and an update then sees and transforms that set (the SE updates
depend on this). That coupling is why the two remain separate hook kinds
rather than being merged into one.

In practice most labels touch none of this. In the standard `JavaProfile`
ten of the eleven labels are factory-only — placed by taclets
(`t<<selectSK>>` in a rule file), travelling or dying with their term —
and only `origin` registers a policy and a refactoring.

### Registration and visibility

- Profiles own the label vocabulary:
  `AbstractProfile.computeTermLabelConfiguration()` returns the
  `TermLabelConfiguration`s; `JavaProfile` registers the standard
  labels, `SymbolicExecutionJavaProfile` adds the SE ones. An
  unregistered label name is a parse error — labels cannot appear out
  of nowhere.
- `TermLabelSettings` (`UseOriginLabels`, default on) controls whether
  origin labels are attached at all; the GUI additionally has per-label
  *display* toggles (`TermLabelVisibilityManager`) which affect printing
  only.
- `TermLabel.isProofRelevant()` marks whether a label participates in
  proof-relevant comparisons (`IRRELEVANT_TERM_LABELS_PROPERTY`, some
  instantiation hashing). Only `origin` returns `false` today.

## Adding a label

See the verified recipe:
[How to add a term label](howto/AddTermLabel/). The short version: define
the label (+ factory), register it in the profile, attach it from a
taclet or through `TermBuilder.label(...)`, and only then decide whether
you need any maintenance hook beyond the default "travels with its
term".
