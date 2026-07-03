# Term Labels

*2026 — written against the term-label rework branch (`termlabel-cleanup`);
describes the system after the label-agnostic-equality change. If you are
reading this before that branch is merged, the equality semantics in
section "Equality" may not match your checkout.*

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

Rules rebuild terms; something must decide which labels the rebuilt
terms carry. That is `TermLabelManager` (in `key.core`,
`de.uka.ilkd.key.logic.label`), invoked from the rule-application
machinery. The `Policy`/`Update`/`Refactoring` hooks all receive the
current rule application bundled in a `TermLabelContext` (rule, rule
application, goal, application and modality terms, hint, …) plus their
own payload (the term being built/refactored, the label set). Per label,
a profile registers a `TermLabelConfiguration` bundling up to five
collaborators:

| Hook | Contract | Runs |
|---|---|---|
| `TermLabelFactory` | parse the label from text (proof loading, taclet parsing) | at parse time |
| `TermLabelPolicy` | per existing label: *keep* it on the new term (possibly transformed) or drop it — declarative, dispatched by label name; variants for the application term and for the modality term | first, when a new term is created |
| `TermLabelUpdate` | imperative transformer of the whole label set: add/remove freely; can be restricted to specific rules | after the policies |
| `TermLabelRefactoring` | rewrite labels of *other* terms than the created one; scope per application: below-updates, application subtree (± parents), or the whole sequent | after rule application |
| `TermLabelMerger` | when a rewritten formula is rejected because an equal-modulo-labels formula already sits in the sequent: rescue labels from the rejected copy onto the surviving one | at sequent insertion |

The execution order within one term creation is fixed and part of the
contract: taclet-provided labels → application-term policies →
modality-term policies → rule-specific updates → all-rules updates. The
`Policy`/`Update` split is intentional and load-bearing: policies
resolve "which existing labels survive" *before* updates transform the
set, and updates (e.g. the symbolic-execution ones) read the set the
policies populated. Collapsing the two into one hook kind was evaluated
during the 2026 rework and rejected for exactly this reason.

Most labels need almost none of this. In the standard `JavaProfile`,
ten of the eleven registered labels are factory-only — they are placed
by taclets (`t<<selectSK>>` in a rule file) and simply travel or die
with their term. Only `origin` registers a policy and a refactoring.

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
