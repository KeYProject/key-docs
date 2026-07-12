# Thread Safety and Determinism

!!! note "Not yet on main"
    The multi-core prover and the CI tests described here are part of the
    multithreading pull request
    [KeYProject/key#3842](https://github.com/KeYProject/key/pull/3842), which is
    not merged yet. Until it lands, the described classes, tests and rules exist
    on that branch only; this page describes the state the PR introduces.

KeY can run its automatic proof search on several *worker threads* at once (the
multi-core prover). This page explains what that means for everyone who writes
prover code — rules, strategy features, anything in `key.core` that runs during
proof search. You do not need any prior experience with multithreading to follow
it; every needed term is introduced on the way.

The page has three parts: a short mental model of what the workers share, four
rules with worked examples taken from real KeY code, and a guide to the CI tests
that catch violations of these rules in pull requests.

## 1. The mental model: what do the workers share?

A proof in KeY is a tree. Its leaves that still need work are the *open goals*.
The single-core prover repeats one loop: pick an open goal, pick the cheapest
applicable rule, apply it, repeat. The multi-core prover runs the same search
with several workers: **each worker owns one open goal at a time**, searches the
best rule for it, and hands the finished rule application back to be committed
to the shared proof tree.

Two kinds of objects exist in this picture:

* **Per-goal objects.** The goal itself, its sequent, its local namespaces, its
  rule-application queue. Only one worker touches a goal at a time, so code that
  only uses what it gets *from the goal it was called for* is automatically safe.
* **Shared objects.** Everything else: taclets, strategy features, rule
  singletons, the taclet index base, `Services`, and every `static` field in the
  program. Several workers use these *at the same moment*.

The danger with shared objects is the *data race*: two threads read and write
the same memory without coordination. Java gives almost no guarantees in that
situation — a `HashMap` written by two threads at once can lose entries, return
wrong values, or make a reader loop forever. Races are nasty to debug because
they depend on timing: the same code can pass a hundred runs and fail the
hundred-and-first.

There is a second, subtler failure class that this page also covers:
**indeterminism**. Proof search in KeY is meant to be *reproducible* — same
problem, same settings, same proof, every time. Reproducibility is what makes
saved proofs reloadable and test failures debuggable. Some mistakes (like
letting a `HashMap`'s iteration order influence which rule is tried first) break
reproducibility even with a single thread; under the multi-core prover the same
mistakes make every run differ visibly.

## 2. The four rules

### Rule 1 — no plain mutable static state on the proving path

A `static` field exists once for the whole program. During multi-core proving,
every worker reads and writes that one field. A plain `HashMap`, `ArrayList` or
non-`final` counter used as a static cache is therefore a data race.

The fix depends on what the field is for. The decision table:

| You need... | Use | Why |
|---|---|---|
| a cache where the value depends **only on the key** | `StripedLruCache` | fastest under many threads; losing an entry only costs recomputation |
| a cache where the value depends on **when it was first stored** | `ConcurrentLruCache` | one exact eviction order; slower, but here eviction order changes results |
| scratch memory for the **current computation only** | `ThreadLocal` | every thread gets its own private copy; nothing is shared |
| a table **filled once, then only read** | `final` + immutable content | data nobody writes can be read by everyone |

The interesting question is the cache row split. Ask about your cache: *"if this
entry were thrown away and computed again later, could the new value be
different?"*

**Worked example, "no" case — the modality cache.** The macro
`SymbolicExecutionOnlyMacro` needs to know, over and over, whether a formula
contains a modality (a `\<...\>` or `\[...\]` program block). Whether a term
contains a modality is a property of the term alone: compute it today or next
week, the answer is identical. So the cache entry `term → yes/no` is a *pure
function of the key*, evicting it early is harmless, and the fast
`StripedLruCache` is the right choice. This is exactly what
`ModalityCache` in `key.core` does.

**Worked example, "yes" case — the introduction-time cache.** KeY's strategy
prefers older formulas over newer ones, so it caches *at which proof step a
formula was first seen*. Suppose that cache evicted entries in a
thread-timing-dependent order. Then on one run the entry for formula `F`
survives and says "step 120"; on another run it is evicted and later recomputed
as "step 470". The strategy cost of every rule touching `F` now differs between
the runs, a different rule wins, and the whole proof unfolds differently — the
proof tree is no longer reproducible. Because the *value depends on when it was
stored*, eviction must follow one exact, deterministic order: `ConcurrentLruCache`.

### Rule 2 — shared singletons must not remember anything between calls

Rules, strategy features and match instructions in KeY are usually single
objects (a `static final INSTANCE`) used for *every* goal by *every* worker. Any
mutable instance field on such an object is shared state in disguise.

The classic trap is the *last-call memo*: "the last query and its answer, so a
repeated call is free". Single-core, this is a harmless micro-optimization.
Multi-core, worker A stores its query, worker B overwrites it with a different
goal's query, and worker A's next read pairs its own question with B's answer.

```java
// BROKEN under the multi-core prover: one memo, all workers
private static Term lastFocus;
private static Instantiation lastResult;
```

Two correct designs, both used in KeY today:

```java
// Design 1: one memo PER THREAD -- nothing is shared.
private static final ThreadLocal<Instantiation> lastInstantiation =
    new ThreadLocal<>();
```

The block and loop contract rules use design 1. Its price: worker threads live
in a pool, so whatever the `ThreadLocal` holds stays reachable until that thread
proves something else — large cached objects can linger.

```java
// Design 2: one volatile snapshot holding BOTH pieces immutably.
private record Snapshot(Term focus, Instantiation result) {}
private static volatile Snapshot lastInstantiation;
```

`UseOperationContractRule` uses design 2. `volatile` tells Java that reads and
writes of this field are ordered between threads. A reader takes the snapshot
*once* and then only looks inside its own copy — so it can never pair one
worker's question with another's answer. The worst case is a snapshot for the
"wrong" goal, which fails the focus comparison and is simply recomputed.
Use design 2 when the memo is one small immutable pair; use design 1 when it is
larger or has no natural single-object form.

### Rule 3 — iteration order must never reach rule selection

`HashMap` and `HashSet` make **no promise** about the order in which iteration
returns elements; in practice the order depends on object hash codes, which
change from one JVM run to the next. If that order influences anything the
strategy sees — the order of candidate rule applications, the order costs are
computed in, the order formulas land in an index — then the same problem proves
differently on every run. Nothing "crashes"; the proofs are just never the same
twice, saved proofs stop replaying, and multi-core runs diverge wildly.

**Worked example.** Suppose a rule collects trigger candidates like this:

```java
Set<Term> candidates = new HashSet<>();
collect(goal, candidates);
for (Term t : candidates) {     // HashSet: order differs per JVM run!
    apps.add(buildApp(t));      // ...so the strategy sees a different order
}
```

On Monday the JVM lays objects out one way, `candidates` iterates `{t2, t1}`,
and `t2`'s rule application is tried first. On Tuesday it iterates `{t1, t2}`.
Both proofs may close — but they are *different proofs*, and the saved Monday
proof will not replay on Tuesday. The fix costs one word:

```java
Set<Term> candidates = new LinkedHashSet<>();   // iterates in insertion order
```

`LinkedHashSet`/`LinkedHashMap` remember insertion order; alternatively sort the
collection by a stable key before iterating, or use KeY's immutable lists. The
same rule forbids comparators built on `Object.hashCode()` or
`System.identityHashCode()` — those are memory addresses in disguise.

### Rule 4 — fresh names come from the goal, not from a global counter

When a rule introduces a new symbol (a skolem constant `x_1`, an anonymizing
heap `heapAfter_m`, ...), the fresh name must be derived from the *goal-local*
namespaces: "find the smallest index not used *on this branch*". It must **not**
come from a counter shared by the whole proof. With a shared counter, the name a
goal receives depends on how many names *other* goals grabbed first — under the
multi-core prover that is a race, and even single-core it makes proof replay
fragile: reloading applies the rules in a different global order, the counter
hands out different numbers, and the saved proof refers to names that no longer
exist ("Could not find program variable x_2").

Sibling branches reusing the same name (both branches introduce their own `x_1`)
is fine and intended — names only need to be unique along one branch.

## 3. The CI tests that enforce these rules

Three test groups run in KeY's CI so that a pull request violating a rule fails
*before* it is merged. Each failure message contains a short version of the
advice below.

**`SharedStateLintTest`** (in the normal unit-test suite, takes seconds) scans
the compiled classes of the proving-path packages for Rule-1 violations: any
non-`final` static field, and any `final` static field holding a plain mutable
collection. If your new field is reported, pick a replacement from the Rule-1
table. If the field is genuinely safe — for example a settings flag written only
before proving starts — add it to `shared-state-allowlist.txt` (next to the
test) with a one-line justification. Do not allowlist by default: most findings
are better fixed.

**`ScDeterminismTest`** (part of the `testMt2w` CI job) proves a fixed set of
example problems **twice in the same JVM with the single-core prover** and
requires the two proof trees to be bit-for-bit identical. There is no threading
involved, so a failure here is exactly reproducible and almost always a Rule-3
violation (with a Rule-1 "wrong cache flavour" as the runner-up). Reproduce with
`./gradlew :key.core:testMt2w --tests '*ScDeterminism*'`.

**`RunSmallProofsMt2wTest` / `RunSmallProofsMt4wTest`** (CI jobs `testMt2w`,
`testMt4w`) prove a corpus stratified over the prover's subsystems —
quantifiers, arithmetic, heap, loops, contracts, sequences and strings, wide
splitting, rewriting — with 2 and 4 workers and assert every proof closes and
reloads. The 4-worker job runs the widest-splitting proofs three times each,
because races are timing-dependent and every extra run is another chance to hit
one. A failure that vanishes when you rerun is still a real finding — treat the
first failure as the signal, not as flakiness. Typical causes are Rule 2 (a
singleton memo), Rule 1 (an unsafe cache) and Rule 4 (a global counter).

One honest caveat about multi-core testing: proofs found with different worker
counts may legitimately *differ* (goal scheduling changes which of two equally
cheap rules is applied first), so these tests check "closes, reloads, size in a
sane band" — not tree equality. Tree equality is only required between two
single-core runs, which is exactly what `ScDeterminismTest` does.

## 4. Opting out: restricting a feature to the single-core prover

The four rules assume you *want* your feature to run multi-core. Sometimes you do
not: the feature inherently couples several goals (like the merge rule), or making
it thread-safe is more work than it is worth right now. Both are legitimate — a
feature that is only correct single-core must simply *say so*, and it will keep
working exactly as before. What is not legitimate is staying silent and racing.

KeY has four opt-out mechanisms, from coarse to fine. Use the coarsest one that
fits; each is shown with the real code that uses it today.

### 4.1 Profile level: do not opt in

A *profile* bundles a calculus and strategy (the standard one is `JavaProfile`).
Whether automode for a profile may run multi-core is a capability of the profile:

```java
// Profile (interface) — the default is the safe answer:
default boolean supportsParallelAutomode() {
    return false;
}

// JavaProfile — the standard profile has been vetted and opts in:
@Override
public boolean supportsParallelAutomode() {
    return true;
}
```

The default is deliberately `false`: **a new profile is single-core until someone
verifies its rules and strategy and opts in**. If you build a specialised profile,
you have to do precisely nothing — even a user who enabled the multi-core prover
gets correct single-core proving for your profile. This is the strongest and
cheapest opt-out.

### 4.2 Macro level: `allowParallel()`

A *proof macro* drives automode with its own strategy. Some macro strategies keep
state that spans **all** goals — a "stop after 1000 steps in total" counter, or a
"one goal hit the breakpoint, everyone stop" flag. Per-goal workers would update
that state concurrently and the macro's meaning would change. Such a macro
declares itself single-core with one override:

```java
// OneStepProofMacro — counts steps across all goals, so goals must
// be processed one after the other:
@Override
protected boolean allowParallel() {
    return false;
}
```

`StrategyProofMacro` routes every macro through a selection seam
(`AutoProvers.create(...)`) that picks the multi-core prover only when the prover
is enabled, the profile supports it (4.1), **and** the macro allows it. Current
single-core macros: `OneStepProofMacro`, `AutoMacro` (breakpoint flag),
`FinishSymbolicExecutionUntilMergePointMacro` (shared merge-point bookkeeping).

### 4.3 Rule level: refuse applicability during a multi-core run

A built-in rule that reaches beyond its own goal cannot run concurrently. The
merge rule is the archetype — it *links several open goals into one*, so it would
have to lock goals that other workers own. It disables itself while a multi-core
run is active:

```java
// MergeRule.isApplicable — merging links several goals and would need
// to lock all of them; not safe under goal-level concurrency:
if (ParallelProver.isMultiThreadedRunActive()) {
    return false;
}
```

`ParallelProver.isMultiThreadedRunActive()` answers "is a multi-worker proof run
happening right now?" — it is the runtime query behind the fine-grained opt-outs.
Single-core proving (and any single-core macro from 4.2) is unaffected: the query
answers `false` there.

### 4.4 Strategy level: keep the search from waiting for a disabled rule

Mechanism 4.3 has a trap: disabling a rule does not stop the *strategy* from
wanting it. If the strategy still ranks the disabled rule as the best next step,
the goal waits forever for a rule that never fires and the proof stalls. Whoever
disables a rule must therefore also teach the strategy what to do instead.

The merge rule's companion fix, from `SymExStrategy` (rule set `merge_point`):
when merge points are configured to "merge" but a multi-core run is active, the
strategy silently treats them like "skip", so symbolic execution passes the merge
point instead of queueing a merge that can never happen:

```java
return ParallelProver.isMultiThreadedRunActive()
        ? NumberRuleAppCost.create(-5000)                       // pass the merge point
        : DeleteMergePointRuleFeature.INSTANCE.computeCost(...); // normal single-core cost
```

A note of caution on 4.3/4.4: every `isMultiThreadedRunActive()` call is a fork in
behaviour — the code now does two different things, and tests must cover both.
Prefer the declarative switches (4.1, 4.2) whenever they fit; reach for the
runtime query only when a single rule or cost function is the problem. (KeY's own
history backs this up: two such case distinctions — in `Goal` and in `Services` —
were later removed again by making the shared path work for both provers.)

Side proofs need no opt-out at all: they always run single-core by design.

### 4.5 Adding an exception to `SharedStateLintTest`

If your single-core-only feature keeps a static field that the linter flags — or
any field the linter flags is genuinely safe — allowlist it instead of
restructuring:

1. Run the linter locally:
   `./gradlew :key.core:test --tests '*SharedStateLintTest*'`.
   The failure names the field, e.g.
   `de.uka.ilkd.key.mypackage.MyClass#myTable`.
2. Add one line to
   `key.core/src/test/resources/de/uka/ilkd/key/prover/mt/shared-state-allowlist.txt`:
   the field id, whitespace, then `#` and a justification saying **why no worker
   thread ever writes the field during proof search**:

   ```
   de.uka.ilkd.key.mypackage.MyClass#myTable   # filled once in the static initializer, read-only afterwards
   ```

   For a feature opted out via 4.2/4.3 the honest justification names the guard,
   e.g. `# only written by MyMacro, which overrides allowParallel() to false`.
3. Re-run the test. Note it also fails on *stale* entries, so the line must be
   removed again when the field disappears — the allowlist cannot silently rot.

The justification is a review contract, not a formality: "it compiles" is not a
reason; "written only during single-threaded problem loading" is. When in doubt,
fix the field with the Rule-1 table instead of allowlisting it.

## 5. Checklist before opening a prover pull request

* No new `static` mutable field on the proving path — or it is one of the four
  sanctioned patterns from the Rule-1 table.
* No mutable instance field on a rule/feature/instruction singleton; per-call
  state lives in parameters, locals, or a `ThreadLocal`.
* No `HashMap`/`HashSet` iteration (and no identity-hash ordering) anywhere the
  result can reach rule selection.
* Fresh names derived from goal-local namespaces.
* `./gradlew :key.core:testMt2w` is green locally.
