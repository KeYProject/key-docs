# Taclet Matching

*2026: class names and the described design checked against the current
sources (`key.ncore.matcher` and `de.uka.ilkd.key.rule.match.vm`).*

A taclet is KeY's format for proof rules. Its `\find` pattern describes
the term shape the rule applies to, using **schema variables** as
placeholders (for terms, formulas, program parts, and so on).
**Matching** decides whether a pattern fits a concrete term and, if it
does, what each schema variable stands for. A successful match yields
`MatchConditions`, the collected (partial) instantiations of the schema
variables; a failed match yields `null`. Matching runs for every rule
application candidate during proof search, millions of times in a larger
proof, which motivates the design below. Where matching sits in the
overall proof search is described in the
[rule application pipeline](RuleApplicationPipeline/).

## One description: the match plan

When the rule base is loaded, each `\find` pattern (and each `\assumes`
formula) is described once as a **match plan**: a small tree of plan
nodes that mirrors the pattern, with one node kind per construct (a
schema variable, an ordinary operator with its subterms, a modality with
its program, an update, and so on). The plan is the single source of
truth for how the pattern is matched: both matcher back-ends described
below are derived from it, so they agree by construction and there is no
second, hand-written matcher to keep in sync.

A pattern built from a construct the framework cannot describe is
rejected when the rule is loaded, with an error naming the construct. It
can therefore never be silently mis-matched during proof search.

The framework is split along language boundaries. The plan skeleton
lives in the module `key.ncore.matcher` and is language independent: it
owns the walk over patterns, the shared matching steps (for example the
child walks and the greedy run of a list schema variable), and the
derivation of both back-ends. A language front-end contributes what is
genuinely its own; for KeY that is `de.uka.ilkd.key.rule.match.vm` with
the match instructions for KeY's schema-variable kinds, the treatment of
modalities, updates, parametric functions and term labels, the binding
of bound variables, and the entry into the Java program of a modality.
Other provers built on the same core can reuse the framework by writing
their own front-end.

## The compiled matcher (the default)

Every plan node compiles into a small matching function, and the
functions nest exactly like the pattern. Matching a candidate term means
calling the root function: it checks its own construct and hands the
subterms to the functions of the subpatterns. Results are threaded
through immutable `MatchConditions`, so a matcher can be shared freely,
also between the worker threads of the multi-core prover. There is no
cursor and no instruction list; the pattern's structure *is* the control
flow.

**Example.** Take the taclet `eqSymm`
(`classicalLogic/firstOrderRules.key`) with pattern
`\find(commEqLeft = commEqRight)`; the two schema variables are
abbreviated as `t1`, `t2`. The plan is an operator node for `=` with two
schema-variable children, and it compiles to this nesting (schematic):

```text
match(candidate) =
    candidate's operator is '='?        otherwise fail
    match t1 against candidate's first subterm
    match t2 against candidate's second subterm

match ti against s =
    record s as ti's instantiation,
    or, if ti is already instantiated, check that it equals s
```

Against `f(c) = g(d)` the root check succeeds, `t1` records `f(c)`,
`t2` records `g(d)`, and the result is
`MatchConditions { t1 ↦ f(c), t2 ↦ g(d) }`. Against `p & q` the root
check fails and the match returns `null`. The "record or check" step is
why a schema variable occurring twice in a pattern (as in
`\find(b & b)`) only matches if both occurrences are instantiated
identically (compared modulo renaming of bound variables).

**Programs.** The Java program inside a modality is matched by the same
idea, applied to the program tree: a pattern element matches a candidate
element of the same kind, and their children are matched recursively. A
program schema variable consumes one element; a **list** schema variable
(such as `#slist`) consumes a maximal run of consecutive statements; the
`.. ...` context pattern of symbolic-execution taclets locates the
active statements inside the candidate's nested block structure and
records the surrounding context. The compiled matcher reads only the
tree structure of pattern and candidate.

## The interpreter

The interpreter is the second back-end, derived from the same plan: each
plan node emits instructions into a flat program, and a small virtual
machine executes that program while a depth-first cursor walks the
candidate term (the children of a term in this traversal are its
operator followed by its subterms). Check instructions inspect the node
under the cursor and extend the running `MatchConditions`; goto
instructions only move the cursor. The first failing instruction aborts
the run with `null`; no backtracking is needed because pattern and
candidate are traversed in lockstep.

For `eqSymm`, the plan emits this program:

| # | Instruction | Effect |
|---|---|---|
| 0 | `CheckNodeKind(Term)` | current node must be a term |
| 1 | `GotoNext` | descend to the operator node |
| 2 | `MatchIdentity(=)` | operator must be `equals` |
| 3 | `GotoNext` | move to the first subterm |
| 4 | `MatchSV(t1)` | instantiate `t1` with the subterm |
| 5 | `GotoNextSibling` | skip over `t1`'s subtree |
| 6 | `MatchSV(t2)` | instantiate `t2` with the subterm |
| 7 | `GotoNextSibling` | done |

Running it against `f(c) = g(d)` performs exactly the checks of the
compiled example above, stepping the cursor between them; against
`p & q` it fails at instruction 2. One difference remains on the program
side: the interpreter matches the Java program of a modality with a
single instruction that compares the program trees of pattern and
candidate directly.

The interpreter is selected by the system property
`key.matcher.interpreter=true`, which switches all matching (find and
assumes) at once; the setting is read when the rule base is loaded. Its
role is that of an independent reference implementation, useful for
comparing the two back-ends and for debugging.

## Finding your way around the code

The sections above describe the design; this one names the classes, so
that a change (a new operator, a changed program construct, a new
schema-variable kind) can be placed quickly.

### The framework module (`key.ncore.matcher`)

Package `org.key_project.prover.rules.matcher.compiler` holds the plans
and the extension interfaces:

| Class | Role |
|---|---|
| `MatchPlan`, `OperatorPlan`, `SchemaVarPlan` | plan nodes for the term part of a pattern; every node has `emit(...)` (interpreter instructions) and `compile()` (compiled matcher) |
| `MatchHead`, `GenericOperatorHead`, `ModalityHead` | the operator-specific part of an `OperatorPlan`: `GenericOperatorHead` checks operator identity, `ModalityHead` also matches the modal kind and enters the program |
| `MatchPlanBuilder` | the abstract dispatch skeleton: walks a term pattern and composes the nodes; subclassed by a front-end |
| `ProgramMatchPlan`, `ProgramLeafPlan`, `ProgramStructuralPlan`, `ProgramListSVPlan` | plan nodes for the program part; `ProgramStructuralPlan` is the generic structural match (same class, children matched recursively, optionally an extra guard check) |
| `ProgramChildSequence`, `ProgramChildCursor` | the shared child walks, including the greedy run of a list schema variable |
| `BinderMatcher`, `ProgramMatchHook`, `ListSVMatcher` | the three interfaces a front-end implements: binding bound variables, entering a modality's program, and judging list-schema-variable runs |

Package `org.key_project.prover.rules.matcher.vm` holds the interpreter:
`VMProgramInterpreter` (the machine), `VMInstruction`/`MatchInstruction`
(the instruction interfaces) and the generic instructions
(`CheckNodeKindInstruction`, `MatchIdentityInstruction`,
`MatchByEqualsInstruction`, `MatchProgramElementInstruction`, the two
goto instructions). `MatchProgram` in the same package is the interface
of a compiled matcher.

### KeY's front-end (`de.uka.ilkd.key.rule.match.vm`)

| Class | Role |
|---|---|
| `VMTacletMatcher` | the matcher of one taclet: builds the find and assumes matchers through the plan framework, handles update prefixes and variable conditions |
| `JavaMatchPlanBuilder` | the term dispatch: `headFor(pattern)` returns the head for an operator (elementary update, parametric function instance, modality, or the generic head); also supplies the schema-variable instructions, the binder and the term-label wrap |
| `ElementaryUpdateHead`, `ParametricFunctionHead` | the Java-DL-specific term heads |
| `JavaProgramMatchPlanBuilder` | the program dispatch: `buildProgramPlan(element)` returns the plan for one program construct; its private `FieldReferencePlan` and `ContextBlockPlan` cover schematic field references and the `.. ...` context pattern |
| `JavaBinderMatcher`, `JavaListSVMatcher`, `JavaProgramMatchHook` | the implementations of the three framework interfaces |
| `instructions/*` | the Java-DL match instructions; `JavaDLMatchVMInstructionSet` is the factory, `MatchSchemaVariableInstruction` the base of the schema-variable instructions (it routes a candidate to its term or program overload) |

### Changing how a construct is matched

The dispatches are the two places where matching behaviour is decided;
everything downstream follows from them.

**A term operator.** `JavaMatchPlanBuilder.headFor` matches ordinary
operators by object identity (`GenericOperatorHead`). An operator that
needs more than identity gets its own `MatchHead` with two methods:
`emit` appends its interpreter instructions, `compileHeadCheck` returns
its compiled check. `ElementaryUpdateHead` is a small example to start
from.

**A program construct.** `JavaProgramMatchPlanBuilder.buildProgramPlan`
decides per element kind. The default is the generic structural match:
it applies to every element class that does not define its own matching
behaviour (`isGenericMatch`), and it compares the concrete class and
then the children, one to one. Two refinements are available where that
is not enough:

- a **guard**: `structuralPlan(element, guard)` takes an extra check
  that runs after the class comparison. The dispatch uses it where two
  elements of the same class are only equal if some attribute also
  agrees (for example the number of array dimensions of a type
  reference). If a change to the program AST makes one class represent
  several constructs, distinguished only by an attribute such as a kind
  field, a guard comparing that attribute is the intended extension
  point;
- an **own plan node**, when the construct's matching is genuinely
  structural logic of its own (`FieldReferencePlan` and
  `ContextBlockPlan` are the examples).

A pattern the dispatch does not describe fails at load time with "the
match-plan framework has no head for this find pattern"; that error is
the signal that one of the two dispatches needs a new case.

### Checking a change

`TestMatchTaclet` (with its rule file `testRuleMatch.txt`) is the unit
test of the matcher; run it on both back-ends, once normally and once
with `-Dkey.matcher.interpreter=true`. The broad net is the
`RunAllProofs` regression suite, which loads the full rule base (and
thereby exercises the fail-at-load contract) and replays proofs over
every construct in shipped taclets.
