---
title: "Treatment of Final Fields"
weight: 95
---

{{< callout type="info" title="In short" >}}
Since KeY 3.0, `final` fields are treated as **immutable**. They are read
through their own heap-independent function instead of the heap. This is the
default (`finalFields: immutable`). Select `finalFields: onHeap` to restore the
old behaviour if your constructor code does not meet the restrictions below,
or if you rely on liberal constructor inlining.
{{< /callout >}}

## Why final fields are special

A Java `final` field can be assigned at most once:

- in its declaration (including instance and static initialisers),
- in every constructor of the declaring class (for an instance field), or
- in a static initialiser (for a `static final` field).

After a correctly constructed object is published, every observer sees the
same value. The Java compiler relies on this for constant folding and for safe
publication, and a verifier can exploit the same property.

Older KeY versions stored final fields on the heap like ordinary fields.
Every heap update then had to be shown not to touch them, and loop invariants
often had to repeat that a final field keeps its value. Because a `final`
field cannot change after construction, that reasoning is unnecessary.

The gain grows with the number of final fields and heap updates in a proof.
KeY's own example suite exercises the treatment, for example in the
`Records` examples, which record `finalFields: immutable` in their proof
settings.

## What changed in KeY

KeY now reads a final field through a function that has no heap argument:

```
select<G>(heap, o, f)   // ordinary field read: heap, object, field
final<G>(o, f)          // final field read: object, field
final<G>(null, C::f)    // static final field read: no receiver object
```

`G` is the sort of the field value (for example `int`). The encoding is used
for field accesses in Java code and in JML expressions alike.

The value read through `final` is tied to what the constructor writes. When
KeY creates a constructor's proof obligation, it adds, for each final field
`f`, the premise

```
final(self, f) = select(heap, self, f)   // both at sort any
```

before the constructor's postcondition. This makes the value written into the
heap during construction the value later read through `final`.

For proofs this means:

- Heap-modifying code cannot change final fields, so their values stay stable
  across loops and method calls without extra framing.
- Loop invariants generally no longer need clauses such as
  `this.f == \old(this.f)` for final fields.
- Proofs can be smaller because final-field updates disappear from the heap.

This is a **breaking change** for proofs and taclets that spell out
`select(heap, o, f)` for a final field. The `finalFields: onHeap` option keeps
the old encoding.

## Choosing the setting

The taclet option `finalFields` has two values:

| Value | Final fields are … | Constructor check | When to use |
| :---- | :----------------- | :---------------- | :---------- |
| `immutable` (default) | stored outside the heap and read via `final<G>(o, f)` | enforced | Default. Your constructors follow the rules below and you do not rely on liberal constructor inlining. |
| `onHeap` | ordinary heap locations, read via `select<G>(heap, o, f)` | skipped | Your constructor code is rejected by the check, you need liberal constructor inlining, or you replay proofs written for older KeY versions. |

Both settings are sound. `immutable` is the optimised treatment and may be
incomplete when constructor bodies are inlined; `onHeap` is the original
heap-based semantics and is always applicable, but gives up the optimisation.

## Changing the option

1. Open **Options → Show Settings** and select **Taclet Options**.
2. Set `finalFields` to `immutable` or `onHeap`.
3. Reload the problem. Taclet options are read when the proof obligation is
   created, so an already loaded proof keeps its setting.

**Proof → Show Active Taclet Options** shows the options of the current proof.

## What KeY checks in constructors

The immutable treatment is only sound if a constructor cannot observe a final
field before it has been written. KeY checks every constructor when it creates
the constructor's proof obligation and aborts with a
`FinalViolationException` (which includes the source location) if any of these
rules is violated:

- No final field of `this` may be read — neither directly in the constructor
  nor in a method called on `this`. The check is conservative: it also rejects
  reads *after* the field has been assigned.
- `this` must not be passed as an argument to a method or constructor.
- `this` must not be stored in a field or a local variable.
- A method called on `this` must be effectively final: declared `final` or
  `private`, or declared in a `final` class.
- The bodies of methods called on `this` are checked transitively for the same
  rules.
- A non-static inner class must not be instantiated in a constructor, because
  the implicit reference to the outer instance leaks `this`.

Secondary constructors that delegate with `this(...)` are exempt from the
check; the constructor they delegate to is checked instead.

## Example

```java
public class Point {
    public final int x;
    public final int y;

    /*@ public normal_behavior
      @   ensures this.x == x && this.y == y;
      @*/
    public Point(int x, int y) {
        this.x = x;
        this.y = y;
    }

    /*@ public normal_behavior
      @   ensures \result == x + y;
      @*/
    public int sum() {
        return x + y;
    }
}
```

The constructor writes both final fields exactly once and never reads them,
so KeY accepts it under the default `finalFields: immutable`. The contract of
`sum` only needs the values of `x` and `y`.

The following constructor is rejected:

```java
public class Bad {
    public final int value;

    //@ ensures this.value == v;
    public Bad(int v) {
        int before = value; // rejected: reads `value` before it is initialised
        this.value = v;
    }
}
```

KeY reports a message such as `Final field value is read.` together with the
source position.
Remove the read rather than merely moving it after the assignment — the check
does not track the order of reads and writes:

```java
public Bad(int v) {
    this.value = v;
}
```

If the code cannot be changed, select `finalFields: onHeap`; the old
heap-based treatment accepts it.

## Static and ghost fields

Static final fields are covered as well. They have no receiver object, so they
are read as `final<G>(null, C::f)`, and the pretty printer shows `C.f`.
Whether the initialiser of a `static final` field is executed depends on the
`initialisation` taclet option. KeY's default,
`initialisation: disableStaticInitialisation`, does not execute static
initialisers; enable it if your proof depends on the initialiser code.

Ghost fields declared `final` are heap locations and receive the same
treatment as Java fields. `\model` fields are not heap locations and are not
covered by the immutable treatment.

## Interaction with inlining

The immutable treatment relies on the constructor's postcondition to connect
`final` with the heap value written during construction. If a constructor body
is expanded (inlined) instead of being used through its contract, that
connection is not established, and a proof may fail even though the program is
correct. This is an incompleteness, not an unsoundness.

The default `methodExpansion: modularOnly` inlines far fewer methods than
liberal inlining. If you select `methodExpansion: noRestriction`, consider also
selecting `finalFields: onHeap` to avoid proofs that fail only because a
constructor was expanded.

## Inspecting the encoding

With **View → Use Pretty Syntax** enabled (the default), a final field read and
an ordinary field read are printed identically as `o.f`; the pretty printer
deliberately hides the `final` function. Uncheck **Use Pretty Syntax** to see
the raw term:

```
select<int>(heap, o, C::f)   // ordinary field
final<int>(o, C::f)          // final field
```

`final` has two arguments (object and field), whereas `select` has three (heap,
object and field). Static final fields use `null` as the receiver:
`final<int>(null, C::f)`.

## Known limitations

- The constructor check is conservative: a primary constructor may not read any
  final field, even after assigning it. Relaxing this needs order-sensitive
  bookkeeping that KeY does not yet implement.
- A method called on `this` must be effectively final. An overridable method is
  rejected even if no subclass actually overrides it.
- A non-static inner class cannot be instantiated in a constructor, because the
  implicit reference to the outer instance leaks `this`.
- `\model` fields are not covered; they are not heap locations.
- Inlining a constructor can make the immutable treatment incomplete (see
  above).

If the check is too strict for your code, `finalFields: onHeap` restores the
previous behaviour.

## Further reading

- [KeY PR #3495 — Improved treatment of final fields](https://github.com/KeYProject/key/pull/3495)
- [KeY 3.0 release notes](../release-notes/)
- [Java Coverage](../features/java-coverage/) for the current feature matrix

No dedicated journal article on this feature had appeared when this page was
written; the pull request and the release notes are the primary references.
