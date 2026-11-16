---
title: "Migrating from KeY 2 to KeY 3"
weight: 95
date: 2026-07-15
date_label: "July 2026"
valid_for: "KeY-3.0.0"
updated: "November 2026"
approved: "weigl, 2026"
---

{{< callout type="info" title="Migrated from the KeY wiki" >}}
This guide was originally published as the
[Migration Guide: KeY‐2.13.0 to KeY‐3.0.0](https://github.com/KeYProject/key/wiki/Migration-Guide:-KeY%E2%80%902.13.0-to--KeY%E2%80%903.0.0)
in the KeY wiki.
{{< /callout >}}

This guide describes the divergences in syntax and behavior between KeY 3.0.0
and its predecessor. While we do our best to avoid breaking changes, some were
inevitable. This note should help you, as a KeY user, to carry your existing
proofs over to major version 3.

In the core, we migrated the whole Java processing from RecodeR (✝ 2012) to the
[key-javaparser fork](https://github.com/wadoon/key-javaparser) of the
[JavaParser project](https://github.com/javaparser/javaparser).

## Naming of contracts in proof obligations

You may encounter exceptions of the kind:

```text
java.lang.IllegalStateException: Contract not found: BinarySearch[BinarySearch::$search([I,int)].JML normal_behavior operation contract.0
```

The renaming of fields and methods has also affected contract naming. There are
two main patterns:

1. Synthetic variables, like `<created>` or `<inv>`, have been renamed. They now
   start with a dollar sign `$` and no longer use angle brackets. This prepares
   the use of polymorphic sorts and generics within JavaDL.

   ```diff-json
    \proofObligation {
   -       "contract": "simple_evoting.Server[java.lang.Object::<inv>()].JML accessible clause.0",
   +       "contract": "simple_evoting.Server[java.lang.Object::$inv()].JML accessible clause.0",
            "class": "de.uka.ilkd.key.proof.init.DependencyContractPO",
     }
   ```

2. Contract names for user-declared methods no longer have a leading `$` sign,
   as that symbol is now reserved for synthetic entities like invariants.

   ```diff-json
    \proofObligation {
   -       "contract": "passwordfile.SecurePasswordFile[passwordfile.SecurePasswordFile::$userIndex()].JML accessible clause.0",
   +       "contract": "passwordfile.SecurePasswordFile[passwordfile.SecurePasswordFile::userIndex()].JML accessible clause.0",
            "class": "de.uka.ilkd.key.proof.init.DependencyContractPO",
     }
   ```

**Suggestion:** Add `$` as a prefix to synthetic field names while removing the
angle brackets. For method names, remove the leading `$` sign.

## Naming of fields

| Kind | Description | KeY 2.x syntax | KeY 3.0 syntax |
| :--- | :---------- | :------------- | :------------- |
| Regular field | Field `f` declared in `package.A` | `package.A::$f` | `package.A::#f` |
| Implicit field | Field `created` in `java.lang.Object` | `java.lang.Object::<created>` | `java.lang.Object::$created` |
| Instance invariant | – | `java.lang.Object::<inv>` | `java.lang.Object::$inv` |
| Static invariant | – | `java.lang.Object::<$inv>` | `java.lang.Object::$staticInv` |
| Free instance invariant | – | `java.lang.Object::<inv_free>` | `java.lang.Object::$inv_free` |
| Free static invariant | – | `java.lang.Object::<$inv_free>` | `java.lang.Object::$staticInv_free` |

## Parametric sorts, predicates, and functions

KeY 3.0 supports parametric sorts, datatypes, predicates, and functions. This
replaces the previous solution of sort-dependent functions with a more general
approach. As a consequence, the syntax for functions like `cast`, `select`, and
`instance` has changed. The table below lists some examples in the old and new
syntax.

| Kind | KeY 2.x syntax | KeY 3.0 syntax |
| :--- | :------------- | :------------- |
| Select | `boolean::select(h, o, f)` | `select<[boolean]>(h, o, f)` |
| Instance of | `T::instance(o)` | `instance<[T]>(o)` |
| Cast | `int::cast(t)` | `cast<[int]>(t)` |

In general, wherever you had a function containing a `T::`, replace it with a
generic parameter `<[T]>`.

## Saved proofs

Saved proofs contain every rule application together with the instantiation of
their schema variables. If instantiations were not found by matching (find or
assumes) but were provided externally by a user or the proof search strategies,
the instantiation is given as a parseable string. That string may still contain
the (implicit) field and method naming conventions from KeY 2.x, or the no longer
supported sort-dependent function syntax. In this case, open the `.proof` file
and edit the corresponding rule instantiation to use the new naming scheme.

```diff-lisp    
- (rule "allLeft" (formula "22") (inst "t=int::select(heap, IntOpt::final(null, IntOpt::$NONE), IntOpt::$value)"))
+ (rule "allLeft" (formula "22") (inst "t=select<[int]>(heap, IntOpt::final(null, IntOpt::#NONE), IntOpt::#value)"))
```

A good first attempt is `s/::$/::#/g`.

## More restrictive JML

With the new Java parser framework, we implemented a new JML parsing strategy
with stricter requirements on where JML annotations may be placed. A major
challenge of JML parsing is assigning JML entities to the appropriate Java AST
nodes. The old framework misused comments for tracking JML annotations. In the
new framework, we decided on a more robust approach, which led to some
restrictions.

First of all, JML annotations are a known token type in our Java parser. This
means that `/*@ ... */` is no longer a comment; it is recognized as a `JML_DOC`
token. Such tokens are expected at certain positions:

1. At the top level of compilation units, where types are declared.
2. Inside classes, where fields, methods, etc. are declared.
3. Wherever a statement could appear.
4. In modifier lists, for example on classes, local declarations, and methods.

This forbids JML annotations in certain positions, but it also leads to more
deterministic behavior and simpler node attachment. The position of a JML
annotation is now tracked by the grammar.

The following differences can be observed.

### Modifiers

The following previously allowed notation is not allowed anymore:

```jml
public void /*@ helper */ m() { ... }
```

Modifiers such as `helper` and `pure` now need to be written before the return
type:

```jml
public /*@ helper */ void m() { ... }
```

### JML annotations are statements

A chunk of JML annotations is a statement and is treated as such. The following
Java/JML code is invalid:

```jml
if (cond)
  /*@ assert cond; */
  print("cond is true");
else
  print("cond is false");
```

Because `/*@ assert cond; */` is treated as a statement, the following
print-statement is not considered part of the `then` block, and the `else` is
left dangling. The parser sees the following:

```jml
if (cond) { /*@ assert cond; */ }
print("cond is true");
else
  print("cond is false");
```

Use braces to make the structure clear:

```jml
if (cond) { /*@ assert cond; */ print("cond is true"); }
else      { print("cond is false"); }
```

This situation also arises with loops and labeled statements:

```jml
k: /*@ loop_invariant true; */
   while (true) ;
```

The invariant annotation is the inner statement of the labeled statement, so the
label is not assigned to the loop. Note that simply putting braces around the
labeled statement would change its semantics. The solution is to place the loop
annotation before the label:

```jml
/*@ loop_invariant true; */
k: while (true) ;
```

### Known issue: class modifiers

We are aware of the following parser bug: class modifiers (`pure`,
`strictly_pure`, `nullable_by_default`) on package-private classes lead to
silent abortion of parsing. For example, the `pure` modifier in

```jml
/*@ pure @*/ class A { ... }
```

causes this effect. As a workaround, do not use class-level JML modifiers on
package-private classes. Instead, either attach the modifier locally to the
relevant methods or fields, or, if possible, use a Java modifier on the class
such as `public`, `protected`, `private`, or `final`. The following works:

```jml
public /*@ pure @*/ class A { ... }
```
