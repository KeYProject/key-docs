---
hide:
  - toc
approved: RB  
---

# Java Coverage

!!! warning "Under construction"

    This page is still under construction; its content may still change.

KeY verifies **sequential Java**. This page summarises which Java language
features the prover currently understands, when each feature entered the Java
language, how it evolved afterwards, and where KeY's support is complete,
partial, or missing. Support for modern Java keeps evolving, so this is a moving
target; the table reflects the status as of **KeY 3.0**.

## Legend

| Symbol | Meaning |
|:---:|---|
| :material-check-bold:{ style="color:#2e9e44" title="Fully supported" } | **Fully supported**: parsed, converted, and backed by proof rules |
| ( :material-check-bold:{ style="color:#d19a00" title="Partially supported" } ) | **Partially supported**: accepted, but with the limitation noted in *Comments* |
| :material-minus:{ style="color:#9aa0a6" title="Not supported" } | **Not supported**: rejected by the front-end, or accepted but not soundly modelled (see *Comments*) |

## Runtime and JVM features

KeY verifies sequential Java without a model of the JVM runtime, so these
concurrency, memory-management, class-loading and reflection capabilities are
not supported (KeY may still *load* code that calls their APIs, but does not
reason about them).

<div class="j-coverage" markdown>

| Feature | Introduced<br>(JEP/JSR) | Later changes<br>(JEP · JLS) | KeY | Comments |
|---|---|---|:---:|---|
| Multithreading | Java 1.0 (1996) | [§17](https://docs.oracle.com/javase/specs/jls/se21/html/jls-17.html){target="_blank" rel="noopener"} (threads & locks) | :material-minus:{ style="color:#9aa0a6" } | Not supported; KeY reasons about sequential Java only. |
| Garbage collection | Java 1.0 (1996) | runtime / JVM feature | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Dynamic class loading | Java 1.0 (1996) | [§12.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-12.html#jls-12.2){target="_blank" rel="noopener"} (class loading) | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Reflection | Java 1.1 (1997) | library (`java.lang.reflect`) | :material-minus:{ style="color:#9aa0a6" } | Not supported. |

</div>

## Java language feature support

The *Introduced* and *Later changes* columns link the defining
**JEP** (or, for Java 5 to 8 features that predate the JEP process, the **JSR**)
together with the relevant **JLS** section.

<div class="j-coverage" markdown>

| Feature | Introduced<br>(JEP/JSR) | Later changes<br>(JEP · JLS) | KeY | Comments |
|---|---|---|:---:|---|
| Classes, interfaces, inheritance, fields, methods | Java 1.0 (1996) | [§8](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html){target="_blank" rel="noopener"}, [§9](https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html){target="_blank" rel="noopener"} (stable core) | :material-check-bold:{ style="color:#2e9e44" } | Fully supported. KeY's core object model. Newer features for interfaces (private/default methods) have their own entry. |
| Statements & control flow (`if`, `while`, `do`, `for`, labelled `break`/`continue`) | Java 1.0 (1996) | [§14](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Fully supported. |
| Arrays, incl. multi-dimensional | Java 1.0 (1996) | [§10](https://docs.oracle.com/javase/specs/jls/se21/html/jls-10.html){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Creation, access, `ArrayStoreException` and out-of-bounds all modelled. |
| Exceptions (`try`/`catch`/`finally`, `throw`) | Java 1.0 (1996) | [§11.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-11.html#jls-11.3){target="_blank" rel="noopener"}, [§14.20](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.20){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Fully supported. |
| Nested, member & anonymous classes | Java 1.1 (1997) | [§8.1.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html#jls-8.1.3){target="_blank" rel="noopener"}, [§15.9.5](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.9.5){target="_blank" rel="noopener"} | :material-check-bold:{ style="color:#2e9e44" } | Static-nested, inner and anonymous classes all load. |
| Local classes (declared in a method body) | Java 1.1 (1997) | [§14.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.3){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Not supported; declare it as a nested or member class instead. |
| `switch` statement | Java 1.0 (1996) | selector types widened: `enum` ([JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"}, Java 5), `String` ([JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"}, Java 7), both under [§14.11](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.11){target="_blank" rel="noopener"}; arrow labels ([JEP 361](https://openjdk.org/jeps/361){target="_blank" rel="noopener"}, Java 14) & patterns ([JEP 441](https://openjdk.org/jeps/441){target="_blank" rel="noopener"}, Java 21); see below | :material-check-bold:{ style="color:#2e9e44" } | Lowered to an `if`-cascade. Integer selectors work; an `enum` selector needs *qualified* case labels (`case E.C:`); the standard unqualified `case C:` fails to resolve (see *Strings in `switch`* for `String`). |
| `instanceof` type test | Java 1.0 (1996) | pattern binding added Java 16 ([JEP 394](https://openjdk.org/jeps/394){target="_blank" rel="noopener"}, see below) | :material-check-bold:{ style="color:#2e9e44" } | Plain type test only; the pattern-binding form is separate. |
| Floating point (`float`, `double`) | Java 1.0 (1996) | always strict semantics restored in Java 17 ([JEP 306](https://openjdk.org/jeps/306){target="_blank" rel="noopener"}, [§15.4](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.4){target="_blank" rel="noopener"}) | :material-check-bold:{ style="color:#2e9e44" } | Supported. Requires installed SMT solver. |
| Generics | Java 5 (2004), [JSR 14](https://jcp.org/en/jsr/detail?id=14){target="_blank" rel="noopener"} | diamond ([JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"}, Java 7, [§15.9.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.9.1){target="_blank" rel="noopener"}), improved inference ([JSR 335](https://jcp.org/en/jsr/detail?id=335){target="_blank" rel="noopener"}, Java 8, [§18](https://docs.oracle.com/javase/specs/jls/se21/html/jls-18.html){target="_blank" rel="noopener"}), `var` lambda params ([JEP 323](https://openjdk.org/jeps/323){target="_blank" rel="noopener"}, Java 11) | :material-minus:{ style="color:#9aa0a6" } | Not supported in any form: `<T>`, `<T extends S>`, wildcards, generic methods and diamond `<>`. See *[Programs with generics](../RemoveGenerics.md)*. |
| Enhanced `for` (for-each) | Java 5 (2004), [JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"} | [§14.14.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.14.2){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Rewritten to an indexed / iterator loop. |
| Autoboxing / unboxing | Java 5 (2004), [JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"} | [§5.1.7](https://docs.oracle.com/javase/specs/jls/se21/html/jls-5.html#jls-5.1.7){target="_blank" rel="noopener"}, [§5.1.8](https://docs.oracle.com/javase/specs/jls/se21/html/jls-5.html#jls-5.1.8){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Parses, but boxing/unboxing is not modelled (method resolution assumes its absence), so reasoning would be unsound. |
| Enums | Java 5 (2004), [JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"} | [§8.9](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html#jls-8.9){target="_blank" rel="noopener"} (stable) | ( :material-check-bold:{ style="color:#d19a00" } ) | Desugared to classes; declarations (including constant-specific bodies) load. Calculus support only partial. See also the `switch` row for the enum-label caveat. |
| Varargs | Java 5 (2004), [JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"} | [§8.4.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html#jls-8.4.1){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Desugared to an array parameter. |
| Static imports | Java 5 (2004), [JSR 201](https://jcp.org/en/jsr/detail?id=201){target="_blank" rel="noopener"} | [§7.5.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-7.html#jls-7.5.3){target="_blank" rel="noopener"}, [§7.5.4](https://docs.oracle.com/javase/specs/jls/se21/html/jls-7.html#jls-7.5.4){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | `import static` is not supported. |
| Annotations | Java 5 (2004), [JSR 175](https://jcp.org/en/jsr/detail?id=175){target="_blank" rel="noopener"} | type annotations ([JEP 104](https://openjdk.org/jeps/104){target="_blank" rel="noopener"}, Java 8, [§9.7.4](https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html#jls-9.7.4){target="_blank" rel="noopener"}), repeating annotations (Java 8, [§9.6.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html#jls-9.6.3){target="_blank" rel="noopener"}) | ( :material-check-bold:{ style="color:#d19a00" } ) | Parsed and ignored on declarations; declaring `@interface` types and type/repeating annotations are not supported. JML lives in comments, not annotations. |
| Binary literals & underscores in numeric literals | Java 7 (2011), [JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"} | [§3.10.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-3.html#jls-3.10.1){target="_blank" rel="noopener"} (stable) | :material-check-bold:{ style="color:#2e9e44" } | Fully Supported. |
| Strings in `switch` | Java 7 (2011), [JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"} | the only Java 7 change to `switch`: `String` selectors, compiled via `hashCode`/`equals` ([§14.11](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.11){target="_blank" rel="noopener"}); unchanged since | ( :material-check-bold:{ style="color:#d19a00" } ) | Parsed and lowered to `==`; reasoning about `String` labels is limited. |
| `try`-with-resources | Java 7 (2011), [JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"} | effectively-final resources ([JEP 213](https://openjdk.org/jeps/213){target="_blank" rel="noopener"}, Java 9, [§14.20.3](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.20.3){target="_blank" rel="noopener"}) | :material-minus:{ style="color:#9aa0a6" } | Loads, but **the resource declaration is silently dropped** so `close()` is never modelled; do not rely on it. |
| Multi-catch (`catch (A \| B e)`) | Java 7 (2011), [JSR 334](https://jcp.org/en/jsr/detail?id=334){target="_blank" rel="noopener"} | [§14.20](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.20){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Union-type catch is not supported; sequential `catch` blocks are fine. |
| Lambda expressions | Java 8 (2014), [JEP 126](https://openjdk.org/jeps/126){target="_blank" rel="noopener"} | `var` parameters ([JEP 323](https://openjdk.org/jeps/323){target="_blank" rel="noopener"}, Java 11, [§15.27.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.27.1){target="_blank" rel="noopener"}) | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Method references | Java 8 (2014), [JEP 126](https://openjdk.org/jeps/126){target="_blank" rel="noopener"} | [§15.13](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.13){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Default / `static` interface methods | Java 8 (2014), [JEP 126](https://openjdk.org/jeps/126){target="_blank" rel="noopener"} | private interface methods ([JEP 213](https://openjdk.org/jeps/213){target="_blank" rel="noopener"}, Java 9, [§9.4](https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html#jls-9.4){target="_blank" rel="noopener"}) | ( :material-check-bold:{ style="color:#d19a00" } ) | Interfaces without private and default methods are supported; private/default methods of interfaces load as well but throw an exception when trying to prove anything |
| Modules (`module-info`, JPMS) | Java 9 (2017), [JEP 261](https://openjdk.org/jeps/261){target="_blank" rel="noopener"} | [§7.7](https://docs.oracle.com/javase/specs/jls/se21/html/jls-7.html#jls-7.7){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Not supported (a `module-info` currently triggers an internal error); KeY verifies classes, not modules. |
| `var` (local variable type inference) | Java 10 (2018), [JEP 286](https://openjdk.org/jeps/286){target="_blank" rel="noopener"} | [§14.4.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.4.1){target="_blank" rel="noopener"} | ( :material-check-bold:{ style="color:#d19a00" } ) | Primitive inference works (`var x = 3`, `for (var i…)`); a reference-typed initializer (e.g. `var s = "…"`) currently throws an internal error. |
| `switch` expressions (arrow labels, `yield`) | Java 14 (2020), [JEP 361](https://openjdk.org/jeps/361){target="_blank" rel="noopener"} | [§15.28](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.28){target="_blank" rel="noopener"}, [§14.11](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.11){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Text blocks | Java 15 (2020), [JEP 378](https://openjdk.org/jeps/378){target="_blank" rel="noopener"} | [§3.10.6](https://docs.oracle.com/javase/specs/jls/se21/html/jls-3.html#jls-3.10.6){target="_blank" rel="noopener"} | :material-check-bold:{ style="color:#2e9e44" } | Desugared to ordinary string literals. |
| Records | Java 16 (2021), [JEP 395](https://openjdk.org/jeps/395){target="_blank" rel="noopener"} | record patterns added Java 21 ([JEP 440](https://openjdk.org/jeps/440){target="_blank" rel="noopener"}, see below) | :material-check-bold:{ style="color:#2e9e44" }<sup>*</sup> | Desugared to classes with final fields (see `examples/Java/Records`).<br><sup>*</sup> Compact and synthetic constructors cannot carry a JML specification. For synthetic ones a default contract is generated. |
| Pattern matching for `instanceof` | Java 16 (2021), [JEP 394](https://openjdk.org/jeps/394){target="_blank" rel="noopener"} | [§14.30.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.30.2){target="_blank" rel="noopener"}, [§15.20.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.20.2){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | The pattern-binding form is not supported; plain `instanceof` is supported. |
| Sealed classes & interfaces | Java 17 (2021), [JEP 409](https://openjdk.org/jeps/409){target="_blank" rel="noopener"} | [§8.1.1.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html#jls-8.1.1.2){target="_blank" rel="noopener"}, [§9.1.1.4](https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html#jls-9.1.1.4){target="_blank" rel="noopener"} | ( :material-check-bold:{ style="color:#d19a00" } ) | `sealed` / `non-sealed` modifiers are accepted, but the `permits` clause is ignored, so sealing is not enforced. |
| Pattern matching for `switch` | Java 21 (2023), [JEP 441](https://openjdk.org/jeps/441){target="_blank" rel="noopener"} | [§14.11.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.11.1){target="_blank" rel="noopener"}, [§14.30](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.30){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Type patterns (`case Integer i`) and record patterns (`case Point(...)`) are not supported. |
| Record patterns | Java 21 (2023), [JEP 440](https://openjdk.org/jeps/440){target="_blank" rel="noopener"} | [§14.30.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.30.1){target="_blank" rel="noopener"} | :material-minus:{ style="color:#9aa0a6" } | Not supported. |
| Java Card (transactions, atomic updates) | Java Card 2.2.x |  | :material-check-bold:{ style="color:#2e9e44" } | Enabled via the `JavaCard` taclet option; KeY provides a complete Java Card 2.2.x calculus. |

</div>

!!! info "How this table was checked"

    Each row is backed by a minimal, `javac`-compiling example (one Java
    construct each, generics in several variants) that is loaded into KeY to see
    whether the front-end accepts or rejects it. These live in KeY's test suite as
    `key.core/.../java/coverage/{supported,rejected}/` and are pinned by the test
    `JavaFeatureCoverageTest`, which fails if a *supported* feature stops parsing
    or a *rejected* one starts, a built-in reminder to update this table. A
    :material-check-bold:{ style="color:#2e9e44" } means the construct loads; a
    :material-minus:{ style="color:#9aa0a6" } means it is rejected at load time
    (usually *"Unsupported element detected given by Java Parser"*) or, where
    noted, loads but is not soundly modelled.
