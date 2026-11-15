# How to add a proof macro

*2026 — the code below was compiled against the current KeY sources and
executed: a problem file whose proof script invokes the macro closes with
"Proved".*

A *proof macro* bundles strategy invocations and rule applications into one
high-level proof step. Macros appear in the GUI (context menu *Strategy
macros*) **and** are callable from [proof scripts](../AddScriptCommand/)
via `macro "<name>";` — you get both for free from one implementation.
(See the [user documentation of the shipped macros](../../../user/ProofScripts/macros/).)

## 1. Where to put the code

Macros live in any module on the classpath. Either add the class to
`key.core` (package `de.uka.ilkd.key.macros`) if it is of general use, or —
for a self-contained feature — put it into your own `keyext.<name>` module
(see [How to add an extension](../AddExtension/) for the module skeleton
and the build-file wiring in `settings.gradle` and `key.ui/build.gradle`;
a macro-only module just needs `implementation project(":key.core")`).

## 2. Pick a base class

| Base class (package `de.uka.ilkd.key.macros`) | Use when |
|---|---|
| `SequentialProofMacro` | your macro is a sequence of existing macros |
| `StrategyProofMacro` | your macro is "run the auto strategy, but modified" (filtered rules, different costs) |
| `AbstractProofMacro` | full control over `canApplyTo`/`applyTo` |

## 3. Example

This macro tries to close all open goals with a step limit, by composing
the existing `TryCloseMacro`:

```java
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.demo;

import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;

public class DemoMacro extends SequentialProofMacro {

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new TryCloseMacro(5000) };
    }

    @Override
    public String getName() {
        return "Demo: try to close all goals";
    }

    @Override
    public String getCategory() {
        return "Demo";    // submenu in the GUI's "Strategy macros" menu
    }

    @Override
    public String getScriptCommandName() {
        return "demo-close";    // name for `macro "demo-close";` in scripts
    }

    @Override
    public String getDescription() {
        return "Tries to close all open goals using at most 5000 rule applications per goal.";
    }
}
```

For a `StrategyProofMacro` example look at `FinishSymbolicExecutionMacro`
(runs the strategy until no modality is left) or
`PropositionalExpansionMacro` (restricts the strategy to an explicit list
of admitted rules); both are in `key.core`.

## 4. Register the macro

Macros are discovered via `ServiceLoader`. Add the fully qualified class
name to the file

```
src/main/resources/META-INF/services/de.uka.ilkd.key.macros.ProofMacro
```

of your module (one class per line). Without this file the macro neither
shows up in the GUI nor resolves in scripts.

## 5. Verify

Compile (`./gradlew :keyext.demo:compileJava`), then check both fronts:

- **GUI**: `./gradlew :key.ui:run`, load any problem, right-click a goal —
  the macro appears under *Strategy macros → Demo*.
- **Script** (headless): create a problem file with an embedded script and
  run it in batch mode:

  ```
  \predicates { p; q; }

  \problem { (p & q) -> (q & p) }

  \proofScript {
      macro "demo-close";
  }
  ```

  ```sh
  ./gradlew :key.ui:run --args='--auto demoScript.key'
  # ... ConsoleUserInterfaceControl Proved
  ```

!!! note "Quote hyphenated names in scripts"
    In the script language, a macro name containing `-` (like
    `demo-close`) must be written as a string: `macro "demo-close";`.
    A bare identifier works only for names without special characters.

## Notes

- `getName()` is the human-readable label, `getScriptCommandName()` the
  script identifier (return `null` if the macro should not be scriptable),
  `getCategory()` groups macros in the GUI menu.
- Macros can accept parameters from scripts
  (`macro "name" key:"value";`) by overriding `hasParameter(String)` and
  `setParameter(String, String)` from `ProofMacro` — see `AutoMacro` for a
  real example.
- Long-running macros run on a worker thread; they must react to
  interruption so users can cancel them.
