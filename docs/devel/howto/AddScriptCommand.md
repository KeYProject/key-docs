# How to add a proof script command

*2026 — the code below was compiled against the current KeY sources and
executed: a problem file whose embedded proof script calls the command
runs through and the proof closes.*

[Proof scripts](../../../user/ProofScripts/) are sequences of commands
(`rule`, `auto`, `macro`, …). This how-to adds a new command end to end.
The background reference for the involved classes is
[Adding a Proof Script Command](../../ScriptCommands/); the generated
catalog of all existing commands is in the
[user documentation](../../../user/ProofScripts/commands/).

## 1. Where to put the code

Commands live in any module on the classpath — either in `key.core`
(package `de.uka.ilkd.key.scripts`, next to the built-in commands) or in
your own `keyext.<name>` module (see
[How to add an extension](../AddExtension/) for the module skeleton and
the build-file wiring in `settings.gradle` and `key.ui/build.gradle`; a
command-only module just needs `implementation project(":key.core")`).

## 2. Implement the command

Extend `de.uka.ilkd.key.scripts.AbstractCommand` and declare a parameter
class; its fields are filled automatically from the script arguments by the
`ValueInjector` (`@Argument` = positional, `@Option("key")` = named,
`@Flag` = boolean switch — all in `de.uka.ilkd.key.scripts.meta`):

```java
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.demo;

import de.uka.ilkd.key.scripts.AbstractCommand;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.scripts.meta.Option;

/**
 * Example proof script command: prints a greeting and the number of open goals.
 * Usage in a script: {@code greet;} or {@code greet name:"world";}
 */
public class GreetCommand extends AbstractCommand {

    public GreetCommand() {
        super(Parameters.class);
    }

    public static class Parameters {
        /** Whom to greet (named argument, optional). */
        @Option("name")
        public String name = "KeY user";
    }

    @Override
    public String getName() {
        return "greet";
    }

    @Override
    public String getDocumentation() {
        return "Prints a greeting and the number of open goals. "
            + "Optional named argument 'name': whom to greet.";
    }

    @Override
    public void execute(ScriptCommandAst args) throws ScriptException, InterruptedException {
        Parameters params = state().getValueInjector().inject(new Parameters(), args);
        int open = state().getProof().openGoals().size();
        String message = "Hello, " + params.name + "! Open goals: " + open;
        var observer = state().getObserver();
        if (observer != null) {
            observer.accept(new ProofScriptEngine.EchoMessage(message));
        }
    }
}
```

Inside `execute` you reach the system through the `EngineState`
(`state()`): `getProof()`, `getFirstOpenAutomaticGoal()`, abbreviations,
script variables. For a command that actually mutates the proof, follow
`CutCommand` (taclet application) or `AutoCommand` (strategy invocation)
in `de.uka.ilkd.key.scripts`.

## 3. Register the command

Commands are discovered via `ServiceLoader` (see `ProofScriptEngine`).
Add the fully qualified class name to

```
src/main/resources/META-INF/services/de.uka.ilkd.key.scripts.ProofScriptCommand
```

of your module. Without this file the script engine reports
"Unknown command".

## 4. Verify

Compile, then run a problem file with an embedded proof script in batch
mode:

```
\predicates { p; q; }

\problem { (p & q) -> (q & p) }

\proofScript {
    greet name: "world";
    macro "demo-close";   // or simply: auto;
}
```

```sh
./gradlew :keyext.demo:compileJava
./gradlew :key.ui:run --args='--auto demoScript.key'
# ... ConsoleUserInterfaceControl Proved
```

A failing command (unknown name, bad arguments, `ScriptException`) aborts
the run with a nonzero exit code, so "Proved" doubles as the test that the
command executed.

## Error handling and conventions

- Throw `ScriptException` with a helpful message for invalid arguments or
  inapplicable state — the engine reports it with the script location.
- React to `InterruptedException` in long-running commands so users can
  abort.
- `getName()` must not clash with existing commands; check the
  [command reference](../../../user/ProofScripts/commands/). Optional
  `getAliases()` adds alternative names (the invoked alias is visible in
  the `ScriptCommandAst`, so behavior may differ per alias — see
  `let`/`letf`).
- `getDocumentation()` and the parameter class feed the generated command
  reference — write them as user documentation.
