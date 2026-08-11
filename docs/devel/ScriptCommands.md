# Adding a Proof Script Command

*2026 — checked against `de.uka.ilkd.key.scripts` in `key.core`.*

[Proof scripts](../../user/ProofScripts/) consist of commands such as
`rule`, `auto`, or `macro`. This page explains how to add your own command.
The complete, generated reference of existing commands is in the
[user documentation](../../user/ProofScripts/commands/).

## Where commands live

Commands are implemented in the package `de.uka.ilkd.key.scripts` of
`key.core` and discovered at runtime via `ServiceLoader` (see
`ProofScriptEngine`). To add a command you therefore need to:

1. implement the interface `de.uka.ilkd.key.scripts.ProofScriptCommand`, and
2. register your class in
   `src/main/resources/META-INF/services/de.uka.ilkd.key.scripts.ProofScriptCommand`.

Your command can live in any module on the classpath — it does not have to
be added to `key.core` itself.

## The `ProofScriptCommand` interface

```java
public interface ProofScriptCommand {
    List<ProofScriptArgument> getArguments();
    void execute(AbstractUserInterfaceControl uiControl,
                 ScriptCommandAst args, EngineState stateMap)
        throws ScriptException, InterruptedException;
    String getName();
    default List<String> getAliases() { return List.of(getName()); }
    String getDocumentation();
}
```

- `getName()` — the keyword under which the command is invoked in scripts.
  Must not clash with existing commands.
- `getAliases()` — optional additional names. The actually used name is
  available in the `ScriptCommandAst` during `execute`, so a command may
  behave differently per alias (e.g. `let` vs. `letf`).
- `getArguments()`/`getDocumentation()` — self-documentation; this is the
  source of the generated [command reference](../../user/ProofScripts/commands/).
- `execute(...)` — performs the actual mutation of the proof. The
  `EngineState` gives access to the current proof, the selected goal, user
  abbreviations, and script variables.

## Use `AbstractCommand` and declarative arguments

In practice you should extend `de.uka.ilkd.key.scripts.AbstractCommand` and
declare a *parameter class* whose fields are filled automatically from the
script's arguments via the `ValueInjector` — including type conversion and
"required argument missing" errors. The annotations live in
`de.uka.ilkd.key.scripts.meta`:

- `@Argument(n)` — positional argument at position `n`,
- `@Option("name")` — named (key-value) argument,
- `@Flag` — boolean switch,
- `@PositionalVarargs` / `@OptionalVarargs` — variable-length arguments.

A minimal example, following the pattern of `CutCommand`:

```java
public class MyCommand extends AbstractCommand {

    public MyCommand() {
        super(Parameters.class);
    }

    public static class Parameters {
        @Argument
        public JTerm formula;       // positional argument

        @Option("steps")
        public int steps = 1000;    // named argument with default
    }

    @Override
    public String getName() {
        return "mycommand";
    }

    @Override
    public String getDocumentation() {
        return "One-paragraph description shown in the generated reference.";
    }

    @Override
    public void execute(ScriptCommandAst arguments)
            throws ScriptException, InterruptedException {
        Parameters args = state().getValueInjector()
                .inject(new Parameters(), arguments);
        Goal goal = state().getFirstOpenAutomaticGoal();
        // ... mutate the proof ...
    }
}
```

Inside `execute`, the protected fields `proof`, `state`, `uiControl`, and
`service` (the `Services` object) are available (with null-safe accessors
such as `state()`).

## Error handling and interruption

- Throw `ScriptException` with a helpful message when arguments are invalid
  or the command is not applicable; the message is reported to the user with
  the script location.
- Long-running commands must react to thread interruption
  (`InterruptedException`) so that users can abort script execution.

## Testing your command

Add a JUnit test that runs a small script through
`ProofScriptEngine` against one of the example problems — see the existing
tests for the script engine in `key.core` (`src/test/java`, package
`de.uka.ilkd.key.scripts`) for the pattern.
