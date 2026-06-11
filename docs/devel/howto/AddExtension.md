# How to add an extension

*2026 — every step below was carried out against the current KeY sources;
the resulting module compiles (`./gradlew :keyext.demo:compileJava`) and the
service file is correctly packaged into the jar.*

This how-to creates a new, self-contained extension module `keyext.demo`
that contributes a main menu entry and a toolbar button to the KeY GUI.
The same module skeleton is the home for any other extension point
(context menus, settings pages, left panels, … — see
[GUI extensions](../../GUIExtensions/)).

## 1. Create the module

Create this directory layout in the repository root (next to the existing
`keyext.*` modules):

```
keyext.demo/
├── build.gradle
└── src/main/
    ├── java/org/key_project/demo/
    │   ├── DemoExtension.java
    │   └── HelloAction.java
    └── resources/META-INF/services/
        └── de.uka.ilkd.key.gui.extension.api.KeYGuiExtension
```

## 2. Build-file wiring

This is the part that is easy to miss. **Three** build files are involved:

**(a) `keyext.demo/build.gradle`** — the module itself. The common
configuration (Java version, repositories, test setup, spotless, …) is
inherited from the root `build.gradle`, so this stays minimal:

```groovy
description = "Demo extension: hello-world menu entry and toolbar button."

dependencies {
    implementation project(":key.core")
    implementation project(":key.ui")
}
```

**(b) `settings.gradle`** (repository root) — make Gradle aware of the
module by adding it next to the other extensions:

```groovy
include "keyext.demo"
```

**(c) `key.ui/build.gradle`** — put the extension on the *runtime*
classpath of the GUI so the `ServiceLoader` finds it when KeY starts.
Add one line to the `dependencies` block, next to the other `keyext.*`
entries:

```groovy
runtimeOnly project(":keyext.demo")
```

(`runtimeOnly` and not `implementation`: `key.ui` must not compile against
your extension — the coupling is only via the service registry.)

## 3. The extension class

`src/main/java/org/key_project/demo/DemoExtension.java`:

```java
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.demo;

import java.util.List;
import javax.swing.Action;
import javax.swing.JToolBar;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

import org.jspecify.annotations.NonNull;

/**
 * A minimal GUI extension contributing one main menu entry and one toolbar button.
 */
@KeYGuiExtension.Info(name = "Demo Extension",
    description = "Minimal example extension (main menu + toolbar).",
    optional = true, experimental = false)
public class DemoExtension
        implements KeYGuiExtension, KeYGuiExtension.MainMenu, KeYGuiExtension.Toolbar {

    private HelloAction helloAction;

    private HelloAction getHelloAction(MainWindow mainWindow) {
        if (helloAction == null) {
            helloAction = new HelloAction(mainWindow);
        }
        return helloAction;
    }

    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        return List.of(getHelloAction(mainWindow));
    }

    @Override
    public @NonNull JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar toolbar = new JToolBar("Demo");
        toolbar.add(getHelloAction(mainWindow));
        return toolbar;
    }
}
```

Notes:

- The class implements the marker interface `KeYGuiExtension` **plus** one
  sub-interface per extension point it participates in
  (`MainMenu`, `Toolbar`, `ContextMenu`, `Settings`, `LeftPanel`,
  `Startup`, …). An extension is instantiated only once, no matter how many
  extension points it serves.
- `@KeYGuiExtension.Info` supplies metadata: `optional = true` lets users
  disable the extension in the settings dialog; `experimental = true` would
  hide it unless KeY runs with `--experimental`. There is also `priority`.
- See `HelloAction` in [How to add a main menu entry](../AddMenuEntry/).

## 4. Register the extension

Extensions are discovered with Java's `ServiceLoader`. Create the file

```
src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension
```

containing the fully qualified name of your class (one per line):

```
org.key_project.demo.DemoExtension
```

Without this file the extension compiles fine but is silently ignored.

## 5. Build and run

```sh
./gradlew :keyext.demo:compileJava   # compile the extension
./gradlew :key.ui:run               # start KeY with the extension loaded
```

You should see a *Demo* toolbar with a *Say Hello* button, the same action
in the main menu, and the extension listed in *Options → Settings →
Extensions* (where users can disable it, since it is `optional`).

The `shadowJar`/`distZip` distributions of `key.ui` pick the extension up
automatically (service files of all modules are merged via
`mergeServiceFiles()` in `key.ui/build.gradle`).

## Real extensions to learn from

| Module | Demonstrates |
|---|---|
| `keyext.exploration` | LeftPanel, Toolbar, ContextMenu, Settings |
| `keyext.caching` | Startup, ContextMenu, StatusLine, Settings, Toolbar, MainMenu, listeners |
| `keyext.slicing` | LeftPanel, ContextMenu, Toolbar, settings |
| `keyext.isabelletranslation` | MainMenu, ContextMenu, Settings |
