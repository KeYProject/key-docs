# How to add a main menu entry

*2026 — code compiled against the current KeY sources.*

Menu entries are contributed by a [GUI extension](../AddExtension/) that
implements `KeYGuiExtension.MainMenu`. If you do not have an extension
module yet, follow [How to add an extension](../AddExtension/) first — it
contains the build-file wiring (`settings.gradle`, `key.ui/build.gradle`)
and the `META-INF/services` registration.

## 1. Write the action

Extend `de.uka.ilkd.key.gui.actions.MainWindowAction` (in `key.ui`), which
gives you the `mainWindow` field and convenient setters from `KeyAction`:

```java
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.demo;

import java.awt.event.ActionEvent;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

public class HelloAction extends MainWindowAction {

    public HelloAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Say Hello");
        setTooltip("Shows a friendly greeting.");
        // Sort this action into the top-level menu "About" of the main menu.
        // Without a menu path, the action ends up in the "Extensions" menu.
        setMenuPath("About");
        setEnabled(true);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        JOptionPane.showMessageDialog(mainWindow, "Hello from the demo extension!");
    }
}
```

## 2. Contribute it from your extension

```java
@Override
public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
    return List.of(new HelloAction(mainWindow));
}
```

## Where does the entry appear?

Placement is controlled by the `PATH` property of the action
(`setMenuPath(...)`), interpreted by `KeYGuiExtensionFacade`:

- **No path set** — the action is added to the **Extensions** menu, which
  KeY creates for extension actions.
- **`setMenuPath("Options")`** — the action is sorted into the existing
  top-level menu *Options*. If no menu of that name exists, a new top-level
  menu is created.
- **Dots create submenus**: `setMenuPath("Options.Demo")` puts the action
  into the submenu *Demo* of *Options* (created on demand).
- `setPriority(int)` (the `PRIORITY` property) orders actions within a
  menu.
- Setting `putValue(CHECKBOX, true)` renders the entry as a
  `JCheckBoxMenuItem` — useful for toggles; see `CachingToggleAction`
  in `keyext.caching` for a real example.

## Useful `KeyAction` helpers

- `setName(String)`, `setTooltip(String)`, `setIcon(Icon)` — labels;
  icons typically come from `de.uka.ilkd.key.gui.fonticons.IconFactory`.
- `setAcceleratorLetter(int)` / `setAcceleratorKey(KeyStroke)` — keyboard
  shortcuts.
- `MainWindowAction(mainWindow, true)` — second parameter `true` enables
  the action only while a proof is loaded.
- Inside `actionPerformed` you reach the rest of the system via
  `getMediator()` (selected proof, goal, …).
