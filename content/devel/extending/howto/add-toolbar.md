# How to add a toolbar

*2026 — code compiled against the current KeY sources.*

Toolbars are contributed by a [GUI extension](../AddExtension/) that
implements `KeYGuiExtension.Toolbar`. If you do not have an extension
module yet, follow [How to add an extension](../AddExtension/) first — it
contains the build-file wiring (`settings.gradle`, `key.ui/build.gradle`)
and the `META-INF/services` registration.

## Contribute a toolbar

The extension point hands back a whole `JToolBar`, which KeY embeds into
the toolbar area above the sequent view (users can rearrange and float it;
its visibility can be toggled via *View → Toolbars*):

```java
@Override
public @NonNull JToolBar getToolbar(MainWindow mainWindow) {
    JToolBar toolbar = new JToolBar("Demo");   // the name shows up in the View menu
    toolbar.add(new HelloAction(mainWindow));  // a KeyAction, see below
    return toolbar;
}
```

`getToolbar` is called once; return the same instance if you keep a
reference. Actions added to a toolbar render as buttons with the action's
icon and tooltip — set both, since toolbar buttons show no text by
default:

```java
setIcon(IconFactory.PLUS.get(MainWindow.TOOLBAR_ICON_SIZE));
setTooltip("Shows a friendly greeting.");
```

(`de.uka.ilkd.key.gui.fonticons.IconFactory` provides the icon set used
throughout KeY; `MainWindow.TOOLBAR_ICON_SIZE` keeps sizes consistent.)

## Beyond plain buttons

You are free to add any Swing component to the toolbar:

- **Toggle buttons**: wrap the action in a `JToggleButton` — see
  `CachingExtension#getToolbar` in `keyext.caching`:

  ```java
  JToolBar tb = new JToolBar("Proof Caching");
  JToggleButton comp = new JToggleButton(toggleAction);
  comp.setToolTipText((String) toggleAction.getValue(Action.LONG_DESCRIPTION));
  tb.add(comp);
  ```

- **Stateful buttons** that react to the proof state: implement
  `KeYSelectionListener` in your extension and update the component — see
  `ReferenceSearchButton` in `keyext.caching` or the slicing toolbar in
  `keyext.slicing`.

## Sharing actions between toolbar and menu

The same `KeyAction` instance can be returned from both
`getMainMenuActions` (see
[How to add a main menu entry](../AddMenuEntry/)) and added to the
toolbar — this keeps the enabled/selected state in sync automatically,
since both Swing components observe the same `Action`.
