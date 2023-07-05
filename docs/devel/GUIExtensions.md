**weigl, 2019**

GUI Extensions defines a couple of extension points for the KeY User Interface.
It allows to add new functionality into the gui, without digging through the old
UI code. It also should make the UI more consistent, decoupling dependencies and
easier to implement new functionality.

#### General extension points

An extension is defined by an interface, which should be implemented by the new
functionality. This interface defines the methods needed to be successfully
injected into the UI. GUI Extensions are loaded and found via the
`ServiceLoader` facility of Java. Therefore, you should mention your extension
in the appropiate serivce file under `META-INF/services/<full-interface-name>`.
For example, the exploration extension specifies the fully qualified class name
`org.key_project.exploration.ExplorationExtension` in `keyext.exploration/src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension`.

Every gui extension should be marked with `KeYGuiExtension` and is only loaded
once. It does not matter on how many extension points it participate.

Different GUI extension should not depend on each other, as 
Gui Extension should loaded independent.


## Basic Extension Metadata

Additional meta data can plugged to an extension by adding the Java annotation
`@KeYGuiExtension.Info`.

Currently: `name`, `description`, `disabled`, `optional`, `priority`.

Annotation because of accessible via the class w/o instantiation.

* Extension Points are now in `KeYGuiExtension`

## General UI facilities 

### Icon Management 

`KeYIconManagement` and `KeYIcon` introduces a way of icon management and configuration via `UIManager`.  

### Key-stroke Management

`KeyStrokeManager` reworked. It is now possible to define `KeyStroke`s in
a properties file.

### Color Management

### Sharing Services accross UI extensions

Brings `Lookup` a successor for a flexible mediator replacement based on
a service architecture, incl. Dependency Injection
 

## `KeYGuiExtension.Startup`
Entry point for KeY startup.
For hooking into the shutdown handler, register a GUIListener at the KeYMediator.

## `KeYGuiExtension.MainMenu`
## `KeYGuiExtension.ContextMenu`

Use this extension point to add items to context menus.
Extend `ContextMenuAdapter` and override the methods of the menus you wish to extend.
It is possible to extend the context menu of the proof list, the proof tree, the taclet info screen and the sequent view.

## `KeYGuiExtension.LeftPanel`

Implement this interface to add a panel to the UI.
It is added to the panel in the left bottom corner.

## `KeYGuiExtension.Toolbar`

Implement this interface to add new elements to the main toolbar above the sequent view.
Sample code:
```java
private JToolBar extensionToolbar = null;

@Nonnull
@Override
public JToolBar getToolbar(MainWindow mainWindow) {
    if (extensionToolbar == null) {
        extensionToolbar = new JToolBar();
        extensionToolbar.add(new FooAction(mainWindow, this));
        extensionToolbar.add(new BarAction(mainWindow, this));
    }
    return extensionToolbar;
}
```

## `KeYGuiExtension.Settings`

* A common settings dialog should replace all existing setting dialogs.
  - A component can register a `SettingsProvider` to the `SettingsManager.getInstance()` 
    to participate in the default instance.
  - A `SettingsProvider` offers mainly a description, a panel, and a handler to save the settings. 
  - A `SettingsProvider` can have children (`SettingsProvider`).  
  - An extension can announce a `SettingsProvider` by declaring to be `KeYGuiExtension.Settings`.
  - Existing settings were adopted.

Changes to settings: It is now possible to hook into the
  proof-independent/-dependent settings by calling `addSettings(Settings)`.

## `KeYGuiExtension.StatusLine`

## `KeYGuiExtension.TermInfo`

This interface allows you to extend the tooltip displayed when hovering on a term in the sequent view.


## `KeYGuiExtension.KeyboardShortcuts`

