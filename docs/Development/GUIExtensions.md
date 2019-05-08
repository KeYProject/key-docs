This merge request changes and brings new GUI Extensions and also a Common UI for Settings.

Gui Extension are now loaded differently.

* Every gui extension should be marked with `KeyGuiExtension` is only loaded once.
* Additional meta data can plugged to an extension by adding  `@KeyGuiExtension.Info`.
  - Currently: `name`, `description`, `disabled`, `optional`, `priority`.
  - Annotation because of accessible via the class w/o instantiation.
* Extension Points are now in `KeyGuiExtension`
  - `KeyGuiExtension.MainMenu`
  - `KeyGuiExtension.ContextMenu`
  - `KeyGuiExtension.LeftPanel`
  - `KeyGuiExtension.Toolbar`
  - `KeyGuiExtension.StatusLine`
  - `KeyGuiExtension.Settings` 
  - `KeyGuiExtension.KeyboardShortcuts`

* A common settings dialog should replace all existing setting dialogs.
  - A component can register a `SettingsProvider` to the `SettingsManager.getInstance()` 
    to participate in the default instance.
  - A `SettingsProvider` offers mainly a description, a panel, and a handler to save the settings. 
  - A `SettingsProvider` can have children (`SettingsProvider`).  
  - An extension can announce a `SettingsProvider` by declaring to be `KeyGuiExtension.Settings`.
  - Existing settings were adopted.
* `KeYIconManagement` and `KeYIcon` introduces a way of icon management and configuration via `UIManager`.  
* Changes to settings: It is now possible to hook into the proof-independent/-dependent settings by calling 
  `addSettings(Settings)`. 
* Brings `Lookup` a successor for a flexible mediator replacement based on a service architecture, incl. Dependency Injection
* Refactoring: Parts of `MiscTools` are split up into `Strings`, `KeyCollections` and `Files` in `key.util`.
* *Update*: `KeyStrokeManager` reworked. 
   It is now possible to define `KeyStroke`s in a properties file.

![Bildschirmfoto_vom_2019-04-09_02-31-54](/uploads/2eab8b873c19b7f6df5ee6f5d3472897/Bildschirmfoto_vom_2019-04-09_02-31-54.png)

![Bildschirmfoto_vom_2019-04-09_02-31-42](/uploads/22fb6b3a353b9f74e03cbc316fbb2a93/Bildschirmfoto_vom_2019-04-09_02-31-42.png)

![Bildschirmfoto_vom_2019-04-09_02-31-20](/uploads/40b6ded69fbb3c9f84fbecddb8a29a55/Bildschirmfoto_vom_2019-04-09_02-31-20.png)
![Bildschirmfoto_vom_2019-04-09_02-33-53](/uploads/22260a924d736267aa96bc5ccc79f1af/Bildschirmfoto_vom_2019-04-09_02-33-53.png)
 

* Todo:
  * [x] Design fine tuning
  * [x] Testing
  * [x] Extension Documentation
  * [x] Translation of Heatmap Options
  * [x] Figure out, how to store additionally settings persistently.

Affect work of @schiffl @lanzinger !122 !164  
Requires: !179 
