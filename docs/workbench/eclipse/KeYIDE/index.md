# KeYIDE

KeYIDE is an alternative user interface for KeY directly integrated into
Eclipse. The goal of this project is to provide the same functionality
as the original user interface of KeY. Up to now only the basics (proof
tree navigation, auto mode, interactive rule application) are available.

The following sections illustrate the main features of the KeYIDE using
screenshots. Each section contains numbered screenshots that explain a
usage scenario step by step. Clicking on each picture produces a more
detailed view. The screenshots may differ from the latest release.

### Prerequisites

The KeYIDE is compatible with [Eclipse](http://www.eclipse.org) Indigo
(3.7) or newer.

Required update-sites and installation instructions are available in the
[download](../../download/index.html#eclipse) area.

### Verify a method contract



1. Select the method to verify.

    ![](verifyMethod01thumb.png "Verify a method contract")

2. Start proof via main menu item "KeY, Start
Proof".

    ![](verifyMethod02thumb.png "Verify a method contract")



3. Select Application
"KeYIDE".

    ![](verifyMethod03thumb.png "Verify a method contract")

4. Select method contract to
prove.

    ![](verifyMethod04thumb.png "Verify a method contract")



5. Switch to perspective
"KeY".

    ![](verifyMethod05thumb.png "Verify a method contract")

6. Do proof directly in
Eclipse.

    ![](verifyMethod06thumb.png "Verify a method contract")


### Start auto mode



1. Change strategy settings if
required.

    ![](auto01thumb.png "Start auto mode")

2. Start auto mode via editor specifc toolbar item "Start Auto Mode".

    ![](auto02thumb.png "Start auto mode")

3. Wait while auto mode is active.

    ![](auto03thumb.png "Start auto mode")

4. Inspect result.

    ![](auto04thumb.png "Start auto mode")


### Stop auto mode when breakpoint is hit


1. Define a Line, Method or Java Exception breakpoint, a Watchpoint or
a KeY Watchpoint as usual.

    ![](breakpoints01thumb.png "Stop auto mode when breakpoint is hit")

2. Select toolbar item "Stop at Breakpoints" before starting the auto
mode.

    ![](breakpoints02thumb.png "Stop auto mode when breakpoint is hit")



3. Auto mode stops when breakpoint is hit.

    ![](breakpoints03thumb.png "Stop auto mode when breakpoint is hit")


### Apply a rule interactively


1. Move the mouse over a term and apply a rule via the context
menu.

    ![](interactive01thumb.png "Apply a rule interactively")


### Generate a counter example


1. Select context menu item "Counterexample" of a goal.

    ![](counterExample01thumb.png "Generate a counter example")

2. Optionally visualize counter example via context menu item
"Visualize Model".

    ![](counterExample02thumb.png "Generate a counter example")



3. Inspect the visualized counter example.

    ![](counterExample03thumb.png "Generate a counter example")


### Generate test cases


1. Select toolbar item "Generate test cases for open goals".

    ![](generateTests01thumb.png "Generate test cases")

2. An additional Java project is created which contains the generated
test cases. Follow the instructions in the Reame.txt file to add
missing libraries.

    ![](generateTests02thumb.png "Generate test cases")


### KeY basics in Eclipse and troubleshooting

-   [KeY basics in Eclipse (Cross-project
    Functionality)](../CrossProject/index.html)
    -   [Create an example project](../CrossProject/index.html#example)
    -   [Change taclet options](../CrossProject/index.html#taclet)
    -   [Define class path used by
        KeY](../CrossProject/index.html#KeYsClassPath)
-   [Troubleshooting](../CrossProject/index.html#troubleshooting)
    -   [Unresolved classtype (support for API
        classes)](../CrossProject/index.html#API)
