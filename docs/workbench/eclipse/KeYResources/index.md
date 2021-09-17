# KeY Resources

KeY Resources provides the "KeY project" with automatic background
proofs. Such projects extends the functionality of a Java project by
maintaining automatically proofs in background. This means that the
tool tries to do proofs automatically whenever files in a project
change. Markers are used to show the proof result directly in the
source editor.

The following sections illustrate the main features of KeY Resources
using screenshots. Each section contains numbered screenshots that
explain a usage scenario step by step. Clicking on each picture produces
a more detailed view. The screenshots may differ from the latest
release.

## Prerequisites

KeY Resources is compatible with [Eclipse](http://www.eclipse.org)
Indigo (3.7) or newer.

Required update-sites and installation instructions are available in the
[download](../../download/index.html#eclipse) area.

## Create a KeY Project


1. Open new project wizard via Package Explorer context menu item
"New, Project\...".

      ![](create01thumb.png "Create a KeY Project")

2. Select "KeY Project".

      ![](create02thumb.png "Create a KeY Project")

3. Define project name and finish the wizard.

    ![](create03thumb.png "Create a KeY Project")


## Work with a KeY Project


1. Edit source code as normal and save it.

    ![](work01thumb.png "Work with a KeY Project")

2. During build proofs are automatically executed\
and results are shown via marker.

    ![](work02thumb.png "Work with a KeY Project")

3. Proofs are automatically\ maintained in folder "proofs".

    ![](work03thumb.png "Work with a KeY Project")

4. Tooltip of a marker explains the proof state and give hints how to
continue.

    ![](work04thumb.png "Work with a KeY Project")

5. Proof files can be opend in KeY or the KeYIDE via a marker by
selecting "Open proof" to inspect and finish the proof. In addition,
a proof can be inspected in the SED via marker menu item "Debug
proof".

    ![](work05thumb.png "Work with a KeY Project")


## Inspect verification status


1. Select main menu item "Window, Show View,
Other\...".

    ![](status01thumb.png "Customize build settings")

2. Open view "Verification
Status".

    ![](status02thumb.png "Customize build settings")



3. Colors of tree items indicate verification
stati.

    ![](status03thumb.png "Customize build settings")

4. HTML report lists tasks and assumptions used by
proofs.

    ![](status04thumb.png "Customize build settings")


## Inspect verification log

1. Select main menu item "Window, Show View, Other\...".

     ![](log01thumb.png "Customize build settings")

2. Open view "Verification Log". 

     ![](log02thumb.png "Customize build settings")

3. Table shows used settings and times of performed verification
   tasks.
    
     ![](log03thumb.png "Customize build settings")


## Customize build settings


1. Open project properties of a KeY project\ via context menu item
"Properties".

    ![](custom01thumb.png "Customize build settings")

2. Select properties page "KeY, KeY Proof Management" and customize
build settings, e.g. enable counter example and test case generation.
    
    ![](custom02thumb.png "Customize build settings")


## Generated Test Cases

Generated test cases are maintained in an additional Java project. In
addition, a test suite which executes all test cases is generated.

![](testGeneration01thumb.png "Generated Test Cases")


## Inspect a counter example


1. Counter examples can be opend via a marker by selecting "Show Counter Examples".
    ![](counterExample01thumb.png "Inspect a counter example")

2. Inspect the opened counter example.
   ![](counterExample02thumb.png "Inspect a counter example")


## Convert a Java Project into a KeY Project

1. Select "Convert to KeY Project" in the context menu of a Java project.
   ![](convert01thumb.png)
2. Proofs are automatically maintained after conversion.
   ![](convert02thumb.png "Convert a Java Project into a KeY Project")


## KeY basics in Eclipse and troubleshooting

-   [KeY basics in Eclipse (Cross-project
    Functionality)](../CrossProject/index.html)
    -   [Create an example project](../CrossProject/index.html#example)
    -   [Change taclet options](../CrossProject/index.html#taclet)
    -   [Define class path used by
        KeY](../CrossProject/index.html#KeYsClassPath)
-   [Troubleshooting](../CrossProject/index.html#troubleshooting)
    -   [Unresolved classtype (support for API
        classes)](../CrossProject/index.html#API)
