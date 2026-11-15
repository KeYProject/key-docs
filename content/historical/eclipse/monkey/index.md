---
title: "MonKeY"
weight: 50
---

{{< callout type="warning" title="Unsupported historical content" >}}
This Eclipse integration is **no longer supported or maintained**. It
targeted old Eclipse releases (Indigo/Luna era) and old versions of
KeY; the update sites may no longer exist. This page is kept for
historical reference.
{{< /callout >}}


MonKeY provides a batch verification of all proof obligations. This
means that the tool lists all proof obligations provided by the source
code and allows to prove them in a batch. Statistics such as the used
time or the complexity of proofs are also provided.

The following sections illustrate the main features of MonKeY using
screenshots. Each section contains numbered screenshots that explain a
usage scenario step by step. Clicking on each picture produces a more
detailed view. The screenshots may differ from the latest release.

## Prerequisites

MonKeY is compatible with [Eclipse](http://www.eclipse.org) Indigo (3.7)
or newer.

Required update-sites and installation instructions are available in the
[download](https://www.key-project.org/download/#eclipse) area.

## Verify all proof obligations of a project

1. Select project to load.

    ![](verifyProject01thumb.png "Verify all proof obligations of a project")

2. Select main menu item "KeY, Load Project".

    ![](verifyProject02thumb.png "Verify all proof obligations of a project")

3. Select Application "MonKeY".

    ![](verifyProject03thumb.png "Verify all proof obligations of a project")

4. Select "Start selected Proofs" and wait until all proofs are done.

    ![](verifyProject04thumb.png "Verify all proof obligations of a project")

5. Inspect the result.

    ![](verifyProject05thumb.png "Verify all proof obligations of a project")

## KeY basics in Eclipse and troubleshooting

-   [KeY basics in Eclipse (Cross-project
    Functionality)](../cross-project/)
    -   [Create an example project](../cross-project/#create-an-example-project)
    -   [Change taclet options](../cross-project/#change-taclet-options)
    -   [Define class path used by
        KeY](../cross-project/#KeYsClassPath)
-   [Troubleshooting](../cross-project/#troubleshooting)
    -   [Unresolved classtype (support for API
        classes)](../cross-project/#unresolved-classtype-support-for-api-classes)
