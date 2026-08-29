---
title: "KeY Documentation"
date: 2024-01-01T00:00:00Z
draft: false
weight: 1
description: "Documentation for the KeY Deductive Verification System"
cascade:
  type: docs
---

# Overview

This web page contains information for users and developers of the KeY Deductive Verification System.

The documentation is split into two major parts:

* **User Guide** — for people who *use* KeY to verify Java programs:
    * [Getting started with the Quicktour](quicktour/)
    * [Core concepts, languages, and UI features](user/)
    * [Proof scripts for resilient, persistent and reapplicable proofs](user/ProofScripts/)
    * [Frequently asked questions](user/FAQ/)
* **Developer Guide** — for people who *build on or contribute to* KeY:
    * [Getting started with the code base](devel/)
    * [Architecture overview](devel/Architecture/)
    * [How to extend KeY](devel/ExtendingKeY/) (taclets, GUI extensions, script commands, SMT solvers)
    * [How we test KeY](devel/Testing/)

If you want to contribute to this documentation, please refer to [*How to write documentation*](devel/howtodoc/).

![KeY Logo](https://git.key-project.org/uploads/-/system/appearance/logo/1/key-color.png)

The KeY Team.
---
title: "Documentation"
description: "KeY Documentation Sections"
cascade:
  - type: docs
---

# Documentation

Browse the documentation by category:

{{< cards >}}
  {{< card link="/user" title="User Guide" icon="book-open" subtitle="For end users" >}}
  {{< card link="/devel" title="Developer Guide" icon="code" subtitle="For contributors" >}}
  {{< card link="/keps" title="KEPs" icon="document-text" subtitle="Enhancement proposals" >}}
{{< /cards >}}
