---
approved: weigl
---

# KEP-2: Unique Java Package Names for KeY Gradle Modules

This KEP proposes a Java package-name scheme for Gradle sub-project in the KeY repository. The goal is to eliminate
split-package problems on the module path, Javadoc, and to make the origin of any class immediately obvious from its fully-qualified name.

- **Motivation:** current modules share the root packages like `de.uka.ilkd.key.util`,
  which prevents them from being placed on the Java module path as separate
  named modules, makes Javadoc linking impossible, and makes it hard to tell which sub-project a class belongs to at a glance.
- **Scope of this page:** the naming convention, the proposed package root
  for KeY's modules, and a migration checklist.

## Naming Convention

1. The proposed root for all KeY packages is:

   ```
   {de.uka.ilkd,org.key_project}.key
   ```

   `de.uka.ilkd.key` for legacy modules, and for new modules `org.key_project.key`.

   The final `.key` distinghish these packages from KeY, to other projects of the KeY project, e.g., ips4o (`org.key_project.ips4o.*`).

   This matches our fqdn and our repo name.

2. Each Gradle module appends a module-specific suffix derived from the Gradle project name, with hyphens replaced by underscores and dots replaced by underscores:

```
org.key_project.key.<module_suffix>
```

## Proposed Package Names

The table below lists every current Gradle module together with its proposed unique package root.

| Gradle module                | Proposed package root                     |
| ---------------------------- | ----------------------------------------- |
| `key.core`                   | `de.uka.ilkd.key.core`                    |
| `key.core.infflow`           | `de.uka.ilkd.key.informationflow`         |
| `key.core.testgen`           | `de.uka.ilkd.key.testgen`                 |
| `key.core.wd`                | `de.uka.ilkd.key.wd`                      |
| `key.ncore`                  | `org.key_project.key.ncore`               |
| `key.ncore.calculus`         | `org.key_project.key.calculus`            |
| `key.ncore.compiler`         | `org.key_project.key.compiler`            |
| `key.ui`                     | `org.key_project.key.ui`                  |
| `key.util`                   | `org.key_project.key.util`                |
| `keyext.caching`             | `org.key_project.key.caching`             |
| `keyext.exploration`         | `org.key_project.key.exploration`         |
| `keyext.isabelletranslation` | `org.key_project.key.isabelletranslation` |
| `keyext.proofmanagement`     | `org.key_project.key.proofmanagement`     |
| `keyext.slicing`             | `org.key_project.key.slicing`             |
| `keyext.ui.testgen`          | `org.key_project.key.testgenui`           |
