# AGENT.md

## Purpose

This repository contains the documentation site for the KeY theorem prover.
It is a MkDocs project that publishes:

- a User Guide
- a Developer Guide
- a Historical section for unsupported legacy material

This is a documentation repository, not the main KeY implementation repository.
Keep guidance local to this repo.

## Core Files

- `mkdocs.yml`: central site configuration, plugins, Markdown extensions, theme, and full navigation tree
- `docs/`: primary authored documentation source
- `README.md`: contributor-oriented local build instructions
- `Makefile`: convenience targets for install/serve/build
- `requirements.txt`, `pyproject.toml`: Python dependencies for building the docs
- `hooks/approval.py`: MkDocs hook that injects per-page review badges
- `docs/extra.css`: custom site styling, including review badge styling
- `.github/workflows/mkdocs.yml`: active GitHub Actions build and Pages deployment workflow
- `.gitlab-ci.yml`: older GitLab CI workflow, still present
- `extractScriptDoc.pl`: helper script related to generated proof-script command docs

## Repository Layout

### Main content

- `docs/index.md`: site landing page
- `docs/user/`: user-facing documentation
- `docs/devel/`: developer-facing documentation
- `docs/quicktour/`: tutorial / getting-started content
- `docs/eclipse/`: unsupported historical Eclipse-plugin documentation
- `docs/old/`: older archival material

### Supporting / special-purpose areas

- `hooks/`: MkDocs hook code
- `disabled/`: intentionally parked or excluded content
- `cinder/`: legacy theme assets; current site uses Material for MkDocs instead
- `python/`: checked-in Python environment / support files; not primary authored content, but it is part of the local docs-build infrastructure footprint
- `site/`: generated build output if `mkdocs build` is run locally

## Build And Preview

Typical local commands:

- `make prepare`
- `make serve`
- `make build`

Equivalent direct commands:

- `mkdocs serve`
- `mkdocs build`

Local output normally goes to `site/`.

## CI And Publishing

### GitHub Actions

Defined in `.github/workflows/mkdocs.yml`.

Current behavior:

- build on push to `master` and `main`
- build on pull requests targeting `master` and `main`
- scheduled weekly run
- manual `workflow_dispatch`
- deploy GitHub Pages only from `master`

The build installs dependencies from `requirements.txt` and runs:

- `mkdocs build -c -d public`

### GitLab CI

Defined in `.gitlab-ci.yml`.

This appears to be an older pipeline, but it is still useful context:

- runs `mkdocs build`
- renames `site` to `public`
- runs a link checker

Do not assume GitLab CI is the primary deployment path unless the repo is updated to say so.

## Navigation Model

Navigation is manually curated in `mkdocs.yml` under `nav:`.

Important consequence: adding a Markdown file under `docs/` is usually not enough.
If you add, rename, move, or reorganize a page, also check whether `mkdocs.yml`
must be updated so the page actually appears in the site navigation.

Directory `index.md` files are used as section landing pages, and the Material
theme features in `mkdocs.yml` rely on that pattern.

## Markdown And Site Features

This repo actively uses rich MkDocs / Material features configured in `mkdocs.yml`:

- admonitions
- tables
- footnotes
- attribute lists
- snippets
- tabbed content
- Mermaid diagrams
- MathJax
- BibTeX references
- Material navigation features such as tabs, sections, indexes, and top navigation

When editing pages, preserve existing style unless there is a good reason to simplify it.

## Review Badge Infrastructure

This repository has a custom page-review system.

### Hook

- `hooks/approval.py`

This MkDocs hook inspects page front matter and injects review-status markup.

Supported front-matter forms:

```yaml
---
approved: rb
approved-on: 2026-06-11
---
```

or shorthand:

```yaml
---
approved: rb 2026-06-11
---
```

Special value:

```yaml
approved: none
```

### Behavior

- missing `approved:`: amber/orange "not yet verified" badge at the top of the page
- `approved: <initials>` or `approved: <initials> <date>`: green/accent review note at the footer
- `approved: none`: suppress the badge entirely, used for generated pages

### Styling

- `docs/extra.css`

This stylesheet defines `.approval` classes and related variants used by the hook.
It also contains some other site-level customizations, such as stronger chapter
weight in the sidebar.

### Agent guidance

- Do not invent reviewer initials or approval dates.
- Do not add `approved:` casually; it changes visible site behavior.
- If a page is generated, `approved: none` may be intentional and should usually stay.

## Generated And Semi-Generated Content

Some pages are generated or maintained by scripts rather than purely hand-authored.
Known example:

- `docs/user/ProofScripts/commands.md`

Signals that a page may be generated:

- `approved: none`
- generated metadata or timestamps in the file
- nearby helper scripts such as `extractScriptDoc.pl`

Before rewriting such a page, check whether the source data or generation process
should be changed instead.

## Historical And Legacy Content

Some sections are intentionally historical.

- `docs/eclipse/`: unsupported Eclipse-plugin documentation
- `docs/old/`: archival documents
- `disabled/`: intentionally excluded material
- `cinder/`: old theme assets from a previous setup

Do not automatically modernize or repurpose these areas. Verify intent first.

## Safe Editing Guidance

Usually safe:

- fix wording, typos, formatting, and broken local links in active docs
- improve structure inside an existing active page
- add missing nav entries for active files
- update docs that clearly belong to active user/developer sections
- adjust CSS or hook logic when working on site presentation / badge behavior

Use caution for:

- generated pages
- historical sections
- broad nav reorganizations
- any change that alters visible badge behavior across the whole site

## Files To Read First For Orientation

Before making non-trivial changes, read:

- `README.md`
- `mkdocs.yml`
- `docs/index.md`
- `docs/user/index.md`
- `docs/devel/index.md`
- `docs/devel/howtodoc/index.md`
- `hooks/approval.py`
- `docs/extra.css`

These files explain the site structure, contributor workflow, and the custom
review-badge infrastructure.

## Verification Checklist

For meaningful documentation or infrastructure changes, prefer to verify with:

1. `mkdocs build`
2. confirm the modified page is reachable from `mkdocs.yml` navigation if needed
3. confirm there are no broken internal links or config errors
4. if front matter or badge logic changed, check that the page renders the expected badge state

## Common Pitfalls

- adding a page under `docs/` but forgetting `mkdocs.yml`
- editing a generated page directly
- treating historical pages as current product documentation
- changing `approved:` metadata without intending to affect visible badges
- forgetting that site-level behavior can be implemented in Python hooks and CSS, not just Markdown

## Scope Reminder

Keep guidance specific to this repository.
Do not assume access to, or rely on, the main KeY code repository when editing this repo.
