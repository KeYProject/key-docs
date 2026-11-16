# AGENT.md

## Purpose

This repository contains the documentation site for the KeY theorem prover.
It is a **Hugo** site (theme: Hextra, consumed as a Go module) that publishes:

- a User Guide
- a Developer Guide
- a Historical section for unsupported legacy material
- KEPs (KeY Enhancement Proposals)

This is a documentation repository, not the main KeY implementation repository.
Keep guidance local to this repo.

## Core Files

- `hugo.yaml`: site configuration — base URL, menus, Markdown options, math,
  search
- `content/`: primary authored documentation source
- `layouts/`: local overrides of the theme (callout, snippet, citation,
  approval badges, Prism, MathJax)
- `assets/`: files processed by Hugo (shared snippets, CSS, Prism grammars)
- `static/`: files copied verbatim (images, PDFs, XML schemas, downloads)
- `data/refs.json`: bibliography database generated from `refs.bib`
- `go.mod`, `go.sum`: pinned Hextra version (v0.13.0)
- `Makefile`: `prepare`, `serve`, `build`, `check`, `clean`
- `.github/workflows/pages.yaml`: build and GitHub Pages deployment
- `scripts/`: migration and bibliography helpers, not needed to build the site
- `content/devel/writing-documentation/index.md`: the authoritative authoring
  guide, with live examples

Intentionally kept but not part of the site build:

- `refs.bib`: BibTeX source for `data/refs.json`
- `springer-basic-author-date.csl`: reference CSL style
- `share/quicktour/`: LaTeX/Java sources for the historical quick tour
- `disabled/`: parked or excluded material, not published
- `DOC_REWORK_CHANGELOG.md`: migration log

## Build And Preview

```bash
make prepare   # hugo mod tidy
make serve     # http://localhost:1313, debug, no fast render
make build     # production build into public/
make check     # scratch build + lychee link check
make ci        # build + check
make update    # update the Hextra module and tidy go.mod/go.sum
make version   # compare local Hugo with HUGO_VERSION (CI pin)
make clean     # remove public/, resources/, /tmp/keydocs-check
```

Direct equivalents:

```bash
hugo mod tidy
hugo server --logLevel debug --disableFastRender -p 1313
hugo --gc --minify
```

Requirements: Hugo **extended** 0.170.0, Go 1.27+, Git. `make check` also needs
lychee; it reports a clear error when lychee is missing. Never edit `public/` or
`resources/` — they are generated.

## Repository Layout

### Content

- `content/_index.md`: site landing page
- `content/user/`: user-facing documentation (including `getting-started/`,
  `proving/`, `proof-scripts/`, `language/`, `smt/`, `bridges/`)
- `content/devel/`: developer-facing documentation
- `content/historical/eclipse/`: unsupported Eclipse-plugin documentation
- `content/keps/`: enhancement proposals

URLs follow the path: `content/user/faq.md` → `/user/faq/`. Directory landing
pages are `_index.md`. Pages with images or downloads are leaf bundles
(`index.md` plus assets next to it).

## Navigation Model

There is no navigation file. The sidebar is generated from the content tree:

- section order and page order come from `weight` in front matter, ascending
- every page and every `_index.md` should have an explicit `weight`; a missing
  weight is treated as 0 and silently sorts first
- leave gaps (10, 20, 30, …) when inserting pages
- the main menu (Home, User Guide, Developer Guide, Historical, KEPs) is
  configured under `menu.main` in `hugo.yaml` — do not edit it per page

Adding a Markdown file under `content/` is enough for it to appear; there is no
separate list to update. Do not put an ordering prefix in the title.

## Front Matter Conventions

```yaml
---
title: "Proof Slicing"
weight: 40
author: "Arne Keller"
date: 2026-06-11
date_label: "June 2026"
valid_for: "KeY-2.12.0"
updated: "June 2026"
approved: mu 2026-06-19
---
```

- `title` is required and is rendered as the page `<h1>`. **Do not add a body
  `#` heading**; start with `##`.
- `weight` is required in practice (see above).
- `date` must be ISO `YYYY-MM-DD`; use `date_label` for human-readable dates.
- `author`, `valid_for`, `updated` feed the author metadata line.
- `aliases` preserves old URLs after a rename.

## Review Badge Infrastructure

The badge is derived from `approved` and rendered by
`layouts/_partials/custom/content-begin.html` and `content-end.html`; styling
lives in `assets/css/custom.css`.

| Front matter | Result |
| :----------- | :----- |
| missing or empty | amber "not yet verified" pill at the top |
| `approved: mu 2026-06-19` | green footer note naming reviewer and date |
| `approved: mu` + `approved-on: 2026-06-19` | same note using `approved-on` |
| `approved: none` | no badge (generated and index pages) |

Agent rules:

- Do not invent reviewer initials or approval dates.
- Do not copy an `approved` line from another page.
- Do not add or change `approved:` unless the task explicitly asks for it.
- Generated pages keep `approved: none`.

## Markdown And Site Features

Enabled and in active use:

- tables, footnotes, definition lists, task lists, strikethrough
- raw HTML (`unsafe: true`); use sparingly
- attribute lists and explicit heading anchors (`## Title {#anchor}`)
- callouts with titles: `{{</* callout type="info" title="…" */>}}`
- collapsible details: `{{%/* details title="…" */%}}`
- tabs: `{{</* tabs */>}}` with `{{</* tab name="…" */>}}`
- shared snippets from `assets/`: `{{</* snippet "snippets/…" */>}}`
- citations: `{{</* cite "KEY" */>}}`, reference lists:
  `{{</* bibliography */>}}`
- icons: `{{</* icon "check-circle" */>}}`
- Mermaid diagrams in ```` ```mermaid ```` fences
- MathJax math via `$…$` and `$$…$$` only

Preserve existing style and shortcode usage unless there is a good reason to
simplify it.

## Code Fencing

Prism highlights in the browser. Use the correct fence language:

| Fence | Use for |
| :---- | :------ |
| `java` | Java source |
| `jml` | Java with JML specifications|
| `key` | KeY problem files and taclets |
| `python`, `bash`, `yaml`, `json` | scripts and configuration |
| `javascript`, `js` | JavaScript source |
| `markdown` | Markdown examples |
| `text` | plain text, ASCII art, output |
| `diff-<lang>` | diffs, using `<lang>` for unchanged/changed lines (e.g. `diff-java`, `diff-key`) |

Additional bundled grammars: `c`, `cpp`, `css`, `html`/`xml`, `latex`, `groovy`,
`ocaml`, `properties`; `shell`/`sh` alias `bash`. Do not invent fence names and
expect highlighting.

## Math Rules

- Inline: `$…$`; display: `$$…$$` on their own lines.
- Never use `\(…\)` or `\[…\]`: KeY program modalities use that syntax and must
  remain literal.
- Inline code and fenced code are not math; do not escape dollar signs there.

## Citations

- The bibliography is generated from `refs.bib` into `data/refs.json` by
  `scripts/bib_to_json.py` (standard library only). `scripts/requirements.txt`
  only covers the one-off migration helpers.
- Cite by BibTeX key; unknown keys render `[KEY]` and produce a build warning.
  Fix the warning instead of ignoring it.
- Keep the `{{< bibliography >}}` list on reference pages, not on every page.

## Generated And Semi-Generated Content

`content/user/proof-scripts/commands.md` is generated from the KeY nightly
build. CI tries to download it (best effort; currently the checked-in copy is
used), strips the obsolete generator stylesheet and forces `approved: none`. Signals that a page may be generated:

- `approved: none`
- generated metadata or timestamps
- `content/user/proof-scripts/*` files overwritten by CI

Before rewriting such a page, change the generator or the CI post-processing
step instead. Do not hand-edit generated pages.

## CI And Publishing

Defined in `.github/workflows/pages.yaml`:

- triggers: push and pull request on `master`/`main`, weekly schedule,
  `workflow_dispatch`
- steps: full-history checkout → Go 1.27.x → fetch the nightly
  `varcond-script-docs` artifact (best effort) → unpack into
  `content/user/proof-scripts/` → post-process `commands.md` → Hugo extended
  0.170.0 → `hugo --gc --minify --baseURL …` → upload `./public`
- deploy job runs only from `master`

Pull requests get the same build as a check. The site is published at
<https://keyproject.github.io/key-docs/>.

## Safe Editing Guidance

Usually safe:

- fix wording, typos, formatting and broken local links in active docs
- improve structure inside an existing active page
- add or adjust `weight` for active pages
- update CSS, layouts or shortcodes when working on site presentation
- update the CI workflow or `Makefile` for build/tooling changes

Use caution for:

- generated pages under `content/user/proof-scripts/`
- historical sections (`content/historical/`)
- `disabled/` and `share/` (not published; verify intent first)
- any change that alters visible badge behavior across the whole site
- broad content reorganisations that break URLs without aliases

## Verification Checklist

For meaningful documentation or infrastructure changes:

1. `hugo mod tidy` and confirm `git diff --exit-code go.mod go.sum` is clean
2. `make build` — must exit 0 with no errors or warnings
3. `make check` — scratch build plus internal link check must pass
4. spot-check the rendered page in `make serve` if layout, shortcode or front
   matter changed
5. confirm the build docs and workflow contain no references to the retired
   static-site generator that preceded Hugo

## Common Pitfalls

- adding a body `#` heading — the title already is the `<h1>`
- forgetting `weight`, so the page silently jumps to the top of the sidebar
- using `date: June 2023` instead of `date_label`
- writing `\(…\)` or `\[…\]` as math delimiters
- linking to `index.md` instead of the directory URL
- putting bundle images in `static/` and referencing them relatively
- editing `public/`, `resources/` or generated proof-script pages
- inventing or copying `approved:` metadata
- treating historical pages as current product documentation

## Scope Reminder

Keep guidance specific to this repository.
Do not assume access to, or rely on, the main KeY code repository when editing
this repo.
