# key-docs

Documentation for the [KeY Theorem Prover](https://github.com/KeYProject/key),
published at <https://keyproject.github.io/key-docs/>.

*Author: Alexander Weigl <weigl@kit.edu>*

The site is built with [Hugo](https://gohugo.io/) and the
[Hextra](https://imfing.github.io/hextra/) theme. Hextra is consumed as a Hugo
module and pinned in `go.mod`; there is no theme checkout to maintain.

## Requirements

- [Hugo extended](https://gohugo.io/installation/) **0.170.0** (the version used
  by CI; any recent extended build works)
- [Go](https://go.dev/dl/) **1.27** or newer, for Hugo modules
- Git
- [lychee](https://github.com/lycheeverse/lychee#installation), optional, for
  `make check`

## Local build and preview

```bash
make prepare   # hugo mod tidy: resolve/download the pinned theme module
make serve     # live preview on http://localhost:1313
make build     # production build into public/
make check     # build into /tmp/keydocs-check and check internal links
```

The underlying commands are `hugo mod tidy`,
`hugo server --logLevel debug --disableFastRender -p 1313`,
`hugo --gc --minify` and a scratch build followed by `lychee`. `make check`
resolves every internal link against the generated site (anchors are not
verified) and fails with an explanatory message if lychee is not installed.
Never edit files under `public/` or `resources/`; they are regenerated.

A detailed authoring guide with live examples lives at
[Developer Guide → Writing Documentation](content/devel/writing-documentation/index.md)
(published at `/devel/writing-documentation/`).

## Repository layout

| Path | Purpose |
| :--- | :------ |
| `content/` | All pages. Directory structure determines URLs. |
| `hugo.yaml` | Site configuration: menus, base URL, Markdown, math, search. |
| `layouts/` | Theme overrides: callout, snippet, citation, badges, Prism, MathJax. |
| `assets/` | Processed by Hugo: shared snippets, CSS, Prism grammars. |
| `static/` | Copied verbatim: images, PDFs, XML schemas, downloads. |
| `data/refs.json` | Bibliography database used by citations. |
| `scripts/` | Migration and bibliography helpers (not needed to build). |
| `go.mod`, `go.sum` | Pin the Hextra version (currently v0.13.0). |
| `.github/workflows/pages.yaml` | CI build and GitHub Pages deployment. |

## Writing content

Pages live under `content/`; `content/user/faq.md` becomes `/user/faq/`.

- **Regular page**: a single `.md` file.
- **Section landing page**: `_index.md` in a directory; its title and `weight`
  place the section in the sidebar.
- **Leaf bundle**: a directory with `index.md` plus its images/downloads, e.g.
  `content/user/getting-started/loading/index.md`. Reference assets relatively
  (`./figure.png`, `./quicktour.zip`).

Every page starts with YAML front matter:

```yaml
---
title: "Proof Slicing"
weight: 40
author: "Arne Keller"
date: 2026-06-11
date_label: "June 2026"
valid_for: "KeY-2.12.0"
approved: mu 2026-06-19
---
```

- `title` is the only page heading; do **not** add a `#` heading in the body.
  Start the body with `##`.
- `weight` orders sibling pages ascending. Set it on every page and leave gaps
  (10, 20, 30, …). A missing weight sorts to the top.
- `author`, `date_label`, `valid_for` and `updated` render in the author line.
  `date` must be an ISO `YYYY-MM-DD`; use `date_label` for free text.
- The sidebar is generated from the content tree — there is no navigation file
  to edit. Only the main menu is configured under `menu.main` in `hugo.yaml`.
- Use lowercase hyphenated file names. When renaming, add
  `aliases: ["/user/old-name/"]` to keep old URLs working.

### Review badges and author metadata

The review state comes from the `approved` field:

| Front matter | Rendered result |
| :----------- | :-------------- |
| missing/empty | Amber `⚠ not yet verified` pill at the top |
| `approved: mu 2026-06-19` | Green footer note naming reviewer and date |
| `approved: mu` + `approved-on: 2026-06-19` | Same note, date from `approved-on` |
| `approved: none` | No badge (generated and index pages) |

Only the person who actually reviewed a page may be named. Do not invent
initials or copy an `approved` line from another page. Generated pages keep
`approved: none`.

### Shortcodes

| Shortcode | Use |
| :-------- | :-- |
| `{{</* callout type="info" title="…" */>}} … {{</* /callout */>}}` | Coloured box; types `default`, `info`, `warning`, `error`, `important`, plus optional `title`, `icon`, `emoji` |
| `{{%/* details title="…" */%}} … {{%/* /details */%}}` | Collapsible aside (`closed="true"` starts collapsed) |
| `{{</* tabs */>}}` / `{{</* tab name="…" */>}}` | Tabbed alternatives |
| `{{</* snippet "snippets/costband-table.md" */>}}` | Include a Markdown file from `assets/` |
| `{{</* cite "KeYBook2016" */>}}` | Inline citation from `data/refs.json` |
| `{{</* bibliography */>}}` | Reference list with `#ref-KEY` anchors |
| `{{</* icon "check-circle" */>}}` | Inline icon |

Cite with the BibTeX key; the bibliography renders every entry sorted by key.
An unknown key renders as `[KEY]` and emits a build warning. `refs.bib` is the
source for `data/refs.json`, which is regenerated with
`scripts/bib_to_json.py` (see `scripts/requirements.txt`).

## Code, math and diagrams

Code fences are highlighted in the browser by Prism. Wired languages include
`java`, `jml`, `key`, `python`, `bash`/`shell`, `yaml`, `json`, `markdown`,
`text`, `c`, `cpp`, `css`, `html`/`xml`, `latex`, `groovy`, `ocaml` and
`properties`. Unknown languages render uncoloured but do not fail the build.

Math is typeset by MathJax with exactly two delimiter pairs: `$…$` inline and
`$$…$$` display. Do **not** use `\(…\)` or `\[…\]`: KeY program modalities are
written that way and must stay literal.

A fenced `mermaid` block becomes a diagram; no front-matter flag is needed.

## Images and downloads

Put page-specific assets in the leaf bundle and link them relatively. Shared
assets live under `static/` and are linked with absolute paths, e.g.
`/images/key.png`, `/devel/KeYCodeStyle.xml`, `/old/Architecture.pdf` or
`/smt/smtDoc.pdf`. Markdown images with a title render as captioned figures.

## CI and deployment

`.github/workflows/pages.yaml` builds and deploys the site:

- on pushes to `master` and `main`, on pull requests targeting either branch,
  on a weekly schedule, and on manual dispatch;
- checks out full history (`fetch-depth: 0`) for `enableGitInfo`;
- installs Go 1.27.x and Hugo extended 0.170.0;
- downloads the `varcond-script-docs` artifact from the latest successful
  nightly build of `KeYProject/key` and unpacks it into
  `content/user/proof-scripts/` (fault-tolerant: the checked-in copy is used
  when the artifact is unavailable);
- strips the generator's obsolete stylesheet from `commands.md` and keeps
  `approved: none`;
- builds with `hugo --gc --minify --baseURL …` and uploads `./public`;
- deploys to GitHub Pages only from `master`.

Pushes to `master` publish automatically. Pull requests run the same build as a
check, so a broken shortcode, unknown citation key or invalid front matter is
caught before merging. Run `make check` locally before pushing.
