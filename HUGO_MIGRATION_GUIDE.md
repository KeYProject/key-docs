# MkDocs to Hugo Migration Guide for KeY Documentation

This document provides a comprehensive guide for migrating the KeY documentation from MkDocs (Material theme) to Hugo with the Docsy theme.

## 1. Configuration Mapping

### MkDocs → Hugo Equivalents

| MkDocs Feature | Hugo Equivalent | Status |
|----------------|-----------------|--------|
| `site_name` | `title` in hugo.toml | ✅ Mapped |
| `site_url` | `baseURL` in hugo.toml | ✅ Mapped |
| `theme: material` | `theme = ['docsy']` | ✅ Mapped |
| `plugins.search` | Docsy offline search | ✅ Configured |
| `plugins.mermaid2` | Mermaid shortcode + JS | ✅ Created |
| `plugins.bibtex` | Custom cite shortcode | ✅ Created |
| `markdown_extensions.*` | Goldmark config | ✅ Mapped |
| `extra_javascript` | Partial hooks/head-end.html | ✅ Migrated |
| `extra_css` | static/css/extra.css | ✅ Migrated |
| `nav` | Hugo menus + section structure | ✅ Planned |

## 2. Directory Structure Conversion

### Current MkDocs Structure
```
key-docs/
├── mkdocs.yml
├── docs/
│   ├── index.md
│   ├── user/
│   │   └── *.md
│   ├── devel/
│   │   └── *.md
│   ├── quicktour/
│   │   └── *.md
│   ├── eclipse/
│   │   └── *.md
│   ├── keps/
│   │   └── *.md
│   └── smt/
│       └── *.md
├── refs.bib
└── includes/
```

### New Hugo Structure
```
key-docs/
├── hugo.toml                    # Main configuration
├── content/                     # All Markdown content
│   ├── _index.md               # Homepage
│   ├── user/                   # User Guide section
│   │   ├── _index.md          # Section index
│   │   └── *.md               # Content pages
│   ├── devel/                  # Developer Guide
│   ├── quicktour/              # Quick Tour
│   ├── eclipse/                # Historical (Eclipse plugins)
│   ├── keps/                   # KeY Enhancement Proposals
│   └── smt/                    # SMT Solver docs
├── data/                       # Data files
│   └── refs.json              # Bibliography (converted from refs.bib)
├── static/                     # Static assets
│   ├── img/                   # Images (copied from docs/)
│   ├── css/
│   │   └── extra.css         # Custom styles
│   └── js/                    # Custom JavaScript
├── layouts/                    # Custom templates
│   ├── partials/
│   │   └── hooks/
│   │       └── head-end.html # Head injection
│   └── shortcodes/            # Custom shortcodes
│       ├── mermaid.html      # Mermaid diagrams
│       ├── cite.html         # Citations
│       └── math.html         # Math expressions
├── archetypes/                 # Content templates
│   ├── default.md
│   └── docs.md
└── assets/                     # SCSS/JS for bundling
    ├── scss/
    └── js/
```

### Migration Commands

```bash
# Copy all content from docs/ to content/
cp -r docs/* content/

# Move images to static/img
find docs -name "*.png" -o -name "*.jpg" -o -name "*.svg" | while read file; do
  dest="static/img/$(basename $file)"
  cp "$file" "$dest"
done
```

## 3. Hugo Modules & Dependencies

### Required Hugo Modules

The following modules are configured in `hugo.toml`:

```toml
[module]
  [[module.imports]]
    path = 'github.com/google/docsy'
  [[module.imports]]
    path = 'github.com/google/docsy/dependencies'
```

### Feature Replacements

#### Search (MkDocs `search` plugin)
- **Hugo Equivalent**: Docsy offline search
- **Configuration**: 
  ```toml
  [outputs]
    home = ['HTML', 'RSS', 'searchIndex']
  
  [params]
    offlineSearch = true
  ```

#### Mermaid Diagrams (MkDocs `mermaid2` plugin)
- **Hugo Equivalent**: Custom shortcode + CDN
- **Usage**:
  ```markdown
  {{</* mermaid */>}}
  graph TD;
      A-->B;
      A-->C;
  {{</* /mermaid */>}}
  ```
- **Implementation**: `layouts/shortcodes/mermaid.html`

#### BibTeX Citations (MkDocs `bibtex` plugin)
- **Hugo Equivalent**: Custom cite shortcode
- **Usage**:
  ```markdown
  According to {{</* cite "KeYBook2016" */>}}, ...
  ```
- **Implementation**: `layouts/shortcodes/cite.html`
- **Data Source**: `data/refs.bib` (or converted JSON)

#### Math Expressions (pymdownx.arithmatex + MathJax)
- **Hugo Equivalent**: Goldmark passthrough + MathJax
- **Inline**: `$E = mc^2$`
- **Display**: `$$E = mc^2$$`
- **Configuration**: In `hugo.toml` markup.goldmark section