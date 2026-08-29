# Hugo Project Structure for KeY Documentation

This document describes the complete Hugo project structure migrated from MkDocs.

## Directory Structure

```
key-docs/
├── hugo.toml                 # Main Hugo configuration (see below)
├── content/                  # Markdown content files
│   ├── _index.md            # Home page
│   ├── user/                # User Guide section
│   │   ├── _index.md        # User Guide landing page
│   │   ├── quicktour/       # Quick tour subsection
│   │   ├── UiFeatures/      # UI Features
│   │   └── ...              # Other user guide sections
│   ├── devel/               # Developer Guide section
│   │   ├── _index.md        # Developer Guide landing page
│   │   ├── howto/           # How-to guides
│   │   ├── howtodoc/        # Documentation guidelines
│   │   ├── Testing/         # Testing documentation
│   │   ├── rpc/             # JSON-RPC interface
│   │   └── ...              # Other developer sections
│   ├── eclipse/             # Historical Eclipse plugins
│   │   ├── _index.md        # Historical section landing
│   │   ├── General/         # Cross-project basics
│   │   ├── SED/             # Symbolic Execution Debugger
│   │   └── ...              # Other historical plugins
│   ├── keps/                # KeY Enhancement Proposals
│   │   ├── _index.md        # KEPs overview
│   │   └── kep-0001-*/      # Individual KEPs
│   ├── quicktour/           # Quick tour (also under user/)
│   ├── changelog/           # Changelog
│   └── smt/                 # SMT solver documentation
│
├── layouts/                  # Custom templates and overrides
│   ├── _default/            # Default templates
│   ├── partials/            # Partial templates
│   │   └── hooks/           # Hugo hooks
│   │       └── head-end.html # Custom head content (MathJax, Mermaid)
│   └── shortcodes/          # Custom shortcodes
│       ├── mermaid.html     # Mermaid diagram shortcode
│       ├── cite.html        # Bibliography citation shortcode
│       ├── math.html        # Math expression shortcode
│       ├── hint.html        # Admonition/note shortcode
│       └── tab.html         # Tabbed content shortcode
│
├── static/                   # Static assets (copied as-is)
│   ├── img/                 # Images
│   │   └── key.png          # Logo/favicon
│   ├── css/                 # Custom CSS
│   │   └── extra.css        # Custom styles (from MkDocs)
│   └── js/                  # Custom JavaScript
│
├── assets/                   # Processed assets (SCSS, bundling)
│   ├── scss/                # SCSS stylesheets
│   └── js/                  # JavaScript to bundle
│
├── data/                     # Data files
│   └── refs.bib             # Bibliography database (from refs.bib)
│
├── archetypes/              # Content templates
│   ├── default.md           # Default archetype
│   └── docs.md              # Documentation page archetype
│
├── scripts/                  # Migration scripts
│   ├── convert_admonitions.py
│   ├── convert_citations.py
│   ├── convert_mermaid.py
│   ├── migrate_frontmatter.py
│   └── validate_migration.py
│
└── hooks/                    # MkDocs hooks (legacy, not used in Hugo)
    ├── approval.py
    └── author.py
```

## Configuration File: hugo.toml

The `hugo.toml` file contains:

### Basic Settings
- `baseURL = "https://keyproject.github.io/key-docs/"`
- `title = "KeY Documentation"`
- `theme = ["docsy"]`

### Markup Configuration (MkDocs markdown_extensions equivalent)
- **goldmark extensions**: definition lists, footnotes, tables, task lists, typographer
- **passthrough delimiters**: MathJax inline (`$`, `\(`) and display (`$$`, `\[`) 
- **highlight**: Code highlighting with Monokai style
- **tableOfContents**: Levels 2-3

### Module Configuration
- Docsy theme from `github.com/google/docsy`
- Docsy dependencies from `github.com/google/docsy/dependencies`

### Output Configuration
- Custom `searchIndex` output format for offline search
- Replaces MkDocs search plugin

### Theme Parameters
- **GitHub integration**: Repository URLs, edit links
- **Search**: Offline search enabled
- **UI/UX**: Breadcrumbs, sidebar, TOC settings
- **Mermaid**: Enabled for diagrams
- **Math**: MathJax enabled
- **Bibliography**: refs.bib configured
- **Dark mode**: Enabled
- **Branding**: Logo and favicon

### Menu Configuration
Direct mapping from mkdocs.yml nav:
- Home (/)
- User Guide (/user/)
- Developer Guide (/devel/)
- Historical (/eclipse/) - marked deprecated
- KEPs (/keps/)

## Shortcodes

### {{</* mermaid */>}}
Renders Mermaid diagrams:
```markdown
{{</* mermaid */>}}
graph TD;
    A-->B;
    A-->C;
{{</* /mermaid */>}}
```

### {{</* cite */>}}
Bibliographic citations:
```markdown
{{</* cite "author2020" */>}}
```

### {{</* hint */>}}
Admonitions (replaces MkDocs admonition):
```markdown
{{</* hint note */>}}
This is a note.
{{</* /hint */>}}

{{</* hint warning */>}}
This is a warning.
{{</* /hint */>}}
```

### {{</* math */>}}
Math expressions (alternative to passthrough):
```markdown
{{</* math */>}}
\sum_{i=1}^n i = \frac{n(n+1)}{2}
{{</* /math */>}}
```

## MkDocs to Hugo Feature Mapping

| MkDocs Feature | Hugo Equivalent |
|----------------|----------------|
| Material theme | Docsy theme |
| search plugin | offlineSearch + searchIndex output |
| mermaid2 plugin | mermaid.html shortcode + CDN |
| bibtex plugin | cite.html shortcode + data/refs.bib |
| pymdownx.arithmatex | MathJax via head-end.html |
| admonition | hint.html shortcode |
| pymdownx.tabbed | tab.html shortcode |
| toc permalink | Docsy toc_enable parameter |
| navigation.tabs | Docsy menu.main |
| navigation.sections | Section structure in content/ |
| extra_javascript | layouts/partials/hooks/head-end.html |
| extra_css | static/css/extra.css |
| edit_uri | github_repo + edit_page_path params |

## Building the Site

```bash
# Install Hugo extended (required for Docsy SCSS)
snap install hugo --channel=extended/stable

# Initialize Hugo modules
hugo mod get -u

# Run development server
hugo server -D

# Build for production
hugo
```

## Deployment

The site is configured for GitHub Pages at:
- URL: https://keyproject.github.io/key-docs/
- Deploy from: `public/` directory after `hugo` build

See `.github/workflows/` for CI/CD configuration.
