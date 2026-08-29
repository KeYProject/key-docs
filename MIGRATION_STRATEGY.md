# MkDocs to Hugo Migration Strategy

**Document Purpose:** Comprehensive plan for migrating KeY documentation from MkDocs (Material theme) to Hugo static site generator.

**Date:** 2026-08-23  
**Status:** Planning Phase

---

## Executive Summary

This document outlines the complete migration strategy for converting the KeY project documentation from MkDocs (with Material theme and various plugins) to Hugo. The migration involves:

- **97 markdown files** across 5 major sections
- **Complex navigation hierarchy** with 4 top-level sections
- **Multiple MkDocs-specific features** requiring conversion
- **Custom Python hooks** for approval/author metadata
- **BibTeX citations** via mkdocs-bibtex plugin
- **Mermaid diagrams**, **math expressions**, **admonitions**, **tabs**, and **footnotes**

---

## 1. Current State Analysis

### 1.1 File Inventory

**Total Markdown Files:** 97 files

```
docs/
├── index.md                           # Home page
├── changelog.md                       # Release notes
├── quicktour/                         # 5 files - Getting started
│   ├── index.md, install.md, loading.md, proving.md, appendix.md
├── user/                              # ~35 files - User Guide
│   ├── index.md, FAQ.md, ADTs.md, Classpath.md, etc.
│   ├── ProofScripts/                  # 8 files
│   ├── SupportedFeatures/             # 1 file
│   ├── IsabelleTranslation/, LLM/, SMT/, TacletMatchDialog/, UiFeatures/, ProofCaching/, ProofSlicing/
├── devel/                             # ~45 files - Developer Guide
│   ├── index.md, Architecture.md, Gradle.md, CodingConventions.md, etc.
│   ├── howto/                         # 8 files
│   ├── Testing/                       # 6 files
│   └── rpc/                           # 1 file
├── eclipse/                           # 10 files - Historical Eclipse plugins
│   └── CrossProject/, JMLEditing/, KeYIDE/, KeYResources/, MonKeY/, SED/, Stubby/, VisualDbC/, Starter/
├── keps/                              # 3 files - KeY Enhancement Proposals
│   └── kep-0001-taclet-generating-transformers/
└── includes/                          # Reusable content snippets
```

### 1.2 Navigation Hierarchy (from mkdocs.yml)

```
Home (index.md)
├── User Guide
│   ├── Welcome (user/index.md)
│   ├── 1. Getting Started
│   │   ├── Quicktour, Installation, Loading, Proving, Appendix
│   ├── 2. Working with the Prover
│   │   ├── UI Features, Taclet Match Dialog, Interactive, Exploration, NodeDiff, 
│   │   ├── ProofTreeLinearMode, ProofCaching, ProofSlicing
│   ├── 3. Structuring Verification Projects
│   │   ├── Classpath, RemoveGenerics, ADTs, JavaDLinJML
│   ├── 4. Proof Scripts (8 sub-pages)
│   ├── 5. SMT Solvers
│   ├── 6. Bridges to Other Tools (Isabelle, LLM)
│   ├── 7. Language Reference (JML, KeyGrammar, JavaGrammar)
│   ├── 8. Supported Features (JavaCoverage)
│   ├── 9. FAQ
│   └── Release Notes (changelog.md)
├── Developer Guide
│   ├── Welcome, Architecture, Gradle
│   ├── 3. Working on the Code (CodingConventions, Spotless, Logging, ThreadSafety)
│   ├── 4. Extending KeY (HowTos, Taclets, GUI, Scripts, SMT, Listeners)
│   ├── 5. Using KeY as a Library (ExternalProject, RPC)
│   ├── 6. Internals (Pipeline, Matching, Costs, Multithreading, Parser, Terms, 
│   │       ProofLoadSave, SMTTranslation, CounterExample, How2ExtRecoder)
│   ├── 7. Testing (6 sub-pages)
│   ├── 8. Writing Documentation
│   └── 9. Appendices (StrategyCostTables)
├── Historical
│   └── Eclipse plugins (10 sub-pages)
└── KeY Enhancement Proposals
    ├── About KEPs
    └── KEP-1: Taclet-Generating Transformers
```

### 1.3 MkDocs Configuration Analysis

**Plugins Used:**
- `search` - Built-in search
- `mermaid2` - Mermaid diagram rendering
- `bibtex` - BibTeX citations (refs.bib with 200+ entries)

**Markdown Extensions:**
| Extension | Usage | Hugo Equivalent |
|-----------|-------|-----------------|
| `admonition` | `!!! note`, `!!! warning`, etc. | Hugo alerts/callouts or custom shortcode |
| `pymdownx.tabbed` | `=== "Tab Name"` | Hugo tabs shortcode |
| `pymdownx.superfences` (mermaid) | ```mermaid blocks | Hugo mermaid shortcode |
| `footnotes` | `[^1]` syntax | Native Hugo support |
| `tables` | Standard Markdown tables | Native Hugo support |
| `toc` | Auto-generated TOC | Hugo `.TableOfContents` |
| `attr_list` | `{#id}` attributes | Hugo goldmark config |
| `def_list` | Definition lists | Hugo goldmark config |
| `pymdownx.arithmatex` | MathJax `$...$`, `$$...$$` | Hugo math shortcode or KaTeX |
| `pymdownx.emoji` | `:material-icon:` | Hugo emoji support or custom mapping |
| `meta` | Front matter | Native Hugo front matter |
| `md_in_html` | Markdown inside HTML | Hugo passthrough config |

**Hooks:**
- `approval.py` - Review status badges (green/amber)
- `author.py` - Author metadata display below title

**Theme Features (Material):**
- Navigation tabs
- Content code annotations
- Content tabs link
- Dark/light mode toggle
- Edit links to GitHub

---

## 2. Feature Conversion Plan

### 2.1 Admonitions → Hugo Alerts

**Current MkDocs Syntax:**
```markdown
!!! note "Optional Title"
    Content here
```

**Hugo Target:**
```markdown
{{% alert type="info" title="Optional Title" %}}
Content here
{{% /alert %}}
```

**Implementation:** Create `layouts/shortcodes/alert.html` with Bootstrap-style classes

**Type Mapping:**
- `note`, `abstract`, `question` → `info` (blue)
- `tip`, `success` → `success` (green)
- `warning` → `warning` (orange)
- `failure`, `danger`, `bug` → `danger` (red)
- `example` → `primary` (purple)
- `quote` → `secondary` (gray)

### 2.2 Tabs → Hugo Tabs Shortcode

**Current MkDocs Syntax:**
```markdown
=== "C"
    ```c
    int main() { return 0; }
    ```

=== "C++"
    ```cpp
    int main() { return 0; }
    ```
```

**Hugo Target:**
```markdown
{{< tabs >}}
{{% tab title="C" %}}
```c
int main() { return 0; }
```
{{% /tab %}}
{{% tab title="C++" %}}
```cpp
int main() { return 0; }
```
{{% /tab %}}
{{< /tabs >}}
```

**Implementation:** Use Hugo's built-in tabs shortcode (0.129+) or create custom

### 2.3 Mermaid Diagrams → Hugo Mermaid Shortcode

**Files with Mermaid (4):**
- `docs/devel/Architecture.md`
- `docs/devel/Multithreading.md`
- `docs/devel/RuleApplicationPipeline.md`
- `docs/devel/SMTTranslation.md`

**Conversion:** 
```markdown
```mermaid
flowchart TB
    A --> B
```
```
→
```markdown
{{< mermaid >}}
flowchart TB
    A --> B
{{< /mermaid >}}
```

### 2.4 BibTeX Citations → Hugo Bibliography

**Current:** `[@JMLReferenceManual11]` and `\full_bibliography`

**Target:** `{{< bibcite "JMLReferenceManual11" >}}` and `{{< bibliography >}}`

**Implementation:** 
- Keep `refs.bib` (200+ entries)
- Create `bibcite.html` and `bibliography.html` shortcodes
- Use `github.com/peaceiris/hugo-bibtex` module

### 2.5 MathJax → Hugo Math Support

**Current:** `$...$` and `$$...$$` with MathJax 2.7

**Target:** Same syntax with MathJax 3 via Hugo passthrough

**Configuration in hugo.toml:**
```toml
[markup.goldmark.extensions.passthrough]
enable = true
[markup.goldmark.extensions.passthrough.delimiters]
block = [['$$', '$$']]
inline = [['$', '$']]
```

### 2.6 Footnotes → Hugo Native

No changes needed - Hugo supports `[^1]` natively

### 2.7 Emoji → Custom Icon Shortcode

**Current:** `:material-check:`, `:octicons-tag-24:`

**Target:** `{{< icon "check" >}}` using SVG sprites

### 2.8 Tables → Hugo Native

No changes needed - Hugo supports standard Markdown tables

---

## 3. Hooks Conversion Strategy

### 3.1 approval.py → Hugo Frontmatter + Shortcode

**Current Behavior:**
- Reads `approved` field from front matter
- Shows green badge in footer if approved
- Shows amber "not yet verified" badge at top if missing

**MkDocs Example:**
```yaml
---
approved: rb 2026-06-11
---
```

**Hugo Target:**
```yaml
---
title: "Page Title"
approved_by: "rb"
approved_on: "2026-06-11"
# or approved_status: "none" to disable
---
```

**Implementation:**
- Create `layouts/shortcodes/approval-badge.html`
- Place missing badge after H1 via layout partial
- Show approved badge in page footer partial

### 3.2 author.py → Hugo Frontmatter + Partial

**Current Behavior:**
- Displays author info right-aligned below page title

**MkDocs Example:**
```yaml
---
author: "Nils Buchholz"
date: "February 2025"
valid_for: "KeY 2.12.3"
---
```

**Hugo Target:**
```yaml
---
title: "Page Title"
author: "Nils Buchholz"
date: "2025-02-01"
valid_for: "KeY 2.12.3"
updated: "2023-11-01"
---
```

**Implementation:**
- Create `layouts/partials/page-author.html`
- Hook into `layouts/_default/single.html` after `<h1>`

---

## 4. Frontmatter Strategy

### 4.1 Required Fields

All pages should have:
```yaml
---
title: "Page Title"           # Required
weight: 10                     # Sort order
draft: false                   # Hide from build
approved_by: ""                # From approval.py
approved_on: ""                # From approval.py
author: ""                     # From author.py
date: ""                       # From author.py
valid_for: ""                  # From author.py
updated: ""                    # From author.py
description: ""                # SEO meta
tags: []                       # Taxonomy
categories: []                 # Taxonomy
---
```

### 4.2 Page Type Examples

**Home Page:**
```yaml
---
title: "Overview"
approved_by: "wp,dd,rb,rh"
approved_on: "2026-06-11"
---
```

**User Guide:**
```yaml
---
title: "JML Grammar"
author: "Alexander Weigl"
date: "2023-09-24"
valid_for: "KeY 2.12.3"
weight: 70
---
```

**KEP Pages:**
```yaml
---
title: "KEP-1: Taclet-Generating Transformers"
kep_number: 1
status: "draft"
authors: ["Author Name"]
created: "2024-01-01"
---
```

---

## 5. Navigation & Menu Structure

### 5.1 Hugo Menu Configuration

```toml
# hugo.toml
[[menu.main]]
  name = "Home"
  pageRef = "/"
  weight = 10

[[menu.main]]
  name = "User Guide"
  pageRef = "/user/"
  weight = 20

[[menu.main]]
  name = "Developer Guide"
  pageRef = "/devel/"
  weight = 30

[[menu.main]]
  name = "Historical"
  pageRef = "/eclipse/"
  weight = 40

[[menu.main]]
  name = "KEPs"
  pageRef = "/keps/"
  weight = 50
```

### 5.2 Section Organization

```
content/
├── _index.md                    # Home
├── changelog.md
├── quicktour/
│   ├── _index.md
│   ├── install.md
│   └── ...
├── user/
│   ├── _index.md
│   └── ...
├── devel/
│   ├── _index.md
│   └── ...
├── eclipse/
│   └── ...
└── keps/
    └── ...
```

---

## 6. URL Structure & Link Migration

### 6.1 Permalink Configuration

```toml
# hugo.toml
[permalinks]
page = "/:sections[1:]/:slug/"
section = "/:sections[1:]/"
```

### 6.2 Internal Link Updates

**Current MkDocs:**
```markdown
[UI Features](UiFeatures/)
[Architecture](../devel/Architecture/)
```

**Hugo Target:**
```markdown
[UI Features]({{< relref "user/uifeatures" >}})
[Architecture]({{< relref "devel/architecture" >}})
```

**Migration Script:** Automated link converter using regex

---

## 7. Theme & Styling

### 7.1 Recommended Theme

**Primary Choice:** Hugo Docsy (designed for documentation)
- Built-in navigation
- Search integration
- Responsive design
- Active maintenance

**Alternative:** Hugo Blox (formerly Wowchemy)

### 7.2 CSS Structure

```
assets/scss/
├── _variables.scss
├── approval.scss       # Badge styles
├── alerts.scss         # Alert/admonition styles
├── tabs.scss           # Tab component
└── main.scss
```

### 7.3 Dark Mode

Implement via CSS variables with toggle button in header partial

---

## 8. Migration Scripts

### 8.1 Script Inventory

Create Python scripts in `scripts/`:

| Script | Purpose |
|--------|---------||
| `migrate_frontmatter.py` | Add Hugo frontmatter |
| `convert_admonitions.py` | `!!!` → `{{% alert %}}` |
| `convert_tabs.py` | `===` → `{{< tabs >}}` |
| `convert_mermaid.py` | ````mermaid` → `{{< mermaid >}}` |
| `convert_citations.py` | `[@key]` → `{{< bibcite >}}` |
| `convert_links.py` | Update internal links |
| `organize_files.py` | Move to `content/` structure |
| `validate_migration.py` | Check for issues |

### 8.2 Sample: convert_admonitions.py

```python
#!/usr/bin/env python3
import re

ADMONITION_MAP = {
    'note': 'info', 'abstract': 'info', 'tip': 'success',
    'warning': 'warning', 'danger': 'danger', 'failure': 'danger',
}

def convert_admonitions(content):
    pattern = r'^!!!\s+(\w+)(?:\s+"([^"]*)")?\s*\n((?:    .*\n?)*)'
    
    def replacer(match):
        ad_type = ADMONITION_MAP.get(match.group(1), 'info')
        title = match.group(2) or ''
        body = re.sub(r'^    ', '', match.group(3), flags=re.MULTILINE)
        
        if title:
            return f'{{{{% alert type="{ad_type}" title="{title}" %}}}}\n{body}{{{{% /alert %}}}}\n'
        return f'{{{{% alert type="{ad_type}" %}}}}\n{body}{{{{% /alert %}}}}\n'
    
    return re.sub(pattern, replacer, content, flags=re.MULTILINE)
```

---

## 9. Implementation Phases

### Phase 1: Foundation (Week 1-2)
- [ ] Set up Hugo project structure
- [ ] Choose and configure base theme (Docsy)
- [ ] Create custom shortcodes (alert, tabs, mermaid, bibcite)
- [ ] Configure hugo.toml (menus, permalinks, markup)
- [ ] Set up asset pipeline (SCSS, JS)

### Phase 2: Content Migration Scripts (Week 2-3)
- [ ] Write all migration scripts
- [ ] Test on sample files (5-10 pages)
- [ ] Refine based on test results

### Phase 3: Batch Conversion (Week 3-4)
- [ ] Run scripts on all 97 files
- [ ] Move files to `content/` structure
- [ ] Fix conversion errors
- [ ] Validate all internal links

### Phase 4: Theme Customization (Week 4-5)
- [ ] Implement approval badge display
- [ ] Implement author metadata display
- [ ] Style components to match Material design
- [ ] Add dark mode toggle
- [ ] Implement search (Fuse.js or Algolia)

### Phase 5: Testing & Validation (Week 5-6)
- [ ] Manual review of all pages
- [ ] Check mermaid diagrams (4 files)
- [ ] Verify citations work
- [ ] Test responsive design
- [ ] Performance testing

### Phase 6: Deployment (Week 6)
- [ ] Set up GitHub Actions for Hugo build
- [ ] Configure GitHub Pages deployment
- [ ] Set up preview deployments for PRs
- [ ] Update documentation links

---

## 10. Risk Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Complex tab conversions fail | Medium | Manual review of converted files |
| Citation system breaks | High | Test early with refs.bib |
| Internal links break | High | Automated link checker |
| Loss of approval badges | Medium | Implement before migration |
| Mermaid diagrams don't render | Low | Test with 4 known files first |
| SEO ranking drops | Medium | Proper 301 redirects from old URLs |

---

## 11. Success Criteria

- ✅ All 97 pages migrated successfully
- ✅ Navigation structure preserved
- ✅ All internal links working
- ✅ Mermaid diagrams rendering (4 files)
- ✅ Citations working (refs.bib integration)
- ✅ Approval badges displaying
- ✅ Author metadata showing
- ✅ Mobile-responsive design
- ✅ Search functionality working
- ✅ Build time < 30 seconds

---

## 12. Next Steps

1. **Review this strategy** with KeY team
2. **Select Hugo theme** (Docsy recommended)
3. **Set up development environment**
4. **Create proof-of-concept** with 5 sample pages
5. **Refine migration scripts** based on POC learnings
6. **Begin Phase 1 implementation**

---

## Appendix A: File Count by Section

| Section | File Count |
|---------|-----------||
| Home | 1 |
| Changelog | 1 |
| Quicktour | 5 |
| User Guide | ~35 |
| Developer Guide | ~45 |
| Eclipse (Historical) | 10 |
| KEPs | 3 |
| **Total** | **97** |

## Appendix B: Special Features by File

**Mermaid (4 files):**
- `devel/Architecture.md`, `devel/Multithreading.md`
- `devel/RuleApplicationPipeline.md`, `devel/SMTTranslation.md`

**Tabs (14+ files):**
- `devel/howtodoc/index.md` (extensive), `devel/AddingSMTSolvers.md`
- `devel/ExtendingKeY.md`, `devel/HowToTaclet.md`, `devel/NewKeyParser.md`
- `user/JMLGrammar.md`, `user/JavaGrammar.md`, `user/ADTs.md`, etc.

**Math (3+ files):**
- `devel/howtodoc/index.md`, `user/ADTs.md`, `devel/HowToTaclet.md`

**Citations:**
- `quicktour/index.md` (uses `\full_bibliography`)
- `devel/ThreadSafety.md`, `devel/HowToTaclet.md`

**Footnotes:**
- `devel/howtodoc/index.md`, `devel/Gradle.md`
- `devel/ThreadSafety.md`, `devel/HowToTaclet.md`

---

*Document Version: 1.0*  
*Last Updated: 2026-08-23*
