# MkDocs to Hugo Migration Scripts

This directory contains Python scripts for automating the migration of KeY documentation from MkDocs to Hugo.

## Prerequisites

```bash
pip install pyyaml
```

## Usage

### 1. Convert Admonitions

Converts MkDocs `!!! note` syntax to Hugo `{{% alert %}}` shortcodes.

```bash
# Single file
./convert_admonitions.py docs/user/FAQ.md

# Entire directory
./convert_admonitions.py --dir docs/
```

**Type Mapping:**
- `note`, `abstract` → `info`
- `tip`, `success` → `success`
- `warning` → `warning`
- `danger`, `failure`, `bug` → `danger`
- `example` → `primary`
- `quote` → `secondary`

---

### 2. Convert Mermaid Diagrams

Converts ```mermaid code blocks to Hugo `{{< mermaid >}}` shortcodes.

```bash
./convert_mermaid.py --dir docs/devel/
```

**Files affected:** 4 files
- `devel/Architecture.md`
- `devel/Multithreading.md`
- `devel/RuleApplicationPipeline.md`
- `devel/SMTTranslation.md`

---

### 3. Convert Citations

Converts BibTeX citations from `[@key]` to `{{< bibcite "key" >}}`.

```bash
./convert_citations.py --dir docs/
```

Also converts `\full_bibliography` → `{{< bibliography >}}`

---

### 4. Migrate Frontmatter

Migrates existing frontmatter to Hugo-compatible format.

```bash
./migrate_frontmatter.py --dir docs/
```

**Handles:**
- `approved: rb 2026-06-11` → `approved_by: rb`, `approved_on: 2026-06-11`
- Title extraction from H1 if missing
- Weight calculation based on filename
- Preserves author, date, valid_for, updated fields

---

### 5. Validate Migration

Checks for common issues after conversion.

```bash
./validate_migration.py --dir docs/
```

**Checks:**
- Unclosed shortcodes
- Missing frontmatter
- Remaining MkDocs syntax (`!!!`, `===`, ```mermaid)
- Links with .md extensions
- Invalid YAML

---

## Recommended Workflow

```bash
# Step 1: Backup original files
cp -r docs/ docs.backup/

# Step 2: Run conversions in order
./migrate_frontmatter.py --dir docs/
./convert_admonitions.py --dir docs/
./convert_mermaid.py --dir docs/
./convert_citations.py --dir docs/

# Step 3: Validate results
./validate_migration.py --dir docs/

# Step 4: Review warnings/errors and fix manually
```

---

## Manual Steps Required

These conversions require manual review:

1. **Tabs** (`=== "Tab Name"`) - Complex nested structure needs careful handling
2. **Internal links** - Update to use `{{< relref >}}` shortcode
3. **Emoji/icons** - `:material-icon:` needs custom shortcode
4. **File organization** - Move to Hugo `content/` structure
5. **Navigation** - Update menu configuration in `hugo.toml`

---

## Testing

After running scripts, test on sample files:

```bash
# Test on a few files first
./convert_admonitions.py docs/user/FAQ.md docs/devel/Gradle.md

# Review changes
git diff docs/user/FAQ.md

# If satisfied, run on all files
```

---

## Troubleshooting

### Script fails with encoding error
Ensure files are UTF-8 encoded:
```bash
file -i docs/**/*.md | grep -v utf-8
```

### YAML parsing errors
Check for invalid frontmatter:
```bash
python3 -c "import yaml; yaml.safe_load(open('docs/file.md').read().split('---')[1])"
```

### Regex doesn't match
Some admonitions may have unusual formatting. Check manually.

---

## Output Examples

### Before (MkDocs):
```markdown
!!! note "Version Information"
    This tutorial was tested for KeY version 2.10.

[@JMLReferenceManual11]

```mermaid
flowchart TB
    A --> B
```
```

### After (Hugo):
```markdown
{{% alert type="info" title="Version Information" %}}
This tutorial was tested for KeY version 2.10.
{{% /alert %}}

{{< bibcite "JMLReferenceManual11" >}}

{{< mermaid >}}
flowchart TB
    A --> B
{{< /mermaid >}}
```

---

*See MIGRATION_STRATEGY.md for complete migration plan*
