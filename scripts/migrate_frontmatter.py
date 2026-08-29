#!/usr/bin/env python3
"""
Migrate MkDocs frontmatter to Hugo-compatible frontmatter.

Handles:
- Existing YAML frontmatter preservation
- approved field splitting (approved_by, approved_on)
- author, date, valid_for, updated fields
- Title extraction from H1 if missing
- weight assignment based on navigation order
"""

import re
import sys
import yaml
from pathlib import Path


def extract_existing_frontmatter(content):
    """Extract existing YAML frontmatter if present."""
    match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
    if match:
        try:
            return yaml.safe_load(match.group(1)), match.end()
        except yaml.YAMLError as e:
            print(f"  Warning: YAML parse error: {e}")
            return {}, 0
    return {}, 0


def extract_title_from_content(content):
    """Extract title from first H1 heading."""
    match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    return None


def calculate_weight(filepath, nav_order=None):
    """Calculate weight based on file position."""
    # Default weight based on directory structure
    parts = filepath.parts
    
    if 'index.md' in filepath.name:
        base = 0
    else:
        base = 10
    
    # Add offset based on filename
    name = filepath.stem
    if name == 'index':
        return 0
    
    # Simple alphabetical weighting
    return base + (ord(name[0].lower()) - ord('a')) * 10


def migrate_frontmatter(content, filepath):
    """Migrate frontmatter to Hugo format."""
    
    existing_meta, end_pos = extract_existing_frontmatter(content)
    body = content[end_pos:] if end_pos > 0 else content
    
    # Build new frontmatter
    frontmatter = {}
    
    # Extract or generate title
    title = existing_meta.get('title') or extract_title_from_content(body)
    if title:
        frontmatter['title'] = title
    
    # Migrate approval fields
    approved = existing_meta.get('approved', '')
    if approved:
        approved_str = str(approved)
        if approved_str.lower() == 'none':
            frontmatter['approved_status'] = 'none'
        elif ' ' in approved_str or ',' in approved_str:
            # Split "rb 2026-06-11" or "wp,dd,rb,rh 2026-06-11"
            parts = approved_str.rsplit(' ', 1)
            if len(parts) == 2 and re.match(r'\d{4}-\d{2}-\d{2}', parts[1]):
                frontmatter['approved_by'] = parts[0]
                frontmatter['approved_on'] = parts[1]
            else:
                frontmatter['approved_by'] = approved_str
        else:
            frontmatter['approved_by'] = approved_str
    
    # Migrate author fields
    for field in ['author', 'date', 'valid_for', 'updated']:
        if field in existing_meta:
            frontmatter[field] = existing_meta[field]
    
    # Add Hugo-specific fields
    frontmatter['draft'] = False
    
    # Calculate weight
    weight = calculate_weight(filepath)
    if weight > 0:
        frontmatter['weight'] = weight
    
    # Generate YAML
    yaml_str = yaml.dump(frontmatter, default_flow_style=False, allow_unicode=True, sort_keys=False)
    
    return f"---\n{yaml_str}---\n{body}"


def process_file(filepath):
    """Process a single markdown file."""
    path = Path(filepath)
    
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    new_content = migrate_frontmatter(content, path)
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"✓ Processed: {path}")
    return True


def main():
    if len(sys.argv) < 2:
        print("Usage: migrate_frontmatter.py <file.md> [file2.md ...]")
        print("       migrate_frontmatter.py --dir <directory>")
        sys.exit(1)
    
    if sys.argv[1] == '--dir':
        directory = Path(sys.argv[2])
        files = sorted(directory.rglob('*.md'))
        print(f"Processing {len(files)} files in {directory}")
        
        for f in files:
            process_file(f)
        
        print(f"\nProcessed {len(files)} files")
    else:
        for filepath in sys.argv[1:]:
            process_file(filepath)


if __name__ == '__main__':
    main()
