#!/usr/bin/env python3
"""
Convert MkDocs admonitions to Hugo alert shortcodes.

MkDocs syntax:
    !!! note "Optional Title"
        Content here

Hugo target:
    {{% alert type="info" title="Optional Title" %}}
    Content here
    {{% /alert %}}
"""

import re
import sys
from pathlib import Path

ADMONITION_MAP = {
    'note': 'info',
    'abstract': 'info',
    'summary': 'info',
    'tip': 'success',
    'hint': 'success',
    'important': 'success',
    'success': 'success',
    'check': 'success',
    'done': 'success',
    'question': 'info',
    'help': 'info',
    'faq': 'info',
    'warning': 'warning',
    'attention': 'warning',
    'caution': 'warning',
    'failure': 'danger',
    'fail': 'danger',
    'missing': 'danger',
    'danger': 'danger',
    'error': 'danger',
    'bug': 'danger',
    'example': 'primary',
    'quote': 'secondary',
    'cite': 'secondary',
}

def convert_admonitions(content):
    """Convert MkDocs admonitions to Hugo alerts."""
    
    # Pattern matches: !!! type "optional title" followed by indented content
    pattern = r'^!!!\s+(\w+)(?:\s+"([^"]*)")?\s*\n((?:(?:    |\t).*\n?)*)'
    
    def replacer(match):
        ad_type = match.group(1).lower()
        title = match.group(2) or ''
        body = match.group(3)
        
        # Map to Hugo type
        hugo_type = ADMONITION_MAP.get(ad_type, 'info')
        
        # Remove leading indentation (4 spaces or 1 tab)
        body = re.sub(r'^(?:    |\t)', '', body, flags=re.MULTILINE)
        
        # Trim trailing whitespace but keep structure
        body = body.rstrip() + '\n'
        
        if title:
            return f'{{{{% alert type="{hugo_type}" title="{title}" %}}}}\n{body}{{{{% /alert %}}}}\n'
        else:
            return f'{{{{% alert type="{hugo_type}" %}}}}\n{body}{{{{% /alert %}}}}\n'
    
    return re.sub(pattern, replacer, content, flags=re.MULTILINE)


def process_file(filepath):
    """Process a single markdown file."""
    path = Path(filepath)
    
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    content = convert_admonitions(content)
    
    if content != original:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"✓ Converted: {path}")
        return True
    else:
        print(f"  No changes: {path}")
        return False


def main():
    if len(sys.argv) < 2:
        print("Usage: convert_admonitions.py <file.md> [file2.md ...]")
        print("       convert_admonitions.py --dir <directory>")
        sys.exit(1)
    
    if sys.argv[1] == '--dir':
        directory = Path(sys.argv[2])
        files = list(directory.rglob('*.md'))
        print(f"Processing {len(files)} files in {directory}")
        
        converted = 0
        for f in files:
            if process_file(f):
                converted += 1
        
        print(f"\nConverted {converted}/{len(files)} files")
    else:
        for filepath in sys.argv[1:]:
            process_file(filepath)


if __name__ == '__main__':
    main()
