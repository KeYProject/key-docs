#!/usr/bin/env python3
"""
Convert MkDocs bibtex citations to Hugo bibcite shortcodes.

MkDocs syntax:
    [@JMLReferenceManual11]
    \full_bibliography

Hugo target:
    {{< bibcite "JMLReferenceManual11" >}}
    {{< bibliography >}}
"""

import re
import sys
from pathlib import Path


def convert_citations(content):
    """Convert bibtex citations to Hugo shortcodes."""
    
    # Pattern 1: [@key] or [@key1][@key2]
    pattern1 = r'\[@([\w:-]+)\]'
    content = re.sub(pattern1, r'{{< bibcite "\1" >}}', content)
    
    # Pattern 2: \full_bibliography
    pattern2 = r'\\full_bibliography'
    content = re.sub(pattern2, '{{< bibliography >}}', content)
    
    return content


def process_file(filepath):
    """Process a single markdown file."""
    path = Path(filepath)
    
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    content = convert_citations(content)
    
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
        print("Usage: convert_citations.py <file.md> [file2.md ...]")
        print("       convert_citations.py --dir <directory>")
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
