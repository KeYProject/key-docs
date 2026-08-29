#!/usr/bin/env python3
"""
Convert MkDocs mermaid code blocks to Hugo mermaid shortcodes.

MkDocs syntax:
    ```mermaid
    flowchart TB
        A --> B
    ```

Hugo target:
    {{< mermaid >}}
    flowchart TB
        A --> B
    {{< /mermaid >}}
"""

import re
import sys
from pathlib import Path


def convert_mermaid(content):
    """Convert mermaid code blocks to Hugo shortcodes."""
    
    # Pattern matches: ```mermaid ... ```
    pattern = r'```mermaid\s*\n(.*?)```'
    
    def replacer(match):
        diagram = match.group(1).strip()
        return f'{{{{< mermaid >}}}}\n{diagram}\n{{{{< /mermaid >}}}}'
    
    return re.sub(pattern, replacer, content, flags=re.DOTALL)


def process_file(filepath):
    """Process a single markdown file."""
    path = Path(filepath)
    
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    content = convert_mermaid(content)
    
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
        print("Usage: convert_mermaid.py <file.md> [file2.md ...]")
        print("       convert_mermaid.py --dir <directory>")
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
