#!/usr/bin/env python3
"""
Validate migrated markdown files for common issues.

Checks:
- Unclosed shortcodes
- Broken internal links
- Missing frontmatter
- Invalid YAML
- Remaining MkDocs syntax
"""

import re
import sys
import yaml
from pathlib import Path
from collections import defaultdict


class Validator:
    def __init__(self):
        self.errors = []
        self.warnings = []
        
    def check_shortcodes(self, content, filepath):
        """Check for unclosed or malformed shortcodes."""
        # Find all shortcodes
        open_pattern = r'\{\{[%<]\s+(\w+)'
        close_pattern = r'\{\{[%<]\s+/\1\s*[%<]\}\}'
        
        opens = re.findall(open_pattern, content)
        
        # Check for common Hugo shortcodes that need closing
        closable = ['alert', 'tabs', 'tab', 'mermaid', 'blockquote']
        
        for shortcode in opens:
            if shortcode in closable:
                close_pat = rf'\{{\{{[%<]\s+/{shortcode}\s*[%<]\}}\}}'
                if not re.search(close_pat, content):
                    self.warnings.append(
                        f"{filepath}: Possibly unclosed shortcode {{{{{shortcode}}}}}"
                    )
    
    def check_frontmatter(self, content, filepath):
        """Check for valid frontmatter."""
        match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        
        if not match:
            self.warnings.append(f"{filepath}: No frontmatter found")
            return
        
        try:
            meta = yaml.safe_load(match.group(1))
            if not meta.get('title'):
                self.warnings.append(f"{filepath}: Missing title in frontmatter")
        except yaml.YAMLError as e:
            self.errors.append(f"{filepath}: Invalid YAML: {e}")
    
    def check_mkdocs_syntax(self, content, filepath):
        """Check for remaining MkDocs-specific syntax."""
        # Check for unconverted admonitions
        if re.search(r'^!!!\s+\w+', content, re.MULTILINE):
            self.errors.append(f"{filepath}: Unconverted admonition (!!!)")
        
        # Check for unconverted tabs
        if re.search(r'^===\s+"', content, re.MULTILINE):
            self.errors.append(f"{filepath}: Unconverted tab (===)")
        
        # Check for unconverted mermaid blocks
        if re.search(r'```mermaid', content):
            self.errors.append(f"{filepath}: Unconverted mermaid block")
        
        # Check for unconverted citations
        if re.search(r'\[@[\w:-]+\]', content):
            self.errors.append(f"{filepath}: Unconverted citation [@key]")
        
        # Check for \full_bibliography
        if re.search(r'\\full_bibliography', content):
            self.errors.append(f"{filepath}: Unconverted \\full_bibliography")
    
    def check_links(self, content, filepath):
        """Check for potentially broken internal links."""
        # Find all relative links
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, link in links:
            # Skip external links
            if link.startswith(('http://', 'https://', 'mailto:')):
                continue
            
            # Check for .md extensions (should be removed in Hugo)
            if '.md' in link and not link.startswith('{{<'):
                self.warnings.append(
                    f"{filepath}: Link still has .md extension: {link}"
                )
            
            # Check for anchor-only links
            if link.startswith('#'):
                continue  # These are fine
    
    def validate_file(self, filepath):
        """Validate a single file."""
        path = Path(filepath)
        
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.errors.append(f"{filepath}: Read error: {e}")
            return
        
        self.check_frontmatter(content, filepath)
        self.check_shortcodes(content, filepath)
        self.check_mkdocs_syntax(content, filepath)
        self.check_links(content, filepath)
    
    def report(self):
        """Print validation report."""
        print("\n" + "="*60)
        print("MIGRATION VALIDATION REPORT")
        print("="*60)
        
        if self.errors:
            print(f"\n❌ ERRORS ({len(self.errors)}):")
            for err in self.errors:
                print(f"  - {err}")
        else:
            print("\n✅ No errors found!")
        
        if self.warnings:
            print(f"\n⚠️  WARNINGS ({len(self.warnings)}):")
            for warn in self.warnings:
                print(f"  - {warn}")
        
        print("\n" + "="*60)
        
        return len(self.errors) == 0


def main():
    validator = Validator()
    
    if len(sys.argv) < 2:
        print("Usage: validate_migration.py <file.md> [file2.md ...]")
        print("       validate_migration.py --dir <directory>")
        sys.exit(1)
    
    if sys.argv[1] == '--dir':
        directory = Path(sys.argv[2])
        files = sorted(directory.rglob('*.md'))
        print(f"Validating {len(files)} files in {directory}...")
        
        for f in files:
            validator.validate_file(str(f))
    else:
        for filepath in sys.argv[1:]:
            validator.validate_file(filepath)
    
    success = validator.report()
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
