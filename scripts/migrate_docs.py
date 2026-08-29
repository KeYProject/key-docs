#!/usr/bin/env python3
"""
MkDocs to Hugo Migration Script for KeY Documentation
"""

import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import argparse

# Configuration
DOCS_DIR = Path("docs")
OUTPUT_DIR = Path("content")
MKDOCS_YML = Path("mkdocs.yml")

ADMONITION_MAP = {
    "note": "info", "abstract": "info", "summary": "info",
    "tip": "success", "hint": "success", "important": "success",
    "success": "success", "check": "success", "done": "success",
    "question": "warning", "help": "warning", "faq": "warning",
    "warning": "warning", "caution": "warning", "attention": "warning",
    "failure": "danger", "fail": "danger", "missing": "danger",
    "danger": "danger", "error": "danger", "bug": "danger",
    "example": "primary", "quote": "secondary", "cite": "secondary",
}


def parse_mkdocs_nav_manual(mkdocs_yml_path: Path) -> Dict[str, dict]:
    """Parse mkdocs.yml navigation manually (avoiding Python-specific YAML tags)."""
    result = {}
    
    with open(mkdocs_yml_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract nav section
    nav_match = re.search(r'^nav:\s*\n((?:  .+\n)+)', content, re.MULTILINE)
    if not nav_match:
        return result
    
    nav_text = nav_match.group(1)
    lines = nav_text.split('\n')
    
    current_section = None
    current_subsection = None
    weight_counter = 0
    
    for line in lines:
        if not line.strip():
            continue
        
        # Count leading spaces for indentation level
        indent = len(line) - len(line.lstrip())
        line = line.strip()
        
        # Skip empty or comment lines
        if not line or line.startswith('#'):
            continue
        
        # Parse navigation items
        if line.startswith('- ') and indent == 0:
            # Top-level section: - "Title": path or - "Title":
            match = re.match(r'- "([^"]+)":\s*(.*)$', line)
            if match:
                title = match.group(1)
                path_or_empty = match.group(2).strip()
                weight_counter += 1
                
                if path_or_empty:
                    # Simple link: - "Home": index.md
                    path = path_or_empty.strip('"')
                    result[path] = {
                        'path': path,
                        'title': title,
                        'level': 0,
                        'weight': weight_counter * 100,
                        'section': Path(path).parent.name if '/' in path else ''
                    }
                else:
                    # Section header
                    current_section = title
                    current_subsection = None
        
        elif line.startswith('- ') and indent == 2:
            # Second-level item
            match = re.match(r'- "([^"]+)":\s*(.*)$', line)
            if match:
                title = match.group(1)
                path_or_empty = match.group(2).strip()
                weight_counter += 1
                
                if path_or_empty:
                    path = path_or_empty.strip('"')
                    result[path] = {
                        'path': path,
                        'title': title,
                        'level': 1,
                        'weight': weight_counter * 10,
                        'section': Path(path).parent.name if '/' in path else ''
                    }
                else:
                    current_subsection = title
        
        elif line.startswith('- ') and indent >= 4:
            # Third-level or deeper item
            match = re.match(r'- "([^"]+)":\s*(.*)$', line)
            if match:
                title = match.group(1)
                path = match.group(2).strip().strip('"')
                weight_counter += 1
                result[path] = {
                    'path': path,
                    'title': title,
                    'level': 2,
                    'weight': weight_counter,
                    'section': Path(path).parent.name if '/' in path else ''
                }
    
    return result


def extract_title_from_markdown(content: str) -> str:
    """Extract title from markdown content."""
    match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    match = re.search(r'^##\s+(.+)$', content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    return "Untitled"


def convert_admonitions(content: str) -> str:
    """Convert MkDocs admonitions to Hugo alerts."""
    pattern = r'^!!!\s+(\w+)(?:\s+"([^"]*)")?(?:\s+(\w+))?\s*\n((?:    .*\n?)+)'
    
    def replace_admonition(match):
        admonition_type = match.group(1).lower()
        title = match.group(2) or ""
        body = match.group(4)
        body = re.sub(r'^    ', '', body, flags=re.MULTILINE)
        hugo_type = ADMONITION_MAP.get(admonition_type, "info")
        
        if title:
            return f'{{{{% alert title="{title}" type="{hugo_type}" %}}}}\n{body}{{{{% /alert %}}}}\n'
        else:
            return f'{{{{% alert type="{hugo_type}" %}}}}\n{body}{{{{% /alert %}}}}\n'
    
    return re.sub(pattern, replace_admonition, content, flags=re.MULTILINE)


def convert_mermaid(content: str) -> str:
    """Convert mermaid code blocks to Hugo shortcode."""
    pattern = r'```mermaid\s*\n(.*?)\n```'
    def replace_mermaid(match):
        diagram = match.group(1).strip()
        return f'{{{{< mermaid >}}}}\n{diagram}\n{{{{< /mermaid >}}}}'
    return re.sub(pattern, replace_mermaid, content, flags=re.DOTALL)


def convert_tabs(content: str) -> str:
    """Convert pymdownx.tabbed to Hugo tabs."""
    lines = content.split('\n')
    result = []
    in_tabs = False
    current_tab_content = []
    tab_title = None
    tab_indent = 0
    
    for line in lines:
        tab_match = re.match(r'^( *)=== "([^"]+)"\s*$', line)
        
        if tab_match:
            indent = len(tab_match.group(1))
            title = tab_match.group(2)
            
            if not in_tabs:
                in_tabs = True
                tab_indent = indent
                result.append('{{% tabpane %}}')
            
            if tab_title is not None:
                result.extend(current_tab_content)
                result.append('{{% /tab %}}')
                current_tab_content = []
            
            tab_title = title
            result.append(f'{{{{% tab header="{title}" %}}}}')
        
        elif in_tabs:
            if line.startswith(' ' * (tab_indent + 4)) or line.strip() == '':
                if line.startswith(' ' * (tab_indent + 4)):
                    line = line[tab_indent + 4:]
                current_tab_content.append(line)
            else:
                if tab_title is not None:
                    result.extend(current_tab_content)
                    result.append('{{% /tab %}}')
                result.append('{{% /tabpane %}}')
                in_tabs = False
                tab_title = None
                current_tab_content = []
                result.append(line)
        else:
            result.append(line)
    
    if in_tabs and tab_title is not None:
        result.extend(current_tab_content)
        result.append('{{% /tab %}}')
        result.append('{{% /tabpane %}}')
    
    return '\n'.join(result)


def convert_citations(content: str) -> str:
    """Convert citations to Hugo shortcodes."""
    content = re.sub(r'\[@(\w+)\]', r'{{< cite "\1" >}}', content)
    content = re.sub(r'\\full_bibliography', '{{< bibliography >}}', content)
    content = re.sub(r'\\cite\{([^}]+)\}', r'{{< cite "\1" >}}', content)
    return content


def extract_hook_metadata(content: str, nav_info: dict) -> Tuple[Dict, str]:
    """Extract metadata from MkDocs hooks."""
    frontmatter = {}
    
    # Parse existing YAML frontmatter
    existing_fm = {}
    fm_match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
    if fm_match:
        try:
            fm_content = fm_match.group(1)
            # Simple key-value parsing
            for line in fm_content.split('\n'):
                if ':' in line:
                    key, val = line.split(':', 1)
                    existing_fm[key.strip()] = val.strip()
        except:
            pass
        content = content[fm_match.end():]
    
    # Extract approval info
    if 'approved' in existing_fm:
        approved = existing_fm['approved']
        match = re.match(r'(\w+)\s+(\d{4}-\d{2}-\d{2})', approved)
        if match:
            frontmatter['approved_by'] = match.group(1)
            frontmatter['approved_date'] = match.group(2)
        else:
            frontmatter['approved_by'] = approved
        frontmatter['approved'] = True
    
    # Extract author info
    for key in ['author', 'date', 'valid_for', 'updated']:
        if key in existing_fm:
            frontmatter[key] = existing_fm[key]
    
    # Add title and navigation metadata
    if 'title' not in frontmatter:
        frontmatter['title'] = nav_info.get('title', extract_title_from_markdown(content))
    
    frontmatter['weight'] = nav_info.get('weight', 100)
    
    source_dir = Path(nav_info.get('path', '')).parent.name
    if source_dir in ['user', 'devel', 'eclipse', 'keps', 'quicktour']:
        frontmatter['menu'] = 'main'
        frontmatter['section'] = source_dir
    
    return frontmatter, content


def create_frontmatter(frontmatter: Dict) -> str:
    """Create YAML frontmatter string."""
    lines = ['---']
    for key, value in sorted(frontmatter.items()):
        if value is not None:
            lines.append(f'{key}: {value}')
    lines.append('---')
    return '\n'.join(lines) + '\n\n'


def convert_file(source_file: Path, nav_info: dict, output_dir: Path) -> Optional[Path]:
    """Convert a single MkDocs file to Hugo format."""
    try:
        with open(source_file, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {source_file}: {e}")
        return None
    
    frontmatter, content = extract_hook_metadata(content, nav_info)
    content = convert_admonitions(content)
    content = convert_mermaid(content)
    content = convert_tabs(content)
    content = convert_citations(content)
    
    rel_path = source_file.relative_to(DOCS_DIR)
    output_path = output_dir / rel_path.parent / rel_path.name
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    try:
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(create_frontmatter(frontmatter))
            f.write(content)
        return output_path
    except Exception as e:
        print(f"Error writing {output_path}: {e}")
        return None


def main():
    parser = argparse.ArgumentParser(description='Migrate MkDocs to Hugo')
    parser.add_argument('--sample', action='store_true', help='Process only sample files')
    parser.add_argument('--output-dir', type=str, default='content', help='Output directory')
    args = parser.parse_args()
    
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"Parsing navigation from {MKDOCS_YML}...")
    nav_map = parse_mkdocs_nav_manual(MKDOCS_YML)
    print(f"Found {len(nav_map)} navigation entries")
    
    md_files = list(DOCS_DIR.rglob('*.md'))
    
    if args.sample:
        sample_files = []
        sections = set()
        for f in sorted(md_files):
            section = f.parent.name
            if section not in sections or len(sample_files) < 10:
                sample_files.append(f)
                sections.add(section)
            if len(sample_files) >= 10:
                break
        md_files = sample_files
        print(f"Processing sample of {len(md_files)} files...")
    else:
        print(f"Found {len(md_files)} markdown files...")
    
    converted = 0
    errors = 0
    
    for source_file in sorted(md_files):
        rel_path = source_file.relative_to(DOCS_DIR)
        nav_info = nav_map.get(str(rel_path), {})
        
        output_path = convert_file(source_file, nav_info, output_dir)
        
        if output_path:
            print(f"✓ Converted: {rel_path}")
            converted += 1
        else:
            print(f"✗ Failed: {rel_path}")
            errors += 1
    
    print(f"\nMigration complete: {converted} files converted, {errors} errors")
    return 0 if errors == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
