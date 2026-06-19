"""MkDocs hook: render author metadata from front matter.

Pages can carry author information in their front matter::

    ---
    author: "Nils Buchholz"
    date: "February 2025"
    valid_for: "a future release of KeY based on KeY 2.12.3"
    ---

Or with optional updated field::

    ---
    author: "Arne Keller"
    date: "December 2022"
    valid_for: "KeY-2.12.0"
    updated: "November 2023"
    ---

The hook renders the author info right-aligned below the page title.
"""


def on_page_markdown(markdown, page, config, files):
    author = page.meta.get("author")
    
    if not author:
        return markdown
    
    date = page.meta.get("date", "")
    valid_for = page.meta.get("valid_for", "")
    updated = page.meta.get("updated", "")
    
    # Build the author line
    parts = [f"Author: {author}"]
    if date:
        parts.append(date)
    
    line = ", ".join(parts)
    
    extras = []
    if valid_for:
        extras.append(f"valid for {valid_for}")
    if updated:
        extras.append(f"last updated: {updated}")
    
    if extras:
        line += f"<br>({', '.join(extras)})"
    
    header = (
        f'<div class="page-author">{line}</div>\n\n'
    )
    
    # Insert after the first heading (title)
    lines = markdown.split('\n')
    result = []
    inserted = False
    
    for i, line in enumerate(lines):
        result.append(line)
        # Look for the first H1 heading
        if not inserted and line.startswith('# '):
            result.append('')
            result.append(header)
            inserted = True
    
    return '\n'.join(result)
