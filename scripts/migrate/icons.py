#!/usr/bin/env python3
"""Replace Material / Octicons / Font Awesome emoji icons with Hugo markup.

Known Material status icons become coloured HTML spans; every other known icon
becomes a Hextra icon shortcode (``{{< icon "name" >}}``).  Unknown names fall
back to their plain text name so that no ``:material-`` / ``:octicons-`` /
``:fontawesome-`` token survives.

Hextra v0.13 ships the Heroicons set (remote icon providers are disabled in
``hugo.yaml``), so the mappings target Heroicon names rather than Tabler: an
unknown name passed to ``{{< icon >}}`` aborts the build.

Usage:
    python3 icons.py [CONTENT_ROOT] [--dry-run] [--check]
                     [--keep-attributes] [--exclude PATH]...

Fenced code blocks and inline code spans are never touched.  MkDocs attribute
lists directly after an icon (``:material-minus:{ style="color:..." }``) are
removed by default because Hugo's Goldmark configuration does not support
inline attribute lists; use --keep-attributes to retain them.

Exit codes: 0 on success, 2 when --check finds remaining icon tokens.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
ICON_RE = re.compile(r":(material|octicons|fontawesome)-([A-Za-z0-9][A-Za-z0-9_-]*):")
CHECK_RE = re.compile(r":(?:material|octicons|fontawesome)-")

#: Icons that carry the KeY feature-table meaning.
#: name -> (default title or None, default colour, glyph)
STATUS_ICONS = {
    "check-bold": ("Fully supported", "#2e9e44", "\u2713"),
    "minus": ("Not supported", "#9aa0a6", "\u2212"),
    "check": (None, "#2e9e44", "\u2713"),
    "check-all": (None, "#2e9e44", "\u2713\u2713"),
    "close": (None, "#c62828", "\u2717"),
}

#: Feature-table colour -> semantic title.  The source often overrides only the
#: colour (`:material-check-bold:{ style="color:#d19a00" }`); inferring the
#: title from the colour keeps amber checks from claiming "Fully supported".
COLOUR_TITLES = {
    "#2e9e44": "Fully supported",
    "#d19a00": "Partially supported",
    "#9aa0a6": "Not supported",
}

#: Material icon -> Heroicon name (Hextra v0.13 data/icons.yaml).
MATERIAL_HERO = {
    "arrow-right": "arrow-right",
    "arrow-left": "arrow-left",
    "arrow-up": "arrow-up",
    "arrow-down": "arrow-down",
    "chevron-right": "chevron-right",
    "chevron-left": "chevron-left",
    "chevron-down": "chevron-down",
    "chevron-up": "chevron-up",
    "info": "information-circle",
    "information": "information-circle",
    "alert": "exclamation",
    "alert-circle": "exclamation-circle",
    "help-circle": "question-mark-circle",
    "download": "download",
    "upload": "upload",
    "file": "document",
    "file-code": "document-text",
    "folder": "folder",
    "folder-open": "folder-open",
    "link": "link",
    "open-in-new": "external-link",
    "magnify": "search",
    "pencil": "pencil",
    "delete": "trash",
    "content-copy": "duplicate",
    "content-save": "save",
    "calendar": "calendar",
    "clock": "clock",
    "account": "user",
    "account-circle": "user-circle",
    "cog": "cog",
    "lightbulb": "light-bulb",
    "rocket": "lightning-bolt",
    "keyboard": "keyboard",
    "mouse": "cursor-click",
    "monitor": "desktop-computer",
    "laptop": "device-mobile",
    "table": "table",
    "image": "photograph",
    "video": "video-camera",
    "music": "music-note",
    "refresh": "refresh",
    "sync": "refresh",
    "menu": "menu",
    "dots-horizontal": "dots-horizontal",
    "filter": "filter",
    "sort": "sort-ascending",
    "star": "star",
    "heart": "heart",
    "plus": "plus",
    "minus-circle": "minus-circle",
    "close-circle": "x-circle",
    "check-circle": "check-circle",
    "tag": "tag",
    "beaker": "beaker",
    "flask": "beaker",
    "shield": "shield-check",
    "terminal": "terminal",
    "code": "code",
    "book": "book-open",
    "wrench": "adjustments",
    "hammer": "adjustments",
}

#: Octicons icon -> Heroicon name (numeric size suffixes are stripped first).
OCTICONS_HERO = {
    "tag": "tag",
    "beaker": "beaker",
    "arrow-right": "arrow-right",
    "arrow-left": "arrow-left",
    "arrow-up": "arrow-up",
    "arrow-down": "arrow-down",
    "check": "check",
    "x": "x",
    "info": "information-circle",
    "alert": "exclamation",
    "file": "document",
    "file-code": "document-text",
    "code": "code",
    "rocket": "lightning-bolt",
    "shield": "shield-check",
    "gear": "cog",
    "search": "search",
    "download": "download",
    "upload": "upload",
    "link": "link",
    "mark-github": "github",
    "repo": "folder",
    "repo-push": "upload",
    "issue-opened": "exclamation-circle",
    "git-pull-request": "arrow-up-right",
    "terminal": "terminal",
    "book": "book-open",
    "light-bulb": "light-bulb",
    "pencil": "pencil",
    "trash": "trash",
    "plus": "plus",
    "dash": "minus",
    "kebab-horizontal": "dots-horizontal",
    "play": "play",
    "stop": "stop",
    "sync": "refresh",
    "lock": "lock-closed",
    "unlock": "lock-open",
    "eye": "eye",
    "comment": "chat",
}

#: Font Awesome icon -> Heroicon name.  Approximations are deliberate; anything
#: missing falls back to the plain text name.
FONTAWESOME_HERO = {
    "paper-plane": "paper-airplane",
    "check": "check",
    "check-double": "check",
    "times": "x",
    "xmark": "x",
    "close": "x",
    "arrow-right": "arrow-right",
    "arrow-left": "arrow-left",
    "arrow-up": "arrow-up",
    "arrow-down": "arrow-down",
    "arrows-rotate": "refresh",
    "rotate": "refresh",
    "rotate-right": "refresh",
    "sync": "refresh",
    "angle-right": "chevron-right",
    "angle-left": "chevron-left",
    "angle-up": "chevron-up",
    "angle-down": "chevron-down",
    "caret-right": "chevron-right",
    "caret-left": "chevron-left",
    "search": "search",
    "magnifying-glass": "search",
    "info-circle": "information-circle",
    "circle-info": "information-circle",
    "exclamation-triangle": "exclamation",
    "triangle-exclamation": "exclamation",
    "warning": "exclamation",
    "exclamation-circle": "exclamation-circle",
    "circle-exclamation": "exclamation-circle",
    "question-circle": "question-mark-circle",
    "circle-question": "question-mark-circle",
    "download": "download",
    "upload": "upload",
    "file": "document",
    "file-code": "document-text",
    "file-pdf": "document-report",
    "file-lines": "document-text",
    "code": "code",
    "terminal": "terminal",
    "book": "book-open",
    "book-open": "book-open",
    "link": "link",
    "external-link": "external-link",
    "github": "github",
    "gitlab": "gitlab",
    "play": "play",
    "circle-play": "play",
    "pause": "pause",
    "plus": "plus",
    "minus": "minus",
    "star": "star",
    "trash": "trash",
    "trash-can": "trash",
    "pen": "pencil",
    "pen-to-square": "pencil",
    "pencil": "pencil",
    "copy": "duplicate",
    "floppy-disk": "save",
    "save": "save",
    "folder": "folder",
    "folder-open": "folder-open",
    "lock": "lock-closed",
    "unlock": "lock-open",
    "eye": "eye",
    "calendar": "calendar",
    "clock": "clock",
    "user": "user",
    "users": "users",
    "cog": "cog",
    "gear": "cog",
    "lightbulb": "light-bulb",
    "rocket": "lightning-bolt",
    "keyboard": "keyboard",
    "computer-mouse": "cursor-click",
    "desktop": "desktop-computer",
    "laptop": "device-mobile",
    "sitemap": "view-boards",
    "graduation-cap": "academic-cap",
    "shield": "shield-check",
    "shield-halved": "shield-exclamation",
    "bell": "bell",
    "envelope": "mail",
    "comment": "chat",
    "comments": "chat-alt",
    "thumbs-up": "thumb-up",
    "thumbs-down": "thumb-down",
    "bars": "menu",
    "ellipsis": "dots-horizontal",
    "filter": "filter",
    "sort": "sort-ascending",
    "table": "table",
    "image": "photograph",
    "video": "video-camera",
    "music": "music-note",
    "list-check": "clipboard-list",
    "delete-left": "backspace",
    "scissors": "scissors",
    "wand-magic-sparkles": "sparkles",
    "spinner": "refresh",
    "circle-notch": "refresh",
    "paperclip": "paper-clip",
    "tag": "tag",
    "tags": "tag",
    "thumbtack": "bookmark",
    "database": "database",
    "server": "server",
    "cloud": "cloud",
    "moon": "moon",
    "sun": "sun",
    "palette": "color-swatch",
    "language": "translate",
    "globe": "globe",
    "twitter": "twitter",
    "facebook": "facebook",
}

# Attribute list attached directly to an icon by MkDocs Material:
# { style="..." }, { .md-button }, {#id}, {target="_blank"}
ATTR_RE = re.compile(r"\{[^{}\n]*\}")


def fenced_flags(lines):
    flags = [False] * len(lines)
    fence = None
    for i, line in enumerate(lines):
        m = FENCE_RE.match(line)
        if fence is None:
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence = (m.group(2)[0], len(m.group(2)))
                flags[i] = True
        else:
            flags[i] = True
            if (
                m
                and m.group(2)[0] == fence[0]
                and len(m.group(2)) >= fence[1]
                and m.group(3).strip() == ""
            ):
                fence = None
    return flags


def protected_flags(lines):
    flags = fenced_flags(lines)
    if lines and lines[0].strip() == "---":
        for i in range(1, len(lines)):
            flags[i] = True
            if lines[i].strip() in ("---", "..."):
                break
    return flags


def code_spans(line):
    """Return [(start, end)] ranges of inline code spans in ``line``."""
    spans = []
    i = 0
    n = len(line)
    while i < n:
        if line[i] == "`" and not (i > 0 and line[i - 1] == "\\"):
            j = i
            while j < n and line[j] == "`":
                j += 1
            ticks = j - i
            k = j
            while k < n:
                if line[k] == "`":
                    m = k
                    while m < n and line[m] == "`":
                        m += 1
                    if m - k == ticks:
                        spans.append((i, m))
                        i = m
                        break
                    k = m
                else:
                    k += 1
            else:
                i = j
            continue
        i += 1
    return spans


def normalise_name(name):
    """Strip an Octicons size suffix such as ``-16`` / ``-24``."""
    return re.sub(r"-(?:12|16|24|32|48)$", "", name)


def icon_replacement(prefix, raw_name, attrs=None):
    """Return the replacement text for one icon token."""
    name = normalise_name(raw_name).lower()
    if prefix == "material" and name in STATUS_ICONS:
        return status_html(name, attrs)
    if prefix == "fontawesome":
        name = re.sub(r"^(?:solid|regular|brands|light|duotone)-", "", name)
        hero = FONTAWESOME_HERO.get(name)
    elif prefix == "octicons":
        hero = OCTICONS_HERO.get(name)
    else:
        hero = MATERIAL_HERO.get(name)
    if hero:
        return '{{< icon "%s" >}}' % hero
    return name


def status_html(name, attrs=None):
    """Build the coloured span for a feature-table status icon.

    Attribute overrides written in the source (``{ style="color:#d19a00"
    title="Partially supported" }``) are honoured, so the amber "partially
    supported" variant stays amber.
    """
    title, color, glyph = STATUS_ICONS[name]
    explicit_title = None
    if attrs:
        if attrs.get("title"):
            explicit_title = attrs["title"]
        style = attrs.get("style", "")
        match = re.search(r"(?:^|;)\s*color\s*:\s*([^;]+)", style)
        if match:
            color = match.group(1).strip()
        if attrs.get("color"):
            color = attrs["color"]
    if explicit_title:
        title = explicit_title
    else:
        title = COLOUR_TITLES.get(color.lower(), title)
    parts = []
    if title:
        parts.append('title="%s"' % title.replace('"', "&quot;"))
    if color:
        parts.append('style="color:%s"' % color)
    return "<span %s>%s</span>" % (" ".join(parts), glyph)


def _attribute_block(text, start):
    """Return ``(end, inner)`` for an attribute list after ``start``.

    ``(start, None)`` is returned when no MkDocs attribute list follows.
    """
    i = start
    while i < len(text) and text[i] in " \t":
        i += 1
    if i >= len(text) or text[i] != "{":
        return start, None
    match = ATTR_RE.match(text, i)
    if not match:
        return start, None
    inside = match.group(0)[1:-1].strip()
    if not (inside.startswith("#") or inside.startswith(".")
            or re.match(r"[A-Za-z_][\w-]*\s*=", inside)):
        return start, None
    return match.end(), inside


def _attribute_values(inside):
    values = {}
    pattern = re.compile(
        r"([A-Za-z_][\w-]*)\s*=\s*(?:\"([^\"]*)\"|'([^']*)'|([^\s}]+))")
    for match in pattern.finditer(inside or ""):
        value = next(group for group in match.groups()[1:]
                     if group is not None)
        values[match.group(1).lower()] = value
    return values


def replace_line(line, keep_attributes=False):
    """Replace icons in one line outside inline code; return (line, count)."""
    spans = code_spans(line)
    pieces = []
    last = 0
    count = 0
    for m in ICON_RE.finditer(line):
        if any(a <= m.start() < b for a, b in spans):
            continue
        prefix, raw_name = m.group(1), m.group(2)
        attrs = None
        end = m.end()
        attr_end, attr_inside = _attribute_block(line, end)
        if attr_inside is not None:
            attrs = _attribute_values(attr_inside)
            if not keep_attributes:
                end = attr_end
        replacement = icon_replacement(prefix, raw_name, attrs)
        pieces.append(line[last:m.start()])
        pieces.append(replacement)
        last = end
        count += 1
    if not count:
        return line, 0
    pieces.append(line[last:])
    return "".join(pieces), count


def convert_text(text, keep_attributes=False):
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    flags = protected_flags(lines)
    out = []
    count = 0
    for i, line in enumerate(lines):
        if flags[i]:
            out.append(line)
            continue
        new_line, n = replace_line(line, keep_attributes=keep_attributes)
        out.append(new_line)
        count += n
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    return result, count


def markdown_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".md"):
                yield os.path.join(dirpath, name)


def find_residuals(text):
    lines = text.splitlines()
    flags = protected_flags(lines)
    hits = []
    for i, line in enumerate(lines):
        if flags[i]:
            continue
        spans = code_spans(line)
        for m in CHECK_RE.finditer(line):
            if any(a <= m.start() < b for a, b in spans):
                continue
            hits.append((i + 1, line.strip()))
            break
    return hits


def norm(path):
    path = path.replace("\\", "/")
    while path.startswith("./"):
        path = path[2:]
    return os.path.normpath(path).replace(os.sep, "/")


def make_excluder(values, root):
    excluded = set()
    for value in values or []:
        for part in str(value).split(","):
            part = part.strip()
            if not part:
                continue
            if os.path.isabs(part):
                rel = os.path.relpath(part, root)
            else:
                rel = part
                for prefix in (root + os.sep, "content" + os.sep, "./"):
                    if rel.startswith(prefix):
                        rel = rel[len(prefix):]
            excluded.add(norm(rel))
    return excluded


def is_excluded(rel, excluded):
    rel = norm(rel)
    return any(rel == prefix or rel.startswith(prefix.rstrip("/") + "/")
               for prefix in excluded)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("root", nargs="?", default="content",
                        help="content root to scan (default: content)")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing files")
    parser.add_argument("--check", action="store_true",
                        help="fail (exit 2) if any icon token remains")
    parser.add_argument("--keep-attributes", action="store_true",
                        help="keep MkDocs attribute lists after an icon")
    parser.add_argument("--exclude", action="append", default=[],
                        metavar="PATH",
                        help="skip this file or directory (repeatable)")
    args = parser.parse_args(argv)

    if not os.path.isdir(args.root):
        print("error: %s is not a directory" % args.root, file=sys.stderr)
        return 1

    root = args.root.rstrip("/") or "content"
    excluded = make_excluder(args.exclude, root)

    scanned = changed = replacements = 0
    failures = []

    for path in markdown_files(root):
        rel = os.path.relpath(path, root).replace(os.sep, "/")
        if is_excluded(rel, excluded):
            continue
        scanned += 1
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()

        if args.check:
            for line_no, content in find_residuals(text):
                failures.append((rel, line_no, content))
            continue

        new_text, count = convert_text(
            text, keep_attributes=args.keep_attributes)
        if count:
            changed += 1
            replacements += count
            if args.dry_run:
                print("would convert %s (%d icon(s))" % (rel, count))
            else:
                with open(path, "w", encoding="utf-8", newline="") as handle:
                    handle.write(new_text)
                print("converted %s (%d icon(s))" % (rel, count))

    if args.check:
        for rel, line_no, content in failures:
            print("%s:%d: remaining icon token: %s" % (rel, line_no, content))
        print("icons --check: %d file(s) scanned, %d failure(s)"
              % (scanned, len(failures)))
        return 2 if failures else 0

    verb = "would change" if args.dry_run else "changed"
    print("icons: %d file(s) scanned, %d %s, %d replacement(s)"
          % (scanned, changed, verb, replacements))
    return 0


if __name__ == "__main__":
    sys.exit(main())
