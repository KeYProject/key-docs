#!/usr/bin/env python3
"""Convert MkDocs/Material admonitions to Hugo (hextra) shortcodes.

    !!! type "Title"        ->  {{< callout type="..." title="..." >}}...{{< /callout >}}
    ???[+-] type "Title"    ->  {{< details title="..." >}}...{{< /details >}}

Usage:
    python3 admonitions.py [CONTENT_ROOT] [--dry-run] [--check] [--expect N]

Markdown fenced code blocks, YAML front matter and MkDocs ``===`` tab regions
are protected: the authoring page intentionally shows ``!!!``/``???`` examples
inside fences and tabs, and those are rewritten by the tabs task, not here.
Admonition bodies are de-indented by four spaces and converted recursively so
that nested admonitions work.  Admonitions nested inside list items (indented
by four or more spaces) are converted in place and keep their indentation.

The script is idempotent: an already converted page contains no ``!!!`` /
``???`` block starts and is left alone.

``--check`` fails when an admonition remains outside the protected regions, or
when the number of converted shortcodes plus the remaining (protected) markers
differs from ``--expect``.  The count check is off by default; this repository
was migrated from a baseline of 78 markers, so run ``--check --expect 78`` to
guard that no block was lost.

Exit codes: 0 on success, 2 when --check finds problems.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

# ---------------------------------------------------------------------------
# Markdown scanning helpers (duplicated in each converter so that every script
# is a self-contained drop-in; stdlib only.)
# ---------------------------------------------------------------------------

FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")

ADMONITION_RE = re.compile(
    r"^( *)(!!!|\?\?\?)([+-]?)[ \t]+([A-Za-z][\w-]*)"
    r"(?:[ \t]+(.*?))?[ \t]*$"
)

#: MkDocs ``=== "Tab title"`` markers (optionally with a ``!``/``+``/``-``).
TAB_RE = re.compile(r"^( *)(===)[!+-]?[ \t]+\S")

#: MkDocs type -> hextra callout type
TYPE_MAP = {
    "note": "info",
    "abstract": "info",
    "summary": "info",
    "info": "info",
    "tip": "default",
    "hint": "default",
    "success": "default",
    "warning": "warning",
    "caution": "warning",
    "attention": "warning",
    "danger": "error",
    "failure": "error",
    "error": "error",
    "bug": "error",
    "example": "default",
    "quote": "default",
    "cite": "default",
}

DEFAULT_CALLOUT_TYPE = "default"

#: Number of MkDocs admonition markers in ``content`` before the migration:
#: 67 convertible blocks plus 9 inside fences and 2 inside ``===`` tab
#: examples.  ``shortcodes + remaining markers`` must stay at this number.
BASELINE_MARKERS = 78


def fence_roles(lines):
    """Classify lines relative to Markdown fences.

    Returns one entry per line: ``"open"`` for an opening fence delimiter,
    ``"close"`` for the matching closing delimiter, ``"content"`` for lines
    between them, and ``None`` for everything else.
    """
    roles = [None] * len(lines)
    fence = None  # (char, length)
    for i, line in enumerate(lines):
        m = FENCE_RE.match(line)
        if fence is None:
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence = (m.group(2)[0], len(m.group(2)))
                roles[i] = "open"
        elif (
            m
            and m.group(2)[0] == fence[0]
            and len(m.group(2)) >= fence[1]
            and m.group(3).strip() == ""
        ):
            roles[i] = "close"
            fence = None
        else:
            roles[i] = "content"
    return roles


def fenced_flags(lines):
    """Return a list of booleans: True for lines inside (or delimiting) fences.

    Fences may be indented (they commonly are inside admonition bodies); the
    closing fence must use the same character, be at least as long, and carry
    no info string.
    """
    return [role is not None for role in fence_roles(lines)]


def tab_region_flags(lines):
    """Return flags for lines that belong to a MkDocs ``===`` tab block.

    A tab starts at a ``=== ...`` marker; its body is every following line that
    is blank or indented at least four columns beyond the marker.  Nested tabs
    (indented markers) are tracked as well.  Admonitions inside these regions
    are examples that the tabs task rewrites, so they must not be converted.
    """
    flags = [False] * len(lines)
    stack = []  # indentation of the active tab markers
    for i, line in enumerate(lines):
        indent = leading_spaces(line)
        m = TAB_RE.match(line)
        if m is not None:
            stack = [level for level in stack if level < indent]
            stack.append(indent)
            flags[i] = True
            continue
        if line.strip() == "":
            flags[i] = bool(stack)
            continue
        if stack and indent >= stack[-1] + 4:
            flags[i] = True
        else:
            stack = []
    return flags


def protected_flags(lines, front_matter=True):
    """Fence, tab-block and (optionally) YAML front matter flags."""
    flags = fenced_flags(lines)
    tabs = tab_region_flags(lines)
    for i, protected in enumerate(tabs):
        flags[i] = flags[i] or protected
    if front_matter and lines and lines[0].strip() == "---":
        for i in range(1, len(lines)):
            flags[i] = True
            if lines[i].strip() in ("---", "..."):
                break
    return flags


def leading_spaces(line):
    return len(line) - len(line.lstrip(" "))


def indent_width(line):
    """Indentation in columns, expanding tabs to the next multiple of four."""
    col = 0
    for char in line:
        if char == " ":
            col += 1
        elif char == "\t":
            col += 4 - (col % 4)
        else:
            break
    return col


def deindent(line, amount):
    """Remove up to ``amount`` indentation columns (tabs count as four)."""
    col = 0
    i = 0
    while i < len(line) and col < amount:
        if line[i] == " ":
            col += 1
        elif line[i] == "\t":
            col += 4 - (col % 4)
        else:
            break
        i += 1
    return line[i:]


def parse_title(rest):
    """Parse the optional title of an admonition.

    Returns ``None`` when no title was given, ``""`` for an explicit empty
    string (``!!! note ""``), and the unescaped title otherwise.
    """
    if rest is None:
        return None
    rest = rest.strip()
    if rest == "":
        return None
    if rest[0] in "\"'":
        quote = rest[0]
        out = []
        i = 1
        while i < len(rest):
            c = rest[i]
            if c == "\\" and i + 1 < len(rest):
                out.append(rest[i + 1])
                i += 2
                continue
            if c == quote:
                break
            out.append(c)
            i += 1
        return "".join(out)
    return rest


def escape_param(value):
    """Escape a value for use inside a double-quoted shortcode parameter."""
    return value.replace("\\", "\\\\").replace('"', '\\"')


def default_title(adm_type):
    return adm_type.replace("-", " ").replace("_", " ").capitalize()


# ---------------------------------------------------------------------------
# Conversion
# ---------------------------------------------------------------------------


def convert_blocks(lines, front_matter=True):
    """Convert all admonition blocks in ``lines``; return (lines, count)."""
    roles = fence_roles(lines)
    flags = protected_flags(lines, front_matter=front_matter)
    out = []
    count = 0
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = None if flags[i] else ADMONITION_RE.match(line)
        if m is None:
            out.append(line)
            i += 1
            continue

        indent = len(m.group(1))
        token = m.group(2)
        adm_type = m.group(4).lower()
        title = parse_title(m.group(5))
        base = indent + 4

        # Collect the block body: blank lines and lines indented by at least
        # ``base`` columns.  A fence that opens inside the body keeps all of
        # its lines, even if they are less indented; a fence that starts at
        # column zero ends the admonition (as it does in MkDocs).
        body = []
        j = i + 1
        in_fence = False
        while j < n:
            nxt = lines[j]
            if in_fence:
                body.append(nxt)
                if roles[j] == "close":
                    in_fence = False
                j += 1
                continue
            if nxt.strip() == "":
                body.append(nxt)
                j += 1
                continue
            if indent_width(nxt) >= base:
                body.append(nxt)
                if roles[j] == "open":
                    in_fence = True
                j += 1
                continue
            break

        # A few pages indent their admonition body by only one to three
        # columns (or a single tab); Markdown then renders an empty block.
        # Recover such loosely indented bodies so the text stays inside the
        # callout instead of dangling below an empty box.
        if not any(line.strip() for line in body):
            k = i + 1
            while k < n and lines[k].strip() == "":
                k += 1
            if k < n and not flags[k] and indent_width(lines[k]) > indent:
                base = indent_width(lines[k])
                body = []
                j = k
                while j < n:
                    nxt = lines[j]
                    if (nxt.strip() == "" or flags[j]
                            or indent_width(nxt) >= base):
                        body.append(nxt)
                        j += 1
                        continue
                    break

        # Trailing blank lines belong to the surrounding document, not to the
        # admonition.  Roll the cursor back so the outer loop re-emits them.
        trailing = 0
        while body and body[-1].strip() == "":
            body.pop()
            trailing += 1
        j -= trailing
        # Leading blank lines add nothing after the shortcode opener.
        while body and body[0].strip() == "":
            body.pop(0)

        deindented = [deindent(b, base) for b in body]
        inner, nested = convert_blocks(deindented, front_matter=False)
        count += 1 + nested

        prefix = " " * indent
        if token == "!!!":
            ctype = TYPE_MAP.get(adm_type, DEFAULT_CALLOUT_TYPE)
            params = 'type="%s"' % escape_param(ctype)
            if title not in (None, ""):
                params += ' title="%s"' % escape_param(title)
            out.append("%s{{< callout %s >}}" % (prefix, params))
            out.extend(prefix + ln if ln.strip() else "" for ln in inner)
            out.append("%s{{< /callout >}}" % prefix)
        else:
            # Details shortcodes need a summary; MkDocs falls back to the
            # title-cased type when no explicit title is present.
            details_title = title
            if details_title is None:
                details_title = default_title(adm_type)
            params = ""
            if details_title != "":
                params = ' title="%s"' % escape_param(details_title)
            out.append("%s{{< details%s >}}" % (prefix, params))
            out.extend(prefix + ln if ln.strip() else "" for ln in inner)
            out.append("%s{{< /details >}}" % prefix)

        i = j

    return out, count


def convert_text(text):
    """Convert a whole Markdown document; return (text, replacement count)."""
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    out, count = convert_blocks(lines)
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    return result, count


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

#: A MkDocs admonition marker, at any indentation.
BLOCK_MARKER_RE = re.compile(r"^( *)(!!!|\?\?\?)[+-]?[ \t]+\S")

#: A converted shortcode opener.
SHORTCODE_RE = re.compile(r"^( *)\{\{<\s*(?:callout|details)\b")


def markdown_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".md"):
                yield os.path.join(dirpath, name)


def find_residuals(text):
    """Return (residual, deferred_tab) lists for unconverted markers.

    ``residual`` holds markers outside every protected region; those are
    failures.  ``deferred_tab`` holds markers inside ``===`` tab examples,
    which the tabs migration task owns.
    """
    lines = text.splitlines()
    fenced = fenced_flags(lines)
    tabs = tab_region_flags(lines)
    front = [False] * len(lines)
    if lines and lines[0].strip() == "---":
        for i in range(1, len(lines)):
            front[i] = True
            if lines[i].strip() in ("---", "..."):
                break
    residual = []
    deferred = []
    for i, line in enumerate(lines):
        if not BLOCK_MARKER_RE.match(line) or fenced[i] or front[i]:
            continue
        if tabs[i]:
            deferred.append((i + 1, line.strip()))
        else:
            residual.append((i + 1, line.strip()))
    return residual, deferred


def count_shortcodes(text):
    lines = text.splitlines()
    fenced = fenced_flags(lines)
    return sum(
        1 for i, line in enumerate(lines)
        if not fenced[i] and SHORTCODE_RE.match(line)
    )


def count_markers(text):
    """All remaining MkDocs markers, protected regions included."""
    return sum(1 for line in text.splitlines() if BLOCK_MARKER_RE.match(line))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("root", nargs="?", default="content",
                        help="content root to scan (default: content)")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing files")
    parser.add_argument("--check", action="store_true",
                        help="fail (exit 2) if any unconverted admonition remains")
    parser.add_argument("--expect", type=int, default=0,
                        help="expected number of shortcodes + remaining markers "
                             "in --check mode (0 disables the count check; the "
                             "baseline of this repository is %d)"
                             % BASELINE_MARKERS)
    args = parser.parse_args(argv)

    root = args.root
    if not os.path.isdir(root):
        print("error: %s is not a directory" % root, file=sys.stderr)
        return 1

    scanned = 0
    changed = 0
    replacements = 0
    failures = []
    deferred = []
    shortcodes = 0
    markers = 0

    for path in markdown_files(root):
        scanned += 1
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()

        if args.check:
            residual, in_tabs = find_residuals(text)
            shortcodes += count_shortcodes(text)
            markers += count_markers(text)
            deferred.extend((path, line_no, content) for line_no, content in in_tabs)
            failures.extend((path, line_no, content) for line_no, content in residual)
            continue

        new_text, count = convert_text(text)
        if count:
            changed += 1
            replacements += count
            rel = os.path.relpath(path, root)
            if args.dry_run:
                print("would convert %s (%d block(s))" % (rel, count))
            else:
                with open(path, "w", encoding="utf-8", newline="") as handle:
                    handle.write(new_text)
                print("converted %s (%d block(s))" % (rel, count))

    if args.check:
        for path, line_no, content in failures:
            print("%s:%d: unconverted admonition: %s" % (path, line_no, content))
        for path, line_no, content in deferred:
            print("%s:%d: deferred ('=== tab' example): %s"
                  % (path, line_no, content))
        total = shortcodes + markers
        print("admonitions --check: %d file(s) scanned, %d shortcode(s), "
              "%d remaining marker(s), %d failure(s), %d deferred"
              % (scanned, shortcodes, markers, len(failures), len(deferred)))
        if args.expect:
            print("admonitions --check: %d shortcode(s) + %d marker(s) = %d "
                  "(expected %d)" % (shortcodes, markers, total, args.expect))
            if total != args.expect:
                print("admonitions --check: FAIL count mismatch: expected %d, "
                      "found %d" % (args.expect, total))
                return 2
        if failures:
            return 2
        print("admonitions --check: PASS")
        return 0

    verb = "would change" if args.dry_run else "changed"
    print("admonitions: %d file(s) scanned, %d %s, %d replacement(s)"
          % (scanned, changed, verb, replacements))
    return 0


if __name__ == "__main__":
    sys.exit(main())
