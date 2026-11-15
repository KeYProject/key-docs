#!/usr/bin/env python3
"""Convert Python-Markdown ``attr_list`` anchors to Goldmark-compatible markup.

The corpus uses two explicit-anchor syntaxes:

* Python-Markdown ``attr_list``: ``{: #id}`` and ``{:#id}`` — 188 occurrences,
  all attached to headings.  Goldmark does not understand them, so they leak
  into the heading text and the table of contents.  On a heading they are
  rewritten to the Goldmark attribute form ``{#id}``; anywhere else they become
  an explicit ``<a id="id"></a>`` immediately before the content.
* Pandoc-style ``{#id}`` on **table cells** (``user/features/java-coverage.md``,
  ``user/getting-started/loading/index.md``): Goldmark block attributes do not
  apply to table cells, so these are rewritten in place to
  ``<a id="id"></a>``.  ``{#id}`` on headings is kept as is.

Fenced code blocks, front matter, and inline code spans are never touched.

Usage:
    python3 anchors.py [CONTENT_ROOT] [--dry-run] [--check] [--exclude PATH]...

``--check`` fails (exit 2) when a ``{: #...}`` anchor or a table-cell ``{#...}``
attribute remains.

Exit codes: 0 on success, 2 on remaining anchors.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
COLON_ANCHOR_RE = re.compile(r"\{\s*:\s*#([^\s{}]+)\s*\}")
ATTR_ANCHOR_RE = re.compile(r"\{#([^\s{}]+)\}")
HEADING_RE = re.compile(r"^\s{0,3}#{1,6}\s")
STANDALONE_ATTR_RE = re.compile(r"^\s*\{#[^\s{}]+\}\s*$")


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


def _inside(position, spans):
    return any(start <= position < end for start, end in spans)


def convert_line(line):
    """Convert anchors in one line; return (line, conversions)."""
    spans = code_spans(line)
    count = 0

    heading = bool(HEADING_RE.match(line))

    def colon_repl(match):
        nonlocal count
        if _inside(match.start(), spans):
            return match.group(0)
        count += 1
        ident = match.group(1)
        if heading and line[match.end():].strip() == "":
            # Goldmark understands heading attributes.
            return "{#%s}" % ident
        return '<a id="%s"></a>' % ident

    new_line = COLON_ANCHOR_RE.sub(colon_repl, line)

    # Pandoc table-cell anchors: Goldmark block attributes do not apply there.
    if not heading and not STANDALONE_ATTR_RE.match(new_line):
        spans = code_spans(new_line)

        def attr_repl(match):
            nonlocal count
            if _inside(match.start(), spans):
                return match.group(0)
            count += 1
            return '<a id="%s"></a>' % match.group(1)

        if "|" in new_line or "![" in new_line:
            new_line = ATTR_ANCHOR_RE.sub(attr_repl, new_line)

    return new_line, count


def convert_text(text):
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    flags = protected_flags(lines)
    out = []
    count = 0
    for i, line in enumerate(lines):
        if flags[i]:
            out.append(line)
            continue
        new_line, n = convert_line(line)
        out.append(new_line)
        count += n
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    return result, count


def find_residuals(text):
    lines = text.splitlines()
    flags = protected_flags(lines)
    hits = []
    for i, line in enumerate(lines):
        if flags[i]:
            continue
        spans = code_spans(line)
        for match in COLON_ANCHOR_RE.finditer(line):
            if not _inside(match.start(), spans):
                hits.append((i + 1, "colon anchor", line.strip()))
                break
        else:
            if (HEADING_RE.match(line) or STANDALONE_ATTR_RE.match(line)
                    or not ("|" in line or "![" in line)):
                continue
            for match in ATTR_ANCHOR_RE.finditer(line):
                if not _inside(match.start(), spans):
                    hits.append((i + 1, "table-cell anchor", line.strip()))
                    break
    return hits


def markdown_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".md"):
                yield os.path.join(dirpath, name)


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
                        help="fail (exit 2) if any unsupported anchor remains")
    parser.add_argument("--exclude", action="append", default=[],
                        metavar="PATH",
                        help="skip this file or directory (repeatable)")
    args = parser.parse_args(argv)

    if not os.path.isdir(args.root):
        print("error: %s is not a directory" % args.root, file=sys.stderr)
        return 1

    root = args.root.rstrip("/") or "content"
    excluded = make_excluder(args.exclude, root)

    scanned = changed = conversions = 0
    failures = []

    for path in markdown_files(root):
        rel = os.path.relpath(path, root).replace(os.sep, "/")
        if is_excluded(rel, excluded):
            continue
        scanned += 1
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()

        if args.check:
            for line_no, kind, content in find_residuals(text):
                failures.append((rel, line_no, kind, content))
            continue

        new_text, count = convert_text(text)
        if count:
            changed += 1
            conversions += count
            if args.dry_run:
                print("would convert %s (%d anchor(s))" % (rel, count))
            else:
                with open(path, "w", encoding="utf-8", newline="") as handle:
                    handle.write(new_text)
                print("converted %s (%d anchor(s))" % (rel, count))

    if args.check:
        for rel, line_no, kind, content in failures:
            print("%s:%d: remaining %s: %s" % (rel, line_no, kind, content))
        print("anchors --check: %d file(s) scanned, %d failure(s)"
              % (scanned, len(failures)))
        return 2 if failures else 0

    verb = "would change" if args.dry_run else "changed"
    print("anchors: %d file(s) scanned, %d %s, %d conversion(s)"
          % (scanned, changed, verb, conversions))
    return 0


if __name__ == "__main__":
    sys.exit(main())
