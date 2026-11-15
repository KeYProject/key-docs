#!/usr/bin/env python3
"""Convert MkDocs/Material content tabs to Hugo (hextra) tab shortcodes.

    === "A"                 {{< tabs >}}
    <4-space indented body>     {{< tab name="A" >}}body{{< /tab >}}
    === "B"                     {{< tab name="B" >}}body{{< /tab >}}
                            {{< /tabs >}}

A run consists of consecutive ``=== "Title"`` headers at column 0.  Headers
inside fenced code blocks or indented by four or more spaces are ignored, which
keeps ``===`` lines inside tab bodies and code samples intact.

Usage:
    python3 tabs.py [PATH ...] [--dry-run] [--check]

PATH may be a file or a directory (directories are scanned recursively for
``*.md``).  Defaults to ``content``.

Exit codes: 0 on success, 2 when --check finds unconverted tab headers.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
TAB_RE = re.compile(r'^=== (.*)$')


def fenced_flags(lines):
    flags = [False] * len(lines)
    fence = None  # (char, length, indent)
    for i, line in enumerate(lines):
        m = FENCE_RE.match(line)
        if fence is None:
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence = (m.group(2)[0], len(m.group(2)),
                         len(m.group(1)))
                flags[i] = True
        else:
            flags[i] = True
            # CommonMark: the closing fence may be indented at most three
            # spaces relative to the opening one.  This keeps an indented
            # ``` inside a column-0 fence from closing it early.
            if (
                m
                and m.group(2)[0] == fence[0]
                and len(m.group(2)) >= fence[1]
                and m.group(3).strip() == ""
                and len(m.group(1)) <= fence[2] + 3
            ):
                fence = None
    return flags


def protected_flags(lines, front_matter=True):
    flags = fenced_flags(lines)
    if front_matter and lines and lines[0].strip() == "---":
        for i in range(1, len(lines)):
            flags[i] = True
            if lines[i].strip() in ("---", "..."):
                break
    return flags


def leading_spaces(line):
    return len(line) - len(line.lstrip(" "))


def deindent(line, amount=4):
    return line[min(leading_spaces(line), amount):]


def parse_title(rest):
    """Parse ``"Title"`` / ``'Title'`` (or a bare title); return the string."""
    rest = rest.strip()
    if rest == "":
        return ""
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
    # Drop a trailing attribute list, e.g. === "Title" {#anchor}
    return re.sub(r"\s*\{[^{}]*\}\s*$", "", rest)


def escape_param(value):
    return value.replace("\\", "\\\\").replace('"', '\\"')


def tab_header(line):
    """Return the raw title of a column-0 tab header, or None."""
    m = TAB_RE.match(line)
    if not m:
        return None
    title = parse_title(m.group(1))
    if title == "" and m.group(1).strip() == "":
        return None
    return title


def collect_body(lines, flags, start):
    """Collect one tab body starting at ``start``; return (body, next_index)."""
    n = len(lines)
    body = []
    i = start
    while i < n:
        line = lines[i]
        if line.strip() == "" or flags[i] or leading_spaces(line) >= 4:
            body.append(line)
            i += 1
            continue
        break
    # Trailing blanks belong to the gap before the next header / paragraph;
    # the run emitter replaces them with exactly one separating blank line.
    while body and body[-1].strip() == "":
        body.pop()
    while body and body[0].strip() == "":
        body.pop(0)
    return [deindent(line) for line in body], i


def convert_blocks(lines, front_matter=True):
    """Convert all tab runs in ``lines``; return (lines, run count)."""
    flags = protected_flags(lines, front_matter=front_matter)
    out = []
    runs = 0
    i = 0
    n = len(lines)
    while i < n:
        title = None if flags[i] else tab_header(lines[i])
        if title is None:
            out.append(lines[i])
            i += 1
            continue

        tabs = []
        while True:
            body, i = collect_body(lines, flags, i + 1)
            tabs.append((title, body))
            # Look ahead over blank lines for another tab header.
            k = i
            while k < n and lines[k].strip() == "" and not flags[k]:
                k += 1
            if k < n and not flags[k]:
                next_title = tab_header(lines[k])
                if next_title is not None:
                    title = next_title
                    i = k
                    continue
            break

        runs += 1
        out.append("{{< tabs >}}")
        for name, body in tabs:
            if name:
                out.append('{{< tab name="%s" >}}' % escape_param(name))
            else:
                out.append("{{< tab >}}")
            out.extend(body)
            out.append("{{< /tab >}}")
        out.append("{{< /tabs >}}")

        # Keep one blank line between the closing shortcode and what follows,
        # even if the source had none (Hugo shortcodes need their own line).
        if i < n:
            out.append("")

    return out, runs


def convert_text(text):
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    out, runs = convert_blocks(lines)
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    return result, runs


RESIDUAL_RE = re.compile(r"^=== ")


def markdown_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".md"):
                yield os.path.join(dirpath, name)


def collect_paths(paths):
    """Expand file/directory arguments into a sorted list of markdown files."""
    files = []
    for path in paths:
        if os.path.isdir(path):
            files.extend(markdown_files(path))
        elif os.path.isfile(path):
            files.append(path)
        else:
            raise SystemExit("error: path does not exist: %s" % path)
    return files


def find_residuals(text):
    lines = text.splitlines()
    flags = protected_flags(lines)
    return [(i + 1, line.strip()) for i, line in enumerate(lines)
            if not flags[i] and RESIDUAL_RE.match(line)]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", default=["content"],
                        metavar="PATH",
                        help="markdown file or content root to scan "
                             "(default: content)")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing files")
    parser.add_argument("--check", action="store_true",
                        help="fail (exit 2) if any column-0 tab header remains")
    args = parser.parse_args(argv)

    paths = args.paths or ["content"]
    files = collect_paths(paths)

    scanned = changed = replacements = 0
    failures = []

    for path in files:
        scanned += 1
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()

        if args.check:
            for line_no, content in find_residuals(text):
                failures.append((path, line_no, content))
            continue

        new_text, runs = convert_text(text)
        if runs:
            changed += 1
            replacements += runs
            if args.dry_run:
                print("would convert %s (%d tab run(s))" % (path, runs))
            else:
                with open(path, "w", encoding="utf-8", newline="") as handle:
                    handle.write(new_text)
                print("converted %s (%d tab run(s))" % (path, runs))

    if args.check:
        for path, line_no, content in failures:
            print("%s:%d: unconverted tab header: %s" % (path, line_no, content))
        print("tabs --check: %d file(s) scanned, %d failure(s)"
              % (scanned, len(failures)))
        return 2 if failures else 0

    verb = "would change" if args.dry_run else "changed"
    print("tabs: %d file(s) scanned, %d %s, %d tab run(s)"
          % (scanned, changed, verb, replacements))
    return 0


if __name__ == "__main__":
    sys.exit(main())
