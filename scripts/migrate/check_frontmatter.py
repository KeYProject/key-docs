#!/usr/bin/env python3
"""Verify the normalised front matter of the Hugo content pages.

Exits non-zero unless, for every ``content/**/*.md`` except the site root page

* ``title`` and ``weight`` are present in the front matter,
* the body does not start with a Markdown H1,
* a ``date`` value (if any) is ISO 8601 (``YYYY-MM-DD``), since Hugo reserves
  that key for real dates; free-text dates belong in ``date_label``.

Usage::

    check_frontmatter.py content
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from frontmatter import (  # noqa: E402
    ISO_DATE_RE,
    ROOT_PAGE,
    entry_value,
    parse_entries,
    read_front_matter,
    strip_h1,
)

WEIGHT_RE = re.compile(r"^-?\d+$")


def check_page(path: Path) -> list[str]:
    """Return the problems found in one page (empty list when it is fine)."""
    problems: list[str] = []
    try:
        front_matter, body, shape = read_front_matter(path.read_text("utf-8"))
    except ValueError as exc:
        return [f"front matter: {exc}"]

    if shape == "none":
        return ["missing front matter"]
    if shape == "unfenced":
        problems.append("front matter keys before the opening '---' fence")

    try:
        entries = {entry[0]: entry for entry in parse_entries(front_matter)}
    except ValueError as exc:
        return [f"front matter: {exc}"]

    if "title" not in entries or not entry_value(entries["title"]):
        problems.append("missing or empty 'title'")
    if "weight" not in entries:
        problems.append("missing 'weight'")
    elif not WEIGHT_RE.match(entry_value(entries["weight"])):
        problems.append(f"'weight' is not an integer: {entry_value(entries['weight'])!r}")

    if "date" in entries:
        date = entry_value(entries["date"]).strip("\"'")
        if not ISO_DATE_RE.match(date):
            problems.append(f"non-ISO 'date' {date!r} (rename to 'date_label')")

    _body, heading, _anchor = strip_h1(body)
    if heading is not None:
        problems.append(f"body starts with an H1: '# {heading}'")

    return problems


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    content = Path(args[0]) if args else Path("content")
    if not content.is_dir():
        print(f"error: {content} is not a directory")
        return 2

    files = [
        path
        for path in sorted(content.rglob("*.md"))
        if path.relative_to(content).as_posix() != ROOT_PAGE
    ]
    failures = 0
    for path in files:
        problems = check_page(path)
        if not problems:
            continue
        failures += 1
        rel = path.relative_to(content).as_posix()
        for problem in problems:
            print(f"FAIL {rel}: {problem}")

    print(f"{len(files)} page(s) checked, {failures} failing")
    if failures:
        print("FAIL")
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
