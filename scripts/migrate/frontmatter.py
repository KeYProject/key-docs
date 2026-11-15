#!/usr/bin/env python3
"""Normalise the Hugo front matter of every migrated content page.

The migration map (``scripts/migration_map.yml``) is authoritative for page
``title`` (its ``label``) and sibling order (its ``weight``).  This script:

* repairs the ``ADTs.md`` shape (keys before the opening ``---`` fence),
* creates front matter where a page has none,
* sets ``title`` and ``weight`` from the map,
* renames a non-ISO ``date`` to ``date_label`` (Hugo reserves ``date`` for
  real dates) and keeps ISO dates as ``date``,
* preserves every other key (``approved``, ``author``, ``valid_for``,
  ``updated``, ``history``, ...) verbatim, and
* removes the first body H1, turning a ``{#id}`` attribute into a leading
  ``<span id="id"></span>`` anchor.

Usage::

    frontmatter.py content scripts/migration_map.yml --check    # verify only
    frontmatter.py content scripts/migration_map.yml --dry-run  # print plan
    frontmatter.py content scripts/migration_map.yml            # apply
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

ROOT_PAGE = "_index.md"
FENCE = "---"
KEY_RE = re.compile(r"^([A-Za-z_][\w-]*):(.*)$")
H1_RE = re.compile(r"^#\s+(.*?)\s*$")
ANCHOR_RE = re.compile(r"\{#([^}\s]+)\}\s*$")
ISO_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
REASONS = ("title", "weight", "date_label", "h1", "frontmatter")


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def repo_root() -> Path:
    """Repository root (``scripts/migrate/frontmatter.py`` -> root)."""
    return Path(__file__).resolve().parents[2]


def yaml_str(value: str) -> str:
    """Quote a scalar for the generated front matter."""
    return json.dumps(value, ensure_ascii=False)


def normalise(text: str) -> str:
    """Normalise BOM, line endings and trailing whitespace."""
    text = text.lstrip("\ufeff").replace("\r\n", "\n").replace("\r", "\n")
    return "\n".join(line.rstrip() for line in text.split("\n"))


def entry_key(line: str) -> str | None:
    """Top-level YAML key of ``line`` (``None`` for continuations)."""
    if line[:1] in (" ", "\t"):
        return None
    match = KEY_RE.match(line)
    return match.group(1) if match else None


def read_front_matter(text: str) -> tuple[list[str], str, str]:
    """Split ``text`` into raw front matter lines, body and a shape marker.

    The marker is ``"fenced"`` for a normal ``---`` block, ``"unfenced"`` for
    the repaired ADTs shape (keys before the first ``---``) and ``"none"``.
    """
    lines = text.split("\n")
    if lines and lines[0].strip() == FENCE:
        for end in range(1, len(lines)):
            if lines[end].strip() == FENCE:
                return lines[1:end], "\n".join(lines[end + 1 :]), "fenced"
        raise ValueError("front matter is not closed by '---'")

    # ADTs shape: the file starts with top-level `key: value` lines and the
    # closing fence is the first `---`.
    if lines and entry_key(lines[0]):
        for end in range(1, len(lines)):
            if lines[end].strip() == FENCE:
                # every line before the fence must belong to the front matter
                allowed = all(
                    line.strip() == ""
                    or entry_key(line) is not None
                    or line[:1] in (" ", "\t")
                    or line.startswith("- ")
                    for line in lines[:end]
                )
                if allowed:
                    return lines[:end], "\n".join(lines[end + 1 :]), "unfenced"

    return [], text, "none"


def parse_entries(front_matter: list[str]) -> list[list]:
    """Group raw front matter lines into ``[key, lines]`` entries."""
    entries: list[list] = []
    for line in front_matter:
        key = entry_key(line)
        if key is not None:
            entries.append([key, [line]])
        elif line.strip() == "":
            continue
        elif entries:
            entries[-1][1].append(line)
        else:
            raise ValueError(f"unexpected front matter line: {line!r}")
    return entries


def entry_value(entry: list) -> str:
    """Scalar value of a one-line entry (empty string for nested values)."""
    first = entry[1][0]
    return first.split(":", 1)[1].strip()


def strip_h1(body: str) -> tuple[str, str | None, str | None]:
    """Remove the first body H1; return body, heading text and ``{#id}`` anchor.

    Blank lines and leading raw HTML ``<style>`` blocks are skipped, so an H1
    that follows a generated style block is still recognised as the page title.
    """
    lines = body.split("\n")
    index = 0
    while index < len(lines):
        if lines[index].strip() == "":
            index += 1
        elif lines[index].lstrip().lower().startswith("<style"):
            while index < len(lines) and "</style>" not in lines[index].lower():
                index += 1
            index += 1
        else:
            break
    if index >= len(lines) or not lines[index].startswith("# "):
        return body.strip("\n"), None, None

    heading = H1_RE.match(lines[index]).group(1)
    anchor = None
    match = ANCHOR_RE.search(heading)
    if match:
        anchor = match.group(1)
        heading = heading[: match.start()].rstrip()
    preamble = lines[:index]
    rest = lines[index + 1 :]
    while preamble and preamble[-1].strip() == "":
        preamble.pop()
    while rest and rest[0].strip() == "":
        rest.pop(0)
    if anchor:
        rest.insert(0, "")
        rest.insert(0, f'<span id="{anchor}"></span>')
    if preamble:
        rest = preamble + [""] + rest
    return "\n".join(rest), heading, anchor


def render(front_matter: list[str], body: str) -> str:
    """Assemble a content page from front matter lines and body."""
    body = body.strip("\n")
    text = FENCE + "\n" + "\n".join(front_matter) + "\n" + FENCE + "\n"
    if body:
        text += "\n" + body + "\n"
    return text


# --------------------------------------------------------------------------
# transformation
# --------------------------------------------------------------------------
def transform(path: Path, label: str, weight: int) -> tuple[str, list[str]]:
    """Return the normalised text for ``path`` plus the reasons it changed."""
    original = path.read_text(encoding="utf-8")
    text = normalise(original)
    front_matter, body, shape = read_front_matter(text)
    entries = parse_entries(front_matter)
    reasons: list[str] = []
    if shape != "fenced":
        reasons.append("frontmatter")

    # title and weight come from the map; keep every other key as written
    head = [f"title: {yaml_str(label)}", f"weight: {weight}"]
    existing = {entry[0]: entry for entry in entries}
    for key, line in zip(("title", "weight"), head):
        if key not in existing or existing[key][1] != [line]:
            reasons.append(key)

    kept: list[str] = []
    for entry in entries:
        key, lines = entry
        if key in ("title", "weight"):
            continue
        if key == "date":
            value = entry_value(entry).strip("\"'")
            if value and not ISO_DATE_RE.match(value):
                lines = ["date_label:" + lines[0].split(":", 1)[1], *lines[1:]]
                reasons.append("date_label")
        kept.extend(lines)

    body, heading, _anchor = strip_h1(body)
    if heading is not None:
        reasons.append("h1")

    new_text = render(head + kept, body)
    unchanged = new_text == original
    return new_text, [] if unchanged else sorted(set(reasons), key=REASONS.index)


def load_map(map_path: Path) -> dict[str, dict]:
    raw = yaml.safe_load(map_path.read_text(encoding="utf-8"))
    if not isinstance(raw, list):
        raise SystemExit(f"error: {map_path} must contain a YAML list")
    pages: dict[str, dict] = {}
    for entry in raw:
        if not isinstance(entry, dict) or not entry.get("new"):
            continue
        new = str(entry["new"]).replace(os.sep, "/")
        pages[new] = entry
    return pages


def content_pages(content: Path) -> list[Path]:
    return [
        path
        for path in sorted(content.rglob("*.md"))
        if path.relative_to(content).as_posix() != ROOT_PAGE
    ]


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("content", nargs="?", default="content")
    parser.add_argument("map", nargs="?", default="scripts/migration_map.yml")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="verify only")
    mode.add_argument("--dry-run", action="store_true", help="print the plan only")
    parser.add_argument("--repo", default=None, help="repository root")
    args = parser.parse_args(argv)

    root = Path(args.repo).resolve() if args.repo else repo_root()
    content = Path(args.content)
    if not content.is_absolute():
        content = root / content
    map_path = Path(args.map)
    if not map_path.is_absolute():
        map_path = root / map_path

    pages = load_map(map_path)
    files = content_pages(content)
    errors = 0
    changed = 0

    print(f"{len(files)} page(s) under {content.relative_to(root)}/")
    for path in files:
        rel = path.relative_to(content).as_posix()
        entry = pages.get(rel)
        if entry is None:
            print(f"ERROR: {rel}: no entry in the migration map")
            errors += 1
            continue
        if not isinstance(entry.get("weight"), int):
            print(f"ERROR: {rel}: map entry has no integer weight")
            errors += 1
            continue
        try:
            new_text, reasons = transform(path, entry["label"], entry["weight"])
        except ValueError as exc:
            print(f"ERROR: {rel}: {exc}")
            errors += 1
            continue
        if not reasons:
            continue
        changed += 1
        detail = ", ".join(reasons)
        if args.check:
            print(f"CHANGED {rel}: {detail}")
        elif args.dry_run:
            print(f"[dry-run] {rel}: {detail}")
        else:
            path.write_text(new_text, encoding="utf-8")
            print(f"updated {rel}: {detail}")

    if args.check:
        if errors or changed:
            print(f"\nFAIL: {changed} page(s) need normalising, {errors} error(s)")
            return 1
        print("\nPASS: front matter, titles, weights and anchors are normalised")
        return 0
    if errors:
        print(f"\nFAIL: {errors} error(s)")
        return 1
    prefix = "[dry-run] " if args.dry_run else ""
    print(f"\n{prefix}{changed} page(s) {'would be ' if args.dry_run else ''}updated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
