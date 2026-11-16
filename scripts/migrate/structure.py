#!/usr/bin/env python3
"""Move the MkDocs page tree into the Hugo content tree according to a map.

The map (``scripts/migration_map.yml``) is the single source of truth for the
MkDocs -> Hugo migration.  One entry per old page::

    - old: quicktour/loading.md
      new: user/getting-started/loading/index.md
      label: Loading JML Contracts
      parent: user/getting-started
      weight: 30
      bundle: true

Semantics (see also ``.superpowers/sdd/target-tree.md``):

* ``bundle: true``  -- ``new`` is a *leaf bundle* directory ending in
  ``/index.md``.  ``old`` may be any ``.md`` file.  When ``old`` itself ends in
  ``/index.md`` the whole old directory is moved with ``git mv`` so that bundle
  assets (images, downloads, ...) travel with the page.
* ``bundle: false`` -- ``new`` is a regular page file, or a section landing page
  ending in ``/_index.md``.  Section landings (``old: null``) are created with
  ``title``, ``weight``, ``approved: none`` and a one-sentence body placeholder.
* ``action`` (optional, default ``move``): ``move``, ``drop`` (delete ``old``)
  or ``already-migrated`` (delete ``old``, leave the existing ``new`` alone).

Usage::

    structure.py --map scripts/migration_map.yml --check     # validate only
    structure.py --map scripts/migration_map.yml --dry-run   # print the plan
    structure.py --map scripts/migration_map.yml             # apply the plan
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

DOCS_DIR = "docs"
CONTENT_DIR = "content"
PLACEHOLDER_BODY = "This chapter is part of the KeY documentation."
ACTIONS = ("move", "drop", "already-migrated")
REQUIRED_KEYS = ("old", "new")
KNOWN_KEYS = ("old", "new", "label", "parent", "weight", "bundle", "action")


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def repo_root() -> Path:
    """Repository root (``scripts/migrate/structure.py`` -> root)."""
    return Path(__file__).resolve().parents[2]


def norm(path: str) -> str:
    """Normalise a repo-relative path (``./a//b`` -> ``a/b``)."""
    path = path.replace(os.sep, "/")
    while path.startswith("./"):
        path = path[2:]
    return os.path.normpath(path).replace(os.sep, "/")


def is_section_page(new: str) -> bool:
    return new.endswith("/_index.md") or new == "_index.md"


def is_bundle_page(new: str) -> bool:
    """``new`` is a leaf bundle, i.e. ``<dir>/index.md`` (not ``_index.md``)."""
    return new.endswith("/index.md") and not new.endswith("/_index.md")


def is_old_index(old: str) -> bool:
    return old.endswith("/index.md") or old == "index.md"


def parent_of(new: str) -> str | None:
    """Expected ``parent`` value for a destination path."""
    if is_bundle_page(new) or is_section_page(new):
        # the page (bundle dir / section page) sits one level below its parent
        parent = os.path.dirname(os.path.dirname(new))
    else:
        parent = os.path.dirname(new)
    parent = parent.replace(os.sep, "/")
    return parent or None


def yaml_str(value: str) -> str:
    """Quote a scalar for the generated front matter."""
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def section_text(label: str, weight: int) -> str:
    return (
        "---\n"
        f"title: {yaml_str(label)}\n"
        f"weight: {weight}\n"
        "approved: none\n"
        "---\n"
        "\n"
        f"{PLACEHOLDER_BODY}\n"
    )


def git(*args: str, root: Path) -> None:
    subprocess.run(["git", *args], cwd=root, check=True)


def describe(kind: str, path: str) -> str:
    return f"{kind} {path}"


# --------------------------------------------------------------------------
# map loading / validation
# --------------------------------------------------------------------------
class Plan:
    """Validated migration plan."""

    def __init__(self, entries: list[dict], root: Path):
        self.root = root
        self.entries = entries
        self.sections = [e for e in entries if e["old"] is None]
        self.drops = [e for e in entries if e["action"] == "drop"]
        self.done = [e for e in entries if e["action"] == "already-migrated"]
        self.moves = [
            e for e in entries if e["action"] == "move" and e["old"] is not None
        ]

    # -- classification ----------------------------------------------------
    @property
    def directory_moves(self) -> list[dict]:
        return [
            e
            for e in self.moves
            if is_old_index(e["old"]) and is_bundle_page(e["new"])
        ]

    @property
    def file_moves(self) -> list[dict]:
        return [e for e in self.moves if e not in self.directory_moves]

    def docs_files(self) -> set[str]:
        docs = self.root / DOCS_DIR
        found = set()
        for path in docs.rglob("*.md"):
            if path.is_file():
                found.add(path.relative_to(docs).as_posix())
        return found


def load_map(path: Path) -> list[dict]:
    raw = yaml.safe_load(path.read_text())
    if not isinstance(raw, list):
        raise SystemExit(f"error: {path} must contain a YAML list of mappings")
    entries = []
    for index, item in enumerate(raw, start=1):
        if not isinstance(item, dict):
            raise SystemExit(f"error: entry #{index} is not a mapping")
        entry = {}
        for key in KNOWN_KEYS:
            entry[key] = item.get(key, None)
        entry["action"] = item.get("action", "move")
        entry["_line"] = index
        entry["_raw"] = item
        for key in REQUIRED_KEYS:
            if key not in item:
                raise SystemExit(f"error: entry #{index} lacks required key {key!r}")
        entries.append(entry)
    return entries


def detect_state(plan: Plan) -> tuple[str, list[str]]:
    """Tell whether the plan is still pending, already applied, or in between."""
    docs = plan.root / DOCS_DIR
    olds = [e["old"] for e in plan.entries if e["old"] is not None]
    present = [old for old in olds if (docs / old).exists()]
    if not olds:
        return "pending", []
    if len(present) == len(olds):
        return "pending", []
    if not present:
        return "applied", []
    missing = [old for old in olds if old not in present]
    return "partial", [
        f"partially applied map: {len(missing)} old page(s) no longer exist, e.g. "
        f"{DOCS_DIR}/{missing[0]}"
    ]


def validate(plan: Plan) -> tuple[list[str], str]:
    errors: list[str] = []
    entries = plan.entries
    docs_found = plan.docs_files()
    state, state_errors = detect_state(plan)
    errors.extend(state_errors)

    # ---- per-entry schema ------------------------------------------------
    for e in entries:
        where = f"entry #{e['_line']}"
        raw = e["_raw"]
        unknown = set(raw) - set(KNOWN_KEYS)
        if unknown:
            errors.append(f"{where}: unknown key(s) {sorted(unknown)}")
        if e["action"] not in ACTIONS:
            errors.append(f"{where}: invalid action {e['action']!r}")
            continue
        if e["old"] is not None:
            e["old"] = norm(str(e["old"]))
        if e["new"] is not None:
            e["new"] = norm(str(e["new"]))

        if e["action"] == "drop":
            if e["old"] is None:
                errors.append(f"{where}: drop requires an 'old' path")
            if e["new"] is not None:
                errors.append(f"{where}: drop must not have a 'new' path")
            continue

        if e["old"] is None and e["action"] != "move":
            errors.append(f"{where}: 'old: null' implies a section landing (move)")
            continue

        if e["new"] is None:
            errors.append(f"{where}: {e['action']} requires a 'new' path")
            continue

        for key in ("label", "parent", "weight", "bundle"):
            if key not in raw:
                errors.append(f"{where}: missing required key {key!r}")
        if not isinstance(e["label"], str) or not e["label"].strip():
            errors.append(f"{where}: 'label' must be a non-empty string")
        if not isinstance(e["weight"], int) or isinstance(e["weight"], bool):
            errors.append(f"{where}: 'weight' must be an integer")
        if not isinstance(e["bundle"], bool):
            errors.append(f"{where}: 'bundle' must be a boolean")
        if e["parent"] is not None:
            e["parent"] = norm(str(e["parent"]))
        expected_parent = parent_of(e["new"])
        if e["parent"] != expected_parent:
            errors.append(
                f"{where}: parent {e['parent']!r} != {expected_parent!r} "
                f"implied by new path {e['new']!r}"
            )

        # bundle semantics
        if e["bundle"] is True and not is_bundle_page(e["new"]):
            errors.append(
                f"{where}: bundle: true needs a 'new' ending in '/index.md', "
                f"got {e['new']!r}"
            )
        if e["bundle"] is False and is_bundle_page(e["new"]):
            errors.append(
                f"{where}: bundle: false but 'new' is a leaf bundle "
                f"({e['new']!r}); use bundle: true"
            )

        # section landings
        if e["old"] is None:
            if not is_section_page(e["new"]):
                errors.append(
                    f"{where}: section landing must end in '/_index.md', "
                    f"got {e['new']!r}"
                )
            if e["bundle"] is True:
                errors.append(f"{where}: section landing must be bundle: false")
        else:
            if "old" not in raw:
                errors.append(f"{where}: missing required key 'old'")
            if not e["old"].endswith(".md"):
                errors.append(f"{where}: old path must be a .md file")
            if state == "pending" and e["old"] not in docs_found:
                errors.append(f"{where}: old file {DOCS_DIR}/{e['old']} not found")
            if is_section_page(e["new"]) and e["bundle"] is True:
                errors.append(
                    f"{where}: section page {e['new']!r} must be bundle: false"
                )

    # ---- uniqueness ------------------------------------------------------
    olds: dict[str, int] = {}
    news: dict[str, int] = {}
    for e in entries:
        if e["old"] is not None:
            olds.setdefault(e["old"], 0)
            olds[e["old"]] += 1
        if e["new"] is not None:
            news.setdefault(e["new"], 0)
            news[e["new"]] += 1
    for old, count in sorted(olds.items()):
        if count > 1:
            errors.append(f"duplicate old path mapped {count} times: {old}")
    for new, count in sorted(news.items()):
        if count > 1:
            errors.append(f"duplicate new path mapped {count} times: {new}")

    # ---- coverage --------------------------------------------------------
    for unmapped in sorted(docs_found - set(olds)):
        errors.append(f"unmapped old page: {DOCS_DIR}/{unmapped}")

    # ---- plan-level rules ------------------------------------------------
    sections = {e["new"] for e in plan.sections}
    mapped_sections = {
        e["new"]
        for e in plan.entries
        if e["new"] is not None and is_section_page(e["new"])
    }
    # every parent needs a section landing
    for e in entries:
        parent = e["parent"]
        if parent is None:
            continue
        if f"{parent}/_index.md" not in mapped_sections:
            errors.append(
                f"entry #{e['_line']}: parent {parent!r} has no '_index.md' section "
                f"entry in the map"
            )
    # every section needs children
    parents = {e["parent"] for e in entries if e["parent"] is not None}
    for section in sorted(sections):
        if section not in {f"{p}/_index.md" for p in parents}:
            errors.append(f"section {section} has no child entries")

    # weights must be unique among siblings
    by_parent: dict[str | None, dict[int, str]] = {}
    for e in entries:
        if e["weight"] is None:
            continue
        weights = by_parent.setdefault(e["parent"], {})
        if e["weight"] in weights:
            errors.append(
                f"duplicate weight {e['weight']} under parent {e['parent']!r}: "
                f"{weights[e['weight']]} and {e['new']}"
            )
        weights[e["weight"]] = e["new"]

    # leaf bundle directory moves must not swallow other pages
    dropped = {e["old"] for e in plan.drops}
    if state == "pending":
        for e in plan.directory_moves:
            old_dir = (plan.root / DOCS_DIR / e["old"]).parent
            for sibling in sorted(old_dir.rglob("*.md")):
                rel = sibling.relative_to(plan.root / DOCS_DIR).as_posix()
                if rel == e["old"] or rel in dropped:
                    continue
                errors.append(
                    f"entry #{e['_line']}: directory move of "
                    f"{old_dir.relative_to(plan.root)}"
                    f" would also move {DOCS_DIR}/{rel}; map or drop it explicitly"
                )

    # ---- targets: free before the move, occupied afterwards --------------
    root = plan.root
    for e in entries:
        if e["new"] is None:
            continue
        target = root / CONTENT_DIR / e["new"]
        if state == "applied":
            if not target.is_file():
                errors.append(
                    f"entry #{e['_line']}: missing target {CONTENT_DIR}/{e['new']}"
                )
            continue
        if e["action"] == "already-migrated":
            if not target.exists():
                errors.append(
                    f"entry #{e['_line']}: already-migrated target missing: "
                    f"{CONTENT_DIR}/{e['new']}"
                )
            continue
        if target.exists() and not (target.is_dir() and not any(target.iterdir())):
            errors.append(f"target already exists: {CONTENT_DIR}/{e['new']}")
        if is_bundle_page(e["new"]) or e["bundle"] is True:
            # bundle directory may not clash with an existing non-empty directory
            bundle_dir = target.parent
            if bundle_dir.exists() and bundle_dir.is_dir():
                if any(bundle_dir.iterdir()):
                    errors.append(
                        f"bundle directory not empty: {bundle_dir.relative_to(root)}"
                    )

    # ---- post-conditions of the created section landings -----------------
    if state == "applied":
        for e in plan.sections:
            target = root / CONTENT_DIR / e["new"]
            if not target.is_file():
                continue  # already reported above
            expected = section_text(e["label"], e["weight"])
            if target.read_text() != expected:
                errors.append(
                    f"entry #{e['_line']}: section page {CONTENT_DIR}/{e['new']} "
                    f"does not match the expected front matter/placeholder"
                )

    return errors, state


# --------------------------------------------------------------------------
# planning / applying
# --------------------------------------------------------------------------
def plan_lines(plan: Plan) -> list[str]:
    lines = []
    for e in plan.drops:
        lines.append(f"drop        {DOCS_DIR}/{e['old']}")
    for e in plan.done:
        lines.append(
            f"delete      {DOCS_DIR}/{e['old']} (already migrated to "
            f"{CONTENT_DIR}/{e['new']})"
        )
    for e in plan.directory_moves:
        src = (plan.root / DOCS_DIR / e["old"]).parent
        dst = (plan.root / CONTENT_DIR / e["new"]).parent
        lines.append(
            f"move dir    {src.relative_to(plan.root)} -> {dst.relative_to(plan.root)}"
        )
    for e in plan.file_moves:
        lines.append(
            f"move file   {DOCS_DIR}/{e['old']} -> {CONTENT_DIR}/{e['new']}"
        )
    for e in plan.sections:
        lines.append(f"create      {CONTENT_DIR}/{e['new']}")
    return lines


def apply_plan(plan: Plan) -> None:
    root = plan.root
    docs = root / DOCS_DIR
    content = root / CONTENT_DIR

    for e in plan.drops:
        git("rm", "-q", str(docs / e["old"]), root=root)

    for e in plan.done:
        if not (content / e["new"]).exists():
            raise SystemExit(
                f"error: already-migrated target missing: {CONTENT_DIR}/{e['new']}"
            )
        git("rm", "-q", str(docs / e["old"]), root=root)

    for e in plan.directory_moves:
        src = (docs / e["old"]).parent
        dst = (content / e["new"]).parent
        dst.parent.mkdir(parents=True, exist_ok=True)
        if dst.exists():
            if any(dst.iterdir()):
                raise SystemExit(f"error: destination not empty: {dst}")
            dst.rmdir()
        git("mv", str(src), str(dst), root=root)

    for e in plan.file_moves:
        src = docs / e["old"]
        dst = content / e["new"]
        dst.parent.mkdir(parents=True, exist_ok=True)
        git("mv", str(src), str(dst), root=root)

    for e in plan.sections:
        dst = content / e["new"]
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(section_text(e["label"], e["weight"]))


def leftover_assets(plan: Plan) -> list[str]:
    docs = plan.root / DOCS_DIR
    leftovers = sorted(
        path.relative_to(plan.root).as_posix()
        for path in docs.rglob("*")
        if path.is_file() and path.suffix != ".md"
    )
    return leftovers


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--map", required=True, help="path to the mapping YAML")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="validate only")
    mode.add_argument("--dry-run", action="store_true", help="print the plan only")
    parser.add_argument("--repo", default=None, help="repository root")
    args = parser.parse_args(argv)

    root = Path(args.repo).resolve() if args.repo else repo_root()
    map_path = Path(args.map)
    if not map_path.is_absolute():
        map_path = root / map_path

    entries = load_map(map_path)
    plan = Plan(entries, root)
    errors, state = validate(plan)

    docs_found = plan.docs_files()
    mapped = sum(1 for e in entries if e["old"] is not None)
    unmapped = len(docs_found - {e["old"] for e in entries if e["old"] is not None})
    collisions = sum(1 for error in errors if "already exists" in error or
                     "not empty" in error)
    print(f"{mapped} mapped, {len(docs_found)} found, {unmapped} unmapped, "
          f"{collisions} collisions")
    print(
        f"sections: {len(plan.sections)} to create, "
        f"moves: {len(plan.moves)} ({len(plan.directory_moves)} directories, "
        f"{len(plan.file_moves)} files), deletions: "
        f"{len(plan.drops) + len(plan.done)}; state: {state}"
    )

    if errors:
        print()
        for error in errors:
            print(f"ERROR: {error}")
        print(f"\n{len(errors)} problem(s) found; nothing was changed")
        return 1

    if args.check:
        print("map OK" if state == "pending" else "map OK (already applied)")
        return 0

    if state == "applied":
        print("nothing to do; the map is already applied")
        return 0

    if args.dry_run:
        print()
        for line in plan_lines(plan):
            print(f"[dry-run] {line}")
        leftover = leftover_assets(plan)
        print(
            f"[dry-run] {len(leftover)} non-Markdown file(s) stay under "
            f"{DOCS_DIR}/ for the asset task"
        )
        return 0

    apply_plan(plan)
    print()
    for line in plan_lines(plan):
        print(f"done        {line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
