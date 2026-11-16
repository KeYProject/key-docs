#!/usr/bin/env python3
"""Rewrite Markdown links after a content move, using an old -> new map.

The mapping file is the ``scripts/migration_map.yml`` produced by the structure
task (JSON is accepted as well).  Example entry::

    - old: quicktour/loading.md
      new: user/getting-started/loading/index.md

``old``/``new`` are relative to the old ``docs/`` root and the new ``content/``
root respectively.  Links are resolved in the *old* namespace, mapped to the new
target, and re-emitted as a **URL-relative** path such as ``../install/`` (the
form the rendered Hugo site needs).  Fragments (``#section``) and queries are
preserved; fragment-only, absolute, and external links are left untouched.

Assets:
* a page bundle keeps its assets beside ``index.md`` (plain relative name),
* a regular page gets its assets from ``static/<parent-of-page-URL>/...`` so
  the link gains the ``../`` prefix Hugo/MkDocs need.

Pandoc/MkDocs leftovers are removed: ``{reference-type="ref" ...}``,
``{: ...}`` / ``{.class}`` attribute lists without meaning, and image
attribute lists (``{ width="800" }``) are turned into literal ``<img>`` tags.
Colon attribute lists that carry an anchor (``{: #id}`` / ``{:#id}``) are
**never** removed; they are owned by ``anchors.py``.

Pipeline order (important):
    links.py  ->  anchors.py  ->  icons.py
``anchors.py`` must run **after** ``links.py``: links only rewrites link
destinations and leaves the colon-form anchors for ``anchors.py`` to convert.

Usage:
    python3 links.py [CONTENT_ROOT] [--map MAPPING] [--dry-run] [--check]
                     [--style {url,md}] [--exclude PATH]...

``--check`` resolves every local link, image, and download against the
published URL namespace and exits 2 when a target cannot be resolved.

Exit codes: 0 on success, 2 when --check finds unresolved targets.
"""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(os.path.dirname(HERE))
DEFAULT_MAP = os.path.join(REPO_ROOT, "scripts", "migration_map.yml")

FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
MD_LINK_RE = re.compile(
    r"(!?\[[^\]]*\]\()"
    r"(\s*)"
    r"(<[^>\n]*>|[^\s)]+)"
    r"(\s+(?:\"[^\"\n]*\"|'[^'\n]*'|\([^)\n]*\)))?"
    r"(\s*\))"
)
REF_DEF_RE = re.compile(r"^(\s{0,3}\[(?!\^)[^\]]+\]:[ \t]*)(<[^>]*>|\S+)(.*)$")
HTML_ATTR_RE = re.compile(r"\b(src|href)=([\"'])([^\"']*)\2")
SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
PAGE_BASENAMES = ("index.md", "_index.md")

# Pandoc cross-reference leftovers: {reference-type="ref" reference="..."}
REF_LEFTOVER_RE = re.compile(
    r"\s*\{(?=[^{}]*\b(?:reference-type|reference)\s*=)[^{}]*\}")
# MkDocs attr_list leftovers on images: ![...](...){ width="800" } / {: style="..."}
IMG_ATTR_RE = re.compile(
    r"(!\[([^\]\n]*)\]\(([^)\s]+)(?:\s+\"([^\"\n]*)\")?\))"
    r"\s*\{:?\s*([^{}\n]*)\}"
)
# Any remaining {: ...} attribute list and class-only {.foo .bar} lists.
# `{: #id}` / `{:#id}` are Python-Markdown anchors owned by anchors.py: the
# negative lookahead keeps links.py idempotent and order-independent.
COLON_ATTR_RE = re.compile(r"\{:\s*(?!\s*#)[^{}\n]*\}")
CLASS_ATTR_RE = re.compile(r"\{\s*(?:\.[\w-]+(?:\s+\.[\w-]+)+|\.[\w-]+)\s*\}")
# Multi-line Pandoc leftovers: image + attribute block, and reference attrs.
MULTI_IMG_ATTR_RE = re.compile(
    r"(!\[([^\]]*)\]\(([^)\s]+)(?:\s+\"([^\"\n]*)\")?\))"
    r"\s*\{([^{}]*)\}", re.S)
MULTI_REF_LEFTOVER_RE = re.compile(
    r"\s*\{(?=[^{}]*\b(?:reference-type|reference)\s*=)[^{}]*\}", re.S)


# ---------------------------------------------------------------------------
# Mapping file loading (YAML subset or JSON, stdlib only)
# ---------------------------------------------------------------------------


def _unquote(raw):
    raw = raw.strip()
    if not raw:
        return ""
    if raw[0] in "\"'":
        quote = raw[0]
        out = []
        i = 1
        escapes = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "'": "'",
                   "\\": "\\"}
        while i < len(raw):
            c = raw[i]
            if c == "\\" and i + 1 < len(raw):
                out.append(escapes.get(raw[i + 1], raw[i + 1]))
                i += 2
                continue
            if c == quote:
                break
            out.append(c)
            i += 1
        return "".join(out)
    comment = re.search(r"\s+#", raw)
    if comment:
        raw = raw[:comment.start()]
    raw = raw.strip()
    if raw in ("", "null", "~", "Null", "NULL"):
        return None
    return raw


def _parse_yaml_subset(text):
    items = []
    current = None
    for raw in text.splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#") or stripped in ("---", "..."):
            continue
        m = re.match(r"^(\s*)-\s+(.*)$", raw)
        if m:
            current = {}
            items.append(current)
            rest = m.group(2)
            kv = re.match(r"^([A-Za-z_][\w-]*):\s*(.*)$", rest)
            if kv:
                current[kv.group(1)] = _unquote(kv.group(2))
            continue
        kv = re.match(r"^\s+([A-Za-z_][\w-]*):\s*(.*)$", raw)
        if kv and current is not None:
            current[kv.group(1)] = _unquote(kv.group(2))
    return items


def load_mapping(path):
    with open(path, "r", encoding="utf-8-sig") as handle:
        text = handle.read()
    stripped = text.lstrip()
    if path.endswith(".json") or stripped.startswith("[") or stripped.startswith("{"):
        data = json.loads(text)
        if isinstance(data, dict):
            data = data.get("pages") or data.get("entries") or []
        return [entry for entry in data if isinstance(entry, dict)]
    return _parse_yaml_subset(text)


def norm(path):
    path = path.replace("\\", "/")
    while path.startswith("./"):
        path = path[2:]
    if path in ("", "."):
        return "."
    return posixpath.normpath(path)


# ---------------------------------------------------------------------------
# URL helpers
# ---------------------------------------------------------------------------


def page_url(rel):
    """Published URL of a content Markdown file (pretty URLs, trailing slash)."""
    rel = norm(rel)
    base = posixpath.basename(rel)
    if base in PAGE_BASENAMES:
        directory = posixpath.dirname(rel)
        return "/" if directory in ("", ".") else "/" + directory + "/"
    return "/" + rel[:-3] + "/"


def norm_url(url):
    trailing = url.endswith("/")
    url = posixpath.normpath(url)
    if not url.startswith("/"):
        url = "/" + url
    if url.startswith("//"):
        url = "/" + url.lstrip("/")
    if trailing and not url.endswith("/"):
        url += "/"
    return url


def rel_url(target, source_rel):
    """Relative URL from the page URL of ``source_rel`` to ``target``."""
    base = page_url(source_rel)
    target_trailing = target.endswith("/")
    rel = posixpath.relpath(target.rstrip("/") or "/", base)
    if rel == ".":
        rel = "./"
    if target_trailing and not rel.endswith("/"):
        rel += "/"
    return rel


# ---------------------------------------------------------------------------
# Site index: published URLs of pages, bundle resources, and static files
# ---------------------------------------------------------------------------


class SiteIndex:
    def __init__(self, content_root, static_root):
        self.content_root = content_root
        self.static_root = static_root
        self.urls = set()
        self._scan()

    def _scan(self):
        bundle_dirs = set()
        for dirpath, dirnames, filenames in os.walk(self.content_root):
            dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
            rel_dir = os.path.relpath(dirpath, self.content_root).replace(
                os.sep, "/")
            if rel_dir == ".":
                rel_dir = ""
            has_page = False
            for name in filenames:
                if not name.endswith(".md"):
                    continue
                rel = posixpath.join(rel_dir, name) if rel_dir else name
                self.urls.add(page_url(rel))
                if name in PAGE_BASENAMES:
                    has_page = True
            if has_page:
                bundle_dirs.add(rel_dir)
            for name in filenames:
                if name.endswith(".md"):
                    continue
                if rel_dir in bundle_dirs and has_page:
                    prefix = page_url(
                        posixpath.join(rel_dir, "index.md")
                        if rel_dir else "index.md")
                    self.urls.add(prefix + name)
        if self.static_root and os.path.isdir(self.static_root):
            for dirpath, dirnames, filenames in os.walk(self.static_root):
                dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
                rel_dir = os.path.relpath(dirpath, self.static_root).replace(
                    os.sep, "/")
                if rel_dir == ".":
                    rel_dir = ""
                for name in filenames:
                    rel = posixpath.join(rel_dir, name) if rel_dir else name
                    self.urls.add("/" + rel)

    def lookup(self, url):
        """Return the canonical stored URL or None."""
        url = norm_url(url)
        if url in self.urls:
            return url
        if url.endswith("/"):
            stripped = url.rstrip("/")
            if stripped in self.urls:
                return stripped
        else:
            with_slash = url + "/"
            if with_slash in self.urls:
                return with_slash
        return None

    def has_path(self, rel_path):
        return os.path.exists(os.path.join(self.content_root, rel_path))


# ---------------------------------------------------------------------------
# Link index and old-namespace resolution
# ---------------------------------------------------------------------------


class LinkIndex:
    def __init__(self, entries, site):
        self.site = site
        self.old_to_new = {}
        self.new_to_old = {}
        self.dir_pairs = []
        self.new_paths = []
        for entry in entries:
            old = entry.get("old")
            new = entry.get("new")
            if not new:
                continue
            new = norm(str(new))
            if new.startswith("content/"):
                new = new[len("content/"):]
            self.new_paths.append(new)
            if not old:
                continue
            old = norm(str(old))
            self.old_to_new[old] = new
            self.new_to_old.setdefault(new, old)
            self.dir_pairs.append(
                (posixpath.dirname(old) or ".", posixpath.dirname(new) or "."))
        # Longest old directory first: more specific asset relocation wins.
        self.dir_pairs.sort(key=lambda pair: len(pair[0]), reverse=True)
        self.new_paths = sorted(set(self.new_paths))

        # Variants used for suffix matching when the source file itself is not
        # in the map (generated landing pages).
        self.suffix_index = []
        for new in self.new_paths:
            variants = {new, new[:-3] if new.endswith(".md") else new}
            base = posixpath.basename(new)
            if base in PAGE_BASENAMES:
                directory = posixpath.dirname(new)
                if directory:
                    variants.add(directory)
            for variant in variants:
                self.suffix_index.append((variant, new))

    # -- helpers ---------------------------------------------------------

    @staticmethod
    def old_url_dir(old_path):
        base = posixpath.basename(old_path)
        directory = posixpath.dirname(old_path)
        if base in PAGE_BASENAMES:
            return directory
        if base.endswith(".md"):
            stem = base[:-3]
            return posixpath.join(directory, stem) if directory else stem
        return directory

    def find_old(self, old_path):
        candidates = []
        if old_path in (".", ""):
            candidates = ["index.md"]
        elif old_path.endswith("/"):
            base = old_path.rstrip("/")
            candidates = [base + ".md", base + "/index.md"]
        else:
            candidates = [old_path]
            if not old_path.endswith(".md"):
                candidates.append(old_path + ".md")
                candidates.append(old_path + "/index.md")
        for candidate in candidates:
            hit = self.old_to_new.get(candidate)
            if hit:
                return hit
        return None

    def find_new_suffix(self, path):
        p = norm(path).strip("/")
        if p in ("", ".", ".."):
            return None
        if p.endswith(".md"):
            p = p[:-3]
        matches = {new for variant, new in self.suffix_index
                   if variant == p or variant.endswith("/" + p)}
        if len(matches) == 1:
            return matches.pop()
        return None

    def find_asset_url(self, old_path):
        """Map an old asset path to its published URL, or None."""
        # 1. Exact global/static placement.
        for prefix, rel in (("content", self.site.content_root),
                            ("static", self.site.static_root)):
            if not rel:
                continue
            candidate = norm(old_path)
            path = os.path.join(rel, candidate)
            if os.path.isfile(path):
                if prefix == "static":
                    return "/" + candidate
                return self._content_url(candidate)
        # 2. Directory relocation (bundle / static parent).
        for old_dir, new_dir in self.dir_pairs:
            if old_dir in ("", "."):
                continue
            prefix = old_dir + "/"
            if not old_path.startswith(prefix):
                continue
            rest = old_path[len(prefix):]
            if not rest:
                continue
            candidate = norm(posixpath.join(new_dir, rest))
            path = os.path.join(self.site.content_root, candidate)
            if os.path.isfile(path):
                url = self._content_url(candidate)
                if url:
                    return url
            if self.site.static_root:
                if os.path.isfile(os.path.join(self.site.static_root, candidate)):
                    return "/" + candidate
        return None

    def _content_url(self, rel):
        di = posixpath.dirname(rel)
        while True:
            for name in PAGE_BASENAMES:
                if os.path.isfile(os.path.join(
                        self.site.content_root, di, name)):
                    prefix = page_url(posixpath.join(di, name) if di else name)
                    return prefix + posixpath.relpath(rel, di or ".")
            if di in ("", "."):
                return None
            di = posixpath.dirname(di)

    # -- API -------------------------------------------------------------

    def resolve(self, target, rel_source):
        """Resolve one link target.

        Returns ``(target_url | None, status)`` where status is one of
        ``fragment``, ``external``, ``unchanged``, ``rewrite``, ``unresolved``.
        """
        path, hash_sep, fragment = target.partition("#")
        path, query_sep, query = path.partition("?")
        suffix = ("?" + query if query_sep else "") + \
                 ("#" + fragment if hash_sep else "")

        if path == "":
            return None, "fragment"
        if SCHEME_RE.match(path) or path.startswith("//"):
            return None, "external"

        # Root-relative links are left alone (they include the baseURL prefix
        # in most cases and are not part of the old source tree).
        if path.startswith("/"):
            return None, "external"

        source_url = page_url(rel_source)
        is_page = (path.endswith(".md") or path.endswith("/")
                   or posixpath.splitext(path)[1] == "")

        # 1. Already valid in the new URL namespace.
        candidate_url = norm_url(posixpath.join(source_url, path))
        hit = self.site.lookup(candidate_url) if is_page else (
            candidate_url if candidate_url in self.site.urls else None)
        if hit:
            return None, "unchanged"

        # 2. Old namespace: source-relative then MkDocs URL-relative.
        old_source = self.new_to_old.get(rel_source)
        if old_source:
            src_dir = posixpath.dirname(old_source)
            url_dir = self.old_url_dir(old_source)
            candidates = []
            for base in (src_dir, url_dir):
                cand = norm(posixpath.join(base, path)) if base else norm(path)
                if cand not in candidates:
                    candidates.append(cand)

            if is_page:
                for cand in candidates:
                    new_md = self.find_old(cand)
                    if new_md:
                        return page_url(new_md), "rewrite"
            else:
                for cand in candidates:
                    url = self.find_asset_url(cand)
                    if url:
                        return url, "rewrite"

        # 3. Fall back to a unique suffix match in the new tree (landing pages
        #    that have no old counterpart).
        if is_page:
            new_md = self.find_new_suffix(path)
            if new_md:
                return page_url(new_md), "rewrite"

        return None, "unresolved"

    def format_target(self, target_url, rel_source, style):
        if style == "url":
            return rel_url(target_url, rel_source)
        # legacy ``md`` style: filesystem-relative path
        target = target_url.strip("/")
        if target == "":
            return "."
        if target_url.endswith("/"):
            target = posixpath.join(target, "index.md")
        rel = posixpath.relpath(target, posixpath.dirname(rel_source))
        return rel


# ---------------------------------------------------------------------------
# Line rewriting
# ---------------------------------------------------------------------------


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


def _resolve_and_format(raw_target, rel_source, index, style,
                        unresolved, line_no, stats):
    wrapped = raw_target.startswith("<") and raw_target.endswith(">")
    inner = raw_target[1:-1] if wrapped else raw_target
    path, hash_sep, fragment = inner.partition("#")
    path, query_sep, query = path.partition("?")
    suffix = ("?" + query if query_sep else "") + \
             ("#" + fragment if hash_sep else "")
    target_url, status = index.resolve(inner, rel_source)
    stats["resolved" if status != "unresolved" else "unresolved"] += 1
    if status == "rewrite" and target_url:
        formatted = index.format_target(target_url, rel_source, style) + suffix
        return ("<%s>" % formatted) if wrapped else formatted
    if status == "unresolved":
        unresolved.append((line_no, inner))
    return None


def _attribute_dict(inside):
    values = {}
    for key, quoted, single, bare in re.findall(
            r"([A-Za-z_][\w-]*)\s*=\s*(?:\"([^\"]*)\"|'([^']*)'|([^\s}]+))",
            inside or ""):
        values[key.lower()] = quoted or single or bare
    return values


def _image_to_html(match):
    """Turn ``![alt](src){ width=... }`` into a literal ``<img>`` tag."""
    original, alt, src, title, attrs = match.groups()
    values = _attribute_dict(attrs)
    ident = None
    id_match = re.search(r"#([^\s{}]+)", attrs or "")
    if id_match:
        ident = id_match.group(1)
    meaningful = {}
    for key in ("width", "height", "style"):
        if key not in values:
            continue
        value = values[key].strip()
        if key in ("width", "height") and not re.match(
                r"^\d+(?:\.\d+)?(?:%|px|em|rem)?$", value):
            continue
        meaningful[key] = value
    if not meaningful and not ident:
        return original  # class/lazy-only lists are simply dropped
    alt = " ".join(alt.split())
    parts = ['src="%s"' % src, 'alt="%s"' % alt.replace('"', "&quot;")]
    if title:
        parts.append('title="%s"' % title.replace('"', "&quot;"))
    if ident:
        parts.append('id="%s"' % ident)
    for key in ("width", "height", "style"):
        if key in meaningful:
            parts.append('%s="%s"' % (key, meaningful[key]))
    return "<img %s />" % " ".join(parts)


def cleanup_line(line):
    """Remove Pandoc/MkDocs leftovers outside inline code."""
    spans = code_spans(line)

    def guard(pattern, repl):
        out = []
        last = 0
        for m in pattern.finditer(line):
            if _inside(m.start(), spans):
                continue
            out.append(line[last:m.start()])
            out.append(repl(m) if callable(repl) else repl)
            last = m.end()
        if not out:
            return line
        out.append(line[last:])
        return "".join(out)

    line = guard(REF_LEFTOVER_RE, "")
    line = guard(IMG_ATTR_RE, _image_to_html)
    line = guard(COLON_ATTR_RE, "")
    line = guard(CLASS_ATTR_RE, "")
    return line


def cleanup_block(block):
    """Document-level cleanup for leftovers that span physical lines."""
    block = MULTI_IMG_ATTR_RE.sub(_image_to_html, block)
    block = MULTI_REF_LEFTOVER_RE.sub("", block)
    block = COLON_ATTR_RE.sub("", block)
    block = CLASS_ATTR_RE.sub("", block)
    return block


def cleanup_document(text):
    """Apply :func:`cleanup_block` to unprotected (non-fenced) runs."""
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    flags = protected_flags(lines)
    out = []
    run = []

    def flush():
        if run:
            out.extend(cleanup_block("\n".join(run)).split("\n"))
            run.clear()

    for i, line in enumerate(lines):
        if flags[i]:
            flush()
            out.append(line)
        else:
            run.append(line)
    flush()
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    return result


def rewrite_line(line, rel_source, index, style, unresolved, line_no, stats):
    spans = code_spans(line)

    def md_repl(match):
        if _inside(match.start(), spans):
            return match.group(0)
        target = match.group(3)
        replacement = _resolve_and_format(
            target, rel_source, index, style, unresolved, line_no, stats)
        if replacement is None:
            return match.group(0)
        stats["replacements"] += 1
        return (match.group(1) + match.group(2) + replacement
                + (match.group(4) or "") + match.group(5))

    new_line = MD_LINK_RE.sub(md_repl, line)

    if new_line.lstrip().startswith("["):
        ref = REF_DEF_RE.match(new_line)
        if ref and not _inside(ref.start(2), code_spans(new_line)):
            replacement = _resolve_and_format(
                ref.group(2), rel_source, index, style,
                unresolved, line_no, stats)
            if replacement is not None:
                stats["replacements"] += 1
                new_line = ref.group(1) + replacement + ref.group(3)

    spans = code_spans(new_line)

    def html_repl(match):
        if _inside(match.start(), spans):
            return match.group(0)
        target = match.group(3)
        replacement = _resolve_and_format(
            target, rel_source, index, style, unresolved, line_no, stats)
        if replacement is None:
            return match.group(0)
        stats["replacements"] += 1
        return "%s=%s%s%s" % (match.group(1), match.group(2), replacement,
                              match.group(2))

    new_line = HTML_ATTR_RE.sub(html_repl, new_line)
    return cleanup_line(new_line)


def rewrite_multiline_links(text, rel_source, index, style, unresolved, stats):
    """Rewrite local links whose label spans physical lines."""
    lines = text.splitlines()
    flags = protected_flags(lines)
    out = []
    run = []
    start_line = 0

    def flush(base_line):
        if not run:
            return
        block = "\n".join(run)
        spans_by_line = [code_spans(line) for line in run]

        def repl(match):
            prefix = block[:match.start()]
            line_index = prefix.count("\n")
            col = match.start() - (prefix.rfind("\n") + 1)
            if _inside(col, spans_by_line[line_index]):
                return match.group(0)
            multiline = "\n" in match.group(0)
            local_unresolved = unresolved if multiline else []
            target = match.group(3)
            replacement = _resolve_and_format(
                target, rel_source, index, style, local_unresolved,
                base_line + line_index + 1, stats)
            if replacement is None:
                return match.group(0)
            stats["replacements"] += 1
            stats["multiline"] = stats.get("multiline", 0) + 1
            return (match.group(1) + match.group(2) + replacement
                    + (match.group(4) or "") + match.group(5))

        out.extend(MD_LINK_RE.sub(repl, block).split("\n"))
        run.clear()

    for i, line in enumerate(lines):
        if flags[i]:
            flush(start_line)
            out.append(line)
        else:
            if not run:
                start_line = i
            run.append(line)
    flush(start_line)
    result = "\n".join(out)
    if text.endswith("\n"):
        result += "\n"
    return result


def rewrite_document(text, rel_source, index, style="url"):
    trailing_newline = text.endswith("\n")
    lines = text.splitlines()
    flags = protected_flags(lines)
    out = []
    unresolved = []
    stats = {"replacements": 0, "resolved": 0, "unresolved": 0}
    for i, line in enumerate(lines):
        if flags[i]:
            out.append(line)
            continue
        out.append(rewrite_line(line, rel_source, index, style,
                                unresolved, i + 1, stats))
    result = "\n".join(out)
    if trailing_newline:
        result += "\n"
    result = cleanup_document(result)
    result = rewrite_multiline_links(result, rel_source, index, style,
                                     unresolved, stats)
    return result, stats, unresolved


# ---------------------------------------------------------------------------
# Exclusions
# ---------------------------------------------------------------------------


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
    for prefix in excluded:
        if rel == prefix or rel.startswith(prefix.rstrip("/") + "/"):
            return True
    return False


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def markdown_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".md"):
                yield os.path.join(dirpath, name)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("root", nargs="?", default="content",
                        help="content root to scan (default: content)")
    parser.add_argument("--map", dest="mapping", default=DEFAULT_MAP,
                        help="old -> new mapping file (YAML or JSON; "
                             "default: scripts/migration_map.yml)")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing files")
    parser.add_argument("--check", action="store_true",
                        help="fail (exit 2) on unresolved local targets")
    parser.add_argument("--style", choices=("url", "md"), default="url",
                        help="link style to emit (default: url)")
    parser.add_argument("--exclude", action="append", default=[],
                        metavar="PATH",
                        help="skip this file or directory (repeatable, "
                             "comma-separated values accepted)")
    args = parser.parse_args(argv)

    if not os.path.isdir(args.root):
        print("error: %s is not a directory" % args.root, file=sys.stderr)
        return 1
    if not os.path.isfile(args.mapping):
        print("error: %s is not a file" % args.mapping, file=sys.stderr)
        return 1

    entries = load_mapping(args.mapping)
    mapped = sum(1 for entry in entries if entry.get("old") and entry.get("new"))
    if not mapped:
        print("error: no usable entries in %s" % args.mapping, file=sys.stderr)
        return 1

    root = args.root.rstrip("/") or "content"
    static_root = os.path.join(os.path.dirname(root) or ".",
                               "static")
    site = SiteIndex(root, static_root)
    index = LinkIndex(entries, site)
    excluded = make_excluder(args.exclude, root)

    scanned = changed = replacements = 0
    all_unresolved = []

    for path in markdown_files(root):
        rel = os.path.relpath(path, root).replace(os.sep, "/")
        if is_excluded(rel, excluded):
            continue
        scanned += 1
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()
        new_text, stats, unresolved = rewrite_document(
            text, rel, index, style=args.style)
        replacements += stats["replacements"]
        for line_no, target in unresolved:
            all_unresolved.append((rel, line_no, target))
        if stats["replacements"] or new_text != text:
            changed += 1
            if not args.check:
                if args.dry_run:
                    print("would rewrite %s (%d link(s))"
                          % (rel, stats["replacements"]))
                else:
                    with open(path, "w", encoding="utf-8", newline="") as handle:
                        handle.write(new_text)
                    print("rewrote %s (%d link(s))"
                          % (rel, stats["replacements"]))

    if args.check:
        for rel, line_no, target in all_unresolved:
            print("%s:%d: unresolved target: %s" % (rel, line_no, target))
        print("links --check: %d file(s) scanned, %d unresolved"
              % (scanned, len(all_unresolved)))
        return 2 if all_unresolved else 0

    for rel, line_no, target in all_unresolved:
        print("warning: %s:%d: unresolved target: %s" % (rel, line_no, target))
    verb = "would change" if args.dry_run else "changed"
    print("links: %d file(s) scanned, %d %s, %d rewrite(s), %d unresolved"
          % (scanned, changed, verb, replacements, len(all_unresolved)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
