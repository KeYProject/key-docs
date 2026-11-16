#!/usr/bin/env python3
"""Convert a BibTeX file into a JSON object keyed by citation key.

Only the fields used by the KeY documentation bibliography are kept
(see KEPT_FIELDS).  The parser is dependency-free and handles the subset of
BibTeX that the KeY ``refs.bib`` uses:

* ``@STRING`` macro definitions (and the standard month macros),
* braced and quoted values, values concatenated with ``#``,
* numeric literals (``year = 1997``, ``volume = 1919``),
* nested/protective braces in titles (``The {KeY} Tool``),
* LaTeX accent escapes (``H\\"{a}hnle``, ``Wei{\\ss}``, ``Pren{\\-}tice``),
* ``@comment`` / ``@preamble`` blocks (ignored).

``note`` and ``howpublished`` are kept so that entries which carry only a
note/URL (``ICS``, ``Simplify``) still render as something readable in the
bibliography instead of a bare citation key.

Usage:
    python3 bib_to_json.py IN.bib OUT.json
"""

from __future__ import annotations

import json
import re
import sys
import unicodedata
from pathlib import Path

KEPT_FIELDS = (
    "author",
    "editor",
    "title",
    "year",
    "booktitle",
    "journal",
    "publisher",
    "series",
    "volume",
    "pages",
    "note",
    "howpublished",
    "doi",
    "url",
)

# Standard BibTeX month macros (resolved but never part of the output).
MONTH_MACROS = {name: name for name in
                ("jan", "feb", "mar", "apr", "may", "jun",
                 "jul", "aug", "sep", "oct", "nov", "dec")}

# Combining diacritics used by LaTeX accent commands.
ACCENTS = {
    "`": "\u0300",  # grave
    "'": "\u0301",  # acute
    "^": "\u0302",  # circumflex
    '"': "\u0308",  # diaeresis
    "~": "\u0303",  # tilde
    "=": "\u0304",  # macron
    ".": "\u0307",  # dot above
    "u": "\u0306",  # breve
    "v": "\u030c",  # caron
    "H": "\u030b",  # double acute
    "c": "\u0327",  # cedilla
    "k": "\u0328",  # ogonek
    "b": "\u0331",  # macron below
    "d": "\u0323",  # dot below
    "r": "\u030a",  # ring above
    "t": "\u0361",  # tie
}

# LaTeX commands that map to a single character (or nothing).
SPECIALS = {
    "ss": "\u00df",
    "SS": "SS",
    "ae": "\u00e6",
    "AE": "\u00c6",
    "oe": "\u0153",
    "OE": "\u0152",
    "o": "\u00f8",
    "O": "\u00d8",
    "aa": "\u00e5",
    "AA": "\u00c5",
    "l": "\u0142",
    "L": "\u0141",
    "i": "i",
    "j": "j",
    "textendash": "\u2013",
    "textemdash": "\u2014",
    "textasciitilde": "~",
    "textasciicircum": "^",
    "ldots": "\u2026",
    "dots": "\u2026",
    "LaTeX": "LaTeX",
    "TeX": "TeX",
    "BibTeX": "BibTeX",
    "copyright": "\u00a9",
    "textregistered": "\u00ae",
    "texttrademark": "\u2122",
}

# Simple backslash escapes: punctuation and spacing commands.
SIMPLE_ESCAPES = {
    "&": "&", "%": "%", "$": "$", "#": "#", "_": "_",
    "{": "{", "}": "}", "-": "", "/": "", "\\": " ",
    ",": " ", ";": " ", ":": " ", "!": "", " ": " ",
    "\n": " ", "\t": " ",
}

# Commands whose single argument is passed through almost verbatim.
VERBATIM_COMMANDS = {"url", "path", "texttt"}

_SPECIAL_NAMES = sorted(SPECIALS, key=len, reverse=True)
_ACCENT_NAMES = sorted(ACCENTS, key=len, reverse=True)


class BibError(Exception):
    """A problem with the input .bib file."""


# --------------------------------------------------------------------------
# low level readers
# --------------------------------------------------------------------------

def _skip_ws(text: str, i: int) -> int:
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def _read_group(text: str, i: int) -> tuple[str, int]:
    """Read a ``{...}`` group starting at ``i``; return content and new index.

    The outermost braces are removed, inner (nested) braces are preserved so
    that later LaTeX decoding can still see accent arguments.
    """
    if text[i] != "{":
        raise BibError("internal error: _read_group expects '{'")
    depth = 1
    i += 1
    out: list[str] = []
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            out.append(text[i:i + 2])
            i += 2
            continue
        if ch == "{":
            depth += 1
            out.append(ch)
            i += 1
            continue
        if ch == "}":
            depth -= 1
            if depth == 0:
                return "".join(out), i + 1
            out.append(ch)
            i += 1
            continue
        out.append(ch)
        i += 1
    raise BibError("unbalanced braces (missing '}' at end of file)")


def _read_quoted(text: str, i: int) -> tuple[str, int]:
    """Read a ``"..."`` value starting at ``i``."""
    if text[i] != '"':
        raise BibError("internal error: _read_quoted expects '\"'")
    i += 1
    out: list[str] = []
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            out.append(text[i:i + 2])
            i += 2
            continue
        if ch == '"':
            return "".join(out), i + 1
        out.append(ch)
        i += 1
    raise BibError("unterminated quoted value")


def _read_balanced(text: str, i: int, open_ch: str, close_ch: str) -> tuple[str, int]:
    """Read an entry body delimited by ``open_ch``/``close_ch``."""
    depth = 1
    i += 1
    out: list[str] = []
    in_quotes = False
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            out.append(text[i:i + 2])
            i += 2
            continue
        if ch == '"' and open_ch == "(":
            in_quotes = not in_quotes
            out.append(ch)
            i += 1
            continue
        if not in_quotes:
            if ch == open_ch:
                depth += 1
            elif ch == close_ch:
                depth -= 1
                if depth == 0:
                    return "".join(out), i + 1
        out.append(ch)
        i += 1
    raise BibError(f"unbalanced entry (missing {close_ch!r})")


# --------------------------------------------------------------------------
# LaTeX to plain text
# --------------------------------------------------------------------------

def _accent_base(text: str, i: int) -> tuple[str, int]:
    """Read the argument of an accent command starting at ``i``."""
    i = _skip_ws(text, i)
    if i >= len(text):
        return "", i
    if text[i] == "{":
        raw, i = _read_group(text, i)
        return latex_to_text(raw).strip()[:1], i
    if text[i] == "\\" and i + 1 < len(text):
        raw = text[i:i + 2]
        return latex_to_text(raw).strip()[:1], i + 2
    return text[i], i + 1


def latex_to_text(value: str) -> str:
    """Decode the LaTeX markup used in ``refs.bib`` into plain Unicode text."""
    out: list[str] = []
    i = 0
    n = len(value)
    while i < n:
        ch = value[i]

        if ch == "{":  # protective / grouping braces are dropped
            i += 1
            continue
        if ch == "}":
            i += 1
            continue
        if ch == "~":  # non-breaking space
            out.append(" ")
            i += 1
            continue

        if ch != "\\":
            out.append(ch)
            i += 1
            continue

        # ---- backslash escape / command ----
        j = i + 1
        if j >= n:
            i = j
            continue

        # Accent commands, including letter accents such as \" \c \v.
        command = None
        if j < n and (value[j] in ACCENTS and not value[j].isalpha()):
            command = value[j]
        elif j < n and value[j].isalpha():
            word = re.match(r"[A-Za-z]+", value[j:])
            assert word is not None
            word = word.group(0)
            # longest known command that is a prefix of the word
            candidates = [c for c in _SPECIAL_NAMES if word.startswith(c)]
            candidates += [c for c in VERBATIM_COMMANDS if word.startswith(c)]
            accent_candidates = [c for c in _ACCENT_NAMES if word.startswith(c)]
            best = max(candidates + accent_candidates, key=len) if (
                candidates or accent_candidates) else None
            if best is not None and (len(best) > 1 or len(word) == 1):
                command = best
            else:
                # Unknown command (e.g. \tt, \noopsort): drop the command,
                # keep whatever follows (a braced argument stays readable).
                i = j + len(word)
                continue

        if command is None:
            replacement = SIMPLE_ESCAPES.get(value[j]) if j < n else None
            if replacement is not None:
                out.append(replacement)
            else:
                out.append(value[j])  # unknown escape: keep the character
            i = j + 1
            continue

        if command in VERBATIM_COMMANDS:
            i = j + len(command)
            i = _skip_ws(value, i)
            if i < n and value[i] == "{":
                raw, i = _read_group(value, i)
                out.append(_simple_unescape(raw))
            continue

        if command in SPECIALS:
            out.append(SPECIALS[command])
            i = j + len(command)
            continue

        if command in ACCENTS:
            base, i = _accent_base(value, j + len(command))
            if not base:
                continue
            if base in ("\u0131", "\u0237"):  # dotless i / j
                base = "i" if base == "\u0131" else "j"
            out.append(unicodedata.normalize("NFC", base + ACCENTS[command]))
            continue

        # Anything else (should not happen): drop the backslash.
        i = j + 1

    text = "".join(out)
    # Typographic dashes, as used for page ranges ("319--336").
    text = text.replace("---", "\u2014").replace("--", "\u2013")
    return " ".join(text.split())


def _simple_unescape(value: str) -> str:
    """Unescape just enough for URLs/DOIs; keep everything else as-is."""
    value = re.sub(r"\{\\([&%$#_{}])", r"\1", value)
    value = re.sub(r"\\([&%$#_{}])", r"\1", value)
    value = value.replace("{", "").replace("}", "")
    return " ".join(value.split())


# --------------------------------------------------------------------------
# BibTeX structure
# --------------------------------------------------------------------------

def _read_value(text: str, i: int, macros: dict[str, str]) -> tuple[str, int]:
    """Read a (possibly ``#``-concatenated) field value starting at ``i``."""
    chunks: list[str] = []
    while True:
        i = _skip_ws(text, i)
        if i >= len(text):
            raise BibError("unexpected end of entry while reading a value")
        ch = text[i]
        if ch == "{":
            raw, i = _read_group(text, i)
        elif ch == '"':
            raw, i = _read_quoted(text, i)
        else:
            m = re.match(r"[A-Za-z][A-Za-z0-9_.:+\-]*|[0-9]+", text[i:])
            if not m:
                raise BibError(f"cannot parse value near {text[i:i + 30]!r}")
            token = m.group(0)
            i += len(token)
            if token.isdigit():
                raw = token
            else:
                expanded = macros.get(token.lower()) or MONTH_MACROS.get(token.lower())
                if expanded is None:
                    raise BibError(f"undefined @STRING macro {token!r}")
                raw = expanded
        chunks.append(raw)
        i = _skip_ws(text, i)
        if i < len(text) and text[i] == "#":
            i += 1
            continue
        break
    return "".join(chunks), i


def _parse_fields(body: str, macros: dict[str, str]) -> dict[str, str]:
    fields: dict[str, str] = {}
    i = 0
    n = len(body)
    while True:
        i = _skip_ws(body, i)
        while i < n and body[i] == ",":
            i += 1
            i = _skip_ws(body, i)
        if i >= n:
            break
        m = re.match(r"([A-Za-z][A-Za-z0-9_\-]*)\s*=", body[i:])
        if not m:
            raise BibError(f"expected 'name = value' near {body[i:i + 40]!r}")
        name = m.group(1).lower()
        i += m.end()
        raw, i = _read_value(body, i, macros)
        fields[name] = raw
        i = _skip_ws(body, i)
        if i < n and body[i] not in ",":
            raise BibError(f"expected ',' or end of entry near {body[i:i + 40]!r}")
    return fields


def _parse_string_def(body: str, macros: dict[str, str]) -> None:
    m = re.match(r"\s*([A-Za-z][A-Za-z0-9_\-]*)\s*=", body)
    if not m:
        raise BibError("@STRING without a name")
    name = m.group(1).lower()
    raw, _ = _read_value(body, m.end(), macros)
    macros[name] = raw


def parse_bib(text: str) -> dict[str, dict[str, str]]:
    """Parse BibTeX text and return ``{key: {field: value}}``."""
    macros: dict[str, str] = {}
    entries: dict[str, dict[str, str]] = {}
    i = 0

    while True:
        i = text.find("@", i)
        if i < 0:
            break
        i += 1
        m = re.match(r"\s*([A-Za-z]+)\s*([{(])", text[i:])
        if not m:
            raise BibError(f"malformed entry header near {text[i:i + 40]!r}")
        entry_type = m.group(1).lower()
        open_ch = m.group(2)
        close_ch = "}" if open_ch == "{" else ")"
        body, i = _read_balanced(text, i + m.start(2), open_ch, close_ch)

        if entry_type == "comment":
            continue
        if entry_type == "preamble":
            continue
        if entry_type == "string":
            _parse_string_def(body, macros)
            continue

        comma = body.find(",")
        if comma < 0:
            key, rest = body.strip(), ""
        else:
            key, rest = body[:comma].strip(), body[comma + 1:]
        if not key:
            raise BibError(f"@{entry_type} entry without a citation key")
        if re.search(r"[\s]", key):
            raise BibError(f"invalid citation key {key!r}")
        if key in entries:
            raise BibError(f"duplicate citation key {key!r}")

        fields = _parse_fields(rest, macros)
        entry: dict[str, str] = {}
        for name in KEPT_FIELDS:
            if name not in fields:
                continue
            raw = fields[name]
            if name in ("url", "doi"):
                value = _simple_unescape(raw)
            else:
                value = latex_to_text(raw)
            if value:
                entry[name] = value
        entries[key] = entry

    return entries


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def convert(in_path: Path, out_path: Path) -> dict[str, dict[str, str]]:
    try:
        text = in_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise BibError(f"cannot read {in_path}: {exc}") from exc

    entries = parse_bib(text)
    if not entries:
        raise BibError(f"no entries found in {in_path}")

    ordered = {key: entries[key] for key in sorted(entries)}
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(ordered, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return ordered


def main(argv: list[str]) -> int:
    if len(argv) == 2 and argv[1] in ("-h", "--help"):
        print(__doc__.strip())
        return 0
    if len(argv) != 3:
        print(f"usage: {Path(argv[0]).name} IN.bib OUT.json", file=sys.stderr)
        return 2

    in_path, out_path = Path(argv[1]), Path(argv[2])
    try:
        entries = convert(in_path, out_path)
    except BibError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    empty = [key for key, entry in entries.items() if not entry]
    print(f"{len(entries)} entries written to {out_path}", file=sys.stderr)
    if empty:
        print(f"warning: entries without any kept field: {', '.join(empty)}",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
