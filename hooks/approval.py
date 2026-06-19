"""MkDocs hook: per-page review status badge.

Every page can carry an ``approved`` field in its front matter holding the
initials of the person who checked the page, plus the date of the check —
either combined or as a separate ``approved-on`` field::

    ---
    approved: rb 2026-06-11
    ---

    ---
    approved: rb
    approved-on: 2026-06-11
    ---

Rendering:

* approved          -> green badge in the page *footer*, with initials and
                       (if given) the verification date,
* field missing     -> amber "not yet verified" badge at the *top* of the
                       page (prominent, as a call to action),
* ``approved: none``-> no badge at all (for generated pages).

Styling lives in ``docs/extra.css`` (``.approval`` classes).
"""

import re

_DATE_RE = re.compile(r"^(?P<who>.*?)[\s,]+(?P<date>\d{4}-\d{2}-\d{2})$")


def _normalize(value):
    # The meta extension yields lists, YAML front matter strings or dates.
    if isinstance(value, list):
        value = " ".join(str(v) for v in value)
    return str(value).strip() if value is not None else ""


def on_page_markdown(markdown, page, config, files):
    approved = _normalize(page.meta.get("approved"))

    if approved.lower() == "none":
        return markdown

    if not approved:
        badge = (
            '<div class="approval approval--missing" '
            'title="The original pages were written by the KeY community. '
            'In June 2026, the structure and content of this documentation has been revised '
            'using support from generative AI. '
            'Pages that carry the badge &quot;not yet verified&quot; need (re-)approval by a KeY core team member after this renovation.">'
            '&#9888; not yet verified</div>\n\n'
        )
        return badge + markdown

    # Date either inside `approved` ("rb 2026-06-11") or in `approved-on`.
    who, date = approved, _normalize(
        page.meta.get("approved-on") or page.meta.get("approved_on"))
    m = _DATE_RE.match(approved)
    if m:
        who, date = m.group("who").strip(), m.group("date")

    text = "&#10003; This page was checked by " + who
    if date:
        text += " on " + date
    text += "."

    footer = (
        '\n\n<div class="approval approval--ok approval--footer" '
        'title="This page has been reviewed.">' + text + "</div>\n"
    )
    return markdown + footer
