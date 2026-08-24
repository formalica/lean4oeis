"""Resolves the model's program boundaries into character spans of the original block.

The model does not echo a whole program back (long verbatim copies drift: whitespace is
normalised, comments are dropped, `...` creeps in). It returns two short anchors instead —
the first characters of the program and the last characters, trailing author credit
included — and this module turns those into a `[start, end)` span of the raw block.

Whatever no span covers is a *gap*: a part of the program section that nothing formalized.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

#: Anchors shorter than this are almost never unique inside a block.
MIN_MARKER = 6

#: Comment-only leftovers (`# _R. J. Mathar_, Nov 15 2014`, `(* ... *)`) carry no program.
_COMMENT_LINE = re.compile(r"^\s*(#.*|\(\*.*\*\)|--.*|/\*.*\*/)?\s*$")


@dataclass(frozen=True)
class Span:
    start: int
    end: int

    def overlaps(self, other: "Span") -> bool:
        return self.start < other.end and other.start < self.end

    def text(self, block: str) -> str:
        return block[self.start : self.end]


@dataclass(frozen=True)
class Markers:
    start: str
    end: str


class SpanError(Exception):
    pass


def _occurrences(haystack: str, needle: str, frm: int = 0) -> list[int]:
    out: list[int] = []
    pos = haystack.find(needle, frm)
    while pos != -1:
        out.append(pos)
        pos = haystack.find(needle, pos + 1)
    return out


def _candidates(block: str, markers: Markers) -> list[Span]:
    """Every `[start, end)` the anchor pair can denote, shortest first."""
    spans: list[Span] = []
    for start in _occurrences(block, markers.start):
        for tail in _occurrences(block, markers.end, start):
            end = tail + len(markers.end)
            if end > start:
                spans.append(Span(start, end))
    spans.sort(key=lambda s: (s.end - s.start, s.start))
    return spans


def resolve(block: str, markers: list[Markers]) -> tuple[list[Span | None], list[str | None]]:
    """Assigns each marker pair a non-overlapping span of `block`.

    Returns `(spans, reasons)`; for every index exactly one of the two is set. Items with
    the fewest candidates are placed first and the search backtracks, so an ambiguous
    anchor pair is still resolved when its neighbours pin it down.
    """
    spans: list[Span | None] = [None] * len(markers)
    reasons: list[str | None] = [None] * len(markers)
    candidates: dict[int, list[Span]] = {}

    for i, m in enumerate(markers):
        reason = _static_error(block, m)
        if reason:
            reasons[i] = reason
            continue
        found = _candidates(block, m)
        if not found:
            reasons[i] = (
                "`end_marker` never occurs at or after `start_marker`; the two anchors must "
                "delimit the program in the order they appear in the block"
            )
            continue
        candidates[i] = found

    order = sorted(candidates, key=lambda i: (len(candidates[i]), i))
    taken = _search(order, candidates, {})
    if taken is None:
        # No global assignment exists: fall back to greedy so the ones that do fit survive.
        taken = {}
        for i in order:
            for span in candidates[i]:
                if all(not span.overlaps(s) for s in taken.values()):
                    taken[i] = span
                    break
    for i in candidates:
        if i in taken:
            spans[i] = taken[i]
        else:
            reasons[i] = (
                "every span these anchors can denote overlaps another item of the same "
                "sequence; programs must not overlap, so anchor each one on its own text"
            )
    return spans, reasons


def _search(
    order: list[int], candidates: dict[int, list[Span]], taken: dict[int, Span]
) -> dict[int, Span] | None:
    if len(taken) == len(order):
        return dict(taken)
    i = order[len(taken)]
    for span in candidates[i]:
        if any(span.overlaps(s) for s in taken.values()):
            continue
        taken[i] = span
        found = _search(order, candidates, taken)
        if found is not None:
            return found
        del taken[i]
    return None


def _static_error(block: str, m: Markers) -> str | None:
    for label, marker in (("start_marker", m.start), ("end_marker", m.end)):
        if not marker.strip():
            return f"`{label}` is empty"
        if len(marker) < MIN_MARKER:
            return (
                f"`{label}` is only {len(marker)} characters long; give at least "
                f"{MIN_MARKER} so it identifies a unique position"
            )
        if marker not in block:
            return (
                f"`{label}` ({marker!r}) does not occur in the block verbatim; "
                + _hint(block, marker)
            )
    return None


def _hint(block: str, marker: str) -> str:
    if marker.strip() in block:
        return "copy it character for character, including leading/trailing whitespace"
    collapsed = re.sub(r"\s+", " ", marker.strip())
    if collapsed and collapsed in re.sub(r"\s+", " ", block):
        return "the text matches only after collapsing whitespace; copy the raw characters"
    head = marker.strip().splitlines()[0] if marker.strip().splitlines() else marker
    if len(head) >= MIN_MARKER and head[:MIN_MARKER] in block:
        return f"only the first {MIN_MARKER} characters match; the rest was altered"
    return "pick an anchor you can see in the block above"


def gaps(block: str, spans: list[Span]) -> list[Span]:
    """The complement of `spans` in `block`, whitespace trimmed and empty stretches dropped."""
    out: list[Span] = []
    cursor = 0
    for span in sorted(spans, key=lambda s: s.start):
        if span.start > cursor:
            out.append(Span(cursor, span.start))
        cursor = max(cursor, span.end)
    if cursor < len(block):
        out.append(Span(cursor, len(block)))
    return [t for t in (_trim(block, s) for s in out) if t is not None]


def _trim(block: str, span: Span) -> Span | None:
    start, end = span.start, span.end
    while start < end and block[start].isspace():
        start += 1
    while end > start and block[end - 1].isspace():
        end -= 1
    return Span(start, end) if end > start else None


def is_trivial(text: str) -> bool:
    """True when a gap holds no program — blank lines, stray delimiters or a credit comment."""
    body = "\n".join(ln for ln in text.splitlines() if not _COMMENT_LINE.match(ln))
    return not body.strip(" \t\n;:,)")
