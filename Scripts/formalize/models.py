"""Structured output contract for the formalization agent."""

from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, Field

ArgKind = Literal["Nat", "PNat", "NatSub", "Int", "IntSub"]

STATUS_UNKNOWN = "STATUS_UNKNOWN"
STATUS_VERIFIED = "STATUS_VERIFIED"
STATUS_COMPILE_ERROR = "STATUS_COMPILE_ERROR"
STATUS_EVAL_MISMATCH = "STATUS_EVAL_MISMATCH"
STATUS_DEP_RANGE = "STATUS_DEP_RANGE"
STATUS_NONCOMPUTABLE = "STATUS_NONCOMPUTABLE"
STATUS_REJECTED = "STATUS_REJECTED"

#: A stretch of the program block that no item claimed.
STATUS_UNFORMALIZED = "STATUS_UNFORMALIZED"
#: A gap holding only blank lines, stray delimiters or an author credit comment.
STATUS_GAP_TRIVIAL = "STATUS_GAP_TRIVIAL"

BATCH_PENDING = "BATCH_PENDING"
BATCH_RUNNING = "BATCH_RUNNING"
BATCH_OK = "BATCH_OK"
BATCH_PARTIAL = "BATCH_PARTIAL"
BATCH_FAILED = "BATCH_FAILED"


class FormalizedProgram(BaseModel):
    """One independent program extracted from one Maple block."""

    oeis_name: str = Field(
        description="A-number of the sequence this program belongs to, e.g. A000045."
    )
    start_marker: str = Field(
        description=(
            "The first characters of this program, copied verbatim from the block. "
            "Long enough to occur only once (roughly 15-60 characters); include the "
            "leading whitespace of the line if that is what makes it unique."
        )
    )
    end_marker: str = Field(
        description=(
            "The last characters of this program, copied verbatim from the block, "
            "including any trailing comment or author credit such as "
            "'# _R. J. Mathar_, Nov 15 2014'. Roughly 15-60 characters. The span from "
            "start_marker to the end of end_marker is what this item claims; whatever "
            "no item claims is recorded as unformalized."
        )
    )
    lean_code: str = Field(
        description=(
            "Lean 4 code defining `formula`, plus optional `formula_`-prefixed helpers. "
            "No imports, namespaces, theorems or #eval."
        )
    )
    arg_kind: ArgKind = Field(description="Index type chosen for `formula`.")
    computable: bool = Field(
        description="False when the translation cannot be executed (real analysis, "
        "generating functions, prime enumeration, ...). Such items are stored but not compiled."
    )
    note: str = Field(
        default="", description="Optional one-line remark about the translation."
    )


class SkippedProgram(BaseModel):
    """A program the model saw but deliberately did not translate."""

    oeis_name: str = Field(description="A-number the skipped program belongs to.")
    start_marker: str = Field(description="First characters of the skipped program, verbatim.")
    reason: str = Field(description="Why it was not translated.")


class BatchResult(BaseModel):
    """Everything the agent produced for one batch."""

    items: list[FormalizedProgram] = Field(
        description="One entry per independent program found across the whole batch."
    )
    skipped: list[SkippedProgram] = Field(
        default_factory=list,
        description=(
            "Programs you chose not to translate, one entry each. Leave empty when you "
            "translated every program in every block."
        ),
    )


class SkillSuggestions(BaseModel):
    """Improvements to the skill file discovered while formalizing a batch."""

    notes: list[str] = Field(
        default_factory=list,
        description="Short, generally useful lessons. Empty when nothing new was learned.",
    )
    table_rows: list[str] = Field(
        default_factory=list,
        description="New markdown rows for the Maple function table, pipe-delimited, "
        "in the format `| keys | usage | lean | notes |`.",
    )
