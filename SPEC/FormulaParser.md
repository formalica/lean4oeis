# FormulaParser

Lean/core library (no `LOEIS` dependency) that turns a human-written formula
line into ranked, elaborated Lean term candidates. It is frontend-independent:
the plain-text OEIS grammar is implemented today, and Wolfram/LaTeX frontends
will produce the same AST later.

Code:

| Module | Role |
| --- | --- |
| `Lex.lean` | tokenizer; normalizes unicode lookalikes (`− × · √`, superscripts), gates implicit multiplication on whitespace, treats `_Author_` identifiers as hard boundaries |
| `Grammar.lean` | segments a noisy line into formula pieces (bracket-depth-aware splits at `,`/`;`, paren repair, longest-match parsing from every position, maximal non-overlapping coverage) |
| `Ast.lean` | the intermediate AST; canonicalized after parsing — additive chains are flattened and re-emitted with all additions before all subtractions, avoiding truncation over `Nat` |
| `Registry.lean` | maps every surface name (`+`, `sqrt`, `A002157`, …) to a list of typed alternatives `Alt` (Lean interpretation, mini-type, cost, source builder); extended by callers via `insert` / `overlay` |
| `Basic.lean` | shared types, configuration, and the coercion lattice (`Nat → Int → Rat → Real`) |
| `Search.lean` | type-directed candidate generation: only alternatives whose result coerces to the expected type are explored; children are searched recursively and capped per node, giving O(nodes · cap²) work |
| `Elab.lean` | elaborates rendered candidate sources with Lean's own parser/type checker; rejects failures, leftover metavariables, and embedded `sorry` — validity is decided by Lean, not by the search |
| `Parser.lean` | public API: `findAll` (all accepted candidates, best-first) and `findFirst?` |
| `Tests.lean` | build-time tests (`lake build FormulaParser.Tests`) using stand-in sequences registered through `Registry.overlay` |

Usage contract:

- The caller supplies a target mini-type (e.g. an `Int → Int` function), a
  validation functor, and an `overlay` binding sequence names to their
  formalized definitions (`main`, `fn`, `fz`, flat variants). The validator
  receives fully elaborated terms only and decides acceptance (in the OEIS
  pipeline: comparison against the known data, see
  [Verification.md](Verification.md)).
- Interpretation order follows cost then validation: e.g. `sqrt` tries
  `Nat.sqrt` before `Int.sqrt` before `Real.sqrt`; ties after typing are
  left for the validator to resolve.
- Only the recognized formula fragment is used; surrounding prose, author
  names and comments are discarded (this is the text whose hash appears in
  `Equiv_<hash>.lean`, see [OEISLib.md](OEISLib.md)).
