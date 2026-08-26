/-
Public API of the formula parser.

Typical use (OEIS side):

```
let alts := Registry.overlay [("A002157", [Alt.constApp `A002157 (.arr .nat .ret) 0, …])]
Formula.findAll line (.arr .nat .nat) (myDataValidator) alts
```

The validation functor receives fully elaborated terms only; `findAll` returns every accepted
candidate best-first, `findFirst?` stops at the first acceptance.
-/

import FormulaParser.Grammar
import FormulaParser.Elab

open Lean Lean.Elab.Term

namespace Formula

/-- Segment a raw line into canonicalized ASTs (no typing, no elaboration). Useful for
debugging and for tests of the segmentation layer. Builtin registry names count as
function-call heads. -/
def parseAst (input : String) (cfg : Config := default) : List Ast :=
  Grammar.parseLine input { cfg with knownHeads := cfg.knownHeads ++ Registry.builtin.map.keys }

private def drive (input : String) (target : Ty) (validate : Result → TermElabM Bool)
    (reg : Registry) (cfg : Config) (stopAtFirst : Bool) : TermElabM (List Result) := do
  let heads := reg.map.keys ++ cfg.knownHeads
  let asts := Grammar.parseLine input { cfg with knownHeads := heads }
  let roots := Search.searchRoots asts target reg cfg
  let mut accepted : List Result := []
  for root in roots.take cfg.maxTotalCandidates do
    if accepted.length ≥ cfg.maxAccepted then break
    let res ← Elab.elabRoot root
    match res with
    | none => pure ()
    | some r =>
      if ← validate r then
        accepted := accepted ++ [r]
        if stopAtFirst ∨ accepted.length ≥ cfg.maxAccepted then return accepted
  return accepted

/-- Parse `input`, elaborate every type-correct candidate of the requested `target` type and
return all candidates the validation functor accepts, cheapest first.
The validator is called at most once per candidate and only on terms that already compiled. -/
def findAll (input : String) (target : Ty) (validate : Result → TermElabM Bool)
    (reg : Registry := Registry.builtin) (cfg : Config := default) : TermElabM (List Result) :=
  drive input target validate reg cfg false

/-- Like `findAll`, but stop at the first validated candidate. -/
def findFirst? (input : String) (target : Ty) (validate : Result → TermElabM Bool)
    (reg : Registry := Registry.builtin) (cfg : Config := default) : TermElabM (Option Result) := do
  let rs ← drive input target validate reg cfg true
  return rs.head?

/-- Ranked, elaborated candidates *without* running any validation functor.
Not subject to `Config.maxAccepted`: the full ranked list is returned. -/
def parseAll (input : String) (target : Ty)
    (reg : Registry := Registry.builtin) (cfg : Config := default) : TermElabM (List Result) :=
  drive input target (fun _ => pure true) reg { cfg with maxAccepted := cfg.maxTotalCandidates }
    false

end Formula
