/-
Elaboration of rendered candidate sources into real Lean terms.

A `Root` carries fully rendered source text (optionally binder-wrapped); this module parses it
with the standard term parser, elaborates it against the requested mini-type rendered as a
Lean type, and rejects anything that fails, still contains metavariables, or sneaks in `sorry`.
This makes Lean's own inference engine (instance selection, coercions, `zpow`, omega-proved
embeddings) the authority on candidate validity, so expensive user validation functors only
ever see terms that already compile.
-/

import Lean
import FormulaParser.Search

open Lean Lean.Elab.Term

namespace Formula

/-- A validated-shape, elaborated candidate term. -/
structure Result where
  /-- Human-readable Lean source of the whole term (authoritative display form). -/
  src : String
  /-- The elaborated term. -/
  expr : Expr
  /-- Requested mini-type realized by the term. -/
  ty : Ty
  /-- Binder of function targets. -/
  binder : Option (String × Ty)
  /-- Canonicalized AST the candidate came from. -/
  ast : Ast
  /-- Search cost (ranking key). -/
  cost : Nat := 0

deriving instance Inhabited for Result

namespace Elab

open Lean Lean.Elab.Term

/-- Wrap a body source into the full term source according to the root binder.
Domains needing visible unwrapping (`PNat`, subtypes) get explicit annotations. -/
def fullSrc (r : Root) : String :=
  match r.binder with
  | none => r.src
  | some (nm, d) =>
    match d with
    | .nat => s!"(fun {nm} => {r.src})"
    | .int => s!"(fun {nm} => {r.src})"
    | _ => s!"(fun ({nm} : {d.render}) => {r.src})"

/-- Parse a source fragment as a Lean term. -/
def parseTermStr (s : String) : TermElabM Syntax := do
  let env ← getEnv
  match Parser.runParserCategory env `term s with
  | .ok stx => pure stx
  | .error e => throwError "formula term parse error: {e}"

/-- Elaborate one search root against its target type. Returns `none` on any failure;
state modifications of failed attempts are rolled back. With `trace`, rejected candidates
are printed to stdout for debugging interpretation quality. -/
def elabRoot (root : Root) (trace : Bool := false) : TermElabM (Option Result) :=
  withoutModifyingState do
    let src := fullSrc root
    try
      let stx ← parseTermStr src
      let tyStx ← parseTermStr root.ty.render
      let expTy ← elabType tyStx
      let e ← elabTerm stx (some expTy)
      -- flush postponed synthesis so leftover metavariables are visible; candidates that
      -- still have them are genuinely ambiguous and rejected
      synthesizeSyntheticMVars (postpone := .no)
      let e ← instantiateMVars e
      if e.hasExprMVar ∨ e.hasSorry then do
        if trace then IO.println s!"[candREJECT] {src}"
        pure none
      else pure (some { src := src, expr := e, ty := root.ty, binder := root.binder,
                        ast := root.ast, cost := root.cost })
    catch e => do
      if trace then logInfo m!"[elabFAIL:{src}] {e.toMessageData}"
      pure none

end Elab

end Formula
