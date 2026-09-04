import GenExpr.Verify
import GenExpr.Render

/-!
The public entry point.

`analyze` runs the whole pipeline — scan, segment, plan, type, render, check against values — and
is pure, so it can be called from tests without a Lean environment. Callers supply their own
catalogue additions, the signatures they want, and whatever values they know.

Nothing here mentions OEIS. A caller that has sequences supplies them as `custom` alternatives or
as `tables` of known points.
-/

namespace GenExpr

open GenExpr.Raw

structure Request where
  input : String
  /-- Names to prefer for the result, most preferred first. -/
  names : Array String := #[]
  /-- Signatures to try, in order; the first that yields a verified reading wins. -/
  types : Array FnTy := #[{ args := [.nat], ret := .nat }]
  /-- Known values, in the order verification should use them. -/
  values : Array (Array Int × Int) := #[]
  /-- Extra catalogue entries. These compete with the built-ins rather than replacing them. -/
  custom : Array Alt := #[]
  /-- Catalogue keys to drop, so a caller can override a built-in outright. -/
  removeBuiltins : Array String := #[]
  /-- Functions known only by data points; a call outside the table proves nothing. -/
  tables : Array (String × Array (Array Int × Int)) := #[]
  verify : VerifyConfig := {}
  /-- Readings kept per result type at each node. -/
  beam : Nat := 4
  /-- Keep every reading that verifies rather than stopping at the first. -/
  allResults : Bool := false
  style : RenderStyle := {}
deriving Inhabited

/-- One accepted formalization. -/
structure Item where
  name : String
  ty : FnTy
  /-- The body alone, with `«self»` for recursion. This is what a database should store: it can
  be re-rendered under any name. -/
  body : String
  /-- A ready-to-paste declaration. -/
  decl : String
  /-- Auxiliary declarations, in dependency order. -/
  aux : Array String
  imports : Array String
  /-- Exactly the parts of the input this was built from. -/
  spans : Array Span
  text : String
  computable : Bool
  /-- Values supplied as base cases, which the declaration lists explicitly. -/
  baseCases : Array (Array Int × Int)
  report : VerifyReport
  cost : Nat
deriving Inhabited

structure Result where
  items : Array Item := #[]
  /-- Everything tried and rejected, with the reason. -/
  rejected : Array (Span × Reject) := #[]
deriving Inhabited

/-- A function known only by its values still needs a catalogue entry so that the parser treats
it as a call and the typer knows its shape. -/
private def tableAlt (name : String) (tbl : Array (Array Int × Int)) : Alt :=
  let arity := (tbl[0]?.map fun (a, _) => a.size).getD 1
  let ret := if tbl.any (fun (_, v) => v < 0) then Ty.int else Ty.nat
  { key := name
    template := name ++ String.join ((List.range arity).map fun i => s!" \{{i}}")
    params := Array.replicate arity .nat, result := ret, prec := 1023
    argPrec := Array.replicate arity 1024 }

private def spanText (inp : Input) (sp : Span) : String :=
  let bytes := inp.bytes
  let idx (b : Nat) : Nat := (bytes.findIdx? (· == b)).getD 0
  inp.extract (idx sp.start) (idx sp.stop)

private def joinSpans (inp : Input) (spans : Array Span) : String :=
  String.intercalate " … " (spans.toList.map (spanText inp))

/-- Run the whole pipeline. Pure: no Lean environment is needed. -/
def analyze (req : Request) : Result := Id.run do
  let reg :=
    (Builtins.standard.merge (req.custom ++ req.tables.map fun (n, t) => tableAlt n t)
      req.removeBuiltins)
  let cls : Classifier := { functions := reg.names ++ req.names, values := reg.constants }
  let sc := scan cls { maxFreeVars := req.types.foldl (fun m t => max m t.arity) 1 } req.input
  let mut items : Array Item := #[]
  let mut rejected : Array (Span × Reject) := #[]
  let mut plannedArities : Array Nat := #[]
  for want in req.types do
    if !items.isEmpty && !req.allResults then break
    let arity := want.arity
    let p := plan sc { names := req.names, arity }
    if !plannedArities.contains arity then
      plannedArities := plannedArities.push arity
      rejected := rejected ++ p.rejected
    for g in p.goals do
      if !items.isEmpty && !req.allResults then break
      let ts := typeGoal reg req.beam g want
      if ts.isEmpty then
        rejected := rejected.push (g.main.span, .typeUnachievable want.ret)
        continue
      -- With no values to check against there is nothing to choose between readings, so the
      -- cheapest one stands; `Item.computable` tells the caller whether it could have been run.
      let (best, tried) :=
        if req.values.isEmpty then (ts.head?.map fun t => (t, ({} : VerifyReport)), #[])
        else firstVerified req.verify ts req.values g.guards req.tables
      match best with
      | none =>
        for (_, r) in tried do
          if let some why := r.reason then rejected := rejected.push (g.main.span, why)
      | some (t, rep) =>
        let name := t.name
        let spans := g.spans
        items := items.push
          { name, ty := t.fnTy
            body := renderBody req.style t
            decl := renderDef req.style t name rep.bases
            aux := t.aux.map fun (n, ps, b) => renderAux req.style n ps b
            imports := typingImports t
            spans, text := joinSpans sc.input spans
            computable := t.computable
            baseCases := rep.patched
            report := rep, cost := t.cost }
  return { items, rejected }

end GenExpr
