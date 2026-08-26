/-
Types, configuration and the coercion lattice for the formula parser.

The library is frontend-independent: parsers for concrete syntaxes (OEIS plain text today,
Wolfram/LaTeX later) produce `Ast` values (see `FormulaParser.Ast`), and the type-directed
search back end (`FormulaParser.Search`, `FormulaParser.Elab`) turns them into Lean terms of a
requested `Ty`.

Term construction happens at the source-string level until `Elab.lean`, so this module needs
nothing beyond Lean core.
-/

import Init.Data.Rat.Basic
import Std.Data.HashMap

namespace Formula

/-- The "mini types" the search reasons about. These mirror the types OEIS formulas are
formalized at: `Nat`, `Int`, `Rat`, `Real`, `PNat`, subtypes of `Nat`/`Int`, function types
between them, and `Prop` (reserved for a later stage). -/
inductive Ty where
  | nat
  | int
  | rat
  | real
  | pnat
  /-- `{n : Nat // b ≤ n}` or `{n : Nat // b < n}`. -/
  | subNat (b : Int) (strict : Bool)
  /-- `{n : Int // b ≤ n}` or `{n : Int // b < n}`. -/
  | subInt (b : Int) (strict : Bool)
  | arr (d r : Ty)
  | prop

deriving instance BEq, Hashable, DecidableEq, Inhabited for Ty

namespace Ty

/-- Is this one of the four numeric tower types? -/
def isNum : Ty → Bool
  | .nat | .int | .rat | .real => true
  | _ => false

/-- Domain of an arrow (the type itself otherwise). -/
def domain : Ty → Ty
  | .arr d _ => d
  | t => t

/-- Codomain of an arrow, through nested arrows (the type itself otherwise). -/
def result : Ty → Ty
  | .arr _ r => r.result
  | t => t

/-- Is this an index type that wraps a `Nat`/`Int` value (`PNat`, subtypes)? -/
def isWrapped : Ty → Bool
  | .pnat | .subNat .. | .subInt .. => true
  | _ => false

/-- Do arrow domains need parens when rendered? -/
def needsParen : Ty → Bool
  | .arr .. => true
  | _ => false

/-- Render a type as Lean source. Subtype bounds use the dummy name `x`, which cannot collide
with user formula variables. -/
def render : Ty → String
  | .nat => "Nat"
  | .int => "Int"
  | .rat => "Rat"
  | .real => "Real"
  | .pnat => "PNat"
  | .subNat b strict =>
    "{" ++ "x : Nat // " ++ toString b ++ (if strict then " < " else " ≤ ") ++ "x}"
  | .subInt b strict =>
    "{" ++ "x : Int // " ++ toString b ++ (if strict then " < " else " ≤ ") ++ "x}"
  | .arr d r =>
    let ds := if d.needsParen then s!"({d.render})" else d.render
    s!"{ds} → {r.render}"
  | .prop => "Prop"

end Ty

/-- Search/segmentation configuration. -/
structure Config where
  /-- Minimum AST size for a segmented piece to count as a formula (drops bare numbers and
  prose words picked up mid-sentence). -/
  minNodes : Nat := 3
  /-- Allow number-led juxtaposition as multiplication: `2n`, `3a(n-1)`, `8(x+1)`. -/
  allowImplicitMul : Bool := true
  /-- Allow lossy finalization coercions (floor/round/ceil/toNat/natAbs). These are how
  formulas with rational or negative intermediates still produce `Nat`/`Int` results. -/
  allowLossyFinal : Bool := true
  /-- Cap on candidates materialized per (AST node, type) pair. -/
  maxCandidatesPerNode : Nat := 24
  /-- Global cap on candidates for one parse request. -/
  maxTotalCandidates : Nat := 96
  /-- Stop searching once this many candidates passed validation. -/
  maxAccepted : Nat := 6
  /-- Maximum AST depth accepted while parsing. -/
  maxAstDepth : Nat := 64
  /-- Maximum coercion path length searched. -/
  maxCoeDepth : Nat := 3
  /-- Maximum distinct coercion paths kept per (source, target) pair. -/
  maxCoePaths : Nat := 3
  /-- Surface names the grammar may parse as function calls (registry keys). Unknown
  multi-character names followed by `(` are treated as prose (`blah (…)`) so they cannot
  steal spans from real formulas. Single-letter calls are always allowed. -/
  knownHeads : List String := []
  /-- Print rejected-candidate sources to stdout (for debugging interpretation quality). -/
  traceFailures : Bool := false
deriving Inhabited

/-- How a value of one mini-type is turned into a value of another at the source level.
Every style knows how to wrap a rendered source string. -/
inductive CoeStyle where
  /-- Type ascription `(src : T)`; used on the exact numeric tower edges. -/
  | castUp
  /-- Projection `src.val`; unwraps `PNat`/subtype index types. -/
  | valOf
  /-- Anonymous constructor with an omega-discharged bound: `⟨src, by omega⟩`. -/
  | embed
  /-- Truncating conversion `src.toNat` (`Int → Nat`). -/
  | toNat
  /-- `src.natAbs` (`Int → Nat`). -/
  | natAbs
  /-- `(Int.floor src).toNat` (`Rat`/`Real → Nat`). -/
  | floorToNat
  /-- `(round src).toNat` (`Rat`/`Real → Nat`). -/
  | roundToNat
  /-- `(Int.ceil src).toNat` (`Rat`/`Real → Nat`). -/
  | ceilToNat
  /-- `Int.floor src` (`Rat`/`Real → Int`). -/
  | floorInt
  /-- `round src` (`Rat`/`Real → Int`). -/
  | roundInt
  /-- `Int.ceil src` (`Rat`/`Real → Int`). -/
  | ceilInt

deriving instance BEq, Hashable, Inhabited for CoeStyle

/-- Cost of one coercion step. Exact casts are cheap, embeddings carry a proof obligation and
lossy finalizations are most expensive so they are tried last. -/
def CoeStyle.cost : CoeStyle → Nat
  | .valOf => 0
  | .castUp => 1
  | .embed => 5
  | .toNat => 6
  | .natAbs => 6
  | .floorToNat => 7
  | .roundToNat => 7
  | .ceilToNat => 7
  | .floorInt => 7
  | .roundInt => 7
  | .ceilInt => 7

/-- Conservative atom test: identifiers and (signed) numerals. -/
def isAtomSrc (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    let ok (ch : Char) : Bool := ch.isAlpha ∨ ch.isDigit ∨ ch == '_' ∨ ch == '\''
    (c.isAlpha ∨ c == '-') ∧ cs.all ok

/-- Parenthesize a source fragment unless it is an atom or already bracketed.
Every renderer in the library guarantees its output is either an atom or fully bracketed;
this helper is used where a fragment's shape depends on data. -/
def parenArg (s : String) : String :=
  if s.startsWith "(" ∨ s.startsWith "{" ∨ s.startsWith "⟨" ∨ isAtomSrc s then s else s!"({s})"

namespace CoeStyle

/-- Wrap a rendered source expression so that it has type `tgt`. -/
def apply (st : CoeStyle) (src : String) (tgt : Ty) : String :=
  let arg := parenArg src
  match st with
  | .castUp => s!"(({src} : {tgt.render}))"
  | .valOf => s!"({src}).val"
  | .embed => s!"((⟨{src}, by omega⟩ : {tgt.render}))"
  | .toNat => s!"({src}).toNat"
  | .natAbs => s!"({src}).natAbs"
  | .floorToNat => s!"((Int.floor {arg}).toNat)"
  | .roundToNat => s!"((round {arg}).toNat)"
  | .ceilToNat => s!"((Int.ceil {arg}).toNat)"
  | .floorInt => s!"(Int.floor {arg})"
  | .roundInt => s!"(round {arg})"
  | .ceilInt => s!"(Int.ceil {arg})"

end CoeStyle

/-- Outgoing edges of the coercion graph: `(target, style, cost)` triples.
Embeddings from `Nat` into *specific* subtypes are added on demand (see `directSteps`),
because the target bound varies. -/
def directCoes (src : Ty) (allowLossy : Bool) : List (Ty × CoeStyle × Nat) :=
  let c := CoeStyle.cost
  let lossyNat : List (Ty × CoeStyle × Nat) :=
    [(.nat, .floorToNat, c .floorToNat), (.nat, .roundToNat, c .roundToNat),
     (.nat, .ceilToNat, c .ceilToNat)]
  let lossyInt : List (Ty × CoeStyle × Nat) :=
    [(.int, .floorInt, c .floorInt), (.int, .roundInt, c .roundInt),
     (.int, .ceilInt, c .ceilInt)]
  match src with
  | .nat =>
    [(.int, .castUp, c .castUp), (.rat, .castUp, c .castUp),
     (.real, .castUp, c .castUp), (.pnat, .embed, c .embed)]
  | .int =>
    [(.rat, .castUp, c .castUp), (.real, .castUp, c .castUp)] ++
    if allowLossy then [(.nat, .toNat, c .toNat), (.nat, .natAbs, c .natAbs)] else []
  | .rat =>
    [(.real, .castUp, c .castUp)] ++
    if allowLossy then lossyNat ++ lossyInt else []
  | .real => if allowLossy then lossyNat ++ lossyInt else []
  | .pnat => [(.nat, .valOf, c .valOf)]
  | .subNat .. => [(.nat, .valOf, c .valOf)]
  | .subInt .. => [(.int, .valOf, c .valOf)]
  | _ => []

/-- Single-step coercion paths from `cur` to `tgt`, including the on-demand embedding edges
into wrapped index types. Each step records the mini-type it produces, so a path can be
applied left-to-right starting from the source expression. -/
def directSteps (cur : Ty) (tgt : Ty) (allowLossy : Bool) :
    List (List (Ty × CoeStyle) × Nat) :=
  let table := (directCoes cur allowLossy).filter (fun (nxt, _, _) => nxt == tgt)
    |>.map (fun (_, st, cst) => ([(tgt, st)], cst))
  let embed : List (List (Ty × CoeStyle) × Nat) :=
    if cur == .nat ∧ tgt.isWrapped then [([(tgt, .embed)], CoeStyle.cost .embed)] else []
  table ++ embed

private partial def pathsFrom (cur : Ty) (tgt : Ty) (cfg : Config) (fuel : Nat)
    (visited : List Ty) : List (List (Ty × CoeStyle) × Nat) :=
  if fuel = 0 then [] else
    let step := directSteps cur tgt cfg.allowLossyFinal
    let deeper : List (List (Ty × CoeStyle) × Nat) :=
      (directCoes cur cfg.allowLossyFinal).flatMap fun (nxt, st, cst) =>
        if nxt == tgt ∨ visited.contains nxt then []
        else
          let rest := pathsFrom nxt tgt cfg (fuel - 1) (nxt :: visited)
          rest.map fun (p, pc) => ((nxt, st) :: p, cst + pc)
    step ++ deeper

/-- All coercion paths `src → tgt`, cheapest first, deduplicated, capped at
`Config.maxCoePaths`. A zero-length path is returned when `src = tgt`. -/
def coePaths (src : Ty) (tgt : Ty) (cfg : Config) : List (List (Ty × CoeStyle) × Nat) :=
  if src == tgt then [([], 0)]
  else
    let raw := pathsFrom src tgt cfg (cfg.maxCoeDepth + 1) [src]
    let dedup := raw.foldl (fun acc p => if acc.any (fun q => q.1 == p.1) then acc else acc ++ [p]) []
    ((dedup.mergeSort fun a b => a.2 < b.2).take cfg.maxCoePaths)

/-- Apply a coercion path to a rendered source expression. -/
def applyPath (steps : List (Ty × CoeStyle)) (src : String) : String :=
  steps.foldl (fun s (t, st) => st.apply s t) src

/-- Cheap prefilter used before any term construction: does *some* coercion route exist? -/
def coeCompatible (src : Ty) (tgt : Ty) (cfg : Config) : Bool :=
  src == tgt ∨ !(coePaths src tgt cfg).isEmpty

end Formula
