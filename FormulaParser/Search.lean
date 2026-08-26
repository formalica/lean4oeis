/-
Type-directed candidate generation: turn a canonicalized `Ast` into a ranked list of
type-correct Lean source fragments for a requested mini-type.

Design:
- every surface name resolves through the `Registry` to typed alternatives; the search only
  descends into alternatives whose result type coerces to the expected type, so combinatorial
  branching is pruned *before* any Lean-side work;
- children are searched recursively, each child list capped at `Config.maxCandidatesPerNode`
  best candidates; parents combine children by cost-ordered cartesian product and re-cap,
  which bounds total work to O(nodes · cap²);
- coercions are inserted along the cheapest paths of the lattice in `FormulaParser.Basic`;
  lossy finalizations (floor/round/…, needed when intermediates are rational or negative but
  the requested result is `Nat`/`Int`) carry high costs so they are tried last.

The output is pure source text; elaboration happens in `FormulaParser.Elab`.
-/

import FormulaParser.Ast
import FormulaParser.Registry

namespace Formula

/-- One rendered candidate term. -/
structure Cand where
  /-- Rendered Lean source; either an atom or fully parenthesized. -/
  src : String
  /-- Mini-type of the rendered term. -/
  ty : Ty
  /-- Accumulated registry + coercion cost. -/
  cost : Nat := 0

/-- A complete root candidate: optionally binder-wrapped body plus realized type.
Carries its originating AST and accumulated cost for downstream ranking/recording. -/
structure Root where
  /-- Binder of a function target (name and domain). `none` for constant targets. -/
  binder : Option (String × Ty)
  /-- Realized full type (`arr d r` when bound). -/
  ty : Ty
  /-- Body source referencing the binder name (or the whole term when unbound). -/
  src : String
  /-- Canonicalized AST this candidate came from. -/
  ast : Ast
  /-- Accumulated search cost. -/
  cost : Nat := 0

namespace Search

private structure Ctx where
  reg : Registry
  cfg : Config

/-- Bound variables with their types (summation/product indices are `Nat`, integral ones
`Real`). -/
private abbrev Env := List (String × Ty)

private def sortCands (cs : List Cand) : List Cand :=
  cs.mergeSort fun a b => a.cost ≤ b.cost

/-- Deduplicate by (source, type): identical renderings under different mini-types are
distinct interpretations (e.g. a literal valid as both `Nat` and `Rat`). -/
private def dedupCands (cs : List Cand) : List Cand :=
  cs.foldl (fun acc c =>
    if acc.any (fun d => d.src == c.src && d.ty == c.ty) then acc else acc ++ [c]) []

private def candListCost (ks : List Cand) : Nat :=
  ks.foldl (fun acc k => acc + k.cost) 0

/-- Coercion paths; when `final = false`, lossy finalization edges are excluded so they can
only ever wrap the *result* of the whole formula, never an intermediate subexpression
(explicit `floor(…)`-style registry entries remain available anywhere). -/
private def coePathsFiltered (src tgt : Ty) (cfg : Config) (final : Bool) :
    List (List (Ty × CoeStyle) × Nat) :=
  let ps := coePaths src tgt cfg
  if final then ps else
    ps.filter fun (steps, _) =>
      !(steps.any fun (_, st) =>
        match st with
        | .toNat | .natAbs | .floorToNat | .roundToNat | .ceilToNat
        | .floorInt | .roundInt | .ceilInt => true
        | _ => false)

private def coerceTo (ctx : Ctx) (c : Cand) (tgt : Ty) (final : Bool) : List Cand :=
  if c.ty == tgt then [c] else
    let paths := coePathsFiltered c.ty tgt ctx.cfg final
    paths.map fun (steps, pc) =>
      { src := applyPath steps c.src, ty := tgt, cost := c.cost + pc }

/-- Extract the argument spine of a curried type: `arr a (arr b c)` with 2 arguments gives
`([a, b], c)`. -/
private def spineOf : Ty → Nat → Option (List Ty × Ty)
  | t, 0 => some ([], t)
  | .arr p r, n + 1 => (spineOf r n).map fun (ps, rt) => (p :: ps, rt)
  | _, _ => none

/-- Cost-ordered bounded cartesian product of child candidate lists. -/
private partial def combosAux (cap : Nat) : List (List Cand) → List (List Cand)
  | [] => [[]]
  | cs :: rest =>
    let tails := combosAux cap rest
    let raw := (cs.take cap).flatMap fun c => tails.map fun t => c :: t
    ((raw.mergeSort fun a b => candListCost a ≤ candListCost b)).take cap

/-- Stable tie-aware sort: `≤` comparators keep insertion order among equals, which preserves
the registry's preference order (exact-type alternatives before cast ones). -/
private def sortAlts (as : List Alt) : List Alt :=
  as.mergeSort fun x y => x.cost ≤ y.cost

mutual

/-- Search an AST node at `target`. Returns ≤ maxCandidatesPerNode candidates, cheapest
first, deduplicated by source. -/
private partial def searchNode (ctx : Ctx) (env : Env) (binder : Option (String × Ty))
    (a : Ast) (target : Ty) (final : Bool) : List Cand :=
  let cap := ctx.cfg.maxCandidatesPerNode
  match a with
  | .lit v =>
    let s := toString v
    let s := if v.num < 0 then s!"({s})" else s
    -- literals are polymorphic over the numeric tower via `OfNat`/`OfScientific`; give the
    -- direct form when possible and keep a concrete-typed fallback for coercion paths
    let direct : List Cand :=
      if target.isNum && (v.den == 1 || target == .rat || target == .real) then
        -- non-Nat targets get an explicit ascription so the elaborator never has to guess
        -- the literal's type (ambiguous instances are expensive to explore and often fail)
        let s' := if target == .nat then s else s!"(({s} : {target.render}))"
        [{ src := s', ty := target, cost := 0 }]
      else []
    let base : Ty := if v.den == 1 then .nat else .rat
    dedupCands ((direct ++ coerceTo ctx { src := s, ty := base, cost := 0 } target final).take cap)
  | .sym name =>
    let varCand : Option Cand :=
      match env.lookup name with
      | some vt => some { src := name, ty := vt, cost := 0 }
      | none =>
        match binder with
        | some (bn, bt) => if bn == name then some { src := name, ty := bt, cost := 0 } else none
        | none => none
    match varCand with
    | some vc => (coerceTo ctx vc target final).take cap
    | none =>
      -- bare symbols must be nullary registry entries; nothing builtin is nullary, so an
      -- unmapped name here simply produces no candidates
      []
  | .call head args => applyName ctx env binder head args target final
  | .add l r => applyName ctx env binder "+" [l, r] target final
  | .sub l r => applyName ctx env binder "-" [l, r] target final
  | .mul l r => applyName ctx env binder "*" [l, r] target final
  | .div l r => applyName ctx env binder "/" [l, r] target final
  | .pow l r => applyName ctx env binder "^" [l, r] target final
  | .neg e => applyName ctx env binder "u-" [e] target final
  | .fact e => applyName ctx env binder "!" [e] target final
  | .sumI v lo hi b => binderNode ctx env binder v lo hi b target false final
  | .prodI v lo hi b => binderNode ctx env binder v lo hi b target true final
  | .intI v lo hi b =>
    -- definite integrals are Real-valued
    let env' := (v, .real) :: env
    let los := searchNode ctx env' binder lo .real true |>.take cap
    let his := searchNode ctx env' binder hi .real true |>.take cap
    let bods := searchNode ctx env' binder b .real false |>.take cap
    let raw := combosAux cap [los, his, bods] |>.filterMap fun ks =>
      match ks with
      | [loC, hiC, bo] =>
        -- written as a plain application; the `∫ … in a..b, …` notation3 is not reliably
        -- available in every importing environment
        some ({ src :=
                  s!"(intervalIntegral (fun ({v} : Real) => ({bo.src})) ({loC.src}) ({hiC.src}) MeasureTheory.volume)",
                ty := .real,
                cost := loC.cost + hiC.cost + bo.cost + 2 } : Cand)
      | _ => none
    let all := dedupCands ((raw.flatMap fun c => coerceTo ctx c target final))
    (all.mergeSort fun a b => a.cost ≤ b.cost).take cap

/-- Summation/product node: bounds searched at `Nat`, body at each monoid in preference
order; `lo = 0` renders as the more readable `Finset.range (hi + 1)`. -/
private partial def binderNode (ctx : Ctx) (env : Env) (binder : Option (String × Ty))
    (v : String) (lo hi b : Ast) (target : Ty) (isProd : Bool) (final : Bool) : List Cand :=
  let cap := ctx.cfg.maxCandidatesPerNode
  let env' := (v, .nat) :: env
  -- bounds may truncate (`final`): a range end like an Int-typed `n - 1` means its Nat value
  let los := searchNode ctx env' binder lo .nat true |>.take cap
  let his := searchNode ctx env' binder hi .nat true |>.take cap
  let op := if isProd then "∏" else "∑"
  let rangeForm :=
    match lo with
    | .lit z => z.den == 1 && z.num == 0
    | _ => false
  let mkSrc (loSrc hiSrc bodySrc : String) : String :=
    if rangeForm then s!"({op} {v} ∈ Finset.range ({parenArg hiSrc} + 1), {bodySrc})"
    else s!"({op} {v} ∈ Finset.Icc {parenArg loSrc} {parenArg hiSrc}, {bodySrc})"
  let perM : List Cand :=
    [.nat, .int, .rat, .real].flatMap fun m =>
      let bods := (searchNode ctx env' binder b m false |>.take cap).take 3
      bods.flatMap fun bo =>
        (los.take 2).flatMap fun loC =>
          (his.take 2).map fun hiC =>
            ({ src := mkSrc loC.src hiC.src bo.src, ty := m,
               cost := loC.cost + hiC.cost + bo.cost + 1 } : Cand)
  let all := dedupCands ((perM.flatMap fun c => coerceTo ctx c target final))
  (all.mergeSort fun a b => a.cost ≤ b.cost).take cap

/-- Resolve a surface name through the registry and combine typed alternatives whose result
type coerces to the expected type. -/
private partial def applyName (ctx : Ctx) (env : Env) (binder : Option (String × Ty))
    (head : String) (args : List Ast) (target : Ty) (final : Bool) : List Cand :=
  let alts := sortAlts (ctx.reg.get head)
  let out := alts.flatMap fun alt =>
    match spineOf alt.ty args.length with
    | none => []
    | some (params, ret) =>
      let reachable := ret == target ∨ !(coePathsFiltered ret target ctx.cfg final).isEmpty
      if !reachable then [] else
      let kids := (args.zip params).map fun (a, p) => searchNode ctx env binder a p false
      (combosAux ctx.cfg.maxCandidatesPerNode kids).map fun k =>
        ({ src := alt.build (k.map (·.src)),
           ty := ret,
           cost := candListCost k + alt.cost } : Cand)
  let all := dedupCands ((out.flatMap fun c => coerceTo ctx c target final))
  (all.mergeSort fun a b => a.cost ≤ b.cost).take ctx.cfg.maxCandidatesPerNode

end

/-- Search canonicalized root ASTs for a requested target type.
For function targets the AST must have at most one free variable; it becomes the binder
(named from the formula, `_` when there is none). -/
def searchRoots (roots : List Ast) (target : Ty) (reg : Registry := Registry.builtin)
    (cfg : Config := default) : List Root :=
  let ctx : Ctx := { reg, cfg }
  let rootsOut := roots.flatMap fun rootAst =>
    match target with
    | .arr d r =>
      let fvs := rootAst.freeVars
      if fvs.length > 1 then [] else
        let bn := fvs.head?.getD "_"
        (searchNode ctx [] (bn, d) rootAst r true).map fun c =>
          ({ binder := some (bn, d), ty := target, src := c.src,
             ast := rootAst, cost := c.cost } : Root)
    | _ =>
      if !(rootAst.freeVars).isEmpty then [] else
        (searchNode ctx [] none rootAst target true).map fun c =>
          ({ binder := none, ty := target, src := c.src,
             ast := rootAst, cost := c.cost } : Root)
  (rootsOut.mergeSort fun a b => a.cost < b.cost).take cfg.maxTotalCandidates

end Search

end Formula
