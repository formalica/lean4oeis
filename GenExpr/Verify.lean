import GenExpr.Eval.Interp

/-!
Checking a candidate against known values.

The policy follows the spec: failures are only forgivable as a *prefix*. A formula that is right
from some index onwards is repaired by turning the leading disagreements into base cases, which
is allowed either because the caller permits that many (`allowedFailures`) or because the text
itself said so (`for n > 1`). A failure in the middle rejects the candidate outright.

Points that time out, or that depend on a value no table knows, never count as failures — they
just do not count as evidence either, so they lower the success rate.
-/

namespace GenExpr

/-- Which backend checks the values.

The interpreter has real step budgets, which a compiled Lean term cannot offer, so it is the
default; `lean` is the ground truth; `crossCheck` asserts the two agree and is what keeps the two
semantics from drifting. -/
inductive Engine where
  | internal
  | lean
  | internalThenLean
  | crossCheck
deriving DecidableEq, Repr, Inhabited

namespace Engine

def ofString? : String → Option Engine
  | "internal" => some .internal
  | "lean" => some .lean
  | "internalThenLean" | "internal+lean" => some .internalThenLean
  | "crossCheck" => some .crossCheck
  | _ => none

def usesInternal : Engine → Bool
  | .lean => false
  | _ => true

def usesLean : Engine → Bool
  | .internal => false
  | _ => true

end Engine

structure VerifyConfig where
  engine : Engine := .internalThenLean
  /-- How many leading disagreements may be turned into base cases. -/
  allowedFailures : Nat := 0
  /-- Fraction of the supplied points that must actually verify. -/
  minSuccessRate : Float := 0.66
  budgetPerPoint : Nat := 200000
deriving Inhabited

inductive PointStatus where
  | pass
  | patched
  | fail (got : String)
  | unknown
  | timeout
deriving Repr, BEq, Inhabited

namespace PointStatus

def symbol : PointStatus → String
  | .pass => "." | .patched => "b" | .fail _ => "X" | .unknown => "?" | .timeout => "t"

end PointStatus

structure VerifyReport where
  statuses : Array PointStatus := #[]
  passed : Nat := 0
  /-- Leading points supplied as base cases; these become the arms of the emitted definition. -/
  patched : Array (Array Int × Int) := #[]
  accepted : Bool := false
  reason : Option Reject := none
deriving Inhabited

namespace VerifyReport

def trace (r : VerifyReport) : String := String.join (r.statuses.toList.map PointStatus.symbol)

/-- Base-case values in index order, ready for `renderDef`. -/
def bases (r : VerifyReport) : Array String := r.patched.map fun (_, v) => toString v

end VerifyReport

/-- Smallest index the text claims the formula holds from, if it says so. -/
def guardLowerBound (guards : Array Guard) (param : String) : Option Int :=
  guards.foldl (init := none) fun acc g =>
    if g.var != param then acc
    else
      let b? := match g.op with
        | .gt => some (g.bound + 1)
        | .ge => some g.bound
        | _ => none
      match acc, b? with
      | some a, some b => some (max a b)
      | none, b => b
      | a, none => a

/-- Everything the interpreter needs, assembled from a typing. -/
def evalCtxOf (t : Typing) (tables : Array (String × Array (Array Int × Int)) := #[]) : EvalCtx :=
  { self := { params := t.params, body := t.expr }
    aux := t.aux.map fun (n, ps, b) => (n, { params := ps, body := b })
    tables }

/-- What to do about one data point. -/
private inductive Decision where
  | pass
  | patch
  | unknown
  | timeoutRest
  | reject (r : Reject)

/-- Run the interpreter over the points, repairing a leading prefix where that is allowed. -/
def verifyInternal (cfg : VerifyConfig) (ctx : EvalCtx) (points : Array (Array Int × Int))
    (lowerBound : Option Int := none) : VerifyReport := Id.run do
  if points.isEmpty then return { accepted := false, reason := some (.belowSuccessRate 0 0) }
  let mut overrides : Array (Array Int × Int) := #[]
  let mut memo : Std.HashMap String Val := {}
  let mut statuses : Array PointStatus := #[]
  let mut passed := 0
  let mut i := 0
  for (args, expected) in points do
    let (r, memo') := evalAt { ctx with overrides } args cfg.budgetPerPoint memo
    memo := memo'
    -- A recursive body cannot produce its own base cases, so *any* outcome at a patchable
    -- position — mismatch, divergence, or an out-of-domain value — is repaired the same way.
    let patchable :=
      i == overrides.size &&
        (overrides.size < cfg.allowedFailures ||
          (match lowerBound, args[0]? with
            | some b, some a => a < b
            | _, _ => false))
    let decision : Decision :=
      match r with
      | .ok v =>
        if v.eqInt expected then .pass
        else if patchable then .patch
        else .reject (.failedAt i (toString expected) v.render)
      | .unknown => .unknown
      | .error .budget => if patchable then .patch else .timeoutRest
      | .error e => if patchable then .patch else .reject (.unsupported e.describe)
    match decision with
    | .pass =>
      statuses := statuses.push .pass
      passed := passed + 1
    | .patch =>
      overrides := overrides.push (args, expected)
      -- Everything downstream of a patched value has to be recomputed.
      memo := {}
      statuses := statuses.push .patched
      passed := passed + 1
    | .unknown => statuses := statuses.push .unknown
    | .timeoutRest =>
      statuses := statuses ++ Array.replicate (points.size - statuses.size) PointStatus.timeout
      break
    | .reject rj =>
      return { statuses := statuses.push (.fail (toString expected)), passed
               patched := overrides, accepted := false, reason := some rj }
    i := i + 1
  let rate := passed.toFloat / points.size.toFloat
  if rate < cfg.minSuccessRate then
    return { statuses, passed, patched := overrides, accepted := false
             reason := some (.belowSuccessRate passed points.size) }
  return { statuses, passed, patched := overrides, accepted := true }

/-- Check one typing against known values. -/
def verify (cfg : VerifyConfig) (t : Typing) (points : Array (Array Int × Int))
    (guards : Array Guard := #[]) (tables : Array (String × Array (Array Int × Int)) := #[]) :
    VerifyReport :=
  if !t.computable then
    { accepted := false, reason := some .notComputable }
  else
    let bound := (t.params[0]?.map (·.1)).bind (guardLowerBound guards)
    verifyInternal cfg (evalCtxOf t tables) points bound

/-- Try the readings in order and return the first that verifies, with its report. -/
def firstVerified (cfg : VerifyConfig) (ts : List Typing) (points : Array (Array Int × Int))
    (guards : Array Guard := #[]) (tables : Array (String × Array (Array Int × Int)) := #[]) :
    Option (Typing × VerifyReport) × Array (Typing × VerifyReport) := Id.run do
  let mut tried : Array (Typing × VerifyReport) := #[]
  for t in ts do
    let r := verify cfg t points guards tables
    tried := tried.push (t, r)
    if r.accepted then return (some (t, r), tried)
  return (none, tried)

end GenExpr
