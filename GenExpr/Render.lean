import GenExpr.Infer
import GenExpr.Normalize

/-!
Printing typed expressions as Lean source.

Two things happen here that are not simple traversal:

* **aggregator lowering.** A binder becomes a `Finset`, a `tsum` with a shifted index, or an
  interval integral, depending on its bounds;
* **cast placement.** A cast is written as an ascription, and a subtree of nothing but literals
  is ascribed once at its root so that Lean does not default it to `ℕ`.

The truncation-safe reordering that `ℕ` needs is *not* here: it is applied in `GenExpr.Infer`,
so that the interpreter and this printer always see the same term.

Bodies are emitted with `«self»` where the definition calls itself, so the same body can be
re-rendered under a different name.
-/

namespace GenExpr

/-- Placeholder standing for the name of the definition being built. -/
def selfToken : String := "«self»"

structure RenderStyle where
  /-- Emit `n !` (needs `open Nat`) instead of `Nat.factorial n`. -/
  postfixFactorial : Bool := false
deriving Inhabited

/-! ## Rendering -/

private def fill (template : String) (args : Array String) : String := Id.run do
  let mut out := template
  for i in [0:args.size] do
    out := out.replace s!"\{{i}}" args[i]!
  return out

private def paren (need : Bool) (s : String) : String := if need then "(" ++ s ++ ")" else s

/-- A subtree of nothing but numerals carries no type information of its own. -/
private partial def allLiterals : TExpr → Bool
  | .lit .. | .dec .. => true
  | .node a args => a.transparent && args.all allLiterals
  | _ => false

mutual

/-- `ctx` is the precedence of the position the term appears in. -/
partial def render (st : RenderStyle) (ctx : Nat) : TExpr → String
  | .lit t ty => paren (ty != .nat && ty.isNumeric && ctx > 1023) s!"{t}"
  | .dec w f ty => paren (ty != .rat) s!"{w}.{f}"
  | .var n _ => n
  | .cast _ d e => s!"({render st 0 e} : {d.render})"
  | e@(.node a args) =>
    -- One ascription pins an all-literal subtree that Lean would otherwise default to `ℕ`.
    if a.result != .nat && a.result.isNumeric && allLiterals e then
      s!"({fill a.template (renderArgs st a args)} : {a.result.render})"
    else paren (a.prec < ctx) (fill a.template (renderArgs st a args))
  | .agg kind v lo hi dv _ hiStrict body ty =>
    -- A big operator's body extends to the right, so an aggregator used as an operand always
    -- needs parentheses.
    paren (ctx > 0) (renderAgg st kind v lo hi dv hiStrict body ty)

partial def renderArgs (st : RenderStyle) (a : Alt) (args : Array TExpr) : Array String :=
  args.mapIdx fun i x => render st (a.argPrec[i]?.getD 1024) x

partial def renderAgg (st : RenderStyle) (kind : AggKind) (v : String) (lo hi dv : Option TExpr)
    (hiStrict : Bool) (body : TExpr) (ty : Ty) : String :=
  -- The body is the rightmost part, so it needs no precedence context of its own.
  match kind, dv, lo, hi with
  | _, some d, _, _ =>
    let sym := if kind == .prod then "∏" else "∑"
    s!"{sym} {v} ∈ Nat.divisors {render st 1024 d}, {render st 0 body}"
  | .integral, none, some l, some h =>
    s!"∫ {v} in ({render st 0 l} : ℝ)..{render st 0 h}, {render st 0 body}"
  | _, none, some l, some h =>
    let sym := if kind == .prod then "∏" else "∑"
    let set :=
      match l with
      | .lit "0" _ => if hiStrict then s!"Finset.range {render st 1024 h}"
                      else s!"Finset.range ({render st 65 h} + 1)"
      | _ => if hiStrict then s!"Finset.Ico {render st 1024 l} {render st 1024 h}"
             else s!"Finset.Icc {render st 1024 l} {render st 1024 h}"
    s!"{sym} {v} ∈ {set}, {render st 0 body}"
  | _, none, some l, none =>
    -- Unbounded: reindex from zero rather than guarding inside the body.
    let sym := if kind == .prod then "∏'" else "∑'"
    let shifted :=
      match l with
      | .lit "0" _ => body
      | .lit s _ => substVar v (natPlus (s.toNat!) (.var v .nat)) body
      | _ => body
    s!"{sym} {v} : ℕ, {render st 0 shifted}"
  | _, _, _, _ => s!"sorry -- unsupported {kind} over {ty.render}"

end

/-! ## Definitions -/

/-- Whether the body calls the definition being built. -/
partial def usesSelf : TExpr → Bool
  | .node a args => a.template.startsWith selfToken || args.any usesSelf
  | e => (TExpr.children e).any usesSelf

partial def usesBigOperator : TExpr → Bool
  | .agg kind _ _ _ _ _ _ _ _ => kind != .integral
  | e => (TExpr.children e).any usesBigOperator

/-- Modules the term needs, beyond whatever the caller already imports. -/
def typingImports (t : Typing) : Array String :=
  let base := t.expr.imports
  if usesBigOperator t.expr then base.push "Mathlib.Algebra.BigOperators.Basic" else base

/-- The body alone, with `«self»` where the definition recurses. Stored as-is, so the same body
can later be re-rendered under a different name. -/
def renderBody (st : RenderStyle) (t : Typing) : String :=
  render st 0 t.expr

private def binders (t : Typing) : String :=
  String.join (t.params.toList.map fun (n, ty) => s!" ({n} : {ty.render})")

/-- A plain `def` for a name, used for auxiliary definitions found in the input. -/
def renderAux (st : RenderStyle) (name : String) (params : Array (String × Ty)) (body : TExpr) :
    String :=
  let bs := String.join (params.toList.map fun (n, ty) => s!" ({n} : {ty.render})")
  let kw := if body.computable then "def" else "noncomputable def"
  s!"{kw} {name}{bs} : {body.ty.render} :=\n  {render st 0 body}"

/-- A complete `def`. `bases` supplies the values of the first indices, which recursion and
patched base cases both need. -/
def renderDef (st : RenderStyle) (t : Typing) (name : String) (bases : Array String := #[]) :
    String :=
  let body := (renderBody st t).replace selfToken name
  let sig := s!"{name}{binders t} : {t.ret.render}"
  let kw := if t.computable then "def" else "noncomputable def"
  if bases.isEmpty then
    if usesSelf t.expr then
      s!"{kw} {sig} :=\n  {body}\ndecreasing_by all_goals simp_wf; omega"
    else s!"{kw} {sig} :=\n  {body}"
  else
    -- Structural form: the listed values, then the general case shifted past them.
    let v := (t.params[0]?.map (·.1)).getD "n"
    let b := bases.size
    let shifted := simplifyOffsets v (substVar v (natPlus b (.var v .nat)) t.expr)
    let arms := bases.toList.mapIdx fun i s => s!"  | {i} => {s}"
    let general := s!"  | {v} + {b} => " ++ (render st 0 shifted).replace selfToken name
    let ty := String.intercalate " → " (t.params.toList.map (·.2.render) ++ [t.ret.render])
    s!"{kw} {name} : {ty}\n" ++ String.intercalate "\n" (arms ++ [general])

end GenExpr
