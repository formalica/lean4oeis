/-
The intermediate AST of the formula parser.

This is the frontend-independent representation every concrete-syntax parser targets: the OEIS
plain-text grammar produces it today, and Wolfram/LaTeX parsers can produce it later, sharing
the same type-directed search and term-construction back end.

The AST is canonicalized right after parsing: additive chains are flattened into signed term
lists and re-emitted with all additions first and all subtractions last
(`3*n^2 - 7*n + 6` ↦ `3*n^2 + 6 - 7*n`). Over `Int`/`Rat`/`Real` this is semantics-neutral, and
over `Nat` it avoids spurious truncation of intermediate differences.
-/

import FormulaParser.Basic

namespace Formula

inductive Ast where
  /-- Integer or decimal literal (always non-negative; sign is a separate node). -/
  | lit (v : Rat)
  /-- A free variable or a registry-resolved symbol used without arguments. -/
  | sym (name : String)
  /-- Application of a named function/sequence to arguments; resolved via `Registry`. -/
  | call (head : String) (args : List Ast)
  | neg (e : Ast)
  | add (l r : Ast)
  | sub (l r : Ast)
  | mul (l r : Ast)
  | div (l r : Ast)
  | pow (l r : Ast)
  | fact (e : Ast)
  /-- Summation `∑ v = lo..hi, body`; the bound variable has type `Nat`. -/
  | sumI (v : String) (lo hi body : Ast)
  /-- Product `∏ v = lo..hi, body`. -/
  | prodI (v : String) (lo hi body : Ast)
  /-- Definite integral over `v` from `lo` to `hi`; always `Real`-valued. -/
  | intI (v : String) (lo hi body : Ast)

deriving instance Inhabited for Ast

namespace Ast

/-- Number of nodes; feeds candidate ranking. -/
def size : Ast → Nat
  | .lit _ => 1
  | .sym _ => 1
  | .call _ args => 1 + (args.map size).sum
  | .neg e => 1 + e.size
  | .add l r => 1 + l.size + r.size
  | .sub l r => 1 + l.size + r.size
  | .mul l r => 1 + l.size + r.size
  | .div l r => 1 + l.size + r.size
  | .pow l r => 1 + l.size + r.size
  | .fact e => 1 + e.size
  | .sumI _ lo hi b => 1 + lo.size + hi.size + b.size
  | .prodI _ lo hi b => 1 + lo.size + hi.size + b.size
  | .intI _ lo hi b => 1 + lo.size + hi.size + b.size

private partial def freeAux (bound : List String) : Ast → List String
  | .lit _ => []
  | .sym s => if bound.contains s then [] else [s]
  | .call _ args => (args.map (freeAux bound)).foldl (· ++ ·) []
  | .neg e | .fact e => freeAux bound e
  | .add l r | .sub l r | .mul l r | .div l r | .pow l r =>
    freeAux bound l ++ freeAux bound r
  | .sumI v lo hi b => binderCase v bound lo hi b
  | .prodI v lo hi b => binderCase v bound lo hi b
  | .intI v lo hi b => binderCase v bound lo hi b
where
  binderCase (v : String) (bound : List String) (lo hi b : Ast) : List String :=
    let bound' := v :: bound
    freeAux bound lo ++ freeAux bound hi ++ freeAux bound' b

/-- Free variables in order of first occurrence, deduplicated. Bound variables of
summations/products/integrals shadow outer bindings. -/
def freeVars (a : Ast) : List String :=
  (freeAux [] a).foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) []

/-- Rebuild a signed term list as `p₁ + … − q₁ − …`, additions before subtractions.
All-positive inputs pass through structurally unchanged. -/
def rebuildSigned (terms : List (Bool × Ast)) : Ast :=
  let pos := (terms.filter (·.1)).map (·.2)
  let neg := (terms.filter (!·.1)).map (·.2)
  match pos, neg with
  | [], [] => .lit 0
  | [p], [] => p
  | _, [] => pos.tail.foldl .add pos.head!
  | [], [n] => .neg n
  | [], n :: ns => ns.foldl (fun acc x => .sub acc x) (.neg n)
  | ps, ns =>
    let base := ps.tail.foldl .add ps.head!
    ns.foldl (fun acc x => .sub acc x) base

mutual
/-- Flatten an additive chain into signed terms; leaves are canonicalized recursively.
`true` marks an added term. -/
partial def flattenAdd : Ast → List (Bool × Ast)
  | .add l r => flattenAdd l ++ flattenAdd r
  | .sub l r => flattenAdd l ++ (flattenAdd r).map (fun p => (!p.1, p.2))
  | .neg e => [(false, canon e)]
  | e => [(true, canon e)]

/-- Canonicalize: reorder additive chains additions-first, recurse everywhere else.
Idempotent; semantics-preserving on `Int`/`Rat`/`Real` and truncation-safe on `Nat`. -/
partial def canon : Ast → Ast
  | .lit v => .lit v
  | .sym s => .sym s
  | .call h args => .call h (args.map canon)
  | .add l r => rebuildSigned (flattenAdd (.add l r))
  | .sub l r => rebuildSigned (flattenAdd (.sub l r))
  | .neg e => .neg (canon e)
  | .mul l r => .mul (canon l) (canon r)
  | .div l r => .div (canon l) (canon r)
  | .pow l r => .pow (canon l) (canon r)
  | .fact e => .fact (canon e)
  | .sumI v lo hi b => .sumI v (canon lo) (canon hi) (canon b)
  | .prodI v lo hi b => .prodI v (canon lo) (canon hi) (canon b)
  | .intI v lo hi b => .intI v (canon lo) (canon hi) (canon b)

end

/-- Precedence level of a node (higher binds tighter). -/
def prec : Ast → Nat
  | .lit _ => 6
  | .sym _ => 6
  | .call .. => 6
  | .fact _ => 5
  | .pow .. => 4
  | .neg _ => 3
  | .mul .. | .div .. => 2
  | .add .. | .sub .. => 1
  | .sumI .. | .prodI .. | .intI .. => 0

private partial def renderAux : Ast → String
  | .lit v =>
    let s := toString v
    if v < 0 then s!"({s})" else s
  | .sym s => s
  | .call h args =>
    let as := (args.map renderAux).foldl (fun acc a => if acc == "" then a else acc ++ ", " ++ a) ""
    h ++ "(" ++ as ++ ")"
  | .neg e => s!"(-{renderAux e})"
  | .fact e =>
    let es := renderAux e
    if e.prec < 5 then s!"({es})!" else es ++ "!"
  | .pow l r =>
    let ls := renderAux l
    let ls := if l.prec < 5 then s!"({ls})" else ls
    let rs := renderAux r
    let rs := if r.prec < 4 then s!"({rs})" else rs
    s!"{ls} ^ {rs}"
  | .mul l r => binCase 2 " * " l r
  | .div l r => binCase 2 " / " l r
  | .add l r => binCase 1 " + " l r
  | .sub l r => binCase 1 " - " l r
  | .sumI v lo hi b =>
    s!"sum_({v}={renderAux lo}..{renderAux hi}) {renderAux b}"
  | .prodI v lo hi b =>
    s!"prod_({v}={renderAux lo}..{renderAux hi}) {renderAux b}"
  | .intI v lo hi b =>
    s!"integral({v}={renderAux lo})^{renderAux hi} {renderAux b}"
where
  binCase (p : Nat) (op : String) (l r : Ast) : String :=
    let ls := renderAux l
    let ls := if l.prec < p then s!"({ls})" else ls
    let rs := renderAux r
    let rs := if r.prec <= p then s!"({rs})" else rs
    s!"{ls}{op}{rs}"

/-- Human-readable math-style rendering, used for debugging, dedup and tests. -/
def render (a : Ast) : String := renderAux a

end Ast

end Formula
