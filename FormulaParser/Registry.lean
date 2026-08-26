/-
The registry of typed function alternatives.

Every surface name in a formula (`+`, `sqrt`, `A002157`, …) maps to a list of `Alt`s: distinct
Lean interpretations with their own mini-type, cost (preference) and a pure source builder.
The type-directed search picks among alternatives by expected type; ties that survive typing
are resolved later by the caller's validation functor.

Callers extend the builtins through `Registry.insert` — this is how OEIS wiring will add
`Axxxxxx → [main def, .fn, .fz]` alternatives.

Builders return either an atom or a fully parenthesized expression; this invariant lets
compositions stay unambiguous without re-parsing.
-/

import FormulaParser.Basic

namespace Formula

structure Alt where
  /-- Full mini-type of this interpretation, curried (`arr nat (arr nat nat)` for `Nat + Nat`). -/
  ty : Ty
  /-- Render the application from already-rendered argument sources. -/
  build : List String → String
  /-- Preference within one name's alternative list; lower is tried first. -/
  cost : Nat := 0

namespace Alt

/-- `(a op b)` infix application. -/
def infixB (op : String) : List String → String
  | [a, b] => s!"({a} {op} {b})"
  | _ => "<bad-arity>"

/-- Prefix application of a Lean function/constant to arguments. -/
def prefixApp (f : String) : List String → String :=
  fun args => s!"({f} {(args.map parenArg |> String.intercalate " ")})"

/-- Postfix operator application (factorial). A space is required: `n!` would lex as a
single Lean identifier, while `n !` hits Mathlib's postfix notation. -/
def postfixB (post : String) : List String → String
  | [a] => s!"{a} {post}"
  | _ => "<bad-arity>"

/-- Unary minus. -/
def negB : List String → String
  | [a] => s!"(-{a})"
  | _ => "<bad-arity>"

/-- Power with a forced integer exponent (Mathlib's `zpow`). -/
def zpowB : List String → String
  | [a, b] => s!"({a} ^ (({b}) : ℤ))"
  | _ => "<bad-arity>"

/-- Alternative applying a named constant/function to its arguments (the common shape for
user-supplied sequence references like `A002157`, or `.fn`/`.fz` variants). -/
def constApp (name : String) (ty : Ty) (cost : Nat := 0) : Alt :=
  { ty, build := prefixApp name, cost }

end Alt

/-- Lookup table from surface names to their typed alternatives. -/
structure Registry where
  map : Std.HashMap String (List Alt)

instance : Inhabited Registry := ⟨⟨{}⟩⟩

namespace Registry

def empty : Registry := ⟨{}⟩

instance : EmptyCollection Registry := ⟨empty⟩

/-- Add or replace the alternatives of `key`. -/
def insert (r : Registry) (key : String) (alts : List Alt) : Registry :=
  ⟨r.map.insert key alts⟩

/-- Remove a key entirely. -/
def erase (r : Registry) (key : String) : Registry :=
  ⟨r.map.erase key⟩

/-- Exact-key lookup first, then a lowercase fallback (`Sum_`-style capitalization). -/
def get (r : Registry) (key : String) : List Alt :=
  match r.map[key]? with
  | some as => as
  | none =>
    let k := key.toLower
    if k == key then [] else r.map[k]?.getD []

/-! ### The builtin registry -/

private def binAlts (op : String) (tys : List (Ty × Nat)) : List Alt :=
  tys.map fun (t, c) => ({ ty := t, build := Alt.infixB op, cost := c })

/-- Same-type binary alternatives over the numeric tower. -/
private def towerArrs (costOf : Ty → Nat) : List (Ty × Nat) :=
  ([.nat, .int, .rat, .real].map fun t => (t, costOf t))
    |>.map fun (t, c) => (.arr t (.arr t t), c)

/-- Prefix two-argument alternatives over the numeric tower (`min`, `max`). -/
private def pairFnAlts (f : String) : List Alt :=
  [.nat, .int, .rat, .real].map fun t =>
    ({ ty := .arr t (.arr t t), build := Alt.prefixApp f, cost := 0 })

private def absBuild : List String → String
  | [a] => s!"(|{parenArg a}|)"
  | _ => "<bad-arity>"

private def floorAlts : List Alt :=
  [{ ty := .arr .rat .int, build := Alt.prefixApp "Int.floor", cost := 0 },
   { ty := .arr .real .int, build := Alt.prefixApp "Int.floor", cost := 2 }]

private def ceilAlts : List Alt :=
  [{ ty := .arr .rat .int, build := Alt.prefixApp "Int.ceil", cost := 0 },
   { ty := .arr .real .int, build := Alt.prefixApp "Int.ceil", cost := 2 }]

private def binomialAlts : List Alt :=
  [{ ty := .arr .nat (.arr .nat .nat), build := Alt.prefixApp "Nat.choose", cost := 0 }]

/-- Core `Nat.log` is curried: `Nat.log base value`. -/
private def natLogBuild : List String → String
  | [a] => s!"(Nat.log 2 {parenArg a})"
  | _ => "<bad-arity>"

private def gcdAlts : List Alt :=
  [{ ty := .arr .nat (.arr .nat .nat), build := Alt.prefixApp "Nat.gcd", cost := 0 },
   { ty := .arr .int (.arr .int .int), build := Alt.prefixApp "Int.gcd", cost := 1 }]

private def modAlts : List Alt :=
  binAlts "%" [(.arr .nat (.arr .nat .nat), 0), (.arr .int (.arr .int .int), 1)]

/-- Built-in surface names and their typed alternatives. Every arithmetic operation carries
several typed interpretations; the searcher narrows by expected type and the caller's data
validation decides among survivors. -/
def builtin : Registry :=
  Registry.empty
  |>.insert "+" (binAlts "+" (towerArrs fun _ => 0))
  |>.insert "-" (
      -- exact subtraction first; truncating Nat subtraction last (the data decides)
      binAlts "-" [(.arr .int (.arr .int .int), 0), (.arr .rat (.arr .rat .rat), 0),
                   (.arr .real (.arr .real .real), 0), (.arr .nat (.arr .nat .nat), 3)])
  |>.insert "*" (binAlts "*" (towerArrs fun _ => 0))
  |>.insert "/" (
      -- exact rational/real division first, truncating integer divisions last
      binAlts "/" [(.arr .rat (.arr .rat .rat), 0), (.arr .real (.arr .real .real), 1),
                   (.arr .nat (.arr .nat .nat), 4), (.arr .int (.arr .int .int), 4)])
  |>.insert "^" (
      ([.nat, .int, .rat, .real].map fun t =>
          ({ ty := .arr t (.arr .nat t), build := Alt.infixB "^", cost := 0 }))
        ++
      -- negative exponents force rational/real powers (`zpow`)
      [{ ty := .arr .rat (.arr .int .rat), build := Alt.zpowB, cost := 2 },
       { ty := .arr .real (.arr .int .real), build := Alt.zpowB, cost := 2 }])
  |>.insert "u-" ([.int, .rat, .real].map fun t =>
      ({ ty := .arr t t, build := Alt.negB, cost := 0 }))
  |>.insert "!" [
      -- written as an application: the `!` postfix notation is not reliably available
      { ty := .arr .nat .nat, build := Alt.prefixApp "Nat.factorial", cost := 0 }]
  |>.insert "sqrt" [
      { ty := .arr .nat .nat, build := Alt.prefixApp "Nat.sqrt", cost := 0 },
      { ty := .arr .real .real, build := Alt.prefixApp "Real.sqrt", cost := 2 }]
  |>.insert "log" [
      { ty := .arr .nat .nat, build := natLogBuild, cost := 0 },
      { ty := .arr .real .real, build := Alt.prefixApp "Real.log", cost := 2 }]
  |>.insert "log2" [
      { ty := .arr .nat .nat, build := natLogBuild, cost := 0 }]
  |>.insert "ln" [
      { ty := .arr .real .real, build := Alt.prefixApp "Real.log", cost := 1 }]
  |>.insert "exp" [
      { ty := .arr .real .real, build := Alt.prefixApp "Real.exp", cost := 0 }]
  |>.insert "floor" floorAlts
  |>.insert "ceil" ceilAlts
  |>.insert "ceiling" ceilAlts
  |>.insert "abs" ([.int, .rat, .real].map fun t =>
      ({ ty := .arr t t, build := absBuild, cost := 0 }))
  |>.insert "min" (pairFnAlts "min")
  |>.insert "max" (pairFnAlts "max")
  |>.insert "binomial" binomialAlts
  |>.insert "choose" binomialAlts
  |>.insert "C" binomialAlts
  |>.insert "gcd" gcdAlts
  |>.insert "lcm" [
      { ty := .arr .nat (.arr .nat .nat), build := Alt.prefixApp "Nat.lcm", cost := 0 }]
  |>.insert "mod" modAlts

/-- Merge caller alternatives over a base registry (replacing shared keys). This is the main
extension point: pass `Axxxxxx → [main def, .fn, .fz]` entries built with `Alt.constApp`. -/
def overlay (extra : List (String × List Alt)) (base : Registry := builtin) : Registry :=
  extra.foldl (fun r kv => r.insert kv.1 kv.2) base

end Registry

end Formula
