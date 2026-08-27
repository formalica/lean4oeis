import OEISLib.Walk3

/-!
# A149352

Number of walks within N^3 (the first octant of Z^3) starting at (0,0,0) and consisting of n steps taken from {(-1, -1, 0), (-1, 1, 0), (0, 0, -1), (1, 0, 1), (1, 1, -1)}.

OEIS offset `0`. Formalized by the `walkN3` template from the `%t` Wolfram program: the main definition is the high-level octant-walk count `OEISLib.Walk3.count` parameterized by this sequence's step vectors. The low-level dynamic-programming transcription of the Wolfram code lives in the `Equiv_<hash>` file.
-/

namespace A149352

/-- Step vectors of `A149352`, exactly as listed in the OEIS title. -/
def steps : List OEISLib.Walk3.Pnt :=
  [(-1, -1, 0), (-1, 1, 0), (0, 0, -1), (1, 0, 1), (1, 1, -1)]

/-- Index type of `A149352` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A149352`. -/
abbrev retType : Type := Nat

/-- OEIS offset: the index of the first known term. -/
abbrev offset : Int := 0

end A149352

/-- Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` and consisting of `n` steps taken from `steps`. -/
def A149352 : A149352.argType → A149352.retType := fun n =>
  OEISLib.Walk3.count A149352.steps n

namespace A149352

/-- Relation that defines `A149352`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Walk3.count steps n = m

/-- `A149352` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A149352

/-- `A149352` as a total function on `Int`; junk value outside the domain.
Always used when composing sequences. -/
def fz : Int → retType := fun n => if 0 ≤ n then A149352 n.toNat else 0

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A149352 n) := rfl

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A149352 n := rfl

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A149352 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A149352
