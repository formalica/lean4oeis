import OEISLib.Walk3

/-!
# A148993

Number of walks within N^3 (the first octant of Z^3) starting at (0,0,0) and consisting of n steps taken from {(-1, 0, 1), (-1, 1, 1), (0, -1, 1), (0, 1, 1), (1, 0, -1)}.

OEIS offset `0`. Formalized by the `walkN3` template from the `%t` Wolfram program: the main definition is the high-level octant-walk count `OEISLib.Walk3.count` parameterized by this sequence's step vectors. The low-level dynamic-programming transcription of the Wolfram code lives in the `Equiv_<hash>` file.
-/

namespace A148993

/-- Step vectors of `A148993`, exactly as listed in the OEIS title. -/
def steps : List OEISLib.Walk3.Pnt :=
  [(-1, 0, 1), (-1, 1, 1), (0, -1, 1), (0, 1, 1), (1, 0, -1)]

/-- Index type of `A148993` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A148993`. -/
abbrev retType : Type := Nat

/-- OEIS offset: the index of the first known term. -/
abbrev offset : Int := 0

end A148993

/-- Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` and consisting of `n` steps taken from `steps`. -/
def A148993 : A148993.argType → A148993.retType := fun n =>
  OEISLib.Walk3.count A148993.steps n

namespace A148993

/-- Relation that defines `A148993`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Walk3.count steps n = m

/-- `A148993` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A148993

/-- `A148993` as a total function on `Int`; junk value outside the domain.
Always used when composing sequences. -/
def fz : Int → retType := fun n => if 0 ≤ n then A148993 n.toNat else 0

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A148993 n) := rfl

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A148993 n := rfl

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A148993 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A148993
