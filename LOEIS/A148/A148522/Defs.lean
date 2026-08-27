import OEISLib.Walk3

/-!
# A148522

Number of walks within N^3 (the first octant of Z^3) starting at (0,0,0) and consisting of n steps taken from {(-1, -1, 1), (-1, 1, -1), (1, -1, 0), (1, 1, 0)}.

OEIS offset `0`. Formalized by the `walkN3` template from the `%t` Wolfram program: the main definition is the high-level octant-walk count `OEISLib.Walk3.count` parameterized by this sequence's step vectors. The low-level dynamic-programming transcription of the Wolfram code lives in the `Equiv_<hash>` file.
-/

namespace A148522

/-- Step vectors of `A148522`, exactly as listed in the OEIS title. -/
def steps : List OEISLib.Walk3.Pnt :=
  [(-1, -1, 1), (-1, 1, -1), (1, -1, 0), (1, 1, 0)]

/-- Index type of `A148522` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A148522`. -/
abbrev retType : Type := Nat

/-- OEIS offset: the index of the first known term. -/
abbrev offset : Int := 0

end A148522

/-- Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` and consisting of `n` steps taken from `steps`. -/
def A148522 : A148522.argType → A148522.retType := fun n =>
  OEISLib.Walk3.count A148522.steps n

namespace A148522

/-- Relation that defines `A148522`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Walk3.count steps n = m

/-- `A148522` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A148522

/-- `A148522` as a total function on `Int`; junk value outside the domain.
Always used when composing sequences. -/
def fz : Int → retType := fun n => if 0 ≤ n then A148522 n.toNat else 0

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A148522 n) := rfl

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A148522 n := rfl

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A148522 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A148522
