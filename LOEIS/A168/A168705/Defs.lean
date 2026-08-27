import OEISLib.Coxeter

/-!
# A168705

Number of reduced words of length n in Coxeter group on 28 generators S_i with relations (S_i)^2 = (S_i S_j)^17 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=28` `r=17`. The rational generating function is ` (t^17 + 2t^{16}+…+1) / (351·t^17 - 26·(t^{16}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168705

/-- Number of generators `g` of `A168705`. -/
abbrev gParam : Nat := 28

/-- Edge label `r` of `A168705`. -/
abbrev rParam : Nat := 17

/-- `C(g-1,2)` for `A168705`. -/
abbrev c1Param : Nat := 351

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A168705` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168705`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168705

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168705 : A168705.argType → A168705.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168705.gParam A168705.rParam n

namespace A168705

/-- Relation that defines `A168705`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168705 n) := rfl

/-- `A168705` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168705

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168705 n := rfl

/-- `A168705` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168705 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168705 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168705
