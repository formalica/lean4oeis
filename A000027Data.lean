--import OEIS.A000027Defs.lean
import Mathlib.Tactic

import Mathlib.Data.PNat.Defs

def A000027 : PNat → Nat := fun n => (n : Nat)

namespace A000027

def argType : Type := PNat
def retType : Type := Nat

abbrev offset : Int := 1

def fn : Nat → Nat := fun k =>
  if h : 0 < k then A000027 ⟨k, h⟩ else 0

def fz : Int → Nat := fun n =>
  if h : n ≥ 1 then A000027 ⟨n.toNat, by grind⟩ else 0

-- TODO what if someone also want to call it with Int as return type? I do not want to define 4 more functions for each combination of argType and retType
-- maybe only Int -> Int is suficcient, or create them only if needed
def prop : PNat → Nat → Prop := fun n r => A000027 n = r

theorem prop_correct (n : PNat) : prop n (A000027 n) := rfl

-- Coherence theorems between fn and fz

theorem fn_eq_fz (n : Nat) (h : 0 < n) : A000027.fn n = A000027.fz n := by
  unfold A000027.fn A000027.fz
  have h_pos : (n : Int) ≥ 1 := by omega
  simp [h, h_pos]

theorem fn_eq (n : Nat) (h : 0 < n) : A000027.fn n = A000027 ⟨n, h⟩ := by
  unfold A000027.fn
  simp [h]

theorem fz_eq (n : Int) (h : 0 < n) : A000027.fz n = A000027 ⟨n.toNat, by omega⟩ := by
  unfold A000027.fz
  grind

end A000027

---------------------------


namespace A000027

abbrev data : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

@[simp]
theorem data_eq {n: PNat} {h : n < 28} : A000027 n = data[(n:Nat)-1]! := by
  unfold A000027
  have h1 : 1 ≤ (n : Nat) := n.2
  have h2 : (n : Nat) < 28 := h
  set m := (n : Nat) with hm
  interval_cases m <;> decide



@[simp]
theorem data_eq_fn {n: Nat} {h0: 0 < n} {h : n < 28} : A000027.fn n = data[n-1]! := by
  unfold A000027.fn
  split_ifs
  rw [data_eq]
  · simp
  · norm_cast

@[simp]
theorem data_eq_fz {n: Int} {h0: 0 < n} {h : n < 28} : A000027.fz n = data[n.toNat-1]! := by
  simp only [fz_eq n h0]
  rw [data_eq]
  · simp
  · cases n <;> simp_all; norm_cast



end A000027
