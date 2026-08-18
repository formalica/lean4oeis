import Mathlib

namespace A000792

abbrev argType := Nat
abbrev retType := Nat
abbrev offset := 0

/--
Relation defining the sequence:
If a set of positive numbers has sum n, this is the largest value of their product.
-/
def prop (n : argType) (max_val : retType) : Prop :=
  (∃ l : List ℕ, (∀ x ∈ l, x > 0) ∧ l.sum = n ∧ l.prod = max_val) ∧
  (∀ l : List ℕ, (∀ x ∈ l, x > 0) → l.sum = n → l.prod ≤ max_val)

/--
Every n has a unique maximum product for its valid partitions.
(Proof omitted as per boilerplate library design, to be filled with specific mathlib partition lemmas).
-/
theorem prop_ex (n : argType) : ∃ max_val, prop n max_val := by
  unfold prop
  simp
  sorry


/-- Total sequence over integers. Returns 0 (junk value) outside the domain. -/
noncomputable def fz (n : Int) : retType :=
  if h : n ≥ 0 then Classical.choose (prop_ex n.toNat) else 0

/-- Sequence restricted to the natural numbers domain. -/
noncomputable def fn (n : Nat) : retType :=
  fz n

end A000792

/-- Main definition for sequence A000792. -/
noncomputable def A000792 (n : A000792.argType) : A000792.retType :=
  A000792.fn n

namespace A000792

theorem prop_correct (n : argType) : prop n (A000792 n) := by
  have h_eq : A000792 n = Classical.choose (prop_ex n) := by
    dsimp [A000792, fn, fz]
  rw [h_eq]
  grind only [Exists.choose_spec]

theorem fn_eq_fz (n : Nat) : fn n = fz n := rfl

theorem fn_eq (n : Nat) : fn n = A000792 n := rfl

theorem fz_eq (n : Int) (h : n ≥ 0) : fz n = A000792 n.toNat := by
  dsimp [A000792, fn]
  have h_cast : (n.toNat : Int) = n := Int.toNat_of_nonneg h
  rw [h_cast]

end A000792

-------------------------------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------


namespace A000792

/-- A finite list of known values. -/
def data : List retType := [1, 1, 2, 3]

/-- Helper lemma to extract uniqueness from the defining property. -/
theorem prop_unique {n : argType} {v1 v2 : retType} (h1 : prop n v1) (h2 : prop n v2) : v1 = v2 := by
  rcases h1 with ⟨⟨l1, hpos1, hsum1, hprod1⟩, hmax1⟩
  rcases h2 with ⟨⟨l2, hpos2, hsum2, hprod2⟩, hmax2⟩
  have le12 : v1 ≤ v2 := by
    subst hprod1
    exact hmax2 l1 hpos1 hsum1
  have le21 : v2 ≤ v1 := by
    subst hprod2
    exact hmax1 l2 hpos2 hsum2
  grind

-- Hardcoded properties for the first 4 elements directly fulfilling the specification text
theorem prop_0 : prop 0 1 := by
  constructor
  · use []
    refine ⟨by intro x hx; simp_all, rfl, rfl⟩
  · intro l hpos hsum
    match l with
    | [] => simp_all
    | a :: tail =>
      have ha : a > 0 := hpos a (by simp)
      simp_all [List.sum_cons]


theorem prop_1 : prop 1 1 := by
  constructor
  · use [1]
    refine ⟨by intro x hx; simp_all, rfl, rfl⟩
  · intro l hpos hsum
    match l with
    | [] => simp_all
    | [a] => simp_all
    | a :: b :: tail =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      simp_all [List.sum_cons]
      omega

theorem prop_2 : prop 2 2 := by
  constructor
  · use [2]
    refine ⟨by intro x hx; simp_all, rfl, rfl⟩
  · intro l hpos hsum
    match l with
    | [] => simp_all
    | [a] => simp_all
    | [a, b] =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      simp_all [List.sum_cons]
      have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      subst ha1 hb1
      omega
    | a :: b :: c :: tail =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      have hc : c > 0 := hpos c (by simp)
      simp_all [List.sum_cons]
      omega

theorem prop_3 : prop 3 3 := by
  constructor
  · use [3]
    refine ⟨by intro x hx; simp_all, rfl, rfl⟩
  · intro l hpos hsum
    match l with
    | [] => simp_all
    | [a] => simp_all
    | [a, b] =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      simp_all [List.sum_cons]
      have h_cases : a = 1 ∨ a = 2 := by omega
      cases h_cases with
      | inl h => grind
      | inr h => grind
    | [a, b, c] =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      have hc : c > 0 := hpos c (by simp)
      simp_all [List.sum_cons]
      have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      have hc1 : c = 1 := by omega
      subst ha1 hb1 hc1
      omega
    | a :: b :: c :: d :: tail =>
      have ha : a > 0 := hpos a (by simp)
      have hb : b > 0 := hpos b (by simp)
      have hc : c > 0 := hpos c (by simp)
      have hd : d > 0 := hpos d (by simp)
      simp_all [List.sum_cons]
      omega

theorem val_0 : A000792 0 = 1 := prop_unique (prop_correct 0) prop_0
theorem val_1 : A000792 1 = 1 := prop_unique (prop_correct 1) prop_1
theorem val_2 : A000792 2 = 2 := prop_unique (prop_correct 2) prop_2
theorem val_3 : A000792 3 = 3 := prop_unique (prop_correct 3) prop_3

@[simp]
theorem data_eq {n : argType} (h : n < 4) : A000792 n = data[n]! := by
  interval_cases n
  · simp_all [val_0]; rfl
  · simp_all [val_1]; rfl
  · simp_all [val_2]; rfl
  · simp_all [val_3]; rfl

@[simp]
theorem data_eq_fn {n : Nat} (h : n < 4) : fn n = data[n]! := by
  rw [fn_eq]
  exact data_eq h

@[simp]
theorem data_eq_fz {n : Int} (h : 0 ≤ n) (h_lt : n < 4) : fz n = data[n.toNat]! := by
  rw [fz_eq n h]
  have h_nat : n.toNat < 4 := by omega
  exact data_eq h_nat

end A000792
