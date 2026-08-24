import LOEIS.A000.A000009.Defs

/-!
# A000009 — alternative definition `Equiv_c57fcae257485e7c`

Expansion of Product_{m >= 1} (1 + x^m); number of partitions of n into distinct parts; number of partitions of n into odd parts.

Machine translation of one Maple program of the OEIS entry.

Original Maple source:

    a:= proc(n) option remember; `if`(n=0, 1, add(a(n-j)*add(
    `if`(d::odd, d, 0), d=numtheory[divisors](j)), j=1..n)/n)
    end:
    seq(a(n), n=0..55);  # _Alois P. Heinz_, Jun 24 2025

Chosen index type: `Nat`. Value type: `Nat`.
-/

namespace A000009.Equiv_c57fcae257485e7c

def formula_f (j : Nat) : Nat :=
  (Nat.divisors j).sum (fun d => if d % 2 = 1 then d else 0)

def formula (n : Nat) : Nat :=
  if h : n = 0 then
    1
  else
    let s := (Finset.range n).attach.sum (fun ⟨k, hk⟩ =>
      have : k < n := Finset.mem_range.mp hk
      formula k * formula_f (n - k)
    )
    s / n
termination_by n

/-- The formalized Maple program agrees with the main definition. -/
theorem formula_eq (n : A000009.argType) :
    formula n = A000009 n := sorry

end A000009.Equiv_c57fcae257485e7c
