import LOEIS.A000.A000009.Defs

/-!
# A000009 — alternative definition `Equiv_0bb81ad07b481ced`

Expansion of Product_{m >= 1} (1 + x^m); number of partitions of n into distinct parts; number of partitions of n into odd parts.

Machine translation of one Maple program of the OEIS entry.

Original Maple source:

    f := proc(i) option remember; local d;
    add(`if`(irem(d, 2) = 1, d, 0), d in NumberTheory:-Divisors(i))
    end proc:
    A000009 := proc(n) option remember; local i;
    `if`(n = 0, 1, add(A000009(n - i)*f(i), i = 1 .. n)/n)
    end proc:
    seq(A000009(n), n = 0 .. 10000); # _Felix Huber_, Apr 10 2026

Chosen index type: `Nat`. Value type: `Nat`.
-/

namespace A000009.Equiv_0bb81ad07b481ced

def formula_f (i : Nat) : Nat :=
  (Nat.divisors i).sum (fun d => if d % 2 = 1 then d else 0)

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

end A000009.Equiv_0bb81ad07b481ced
