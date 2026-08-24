import LOEIS.A000.A000002.Defs

/-!
# A000002 — alternative definition `Equiv_749042cf2779db9e`

Kolakoski sequence: a(n) is length of n-th run; a(1) = 1; sequence consists just of 1's and 2's.

Machine translation of one Maple program of the OEIS entry.

Original Maple source:

    A000002 := proc(n)
    local ksu,k ;
    option remember;
    if n = 1 then
    1;
    elif n <=3 then
    2;
    else
    for k from 1 do
    ksu := add(procname(i),i=1..k) ;
    if n = ksu then
    return (3+(-1)^k)/2 ;
    elif n = ksu+ 1 then
    return (3-(-1)^k)/2 ;
    end if;
    end do:
    end if;
    end proc:

Chosen index type: `PNat`. Value type: `Nat`.
-/

namespace A000002.Equiv_749042cf2779db9e

def formula_aux (n : Nat) : Nat :=
  let rec loop (m : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel' + 1 =>
      if m = 0 then 0
      else if m = 1 then 1
      else if m ≤ 3 then 2
      else
        let rec find_k (k : Nat) (ksu : Nat) (fk_fuel : Nat) : Nat :=
          match fk_fuel with
          | 0 => 0
          | fk_fuel' + 1 =>
            if k < m then
              let ksu' := ksu + loop k k
              if m = ksu' then
                if k % 2 == 0 then 2 else 1
              else if m = ksu' + 1 then
                if k % 2 == 0 then 1 else 2
              else
                find_k (k + 1) ksu' fk_fuel'
            else
              0
        find_k 1 0 m
  loop n n

def formula (n : PNat) : Nat :=
  formula_aux n.val

/-- The formalized Maple program agrees with the main definition. -/
theorem formula_eq (n : A000002.argType) :
    formula n = A000002 n := sorry

end A000002.Equiv_749042cf2779db9e
