import Mathlib.Tactic

/-!
Helper used by the machine generated `Check.B<batch>.*` modules that validate LLM produced
`Equiv_<hash>.lean` files against the terms OEIS knows.

Each check module `#eval`s `Oeis.Check.report`, which throws on the first indices that
disagree so that `lake build` fails. Translations calling another sequence cannot go through
the real `Axxxxxx.fn` — its body is still `sorry` — so the check module evaluates a copy of
the code redirected to data-backed shims.
-/

namespace Oeis.Check

/-- Reports every index at which a formalized formula disagrees with the OEIS terms.
Throws so that `#eval` turns the mismatch into a build error. -/
def report (name : String) (offset : Int) (expected actual : List Int) : IO Unit := do
  let n := min expected.length actual.length
  let mut bad : Array String := #[]
  for i in [0:n] do
    let e := expected[i]!
    let a := actual[i]!
    if e != a then
      bad := bad.push s!"n={offset + i}: expected {e}, got {a}"
  if h : bad.size > 0 then
    let shown := String.intercalate "; " (bad.toList.take 5)
    let more := if bad.size > 5 then s!" (+{bad.size - 5} more)" else ""
    throw <| IO.userError s!"OEIS_CHECK_FAIL {name}: {shown}{more}"

end Oeis.Check
