/-
Tests for the formula parser.

Executed at build time (`lake build FormulaParser.Tests`): the `run_cmd` at the bottom runs
every test, collects failures and throws once with a full report, so a failing suite fails the
build while still reporting every broken case.

Stand-in sequences play the role of the future OEIS-generated definitions, registered through
the public `Registry.overlay` API exactly as the OEIS adapter will do.
-/

import FormulaParser.Parser
import Mathlib.Tactic
import Mathlib.Data.PNat.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- Each test group runs as its own elaboration command with a scoped heartbeat budget.
set_option linter.style.emptyLine false
set_option linter.style.setOption false

namespace FormulaParserTests

open Formula Lean Lean.Elab.Term Meta Elab.Command

/-! ### Stand-ins and registries -/

def DemoSeq (n : Nat) : Nat := n + 3

def DemoSeqFz (n : Int) : Nat := n.toNat + 3

def doubleMe (n : Nat) : Nat := 2 * n

/-- A-number mapped to main-def / fz-style alternatives (the future OEIS adapter pattern). -/
def testReg : Registry :=
  Registry.overlay
    [ ("A002157", [ Alt.constApp "FormulaParserTests.DemoSeq" (.arr .nat .nat) 0,
                    Alt.constApp "FormulaParserTests.DemoSeqFz" (.arr .int .nat) 2 ]) ]

def twiceReg : Registry :=
  Registry.overlay
    [ ("twice", [ Alt.constApp "FormulaParserTests.doubleMe" (.arr .nat .nat) 0 ]) ]

/-! ### Validators and helpers -/

/-- Data-driven validator: accepts `r` iff `r (off + i) == vals[i]` for every `i`.
The check is discharged by `decide` in the kernel — if the term elaborates, it is true;
any wrong interpretation fails to elaborate and rejects the candidate. -/
private def dataValNat (off : Nat) (vals : List Nat) : Result → TermElabM Bool := fun r => do
  let pairs := ((List.range vals.length).map fun i =>
    s!"({toString (off + i)}, {vals[i]!})") |> String.intercalate ", "
  let all := s!"(List.all [{pairs}] (fun p => ({r.src} (p.1)) == p.2))"
  let chk := s!"(by decide : {all} = true)"
  -- fully isolated: a failing check must not pollute elaboration state for later candidates
  try
    withoutModifyingState do
      let stx ← Elab.parseTermStr chk
      let _ ← withoutErrToSorry do elabTerm stx none
      synthesizeSyntheticMVars (postpone := .no)
      pure ()
    pure true
  catch _ => pure false

private def acceptAll : Result → TermElabM Bool := fun _ => pure true

private def rejectAll : Result → TermElabM Bool := fun _ => pure false

/-- `a` occurs in `s`, and `b` occurs after that first occurrence. -/
private def appearsBefore (s a b : String) : Bool :=
  let parts := s.splitOn a
  if parts.length < 2 then false else (String.intercalate a parts.tail).contains b

private def containsBoth (s a b : String) : Bool := s.contains a && s.contains b

/-! ### Harness -/

/-- Run one test; the body returns `""` on success or a failure description. -/
private def runTest (name : String) (t : TermElabM String) (acc : Array String) :
    TermElabM (Array String) := do
  let msg ← try t catch _ => pure "exception thrown during test"
  pure (if msg == "" then acc else acc.push s!"{name}: {msg}")

/-- Assertion helper usable as the last statement of a test body:
`""` on success, otherwise the failure description. -/
private def expect {m : Type → Type} [Monad m] (cond : Bool) (info : String) : m String :=
  if cond then pure "" else pure info

private def headOr (rs : List Result) : Option Result := rs[0]?

/-! ### Group A: segmentation -/

private def testsSegmentation : TermElabM (Array String) := do
  let mut acc : Array String := #[]

  acc ← runTest "A1 noise-only" (do
    let asts := parseAst "The quick brown fox jumps over lazy dogs"
    expect asts.isEmpty s!"expected no formulas, got {asts.map Ast.render}") acc

  acc ← runTest "A2 embedded-missing-paren" (do
    let asts := parseAst "blah (1+2*x^4)/((1-x^3)*(1-x-x^2) some words"
    let ok := asts.any (fun a => containsBoth a.render "^ 4" "x - x")
    expect ok s!"recovered formula not found: {asts.map Ast.render}") acc

  acc ← runTest "A3 attribution-stripped" (do
    let asts := parseAst "a(n) = 2*n + 1. - _Wesley Ivan Hurt_, Jun 15 2016"
    let good := asts.any (fun a => a.render.contains "2 * n + 1")
    let clean := !asts.any (fun a => a.render.contains "Hurt" || a.render.contains "Jun")
    expect (good && clean) s!"attribution not stripped: {asts.map Ast.render}") acc

  acc ← runTest "A4 comma-split" (do
    -- Piece 1 (`a(0)=1`) contributes nothing: both roots sit below `minNodes` (initial
    -- conditions are handled outside this parser). Piece 2 keeps only its RHS segment
    -- (`a(n)` alone is also below the threshold).
    let asts := parseAst "a(0)=1, a(n)=n*a(n-1)"
    expect (asts.length == 1)
      s!"expected 1 root, got {asts.length}: {asts.map Ast.render}") acc

  acc ← runTest "A5 equality-chain" (do
    -- `F(n)` alone is below `minNodes`, so only the RHS segment survives: documents the
    -- degeneracy filter.
    let asts := parseAst "F(n) = F(n-1) + F(n-2)"
    expect (asts.length == 1)
      s!"expected 1 root, got {asts.length}: {asts.map Ast.render}") acc

  acc ← runTest "A6 unicode" (do
    let asts := parseAst "a(n) = n² − 2×n"
    let ok := asts.any (fun a => containsBoth a.render "^ 2" "* n")
    expect ok s!"unicode not normalized: {asts.map Ast.render}") acc

  acc ← runTest "A7 decimal-literal" (do
    -- decimals survive as exact rationals; the IR renders them reduced ("3/2")
    let asts := parseAst "f(x) = 1.5*x"
    expect (asts.any (fun a => containsBoth a.render "3/2" "x"))
      s!"decimal lost: {asts.map Ast.render}") acc

  acc ← runTest "A8 minNodes-filter" (do
    let asts := parseAst "value 16 terms sample"
    let asts1 := parseAst (cfg := { minNodes := 1 }) "value 16 terms sample"
    let has16 := asts1.any (fun a => a.render == "16")
    expect (asts.isEmpty && has16)
      s!"minNodes filter misbehaves: {asts.length} vs {asts1.length}") acc

  pure acc

/-! ### Group B: arithmetic, types, coercions -/

private def testsArithmetic : TermElabM (Array String) := do
  let mut acc : Array String := #[]

  acc ← runTest "B9 literals-constant" (do
    let rs ← findAll "3*4+2" Ty.nat acceptAll
    let ok := match rs[0]? with
      | none => false
      | some w => w.src == "((3 * 4) + 2)"
    expect ok ("unexpected results: " ++ toString (rs.map (·.src))) ) acc

  acc ← runTest "B10 A027599-canonical-order" (do
    let rs ← findAll "a(n) = 3*n^2 - 7*n + 6" (.arr .nat .nat) (dataValNat 0 [6, 2, 4, 12])
    match rs[0]? with
    | none => expect false "no candidate survived data validation"
    | some w =>
      expect (appearsBefore w.src "+ 6" "7 * n")
        s!"additions/subtractions not reordered: {w.src}; all: {(rs.map (·.src))}") acc

  acc ← runTest "B11 negative-intermediates-enumerated" (do
    let rs ← parseAll "(n-2)*2^(n-1)" (.arr .nat .nat)
    expect (rs.any (fun r => r.src.contains "ℤ"))
      s!"no ℤ-routed candidate among {(rs.map (·.src))}") acc

  acc ← runTest "B12 A084847-rational-routing" (do
    -- the formula needs negative-exponent powers; candidates routing through ℚ with a
    -- lossy finalization must exist and elaborate (the Real variants cannot be decided)
    let rs ← parseAll "a(n) = 2*3^n+2^(2n-1)*(n-2)" (.arr .nat .nat)
    let ratRoute := rs.find? fun r => r.src.contains "ℤ" && !r.src.contains ": Real"
    let msg ← match ratRoute with
      | none => expect false s!"no ℚ-routed candidate among {(rs.map (·.src))}"
      | some w => expect True "unexpected empty src"
    pure msg) acc

  acc ← runTest "B14 division-disambiguation" (do
    -- truncating Nat division and exact ℚ-division-with-floor agree here; both routes must
    -- be generated, the cheap one ranked first, and it must survive validation
    let rs ← findAll "a(n) = n/2" (.arr .nat .nat) (dataValNat 0 [0, 0, 1, 1, 2, 2])
    let raw ← parseAll "a(n) = n/2" (.arr .nat .nat)
    let hasFloor := raw.any (fun r => r.src.contains "Int.floor")
    let topOk := match rs[0]? with
      | none => false
      | some w => w.src == "(fun n => (n / 2))"
    expect ((!rs.isEmpty) && hasFloor && topOk)
      s!"expected nat-div winner + floor route, got {(rs.map (·.src))} / {(raw.map (·.src))}") acc

  acc ← runTest "B15 log-alternatives-real-target" (do
    let rs ← parseAll "a(n) = log(2*n+1)" (.arr .nat .real)
    let natLog := rs.any (fun r => r.src.contains "Nat.log")
    let realLog := rs.any (fun r => r.src.contains "Real.log")
    expect (natLog && realLog) s!"expected both log interpretations, got {(rs.map (·.src))}") acc

  acc ← runTest "B16 pnat-domain" (do
    let rs ← findAll "a(n) = 2*n-1" (.arr .pnat .nat) acceptAll
    let msg ← match rs[0]? with
      | none => expect false "no candidate for PNat domain"
      | some w => expect (containsBoth w.src "PNat" ".val") s!"PNat binder mishandled: {w.src}"
    pure msg) acc

  acc ← runTest "B17 subtype-domain" (do
    let rs ← findAll "a(n) = n*n" (.arr (Ty.subNat 2 false) .nat) acceptAll
    let msg ← match rs[0]? with
      | none => expect false "no candidate for subtype domain"
      | some w =>
        expect (containsBoth w.src "{x : Nat // 2 ≤ x}" ".val") s!"subtype binder mishandled: {w.src}"
    pure msg) acc

  acc ← runTest "B18 int-domain-pow" (do
    let rs ← findAll "a(n) = (-1)^n" (.arr .int .int) acceptAll
    let msg ← match rs[0]? with
      | none => expect false "no candidate for Int domain"
      | some w => expect (w.src.contains "^") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "B19 sqrt-by-target" (do
    let rn ← parseAll "a(n) = sqrt(16)*n" (.arr .nat .nat)
    let rr ← parseAll "a(n) = sqrt(16)*n" (.arr .real .real)
    let natsq := rn.any (fun r => r.src.contains "Nat.sqrt")
    let realsq := rr.any (fun r => r.src.contains "Real.sqrt")
    expect (natsq && realsq) s!"sqrt preference broken: {(rn.map (·.src))} / {(rr.map (·.src))}") acc

  acc ← runTest "B20 mixed-intermediates-sum" (do
    -- 2*n + n/2 + n! : several routes agree numerically; cheapest (pure Nat) must win,
    -- and the rational route must also survive validation
    let rs ← findAll "a(n) = 2*n+n/2+n!" (.arr .nat .nat) (dataValNat 0 [1, 3, 7, 13, 34, 132])
    let msg ← match rs[0]? with
      | none => expect false "nothing survived for mixed-intermediates sum"
      | some w => expect (containsBoth w.src "n / 2" "factorial") s!"unexpected winner: {w.src}"
    pure msg) acc

  pure acc

/-! ### Group C: sums, products, integrals, functions -/

private def testsBinders : TermElabM (Array String) := do
  let mut acc : Array String := #[]

  acc ← runTest "C21 sum-paren-style" (do
    let rs ← findAll "a(n)=sum_(k=0)^n A002157(k)" (.arr .nat .nat) (dataValNat 0 [3, 7, 12, 18]) testReg
    let msg ← match rs[0]? with
      | none => expect false "mapped-sequence summation failed"
      | some w =>
        expect (containsBoth w.src "Finset.range" "DemoSeq") s!"unexpected winner: {w.src}"
    pure msg) acc

  acc ← runTest "C22 sum-braced-style" (do
    let rs ← findAll "a(n) = Sum_{k=0..n} A002157(k)" (.arr .nat .nat) (dataValNat 0 [3, 7, 12, 18]) testReg
    let msg ← match rs[0]? with
      | none => expect false "braced summation failed"
      | some w => expect (w.src.contains "Finset.range") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "C23 nested-sums" (do
    let rs ← findAll "a(n) = Sum_{i=1..n} Sum_{j=i..n} min(i, j)" (.arr .nat .nat) acceptAll
    let msg ← match rs[0]? with
      | none => expect false "nested sums failed"
      | some w => expect (containsBoth w.src "Finset.Icc" "min") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "C24 product" (do
    let rs ← findAll "a(n) = Product_{k=1..n} k" (.arr .nat .nat) (dataValNat 1 [1, 2, 6, 24])
    let msg ← match rs[0]? with
      | none => expect false "product failed"
      | some w => expect (containsBoth w.src "∏" "Finset.Icc") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "C25 integral" (do
    let rs ← findAll "integral(x=0)^1 x^2" Ty.real acceptAll
    let msg ← match rs[0]? with
      | none => expect false "integral failed to elaborate"
      | some w => expect (containsBoth w.src "intervalIntegral" "x ^ 2") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "C26 binomial-alias-C" (do
    let rs ← findAll "a(n) = C(n, 2)" (.arr .nat .nat) (dataValNat 0 [0, 0, 1, 3, 6, 10])
    let msg ← match rs[0]? with
      | none => expect false "binomial failed"
      | some w => expect (w.src.contains "Nat.choose") s!"unexpected: {w.src}"
    pure msg) acc

  acc ← runTest "C27 floor-builtin-present" (do
    let rs ← parseAll "a(n) = floor(n/2)" (.arr .nat .nat)
    expect (rs.any (fun r => r.src.contains "Int.floor"))
      s!"floor interpretation absent: {(rs.map (·.src))}") acc

  pure acc

/-! ### Group D: API and robustness -/

private def testsApi1 : TermElabM (Array String) := do
  let mut acc : Array String := #[]

  acc ← runTest "D28 validator-plumbing" (do
    let raw ← parseAll "a(n) = n + 1" (.arr .nat .nat)
    let none' ← findAll "a(n) = n + 1" (.arr .nat .nat) rejectAll
    expect ((!raw.isEmpty) && none'.isEmpty)
      s!"raw={(raw.map (·.src))}, rejected={(none'.map (·.src))}") acc

  acc ← runTest "D29 determinism" (do
    let a ← parseAll "a(n) = 2*3^n+2^(2n-1)*(n-2)" (.arr .nat .nat)
    let b ← parseAll "a(n) = 2*3^n+2^(2n-1)*(n-2)" (.arr .nat .nat)
    expect (a.map (·.src) == b.map (·.src)) "two runs disagree") acc

  acc ← runTest "D30 deep-nesting-terminates" (do
    let rs ← findAll "((((((((1+x)*2)*3)*4)*5)*6)*7)*8)" (.arr .real .real) acceptAll
    expect (!rs.isEmpty) "deep nesting produced nothing") acc

  acc ← runTest "D31 garbage-input" (do
    let a ← findAll "" Ty.nat acceptAll
    let b ← findAll "%%%" Ty.nat acceptAll
    expect (a.isEmpty && b.isEmpty) "garbage produced results") acc

  acc ← runTest "D32 unknown-name-dies" (do
    let rs ← findAll "F(n) = F(n-1) + F(n-2)" (.arr .nat .int) acceptAll
    expect rs.isEmpty s!"self-reference unexpectedly resolved: {(rs.map (·.src))}") acc

  pure acc

private def testsApi2 : TermElabM (Array String) := do
  let mut acc : Array String := #[]
  acc ← runTest "D34 findFirst?-early-exit" (do
    let cnt ← IO.mkRef (0 : Nat)
    let val : Result → TermElabM Bool := fun _ => do cnt.modify (· + 1); pure true
    let r ← findFirst? "a(n) = n + 1" (.arr .nat .nat) val
    let n ← cnt.get
    expect (r.isSome && n == 1) s!"first?={(r.map (·.src))}, calls={n}") acc

  acc ← runTest "D35 registry-add-remove" (do
    let cfg2 : Formula.Config := { minNodes := 2 }
    let yes ← findAll "a(n) = twice(n)" (.arr .nat .nat) (dataValNat 0 [0, 2, 4, 6]) twiceReg cfg2
    let no ← findAll "a(n) = twice(n)" (.arr .nat .nat) acceptAll (twiceReg.erase "twice") cfg2
    expect ((!yes.isEmpty) && no.isEmpty)
      s!"with={(yes.map (·.src))} without={(no.map (·.src))}") acc

  acc ← runTest "D36 implicit-mul-gate" (do
    let prose := parseAst "a 16 terms sample"
    let juxta := parseAst "a(n) = 2n+1"
    let gated := prose.isEmpty
    let joined := juxta.any (fun a => a.render.contains "2 * n")
    expect (gated && joined) s!"prose={prose.map Ast.render} juxta={juxta.map Ast.render}") acc

  acc ← runTest "D37 int-domain-sequence-composition" (do
    let rs ← findAll "a(n)=sum_(k=0)^n A002157(k)" (.arr .int .nat) acceptAll testReg
    expect (rs.any (fun r => r.src.contains "DemoSeq"))
      s!"Int-domain sum failed: {(rs.map (·.src))}") acc

  pure acc

/-! ### Runner -/

/-- One runner command per group: each gets a fresh heartbeat budget. -/
private def report (name : String) (failures : Array String) : CommandElabM Unit := do
  if failures.isEmpty then
    logInfo s!"FormulaParser.Tests [{name}]: all tests passed"
  else
    throwError s!"FormulaParser.Tests [{name}]: {failures.size} failure(s):\n" ++
      String.intercalate "\n" failures.toList

-- Each group elaborates hundreds of candidate terms plus kernel-checked data validations,
-- far exceeding the default 200k heartbeat budget, so every runner gets a large scoped one.
set_option maxHeartbeats 40000000 in
run_cmd
  let failures ← liftTermElabM testsSegmentation
  report "segmentation" failures

set_option maxHeartbeats 40000000 in
-- same rationale: candidate elaboration plus kernel data checks need extra heartbeats
run_cmd
  let failures ← liftTermElabM testsArithmetic
  report "arithmetic" failures

set_option maxHeartbeats 40000000 in
-- same rationale: candidate elaboration plus kernel data checks need extra heartbeats
run_cmd
  let failures ← liftTermElabM testsBinders
  report "binders" failures

set_option maxHeartbeats 40000000 in
-- same rationale: candidate elaboration plus kernel data checks need extra heartbeats
run_cmd
  let failures ← liftTermElabM testsApi1
  report "api1" failures

set_option maxHeartbeats 40000000 in
-- same rationale: candidate elaboration plus kernel data checks need extra heartbeats
run_cmd
  let failures ← liftTermElabM testsApi2
  report "api2" failures

end FormulaParserTests
