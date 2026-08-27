import Scripts.OeisTemplate.Registry
import Scripts.OeisGen.Render
import Scripts.OeisIngest.Parse

/-!
# Template `walkN3`

> Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` and
> consisting of `n` steps taken from `{...}`

~3250 sequences (Bostan–Kauers 2008), all carrying a `%t` Wolfram program of the shape

```wolfram
aux[i_Integer, j_Integer, k_Integer, n_Integer] := Which[
  Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,
  n == 0, KroneckerDelta[i, j, k, n],
  True, aux[i, j, k, n] = aux[<off1> + i, <off2> + j, <off3> + k, -1 + n] + ...];
Table[Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}], {n, 0, 10}]
```

For each sequence the template:

1. parses the step set out of the title,
2. recognizes exactly this Wolfram pattern in the `%t` section (whitespace/formatting
   tolerant), extracting the step set from the recursion offsets; anything after the
   recognized prefix — e.g. extra recurrences appended by later authors — stays
   unrecognized on purpose,
3. cross-checks both step sets and evaluates a transcription of the DP against the OEIS
   data over the `Table` range,
4. writes `Defs.lean` (main definition via the high-level `OEISLib.Walk3.count`) and
   `Equiv_<hash>.lean` (low-level DP + `formula_eq`),
5. marks the matched `%t` snippet as formalized in `oeis.db` (`source_tag 'T'`,
   `STATUS_VERIFIED` together with the checked values); unmatched snippets stay untouched.

Template-specific parameters (after the common ones):

* `--table-max=K`  verify `K+1` values instead of the Wolfram `Table` range
* `--check-cap=K`  hard cap on how many values to verify (default 12)
-/

namespace Oeis.Template.WalkN3

/-! ## Title parsing -/

private def titlePrefix : String :=
  "Number of walks within N^3 (the first octant of Z^3) starting at (0,0,0) and \
   consisting of n steps taken from {"

/-- Extracts the step vectors listed in the title. -/
def parseTitleSteps (title : String) : Option (Array (Int × Int × Int)) := do
  guard (title.startsWith titlePrefix)
  let rest := (title.drop titlePrefix.length).toString
  guard (rest.endsWith "}.")
  let body := (rest.dropEnd 2).toString
  let mut steps := #[]
  for p in body.splitOn "), (" do
    -- the outer parentheses are shared between neighbors, so strip them per-piece
    let mut p := p.trimAscii.toString
    if p.startsWith "(" then p := (p.drop 1).toString
    if p.endsWith ")" then p := (p.dropEnd 1).toString
    let parts := p.splitOn "," |>.map (·.trimAscii.toString)
    guard (parts.length == 3)
    let x ← parts[0]!.toInt?
    let y ← parts[1]!.toInt?
    let z ← parts[2]!.toInt?
    steps := steps.push (x, y, z)
  return steps

/-! ## Wolfram section extraction -/

/-- Contents of every `%t` record line, paired with its line index in the file. -/
def extractWolfram (seqText : String) : Array (String × Nat) := Id.run do
  let lines := seqText.splitOn "\n"
  let mut out := #[]
  for i in [0:lines.length] do
    match Oeis.parseRecordLine lines[i]! with
    | some ("%t", _, content) => out := out.push (content, i)
    | _ => pure ()
  return out

/-! ## Pattern recognition

A tiny whitespace-tolerant cursor parser over the `%t` text. It accepts both
`aux[i_Integer, ...]` and `aux[i_, ...]`, any spacing, and any `Table` range. -/

private def skipWs (a : Array Char) (i : Nat) : Nat :=
  if h : i < a.size then
    let c := a[i]'h
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipWs a (i + 1) else i
  else i

private def atStr (a : Array Char) (i : Nat) (lit : String) : Bool :=
  a.extract i (i + lit.length) == lit.toList.toArray

private partial def eatLitGo (a : Array Char) (i : Nat) (ls : List Char) : Option Nat :=
  match ls with
  | [] => some i
  | c :: rest =>
    let i := skipWs a i
    if c.isWhitespace then
      -- a literal space stands for any amount of whitespace, possibly none;
      -- we have already skipped over it, so just carry on
      eatLitGo a i rest
    else if a[i]? == some c then
      eatLitGo a (i + 1) rest
    else
      none

/-- Skips whitespace, then matches the literal (whitespace-insensitively throughout). -/
private def eatLit (a : Array Char) (i0 : Nat) (lit : String) : Option Nat :=
  eatLitGo a i0 lit.toList

private partial def digitsGo (a : Array Char) (i : Nat) (acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let c := a[i]'h
    if c.isDigit then digitsGo a (i + 1) (acc * 10 + (c.toNat - '0'.toNat)) else (acc, i)
  else (acc, i)

private def digitsFrom (a : Array Char) (i : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i
  match a[i]? with
  | some c => if c.isDigit then some (digitsGo a (i + 1) (c.toNat - '0'.toNat)) else none
  | none => none

/-- A binder variable: `v`, `v_` or `v_Integer`. -/
private def eatVar (a : Array Char) (i0 : Nat) : Option (Char × Nat) :=
  let i := skipWs a i0
  match a[i]? with
  | some c =>
    if c == 'i' || c == 'j' || c == 'k' || c == 'n' then
      if atStr a (i + 1) "_" then
        if atStr a (i + 2) "Integer" then some (c, i + 9) else some (c, i + 2)
      else
        some (c, i + 1)
    else
      none
  | none => none

/-- One coordinate expression: `<int>+v` or bare `v`. Returns coefficient and variable. -/
private def eatComp (a : Array Char) (i0 : Nat) : Option (Int × Char × Nat) :=
  let signed : Option (Int × Nat) := do
    let i := skipWs a i0
    match a[i]? with
    | some '-' =>
      let (v, j) ← digitsFrom a (i + 1)
      return (-(v : Int), j)
    | some c =>
      if c.isDigit then
        let (v, j) ← digitsFrom a i
        return ((v : Int), j)
      else none
    | none => none
  match signed with
  | some (c, j) => do
    let j ← eatLit a j "+"
    let (v, k) ← eatVar a j
    return (c, v, k)
  | none => do
    let (v, k) ← eatVar a i0
    return (0, v, k)

/-- `aux[c1+i, c2+j, c3+k, -1+n]`; returns the negated offsets (= the forward step). -/
private def eatSummand (a : Array Char) (i0 : Nat) :
    Option ((Int × Int × Int) × Nat) := do
  let i ← eatLit a i0 "aux["
  let (c1, v1, i) ← eatComp a i
  guard (v1 == 'i')
  let i ← eatLit a i ","
  let (c2, v2, i) ← eatComp a i
  guard (v2 == 'j')
  let i ← eatLit a i ","
  let (c3, v3, i) ← eatComp a i
  guard (v3 == 'k')
  let i ← eatLit a i ", -1 + n]"
  return ((-c1, -c2, -c3), i)

private partial def eatSummands (a : Array Char) (i : Nat)
    (acc : Array (Int × Int × Int)) : Option (Array (Int × Int × Int) × Nat) := do
  let (o, j) ← eatSummand a i
  let acc := acc.push o
  let j2 := skipWs a j
  if a[j2]? == some '+' then eatSummands a (j2 + 1) acc else some (acc, j)

/-- First-occurrence dedup, keeping order. -/
partial def dedupSteps (xs : List (Int × Int × Int))
    (seen : Array (Int × Int × Int) := #[]) : Array (Int × Int × Int) :=
  match xs with
  | [] => seen
  | x :: rest => dedupSteps rest (if seen.contains x then seen else seen.push x)

private structure Recog where
  /-- Exclusive char index into the parsed text where the matched region ends. -/
  endPos : Nat
  steps : Array (Int × Int × Int)
  tableMax : Nat

/-- Recognizes the template program; the error names the pattern piece that did not match,
which doubles as the runner's diagnostic. -/
def recognize (text : String) : Except String Recog := do
  let a := text.toList.toArray
  let stage : Option Nat → String → Except String Nat
    | some v, _ => pure v
    | none, msg => throw s!"did not find '{msg}'"
  let varAt : Nat → Except String (Char × Nat)
    | i =>
      match eatVar a i with
      | some p => pure p
      | none => throw "did not find 'a binder variable (i/j/k/n)'"
  let mut i ← stage (eatLit a 0 "aux[") "aux["
  -- aux[i_, j_, k_, n_] := Which[
  let (_, j) ← varAt i
  i := j
  i ← stage (eatLit a i ",") ","
  let (_, j) ← varAt i
  i := j
  i ← stage (eatLit a i ",") ","
  let (_, j) ← varAt i
  i := j
  i ← stage (eatLit a i ",") ","
  let (_, j) ← varAt i
  i := j
  i ← stage (eatLit a i "] := Which[") "] := Which["
  i ← stage (eatLit a i "Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,")
    "Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,"
  i ← stage (eatLit a i "n == 0, KroneckerDelta[i, j, k, n], True,")
    "n == 0, KroneckerDelta[i, j, k, n], True,"
  i ← stage (eatLit a i "aux[i, j, k, n] = ") "aux[i, j, k, n] = "
  -- the step summands
  let (offsets, j) ←
    match eatSummands a i #[] with
    | some r => pure r
    | none => throw "did not find the step summands aux[c*i + ...]"
  i := j
  -- ]; Table[ Sum[aux[i,j,k,n], {i,0,n}, {j,0,n}, {k,0,n}], {n,0,K}]
  i ← stage (eatLit a i "]; Table[ Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}]")
    "]; Table[ Sum[...]"
  i ← stage (eatLit a i ", {n, 0,") ", {n, 0,"
  let (tableMax, j) ←
    match digitsFrom a i with
    | some r => pure r
    | none => throw "did not find the Table range digits"
  i ← stage (eatLit a j "}]") "}]"
  -- every offset must be built from {-1, 0, 1}
  for o in offsets do
    unless o.1.natAbs ≤ 1 && o.2.1.natAbs ≤ 1 && o.2.2.natAbs ≤ 1 do
      throw s!"step offset {o} is outside the cube -1..1"
  return { endPos := i, steps := dedupSteps offsets.toList, tableMax }

/-! ## Verification against the OEIS data -/

private abbrev Cube := Array (Array (Array Nat))

/-- Level 0 of the DP: `KroneckerDelta[i,j,k,n]`. -/
private def baseLayer (sz : Nat) : Cube :=
  (Array.range sz).map fun i =>
    (Array.range sz).map fun j =>
      (Array.range sz).map fun k => if i = 0 ∧ j = 0 ∧ k = 0 then 1 else 0

/-- One recursion layer of `aux`: level `m` from level `m-1`, including the exact pruning
of the Wolfram code (out-of-octant or `Max[i,j,k] > m` cells stay 0). -/
private def stepLayer (steps : Array (Int × Int × Int)) (m : Nat) (old : Cube) : Cube :=
  (Array.range old.size).map fun i =>
    (Array.range old.size).map fun j =>
      (Array.range old.size).map fun k =>
        if i ≤ m ∧ j ≤ m ∧ k ≤ m then
          steps.foldl (init := 0) fun v s =>
            let pi := (i : Int) - s.1
            let pj := (j : Int) - s.2.1
            let pk := (k : Int) - s.2.2
            if 0 ≤ pi ∧ pi ≤ m - 1 ∧ 0 ≤ pj ∧ pj ≤ m - 1 ∧ 0 ≤ pk ∧ pk ≤ m - 1 then
              v + old[pi.toNat]![pj.toNat]![pk.toNat]!
            else v
        else 0

private def boxSum (layer : Cube) (m : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:m + 1] do
    for j in [0:m + 1] do
      for k in [0:m + 1] do
        t := t + layer[i]![j]![k]!
  return t

/-- Evaluates the DP for `n = 0 .. N` and compares against the OEIS terms.
Returns the `(n, value)` pairs checked. -/
def verifyValues (steps : Array (Int × Int × Int)) (tableMax cap : Nat)
    (terms : Array String) : Except String (Array (Nat × Nat)) := do
  if terms.isEmpty then throw "sequence has no known terms"
  let n := min tableMax (min (terms.size - 1) cap)
  if n < 2 then throw "not enough known terms below the Table range to verify"
  let sz := n + 1
  let mut layer := baseLayer sz
  let mut checked := #[]
  for m in [0:sz] do
    if m > 0 then
      layer := stepLayer steps m layer
    let got := boxSum layer m
    match terms.getD m "" |>.toNat? with
    | none => throw s!"cannot parse term {m}: '{terms.getD m ""}'"
    | some exp =>
      unless got == exp do
        throw s!"value mismatch at n = {m}: wolfram computes {got}, OEIS data says {exp}"
      checked := checked.push (m, got)
  return checked

/-! ## Rendering -/

private def tripleStr (t : Int × Int × Int) : String :=
  s!"({t.1}, {t.2.1}, {t.2.2})"

private def renderStepList (steps : Array (Int × Int × Int)) : String :=
  String.intercalate ", " (steps.toList.map tripleStr)

open Oeis.Template in
/-- Contents of `<out>/<bucket>/<name>/Defs.lean`. -/
def renderDefs (libName : String) (inp : SeqInput) (steps : Array (Int × Int × Int)) :
    String :=
  let ns := inp.name
  "import OEISLib.Walk3\n\n" ++
  "/-!\n# " ++ ns ++ "\n\n" ++ Oeis.Gen.sanitizeDoc inp.title ++ "\n\n" ++
  "OEIS offset `" ++ toString inp.offset ++ "`. Formalized by the `walkN3` template from \
    the `%t` Wolfram program: the main definition is the high-level octant-walk count \
    `OEISLib.Walk3.count` parameterized by this sequence's step vectors. The low-level \
    dynamic-programming transcription of the Wolfram code lives in the `Equiv_<hash>` \
    file.\n-/\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Step vectors of `" ++ ns ++ "`, exactly as listed in the OEIS title. -/\n" ++
  "def steps : List OEISLib.Walk3.Pnt :=\n  [" ++ renderStepList steps ++ "]\n\n" ++
  "/-- Index type of `" ++ ns ++ "` (OEIS offset `" ++ toString inp.offset ++ "`). -/\n" ++
  "abbrev argType : Type := Nat\n\n" ++
  "/-- Value type of `" ++ ns ++ "`. -/\n" ++
  "abbrev retType : Type := Nat\n\n" ++
  "/-- OEIS offset: the index of the first known term. -/\n" ++
  "abbrev offset : Int := " ++ toString inp.offset ++ "\n\n" ++
  "end " ++ ns ++ "\n\n" ++
  "/-- Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` \
    and consisting of `n` steps taken from `steps`. -/\n" ++
  "def " ++ ns ++ " : " ++ ns ++ ".argType → " ++ ns ++ ".retType := fun n =>\n" ++
  "  OEISLib.Walk3.count " ++ ns ++ ".steps n\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Relation that defines `" ++ ns ++ "`. -/\n" ++
  "def prop : argType → retType → Prop := fun n m =>\n" ++
  "  OEISLib.Walk3.count steps n = m\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Nat`; junk value outside the domain. -/\n" ++
  "def fn : Nat → retType := " ++ ns ++ "\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Int`; junk value outside the domain.\n" ++
  "Always used when composing sequences. -/\n" ++
  "def fz : Int → retType := fun n => if 0 ≤ n then " ++ ns ++ " n.toNat else 0\n\n" ++
  "/-- The main definition satisfies its defining relation. -/\n" ++
  "theorem prop_correct (n : argType) : prop n (" ++ ns ++ " n) := rfl\n\n" ++
  "/-- `fn` agrees with the main definition. -/\n" ++
  "theorem fn_eq (n : Nat) : fn n = " ++ ns ++ " n := rfl\n\n" ++
  "/-- `fz` agrees with the main definition on the domain. -/\n" ++
  "theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = " ++ ns ++ " n.toNat := by\n" ++
  "  simp only [fz, if_pos h]\n\n" ++
  "/-- `fn` and `fz` agree on the overlapping domain. -/\n" ++
  "theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by\n" ++
  "  have hn : 0 ≤ (n : Int) := by omega\n" ++
  "  simp only [fn, fz, if_pos hn]\n" ++
  "  congr 1\n\n" ++
  "end " ++ ns ++ "\n"

open Oeis.Template in
/-- Contents of `<out>/<bucket>/<name>/Equiv_<hash>.lean`. -/
def renderEquiv (libName bucket : String) (inp : SeqInput)
    (steps : Array (Int × Int × Int)) (hash wolframText : String) : String :=
  let ns := inp.name
  "import " ++ libName ++ "." ++ bucket ++ "." ++ ns ++ ".Defs\n\n" ++
  "/-!\n# " ++ ns ++ " — low-level definition (`Equiv_" ++ hash ++ "`)\n\n" ++
  "Alternative definition transcribed from the `%t` Wolfram program (formalized in \
    `oeis.db` under formula hash `" ++ hash ++ "`):\n\n" ++
  "```wolfram\n" ++ Oeis.Gen.sanitizeDoc wolframText ++ "\n```\n\n" ++
  "`dpCount` is the dynamic-programming transcription; `formula_eq` shows it coincides \
    with the high-level walk-count main definition in `Defs.lean`.\n-/\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Low-level DP recursion (`aux`) specialized to `" ++ ns ++ "`. -/\n" ++
  "def dpAux : OEISLib.Walk3.Pnt → Nat → Nat :=\n" ++
  "  OEISLib.Walk3.aux steps\n\n" ++
  "/-- Low-level DP count: `Table[Sum[aux[i,j,k,n], {i,0,n}, {j,0,n}, {k,0,n}], ...]`\n" ++
  "specialized to `" ++ ns ++ "`. -/\n" ++
  "def dpCount : Nat → Nat :=\n" ++
  "  OEISLib.Walk3.countDp steps\n\n" ++
  "/-- Every step of `" ++ ns ++ "` lies in `{-1,0,1}^3`, which makes the pruning of the \
    DP value-preserving. -/\n" ++
  "theorem steps_in_unitCube : ∀ s ∈ steps, s ∈ OEISLib.Walk3.unitCube := by decide\n\n" ++
  "/-- **formula_eq**: the low-level count equals the main (high-level) definition. -/\n" ++
  "theorem formula_eq (n : Nat) : dpCount n = " ++ ns ++ " n :=\n" ++
  "  OEISLib.Walk3.countDp_eq_count steps steps_in_unitCube n\n\n" ++
  "end " ++ ns ++ "\n"

/-! ## The template -/

/-- Same multiset of steps? Both lists are already deduplicated, so this is set equality. -/
private def sameStepSet (a b : List (Int × Int × Int)) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

open Oeis.Template in
/-- Applies the walkN3 template to one sequence. -/
def run (ctx : Context) (inp : SeqInput) : IO Outcome := do
  try
    -- template-private parameters
    let mut cap : Nat := 12
    let mut tableOverride : Option Nat := none
    for e in ctx.extras do
      if e.startsWith "--table-max=" then
        tableOverride := (e.drop "--table-max=".length).toNat?
      else if e.startsWith "--check-cap=" then
        if let some v := (e.drop "--check-cap=".length).toNat? then cap := v
      else
        return Outcome.failed s!"unrecognized template parameter '{e}'"
    -- 1. title
    let tStepsOpt := parseTitleSteps inp.title
    if tStepsOpt.isNone then
      return Outcome.skipped "title does not match the walkN3 template"
    let tSteps := tStepsOpt.getD #[]
    if inp.offset != 0 then
      return Outcome.skipped s!"unsupported offset {inp.offset} (template emits a Nat API)"
    if inp.terms.any (·.startsWith "-") then
      return Outcome.failed "unexpected negative terms"
    -- 2. wolfram section
    let wt := extractWolfram inp.seqText
    if wt.isEmpty then
      return Outcome.failed "no %t (wolfram) section found in the seq file"
    let firstLine := wt.getD 0 ("", 0)
    let joined := String.intercalate " " (wt.toList.map (·.1))
    let rec_ ←
      match recognize joined with
      | Except.ok r => pure r
      | Except.error e =>
        return Outcome.failed s!"the %t wolfram code does not match the walkN3 \
          pattern: {e}"
    -- cross-check the two step sets
    unless sameStepSet rec_.steps.toList tSteps.toList do
      return Outcome.failed s!"step set mismatch: title says {tSteps} \
        but the wolfram recursion encodes {rec_.steps}"
    -- 3. verify against the data
    let tableMax := tableOverride.getD rec_.tableMax
    let checked ←
      match verifyValues rec_.steps tableMax cap inp.terms with
      | Except.error e => throw <| IO.userError s!"verification failed: {e}"
      | Except.ok c => pure c
    -- 4. files
    let matchedText := (joined.take rec_.endPos).toString
    let hash := Oeis.formulaHash matchedText
    let bucket := (inp.name.take 4).toString
    let dir := ctx.outDir / bucket / inp.name
    let defsPath := dir / "Defs.lean"
    let equivPath := dir / s!"Equiv_{hash}.lean"
    if !ctx.force && ((← defsPath.pathExists) || (← equivPath.pathExists)) then
      return Outcome.skipped "generated files already exist (use --force to override)"
    let defsBody := renderDefs ctx.libName inp tSteps
    let equivBody := renderEquiv ctx.libName bucket inp rec_.steps hash matchedText
    unless ctx.dryRun do
      IO.FS.createDirAll dir
      IO.FS.writeFile defsPath defsBody
      IO.FS.writeFile equivPath equivBody
      -- 5. mark in the database
      markFormalized ctx inp.name hash matchedText equivBody "computable_definition"
        "STATUS_VERIFIED" "T"
        (checked.map fun p => s!"{p.1}:{p.2}") (some (Int.ofNat firstLine.2))
    return Outcome.ok
      (s!"verified {checked.size} values, wrote Defs.lean + Equiv_{hash}.lean" ++
        if ctx.dryRun then " (dry-run)" else "")
  catch e =>
    return Outcome.failed (toString e)

/-- The template registration consumed by the runner's registry. -/
def template : Template where
  name := "walkN3"
  descr := "walks within N^3 (first octant of Z^3) from a fixed step set (Bostan-Kauers)"
  selectWhere := "title LIKE 'Number of walks within N^3%'"
  run := run

end Oeis.Template.WalkN3
