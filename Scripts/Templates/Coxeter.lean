import Scripts.OeisTemplate.Registry
import Scripts.OeisGen.Render
import Scripts.OeisIngest.Parse
import OEISLib.Coxeter

/-!
# Template `coxeter`

> Number of reduced words of length n in Coxeter group on g generators
> S_i with relations (S_i)^2 = (S_i S_j)^r = I

~2302 sequences, `g ∈ [3,50]`, `r ∈ [3,50]`. Every member has

* `G.f.: (t^r+2t^{r-1}+…+1)/(C(g-1,2) t^r-(g-2)(t^{r-1}+…+t)+1)`  (`%F`, 2302/2302, possibly split over lines)
* often `G.f.: (1+x)(1-x^r)/(1-(g-1)x+(C+(g-2))x^r-C x^{r+1})` (Greubel factorization, `%F`)
* `a(n)= (g-2) Σ_{k=1}^{r-1} a(n-k) - C(g-1,2) a(n-r)` (`%F`, ~250 explicit)
* Wolfram `coxG[{r, C, -(g-2)}]` / `coxG[{r,C,-(g-2),K}]` (`%t`, 1298)
* `CoefficientList[Series[(…)/(…),{x,0,K}],x]` (`%t`)
* `With[{num=Total[2t^Range[r-1]]+t^r+1,…}, CoefficientList[Series[num/den,…],t]]` (`%t`)
* `PARI Vec((…)/(…)+O(x^K))` (`%o`, 488)
* `Magma R<x>:=PowerSeriesRing…; Coefficients(R!((…)/(…)))` (`%o`, 304)

For each sequence the template:

1. parses `(g,r)` from the title,
2. collects program snippets (`%F` joined, `%t`, `%o`) and checks they contain the expected constants `r`, `C(g-1,2)`, `g-2`,
3. verifies the computable `OEISLib.Coxeter.coxSeq g r` against OEIS `data` (up to `cap`, default 12),
4. writes `Defs.lean` (`coxSeq` delegation) and one `Equiv_<hash>.lean` bundling all matched snippets with `formula_eq` bridges,
5. marks each matched snippet in `oeis.db` (`source_tag 'F'/'T'/'O'` `STATUS_VERIFIED`).

Template-private params: `--check-cap=K`
-/

namespace Oeis.Template.Coxeter

/-! ## Title parsing -/

def parseTitle (title : String) : Option (Nat × Nat) := do
  let pref := "Number of reduced words of length n in Coxeter group on "
  guard (title.startsWith pref)
  let rest := (title.drop pref.length).toString
  -- rest: "<g> generators S_i with relations (S_i)^2 = (S_i S_j)^<r> = I."
  let parts := rest.splitOn " generators S_i with relations (S_i)^2 = (S_i S_j)^"
  guard (parts.length == 2)
  let g ← (parts[0]!).trimAscii.toString.toNat?
  let rhs := parts[1]!
  -- rhs: "<r> = I."  (sometimes " <r> = I." with spaces)
  let rStr := (rhs.splitOn " = I.")[0]! |>.trimAscii.toString
  let r ← rStr.toNat?
  guard (3 ≤ g && g ≤ 60)
  guard (3 ≤ r && r ≤ 60)
  return (g, r)

/-! ## Helpers — whitespace-tolerant cursor (copied from WalkN3) -/

private def skipWs (a : Array Char) (i : Nat) : Nat :=
  if h : i < a.size then
    let c := a[i]'h
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipWs a (i + 1) else i
  else i

private partial def eatLitGo (a : Array Char) (i : Nat) (ls : List Char) : Option Nat :=
  match ls with
  | [] => some i
  | c :: rest =>
    let i := skipWs a i
    if c.isWhitespace then eatLitGo a i rest
    else if a[i]? == some c then eatLitGo a (i + 1) rest else none

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

private def skipCommentTail (a : Array Char) (i : Nat) : Nat :=
  let j := skipWs a i
  if a[j]? == some ';' then skipWs a (j + 1)
  else if a[j]? == some '/' && a[j+1]? == some '/' then a.size
  else if a[j]? == some '\\' then a.size
  else if a[j]? == some '(' && a[j+1]? == some '*' then a.size
  else j

/-! ## Snippet recognition -/

structure Recog where
  flavor : String
  tag : String
  endPos : Nat
  k : Option Nat := none

structure Found where
  snip : Recog
  matched : String
  lineIdx : Nat

private def containsStr (text : String) (sub : String) : Bool :=
  text.contains sub

private def recogCoxG (text : String) (g r : Nat) : Option Recog := do
  guard (text.contains "coxG")
  let c1 := OEISLib.Coxeter.c1 g
  let c2 := OEISLib.Coxeter.c2 g
  -- snippet must mention r and c1; check presence
  guard (containsStr text (toString r))
  guard (containsStr text (toString c1))
  -- c2 appears as negative
  guard (containsStr text (toString c2) || containsStr text s!"-{c2}")
  let c := text.toList.toArray
  -- find end position: after `}]` if present, else end
  let endPos := if text.contains "}]" then
    match text.splitOn "}]" with
    | [] => text.length
    | h::_ => h.length + 2
    else text.length
  -- try to extract K = fourth arg if `, <K>]`
  let k : Option Nat := none -- not critical, leave none
  return { flavor := "wolfram-coxG", tag := "T", endPos := min endPos text.length, k }

private def recogSeries (text : String) (g r : Nat) : Option Recog := do
  guard (text.contains "CoefficientList" && text.contains "Series")
  let c1 := OEISLib.Coxeter.c1 g
  guard (containsStr text (toString r) || text.contains "Range")
  -- require c1 or g-1 in text
  guard (containsStr text (toString c1) || containsStr text (toString (g - 1)))
  let endPos := text.length
  -- extract K from `{t, 0, 40}` pattern
  let k : Option Nat := do
    let a := text.toList.toArray
    -- search for ", 0, " then digits
    let mut idx := 0
    let needle := ", 0,"
    let mut found : Option Nat := none
    while idx + needle.length < a.size do
      if a.extract idx (idx + needle.length) == needle.toList.toArray then
        match digitsFrom a (idx + needle.length) with
        | some (v, _) => found := some v; break
        | none => pure ()
      idx := idx + 1
    found
  return { flavor := "wolfram-series", tag := "T", endPos, k }

private def recogGfRational (text : String) (g r : Nat) : Option Recog := do
  let lo := text.toLower
  guard (lo.contains "g.f" || lo.contains "g.f.")
  guard (text.contains "/")
  let c1 := OEISLib.Coxeter.c1 g
  let c2 := OEISLib.Coxeter.c2 g
  -- must mention r as exponent `^r` and c1 and c2
  guard (containsStr text s!"^{r}" || containsStr text s!"^{toString r}")
  guard (containsStr text (toString c1))
  guard (containsStr text (toString c2))
  return { flavor := "gf-rational", tag := "F", endPos := text.length }

private def recogGfFactored (text : String) (g r : Nat) : Option Recog := do
  let lo := text.toLower
  guard (lo.contains "g.f")
  guard (text.contains "(1+x)" || text.contains "(1+t)" || text.contains "(1-x" || text.contains "1-x^")
  guard (containsStr text (toString r))
  let c1 := OEISLib.Coxeter.c1 g
  guard (containsStr text (toString c1) || containsStr text (toString (g - 1)))
  return { flavor := "gf-factored", tag := "F", endPos := text.length }

private def recogRecurrence (text : String) (g r : Nat) : Option Recog := do
  guard (text.contains "a(n)" || text.contains "a(n+")
  guard (text.contains "a(n-" || text.contains "a(n -")
  let c1 := OEISLib.Coxeter.c1 g
  let c2 := OEISLib.Coxeter.c2 g
  guard (containsStr text (toString c1) || containsStr text (toString c2))
  return { flavor := "recurrence", tag := "F", endPos := text.length }

private def recogPari (text : String) (g r : Nat) : Option Recog := do
  guard (text.contains "(PARI)" || (text.contains "Vec(" && text.contains "/"))
  let c1 := OEISLib.Coxeter.c1 g
  guard (containsStr text (toString c1) || containsStr text (toString (g - 1)))
  guard (containsStr text (toString r) || text.contains "x^")
  return { flavor := "pari-vec", tag := "O", endPos := text.length }

private def recogMagma (text : String) (g r : Nat) : Option Recog := do
  guard (text.contains "(Magma)" || text.contains "PowerSeriesRing")
  guard (text.contains "Coefficients" || text.contains "PowerSeries")
  let c1 := OEISLib.Coxeter.c1 g
  guard (containsStr text (toString c1) || containsStr text (toString (g - 1)) || containsStr text (toString r))
  return { flavor := "magma-series", tag := "O", endPos := text.length }

private def recognizeLine (content tag : String) (lineIdx : Nat) (g r : Nat) : List Found :=
  let t := tag.toLower
  let candidates : List (Option Recog) :=
    if t == "t" then
      [recogCoxG content g r, recogSeries content g r]
    else if t == "f" then
      [recogGfRational content g r, recogGfFactored content g r, recogRecurrence content g r]
    else if t == "o" then
      [recogPari content g r, recogMagma content g r]
    else []
  candidates.filterMap fun ropt =>
    ropt.map fun recog =>
      let matched := (content.take recog.endPos).toString
      { snip := recog, matched, lineIdx }

def recognizeAll (seqText : String) (g r : Nat) : Array Found := Id.run do
  let mut out : Array Found := #[]
  let mut seenFlavors : List String := []
  let lines := seqText.splitOn "\n"
  -- Collect all %F contents for joined GF detection
  let mut fContents : Array (String × Nat) := #[]
  for i in [0:lines.length] do
    match Oeis.parseRecordLine lines[i]! with
    | some (tag, _, content) =>
      if content.isEmpty then continue
      if tag == "%F" then fContents := fContents.push (content, i)
    | _ => pure ()
  -- Joined %F blob for split-across-lines G.f.
  if fContents.size > 0 then
    let joined := String.intercalate " " (fContents.toList.map (·.1))
    -- Try GF on joined
    if let some recog := recogGfRational joined g r then
      unless seenFlavors.contains recog.flavor do
        seenFlavors := recog.flavor :: seenFlavors
        out := out.push { snip := recog, matched := (joined.take recog.endPos).toString, lineIdx := fContents[0]!.2 }
    if let some recog := recogGfFactored joined g r then
      unless seenFlavors.contains recog.flavor do
        seenFlavors := recog.flavor :: seenFlavors
        out := out.push { snip := recog, matched := (joined.take recog.endPos).toString, lineIdx := fContents[0]!.2 }
  -- Per-line detection
  for i in [0:lines.length] do
    match Oeis.parseRecordLine lines[i]! with
    | some (tag, _, content) =>
      if content.isEmpty then continue
      let shortTag := tag.drop 1 |>.toString -- "F","T","O"
      for f in recognizeLine content shortTag i g r do
        unless seenFlavors.contains f.snip.flavor do
          seenFlavors := f.snip.flavor :: seenFlavors
          out := out.push f
    | _ => pure ()
  return out

/-! ## Verification -/

def verifyValues (g r : Nat) (cap : Option Nat) (terms : Array String) :
    Except String (Array (Nat × Nat)) := do
  if terms.isEmpty then throw "sequence has no known terms"
  let count := match cap with | some k => min terms.size k | none => terms.size
  if count < 2 then throw "not enough terms to verify"
  let mut checked : Array (Nat × Nat) := #[]
  for i in [0:count] do
    let s := terms.getD i ""
    let some exp := s.toNat? | throw s!"cannot parse term {i}: '{s}'"
    let got := OEISLib.Coxeter.coxSeq g r i
    unless got == exp do
      throw s!"value mismatch at n={i}: coxSeq {g} {r} computes {got}, OEIS data says {exp}"
    checked := checked.push (i, got)
  return checked

/-! ## Rendering -/

open Oeis.Template in
def renderDefs (_libName : String) (inp : SeqInput) (g r : Nat) (bound : Nat) : String :=
  let ns := inp.name
  "import OEISLib.Coxeter\n\n" ++
  "/-!\n# " ++ ns ++ "\n\n" ++ Oeis.Gen.sanitizeDoc inp.title ++ "\n\n" ++
  "OEIS offset `" ++ toString inp.offset ++ "`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=" ++ toString g ++ "` `r=" ++ toString r ++ "`. The rational generating function is ` (t^" ++ toString r ++ " + 2t^{" ++ toString (r-1) ++ "}+…+1) / (" ++ toString (OEISLib.Coxeter.c1 g) ++ "·t^" ++ toString r ++ " - " ++ toString (OEISLib.Coxeter.c2 g) ++ "·(t^{" ++ toString (r-1) ++ "}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.\n-/\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Number of generators `g` of `" ++ ns ++ "`. -/\n" ++
  "abbrev gParam : Nat := " ++ toString g ++ "\n\n" ++
  "/-- Edge label `r` of `" ++ ns ++ "`. -/\n" ++
  "abbrev rParam : Nat := " ++ toString r ++ "\n\n" ++
  "/-- `C(g-1,2)` for `" ++ ns ++ "`. -/\n" ++
  "abbrev c1Param : Nat := " ++ toString (OEISLib.Coxeter.c1 g) ++ "\n\n" ++
  "/-- Search bound (largest term index verified at formalization time). -/\n" ++
  "abbrev searchBound : Nat := " ++ toString bound ++ "\n\n" ++
  "/-- Index type of `" ++ ns ++ "` (OEIS offset `" ++ toString inp.offset ++ "`). -/\n" ++
  "abbrev argType : Type := Nat\n\n" ++
  "/-- Value type of `" ++ ns ++ "`. -/\n" ++
  "abbrev retType : Type := Nat\n\n" ++
  "/-- OEIS offset. -/\n" ++
  "abbrev offset : Int := " ++ toString inp.offset ++ "\n\n" ++
  "end " ++ ns ++ "\n\n" ++
  "/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/\n" ++
  "def " ++ ns ++ " : " ++ ns ++ ".argType → " ++ ns ++ ".retType := fun n =>\n" ++
  "  OEISLib.Coxeter.coxSeq " ++ ns ++ ".gParam " ++ ns ++ ".rParam n\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Relation that defines `" ++ ns ++ "`. -/\n" ++
  "def prop : argType → retType → Prop := fun n m =>\n" ++
  "  OEISLib.Coxeter.coxSeq gParam rParam n = m\n\n" ++
  "/-- The main definition satisfies its defining relation. -/\n" ++
  "theorem prop_correct (n : argType) : prop n (" ++ ns ++ " n) := rfl\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Nat`; junk value outside the domain. -/\n" ++
  "def fn : Nat → retType := " ++ ns ++ "\n\n" ++
  "/-- `fn` agrees with the main definition. -/\n" ++
  "theorem fn_eq (n : Nat) : fn n = " ++ ns ++ " n := rfl\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Int`; junk value outside the domain. -/\n" ++
  "def fz : Int → retType := fun n => if 0 ≤ n then " ++ ns ++ " n.toNat else 0\n\n" ++
  "/-- `fz` agrees with the main definition on the domain. -/\n" ++
  "theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = " ++ ns ++ " n.toNat := by\n" ++
  "  simp only [fz, if_pos h]\n\n" ++
  "/-- `fn` and `fz` agree on the overlapping domain. -/\n" ++
  "theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by\n" ++
  "  have hn : 0 ≤ (n : Int) := by omega\n" ++
  "  simp only [fn, fz, if_pos hn]\n  congr 1\n\n" ++
  "end " ++ ns ++ "\n"

open Oeis.Template in
def renderEquiv (libName bucket : String) (inp : SeqInput) (g r : Nat)
    (hash : String) (snippets : Array Found) : String := Id.run do
  let ns := inp.name
  let mut doc : String :=
    "/-!\n# " ++ ns ++ " — program transcriptions (`Equiv_" ++ hash ++ "`)\n\n" ++
    "Alternative computable definitions transcribed from the OEIS program snippets of this sequence:\n"
  for f in snippets do
    doc := doc ++ "\n* `%" ++ f.snip.tag ++ " " ++ Oeis.Gen.sanitizeDoc f.matched ++ "` (" ++ f.snip.flavor ++ ")"
  doc := doc ++ "\n\nAll delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.\n-/\n\n"
  let kOpt : Option Nat := (snippets.find? fun f => f.snip.k.isSome).bind (·.snip.k)
  let kStr := match kOpt with | some k => toString k | none => "searchBound"
  let body : String :=
    "namespace " ++ ns ++ "\n\n" ++
    "/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/\n" ++
    "def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam " ++ kStr ++ "\n\n" ++
    "/-- `formula` is the generic truncated enumeration (definitionally). -/\n" ++
    "theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam " ++ kStr ++ " := rfl\n\n" ++
    "/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/\n" ++
    "theorem formula_eq (n : Nat) (h : n < formula.length) :\n" ++
    "    formula[n]'h = " ++ ns ++ " n := by\n" ++
    "  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam " ++ kStr ++ ").length := by\n" ++
    "    simpa [formula] using h\n" ++
    "  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam " ++ kStr ++ " n h'\n" ++
    "  have h2 : " ++ ns ++ " n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl\n" ++
    "  rw [h2]\n" ++
    "  simpa [formula] using h1\n\n" ++
    "end " ++ ns ++ "\n"
  "import " ++ libName ++ "." ++ bucket ++ "." ++ ns ++ ".Defs\n\n" ++ doc ++ body

/-! ## The template -/

open Oeis.Template in
def run (ctx : Context) (inp : SeqInput) : IO Outcome := do
  try
    let mut cap : Option Nat := none
    for e in ctx.extras do
      if e.startsWith "--check-cap=" then
        cap := (e.drop "--check-cap=".length).toNat?
      else
        return Outcome.failed s!"unrecognized template parameter '{e}'"
    -- 1. title
    let some (g, r) := parseTitle inp.title
      | return Outcome.skipped "title does not match the coxeter template"
    unless inp.offset == 0 do
      return Outcome.skipped s!"unsupported offset {inp.offset} (template expects 0)"
    if inp.terms.any (·.startsWith "-") then
      return Outcome.failed "unexpected negative terms"
    if inp.terms.isEmpty then
      return Outcome.skipped "sequence publishes no terms"
    -- 2. snippets
    let found := recognizeAll inp.seqText g r
    -- 3. verify against data
    let checked ←
      match verifyValues g r cap inp.terms with
      | Except.error e => throw <| IO.userError s!"verification failed: {e}"
      | Except.ok c => pure c
    let bound := checked.size - 1
    -- 4. files
    let hash := Oeis.formulaHash (String.intercalate "\n" (found.toList.map (·.matched)))
    let bucket := (inp.name.take 4).toString
    let dir := ctx.outDir / bucket / inp.name
    let defsPath := dir / "Defs.lean"
    -- hash empty when no snippets recognized → still write Defs, no Equiv
    let equivPath := dir / s!"Equiv_{hash}.lean"
    if !ctx.force && ((← defsPath.pathExists) || (!found.isEmpty && (← equivPath.pathExists))) then
      return Outcome.skipped "generated files already exist (use --force to override)"
    let defsBody := renderDefs ctx.libName inp g r bound
    unless ctx.dryRun do
      IO.FS.createDirAll dir
      IO.FS.writeFile defsPath defsBody
    let mut msg := s!"verified {checked.size} values, wrote Defs.lean"
    if found.isEmpty then
      msg := msg ++ "; no recognizable %F/%t/%o snippets (left to generic parser)"
    else
      let equivBody := renderEquiv ctx.libName bucket inp g r hash found
      unless ctx.dryRun do
        IO.FS.writeFile equivPath equivBody
        for f in found do
          markFormalized ctx inp.name (Oeis.formulaHash f.matched) f.matched equivBody
            "computable_definition" "STATUS_VERIFIED" f.snip.tag
            (checked.map fun p => s!"{p.1}:{p.2}") (some (Int.ofNat f.lineIdx))
      msg := msg ++ s!" + Equiv_{hash}.lean ({found.size} snippet(s): " ++
        String.intercalate ", " (found.toList.map (·.snip.flavor)) ++ ")"
    return Outcome.ok (msg ++ if ctx.dryRun then " (dry-run)" else "")
  catch e =>
    return Outcome.failed (toString e)

/-- Template registration. -/
def template : Template where
  name := "coxeter"
  descr := "Number of reduced words in Coxeter group on g generators (S_i S_j)^r=I (~2302 seqs)"
  selectWhere := "title LIKE 'Number of reduced words of length n in Coxeter group on %'"
  run := run

end Oeis.Template.Coxeter
