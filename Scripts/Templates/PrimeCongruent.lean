import Scripts.OeisTemplate.Registry
import Scripts.OeisGen.Render
import Scripts.OeisIngest.Parse
import OEISLib.Residue

/-!
# Template `primeCongruent`

> Primes congruent to `a` mod `m`.

~980 sequences (single-residue titles; the multi-residue `{…} mod m` variants are their
own templates and are skipped here). Every member carries uniform program snippets; the
template recognizes the shapes shared across the whole family:

* `%t` `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]` — members among the first `K`
  primes (~800 sequences),
* `%o` `(PARI) is(n)=isprime(n) && n%<m>==<a>` — characteristic function (~700),
* `%o` `(Magma) [p: p in PrimesUpTo(<B>) | p mod <m> eq <a>]` — bounded enumeration
  (~970),
* `%t` `Select[Range[s, e, st], PrimeQ]` — arithmetic progression filtered to primes
  (~700).

For each sequence the template:

1. parses `(a, m)` out of the title,
2. recognizes those snippet patterns (whitespace-tolerant); anything else — one-off
   programs, the asymptotic `%F` estimates — stays untouched for the generic parser,
3. evaluates the bounded enumeration against the OEIS data (the search bound is the
   largest published term, so the data itself guarantees enough members exist below it),
4. writes `Defs.lean` (main definition = high-level `OEISLib.Residue.nthIn`, plus the
   propositional characterization `nth_spec`) and one `Equiv_<hash>.lean` holding the
   transcriptions with proved bridges (`formula_eq`),
5. marks every recognized snippet as formalized in `oeis.db` (`source_tag 'T'` / `'O'`,
   `STATUS_VERIFIED`, together with the checked values).

Template-private parameters:

* `--check-cap=K`  verify at most the first `K` values (default: all)
-/

namespace Oeis.Template.PrimeCongruent

/-! ## Title parsing -/

/-- Extracts the residue parameters from `Primes congruent to <a> mod <m>.` -/
def parseTitle (title : String) : Option (Nat × Nat) := do
  guard (title.startsWith "Primes congruent to ")
  let rest := (title.drop "Primes congruent to ".length).toString
  let parts := rest.splitOn " mod "
  guard (parts.length == 2)
  let a ← (parts[0]!).trimAscii.toString.toNat?
  let mEnd := (parts[1]!).trimAscii.toString
  guard (mEnd.endsWith ".")
  let m ← (mEnd.dropEnd 1).toString.toNat?
  guard (2 ≤ m)
  guard (a < m)
  return (a, m)

/-! ## Whitespace-tolerant cursor parsing (same machinery as `WalkN3`) -/

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
    else if a[i]? == some c then eatLitGo a (i + 1) rest
    else none

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

/-- Skips an optional trailing attribution: `(* … *)`, `// …`, `\ …` or `;`. -/
private def skipCommentTail (a : Array Char) (i : Nat) : Nat :=
  let j := skipWs a i
  if a[j]? == some ';' then skipWs a (j + 1)
  else if a[j]? == some '/' && a[j+1]? == some '/' then a.size
  else if a[j]? == some '\\' then a.size
  else if a[j]? == some '(' && a[j+1]? == some '*' then a.size
  else j

/-! ## Snippet recognizers -/

/-- One recognized program snippet. -/
structure Recog where
  /-- Flavor key: at most one snippet per flavor is formalized per sequence. -/
  flavor : String
  /-- `T` = `%t` Wolfram section, `O` = `%o` other language. -/
  tag : String
  /-- End position of the semantic part inside the line (trailing attributions are cut
  off before hashing). -/
  endPos : Nat
  /-- The `K` of `Select[Prime[Range[K]], …]`, when present. -/
  k : Option Nat := none

/-- `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]` -/
def recogWolframFirstPrimes (text : String) (a m : Nat) : Option Recog := do
  let c := text.toList.toArray
  let i ← eatLit c 0 "Select[Prime[Range["
  let (K, i) ← digitsFrom c i
  let i ← eatLit c i "],MemberQ[{"
  let (a', i) ← digitsFrom c i
  guard (a' == a)
  let i ← eatLit c i "},Mod[#,"
  let (m', i) ← digitsFrom c i
  guard (m' == m)
  let i ← eatLit c i "]]&]"
  let j := skipCommentTail c i
  return { flavor := "wolfram-first-primes", tag := "T", endPos := j, k := some K }

/-- `Select[Range[s, e, st], PrimeQ]` — arithmetic progression filtered to primes. -/
def recogWolframProgression (text : String) (a m : Nat) : Option Recog := do
  let c := text.toList.toArray
  let i ← eatLit c 0 "Select[Range["
  let (s, i) ← digitsFrom c i
  let i ← eatLit c i ","
  let (_, i) ← digitsFrom c i
  let i ← eatLit c i ","
  let (st, i) ← digitsFrom c i
  guard (st == m)
  guard (s % m == a % m)
  let i ← eatLit c i "],PrimeQ]"
  let j := skipCommentTail c i
  return { flavor := "wolfram-progression", tag := "T", endPos := j }

/-- `(PARI) is(n)=isprime(n) && n%m==a` -/
def recogPariChar (text : String) (a m : Nat) : Option Recog := do
  let c := text.toList.toArray
  let i ← eatLit c 0 "(PARI)"
  let i ← eatLit c i "is(n)=isprime(n)&&n%"
  let (m', i) ← digitsFrom c i
  guard (m' == m)
  let i ← eatLit c i "=="
  let (a', i) ← digitsFrom c i
  guard (a' == a)
  let j := skipCommentTail c i
  return { flavor := "pari-characteristic-function", tag := "O", endPos := j }

/-- `(Magma) [p: p in PrimesUpTo(B) | p mod m eq a]`, tolerant of the many spacing
variants shipped in these entries. -/
def recogMagma (text : String) (a m : Nat) : Option Recog := do
  let c := text.toList.toArray
  let i ← eatLit c 0 "(Magma)"
  let i ← eatLit c i "[p:p"
  let i ← eatLit c i "inp"
  let i ← eatLit c i "inPrimesUpTo("
  let (_, i) ← digitsFrom c i
  let i ← eatLit c i ")|pmod"
  let (m', i) ← digitsFrom c i
  guard (m' == m)
  let i ← eatLit c i "eq"
  let (a', i) ← digitsFrom c i
  guard (a' == a)
  let i ← eatLit c i "]"
  let j := skipCommentTail c i
  return { flavor := "magma-list", tag := "O", endPos := j }

/-- One recognized occurrence together with its source position. -/
structure Found where
  snip : Recog
  /-- Exact semantic text (for hashing into `oeis.db`). -/
  matched : String
  /-- 0-based index of the `%`-record line inside the `.seq` file. -/
  lineIdx : Nat

/-- Runs every recognizer over one record line. -/
def recognizeLine (content : String) (lineIdx : Nat) (a m : Nat) : List Found :=
  let cands := [("wolfram-first-primes", recogWolframFirstPrimes content a m),
      ("wolfram-progression", recogWolframProgression content a m),
      ("pari-characteristic-function", recogPariChar content a m),
      ("magma-list", recogMagma content a m)]
  cands.filterMap fun (flavorName, r) =>
    r.map fun r' =>
      ⟨{ r' with flavor := flavorName }, (content.take r'.endPos).toString, lineIdx⟩

/-- Extracts every recognizable snippet from the raw `.seq` text. At most one snippet
per flavor survives (the first); later duplicates stay unformalized for the generic
parser. -/
def recognizeAll (seqText : String) (a m : Nat) : Array Found := Id.run do
  let mut out : Array Found := #[]
  let mut seenFlavors : List String := []
  let lines := seqText.splitOn "\n"
  for i in [0:lines.length] do
    match Oeis.parseRecordLine lines[i]! with
    | some ("%t", _, content) | some ("%o", _, content) =>
      if content.isEmpty then continue
      for f in recognizeLine content i a m do
        unless seenFlavors.contains f.snip.flavor do
          seenFlavors := f.snip.flavor :: seenFlavors
          out := out.push f
    | _ => pure ()
  return out

/-! ## Verification against the OEIS data -/

/-- Evaluates the bounded enumeration and compares it with the OEIS terms. The search
bound is the largest known term, so the published data itself guarantees that enough
members exist below it. Returns the checked `(n, value)` pairs (1-based). -/
def verifyValues (a m : Nat) (cap : Option Nat) (terms : Array String) :
    Except String (Array (Nat × Nat)) := do
  let some lastStr := terms[terms.size - 1]?
    | throw "sequence has no known terms"
  let some bound := lastStr.toNat?
    | throw s!"cannot parse last term '{lastStr}'"
  let count := match cap with | some k => min terms.size k | none => terms.size
  let list := OEISLib.Residue.membersUpTo a m bound
  if list.length < count then
    throw s!"enumeration produced only {list.length} members up to {bound}, but the \
      sequence publishes {count} terms"
  let mut checked : Array (Nat × Nat) := #[]
  for i in [0:count] do
    let some expected := (terms.getD i "").toNat?
      | throw s!"cannot parse term {i}: '{terms.getD i ""}'"
    let got := list.getD i 0
    unless got == expected do
      throw s!"value mismatch at n = {i + 1}: computed {got}, OEIS data says {expected}"
    checked := checked.push (i + 1, got)
  return checked

/-! ## Rendering -/

open Oeis.Template in
/-- Contents of `<out>/<bucket>/<name>/Defs.lean`. -/
def renderDefs (_libName : String) (inp : SeqInput) (a m bound : Nat) : String :=
  let ns := inp.name
  "import OEISLib.Residue\n\n" ++
  "/-!\n# " ++ ns ++ "\n\n" ++ Oeis.Gen.sanitizeDoc inp.title ++ "\n\n" ++
  "OEIS offset `" ++ toString inp.offset ++ "`. Formalized by the `primeCongruent` \
    template: the main definition delegates to the generic bounded enumeration \
    `OEISLib.Residue.nthIn` of the primes congruent to `" ++ toString a ++
    "` modulo `" ++ toString m ++ "`. The propositional characterization is `nth_spec`; \
    the transcribed `%t`/`%o` programs live in the `Equiv_<hash>` files.\n-/\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Residue parameter `a` of `" ++ ns ++ "`, exactly as in the OEIS title. -/\n" ++
  "abbrev aRes : Nat := " ++ toString a ++ "\n\n" ++
  "/-- Modulus parameter `m` of `" ++ ns ++ "`. -/\n" ++
  "abbrev modulus : Nat := " ++ toString m ++ "\n\n" ++
  "/-- Search bound: the largest term published by OEIS at formalization time. -/\n" ++
  "abbrev searchBound : Nat := " ++ toString bound ++ "\n\n" ++
  "/-- Index type of `" ++ ns ++ "` (OEIS offset `" ++ toString inp.offset ++ "`). -/\n" ++
  "abbrev argType : Type := PNat\n\n" ++
  "/-- Value type of `" ++ ns ++ "`. -/\n" ++
  "abbrev retType : Type := Nat\n\n" ++
  "/-- OEIS offset: the index of the first known term. -/\n" ++
  "abbrev offset : Int := " ++ toString inp.offset ++ "\n\n" ++
  "end " ++ ns ++ "\n\n" ++
  "/-- Primes congruent to `" ++ toString a ++ "` mod `" ++ toString m ++ "`: the \
    `n`-th member of the class (OEIS indexing starts at 1). Junk value `0` past the \
    search bound. -/\n" ++
  "def " ++ ns ++ " : " ++ ns ++ ".argType → " ++ ns ++ ".retType := fun n =>\n" ++
  "  OEISLib.Residue.nthIn " ++ ns ++ ".aRes " ++ ns ++ ".modulus (n.val - 1) " ++
    ns ++ ".searchBound\n\n" ++
  "namespace " ++ ns ++ "\n\n" ++
  "/-- Relation that defines `" ++ ns ++ "`: `z` is the (`n - 1`)-th member (0-indexed) \
    of the class up to the search bound. -/\n" ++
  "def prop : argType → retType → Prop := fun n z =>\n" ++
  "  OEISLib.Residue.nthIn aRes modulus (n.val - 1) searchBound = z\n\n" ++
  "/-- The main definition satisfies its defining relation. -/\n" ++
  "theorem prop_correct (n : argType) : prop n (" ++ ns ++ " n) := rfl\n\n" ++
  "/-- **High-level characterization**: within the enumerated range, the `n`-th term is \
    prime, congruent to `aRes` modulo `modulus`, and preceded by exactly `n - 1` smaller \
    members of the class. -/\n" ++
  "theorem nth_spec (n : argType)\n" ++
  "    (h : n.val - 1 <\n" ++
  "        (OEISLib.Residue.membersUpTo aRes modulus searchBound).length) :\n" ++
  "    Nat.Prime (" ++ ns ++ " n) ∧ " ++ ns ++ " n % modulus = aRes ∧\n" ++
  "      (OEISLib.Residue.membersUpTo aRes modulus (" ++ ns ++ " n - 1)).length =\n" ++
  "        n.val - 1 :=\n" ++
  "  OEISLib.Residue.nthIn_spec h\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Nat`; junk value outside the domain. -/\n" ++
  "def fn : Nat → retType := fun n => if h : 0 < n then " ++ ns ++ " ⟨n, h⟩ else 0\n\n" ++
  "/-- `fn` agrees with the main definition. -/\n" ++
  "theorem fn_eq (n : Nat) (h : 0 < n) : fn n = " ++ ns ++ " ⟨n, h⟩ := by\n" ++
  "  unfold fn\n  split\n  · rfl\n  · omega\n\n" ++
  "/-- `" ++ ns ++ "` as a total function on `Int`; junk value outside the domain.\n" ++
  "Always used when composing sequences. -/\n" ++
  "def fz : Int → retType := fun i => if h : 1 ≤ i then " ++ ns ++
    " ⟨i.toNat, by omega⟩ else 0\n\n" ++
  "/-- `fz` agrees with the main definition on the domain. -/\n" ++
  "theorem fz_eq (i : Int) (h : 1 ≤ i) : fz i = " ++ ns ++
    " ⟨i.toNat, by omega⟩ := by\n" ++
  "  unfold fz\n  split\n  · rfl\n  · omega\n\n" ++
  "/-- `fn` and `fz` agree on the overlapping domain. -/\n" ++
  "theorem fn_eq_fz (n : Nat) (h : 0 < n) : fn n = fz (n : Int) := by\n" ++
  "  unfold fn fz\n  split\n  · split\n    · congr 1\n    · omega\n  · omega\n\n" ++
  "end " ++ ns ++ "\n"

open Oeis.Template in
/-- Contents of `<out>/<bucket>/<name>/Equiv_<hash>.lean`. -/
def renderEquiv (libName bucket : String) (inp : SeqInput) (a m bound : Nat)
    (hash : String) (snippets : Array Found) : String := Id.run do
  let ns := inp.name
  let mut doc : String :=
    "/-!\n# " ++ ns ++ " — program transcriptions (`Equiv_" ++ hash ++ "`)\n\n" ++
    "Alternative computable definitions transcribed from the OEIS program snippets of \
      this sequence:\n"
  for f in snippets do
    doc := doc ++ "\n* `%" ++ f.snip.tag ++ " " ++ Oeis.Gen.sanitizeDoc f.matched ++ "`"
  doc := doc ++ "\n\nEverything delegates to the shared library `OEISLib.Residue`, so \
    the bridges to the main definition are proved once there and instantiated here.\n\
    -/\n\n"
  let kOpt : Option Nat := (snippets.find? fun f => f.snip.k.isSome).bind (fun f => f.snip.k)
  let mut body : String := doc ++ "namespace " ++ ns ++ "\n\n" ++
    "/-- The canonical bounded enumeration (transcription of the Magma list \
      comprehension and of `Select[Range[…], PrimeQ]`): every member of the class up to \
      `searchBound`, increasing. -/\n" ++
    "def programList : List Nat := OEISLib.Residue.membersUpTo aRes modulus searchBound\n\n" ++
    "/-- `programList` is the generic bounded enumeration (definitionally). -/\n" ++
    "theorem programList_eq :\n" ++
    "    programList = OEISLib.Residue.membersUpTo aRes modulus searchBound := rfl\n\n" ++
    "/-- **formula_eq** (main bridge): reading `programList` position by position is \
      exactly the main definition. -/\n" ++
    "theorem formula_eq (i : Nat) (h : i < programList.length) :\n" ++
    "    programList[i]? = some (" ++ ns ++ " ⟨i + 1, by omega⟩) := by\n" ++
    "  have h1 : programList[i]? =\n" ++
    "      (OEISLib.Residue.membersUpTo aRes modulus searchBound)[i]? := rfl\n" ++
    "  have h2 : " ++ ns ++ " ⟨i + 1, by omega⟩ =\n" ++
    "      OEISLib.Residue.nthIn aRes modulus i searchBound := rfl\n" ++
    "  have h' : i < (OEISLib.Residue.membersUpTo aRes modulus searchBound).length := h\n" ++
    "  rw [h1, h2]\n" ++
    "  rcases OEISLib.Residue.getElem?_nthIn aRes modulus i searchBound with hs | hz\n" ++
    "  · exact hs\n" ++
    "  · exact absurd (OEISLib.Residue.nthIn_pos h') (by rw [hz]; simp)\n\n" ++
    "/-- Characteristic function of the class (transcription of the PARI one-liner). -/\n" ++
    "def pariIs : Nat → Bool := OEISLib.Residue.isMember aRes modulus\n\n" ++
    "/-- The PARI test decides membership in the residue class of primes: `n` is prime \
      and congruent to `aRes` modulo `modulus`. -/\n" ++
    "theorem pariIs_iff (n : Nat) :\n" ++
    "    pariIs n = true ↔ Nat.Prime n ∧ n % modulus = aRes :=\n" ++
    "  OEISLib.Residue.isMember_iff\n\n" ++
    "/-- Every member of the canonical enumeration passes the PARI test. -/\n" ++
    "theorem pariIs_of_mem {n : Nat} (h : n ∈ programList) : pariIs n = true :=\n" ++
    "  (OEISLib.Residue.mem_membersUpTo.mp h).2\n"
  if let some k := kOpt then
    body := body ++
      "/-- Transcription of the Wolfram `Select[Prime[Range[" ++ toString k ++
        "]], MemberQ[{a}, Mod[#, m]] &]`: members sitting among the first " ++
        toString k ++ " primes. -/\n" ++
      "def wolframFirstPrimes : List Nat :=\n" ++
      "  OEISLib.Residue.selectFrom ((OEISLib.Residue.primesUpTo searchBound).take " ++
        toString k ++ ") aRes modulus\n\n" ++
      "/-- It is the canonical enumeration restricted to early members. -/\n" ++
      "theorem wolframFirstPrimes_sub :\n" ++
      "    List.Sublist wolframFirstPrimes programList := by\n" ++
      "  unfold wolframFirstPrimes programList\n" ++
      "  exact OEISLib.Residue.selectFrom_take_sub ..\n\n" ++
      "/-- **formula_eq**: if every member up to the bound sits among the first " ++
        toString k ++ " primes, the Wolfram transcription equals the full enumeration. -/\n" ++
      "theorem wolframFirstPrimes_eq (h : wolframFirstPrimes.length = programList.length) :\n" ++
      "    wolframFirstPrimes = programList :=\n" ++
      "  OEISLib.Residue.eq_of_sub_of_length wolframFirstPrimes_sub h\n"
  body := body ++ "\nend " ++ ns ++ "\n"
  "import " ++ libName ++ "." ++ bucket ++ "." ++ ns ++ ".Defs\n\n" ++
    "set_option maxRecDepth 4096\n\n" ++ body

/-! ## The template -/

open Oeis.Template in
/-- Applies the primeCongruent template to one sequence. -/
def run (ctx : Context) (inp : SeqInput) : IO Outcome := do
  try
    -- template-private parameters
    let mut cap : Option Nat := none
    for e in ctx.extras do
      if e.startsWith "--check-cap=" then
        cap := (e.drop "--check-cap=".length).toNat?
      else
        return Outcome.failed s!"unrecognized template parameter '{e}'"
    -- 1. title
    let some (a, m) := parseTitle inp.title
      | return Outcome.skipped "title does not match the primeCongruent template"
    unless inp.offset == 1 do
      return Outcome.skipped s!"unsupported offset {inp.offset} (template emits a PNat API)"
    if inp.terms.any (·.startsWith "-") then
      return Outcome.failed "unexpected negative terms"
    if inp.terms.isEmpty then
      return Outcome.skipped "sequence publishes no terms"
    -- 2. snippets
    let found := recognizeAll inp.seqText a m
    -- 3. verify against the data
    let checked ←
      match verifyValues a m cap inp.terms with
      | Except.error e => throw <| IO.userError s!"verification failed: {e}"
      | Except.ok c => pure c
    let bound := (inp.terms[inp.terms.size - 1]?).bind (·.toNat?) |>.getD 0
    -- 4. files
    let hash := Oeis.formulaHash
      (String.intercalate "\n" (found.toList.map (·.matched)))
    let bucket := (inp.name.take 4).toString
    let dir := ctx.outDir / bucket / inp.name
    let defsPath := dir / "Defs.lean"
    let equivPath := dir / s!"Equiv_{hash}.lean"
    if !ctx.force && ((← defsPath.pathExists) || (← equivPath.pathExists)) then
      return Outcome.skipped "generated files already exist (use --force to override)"
    let defsBody := renderDefs ctx.libName inp a m bound
    unless ctx.dryRun do
      IO.FS.createDirAll dir
      IO.FS.writeFile defsPath defsBody
    let mut msg := s!"verified {checked.size} values, wrote Defs.lean"
    -- 5. Equiv file + DB marking (only when at least one snippet was recognized)
    if found.isEmpty then
      msg := msg ++ "; no recognizable %t/%o snippets (left to the generic parser)"
    else
      let equivBody := renderEquiv ctx.libName bucket inp a m bound hash found
      unless ctx.dryRun do
        IO.FS.writeFile equivPath equivBody
        for f in found do
          markFormalized ctx inp.name (Oeis.formulaHash f.matched) f.matched equivBody
            "computable_definition" "STATUS_VERIFIED" f.snip.tag
            (checked.map fun p => s!"{p.1}:{p.2}") (some (Int.ofNat f.lineIdx))
      msg := msg ++ s!" + Equiv_{hash}.lean ({found.size} snippet(s))"
    return Outcome.ok (msg ++ if ctx.dryRun then " (dry-run)" else "")
  catch e =>
    return Outcome.failed (toString e)

/-- The template registration consumed by the runner's registry. -/
def template : Template where
  name := "primeCongruent"
  descr := "primes congruent to a mod m (~980 sequences; %t Select / %o PARI+Magma programs)"
  selectWhere := "title LIKE 'Primes congruent to % mod %.' AND title NOT LIKE '%{%'"
  run := run

end Oeis.Template.PrimeCongruent
