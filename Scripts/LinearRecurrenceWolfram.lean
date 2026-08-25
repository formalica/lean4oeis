import SQLite
import Std.Data.HashMap
import Scripts.OeisIngest.Db
import Scripts.OeisIngest.Json

/-!
Formalize Mathematica `LinearRecurrence[...]` `%t` lines into Lean 4 + Mathlib.

Walks OEIS `.seq` files (or queries the `program` table of `Metadata/oeis.db`)
for Mathematica blocks containing calls of the form

    LinearRecurrence[{2, 1, -2}, {3, 5, 13}, 50] (* G. C. Greubel, Jun 27 2018 *)

For each such call it generates:

  * `LOEIS/<bucket>/<A-number>/Equiv_<hash>.lean` — the Lean definition, built
    from `Mathlib.Algebra.LinearRecurrence.LinearRecurrence.mk` and
    `LinearRecurrence.mkSol`;
  * a temporary check module under `Check/LinearRecurrence/B<n>/` that
    `#eval`s the formula against the OEIS terms;

compiles them with `lake build`, and on success marks the formula as
`STATUS_VERIFIED` in `oeis.db`.

    lake exe oeis-linearrec [--seq-dir DIR] [--db PATH]
                            [--bucket A000]... [--seq A000001]...
                            [--terms N] [--timeout SECONDS]
                            [--limit N] [--dry-run] [--keep-check-files]
-/

namespace Oeis.LinearRecurrenceWolfram

open SQLite

-- ---------------------------------------------------------------------------
-- Configuration
-- ---------------------------------------------------------------------------

structure Config where
  dbPath : System.FilePath := "Metadata/oeis.db"
  seqDir : System.FilePath := "oeisdata/seq"
  outDir : System.FilePath := "LOEIS"
  checkDir : System.FilePath := "Check"
  buckets : Array String := #[]
  seqs : Array String := #[]
  terms : Nat := 20
  timeout : Nat := 900
  limit : Nat := 0
  dryRun : Bool := false
  keepCheckFiles : Bool := false
  deriving Inhabited

-- ---------------------------------------------------------------------------
-- Data model
-- ---------------------------------------------------------------------------

/-- One parsed `LinearRecurrence[...]` call. -/
structure Formula where
  oeisName : String
  coeffs : Array Int
  init : Array Int
  rangeArg : String
  author : String := ""
  date : String := ""
  originalText : String := ""
  blockText : String := ""
  sourceHash : String := ""
  title : String := ""
  offset : Int := 0
  terms : Array String := #[]
  formulaHash : String := ""
  deriving Inhabited

-- ---------------------------------------------------------------------------
-- Hashing — blake2b 8-byte digest via `b2sum`, matching the Python pipeline.
-- ---------------------------------------------------------------------------

/-- Compute `blake2b(text, digest_size=8)` via `b2sum -l 64`, return 16 hex chars.
Matches `hashlib.blake2b(text, digest_size=8).hexdigest()` in the Python pipeline. -/
def blake2b8 (text : String) : IO String := do
  let tmpRaw ← IO.Process.run { cmd := "mktemp", args := #[] }
  let tmp : System.FilePath := ⟨tmpRaw.trimAscii.toString⟩
  IO.FS.writeFile tmp text
  let out ← IO.Process.run {
    cmd := "b2sum", args := #["-l", "64", tmp.toString]
  }
  IO.FS.removeFile tmp
  -- Output: "<hex>  <filename>\n"
  return (out.trimAscii.toString.splitOn " ").headD ""

-- ---------------------------------------------------------------------------
-- Parsing helpers (work on List Char to avoid String.Slice issues)
-- ---------------------------------------------------------------------------

/-- Parse an integer from a string. Returns `none` on any non-digit. -/
private def parseInt (s : String) : Option Int :=
  let s := s.trimAscii.toString
  if s.isEmpty then none
  else
    let (sign, body) :=
      if s.startsWith "-" then ((-1 : Int), (s.drop 1).toString)
      else if s.startsWith "+" then ((1 : Int), (s.drop 1).toString)
      else ((1 : Int), s)
    if body.isEmpty then none
    else if body.any (fun c => !c.isDigit) then none
    else
      let digits := body.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat : Int)) 0
      some (sign * digits)

/-- Parse `"1, -2, 3"` into `#[1, -2, 3]`. Returns `none` on any non-integer. -/
private def parseIntList (raw : String) : Option (Array Int) :=
  let parts := (raw.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let result := parts.foldl (fun acc p =>
    match acc with
    | none => none
    | some arr =>
      match parseInt p with
      | some v => some (arr.push v)
      | none => none) (some #[])
  result

/-- Check whether `needle` occurs in `haystack` starting at position `from`. -/
private def startsAt (haystack needle : List Char) (from : Nat) : Bool :=
  if from + needle.length > haystack.length then false
  else (haystack.drop from).take needle.length == needle

/-- Find the first position of `needle` in `haystack` at or after `from`. -/
partial def findSubstr (haystack needle : List Char) (from : Nat := 0) : Option Nat :=
  if from + needle.length > haystack.length then none
  else if startsAt haystack needle from then some from
  else findSubstr haystack needle (from + 1)

/-- Given a list starting with `{`, extract contents between matching braces.
Returns `(contents, indexAfterClosingBrace)`. -/
partial def readBrace (cs : List Char) (start : Nat) : Option (String × Nat) :=
  if start >= cs.length then none
  else if cs.get? start != some '{' then none
  else
    let rec go (i : Nat) (depth : Nat) (content : List Char) : Option (String × Nat) :=
      match cs.get? i with
      | none => none
      | some c =>
        if c == '{' then go (i+1) (depth+1) (c :: content)
        else if c == '}' then
          if depth == 1 then
            some (String.mk content.reverse, i+1)
          else go (i+1) (depth-1) (c :: content)
        else go (i+1) depth (c :: content)
    go (start+1) 1 []

/-- Find the closing bracket `]` at nesting depth 0, starting after `from`
(which is just inside an opening `[`). -/
partial def findCloseBracket (cs : List Char) (from : Nat) : Option Nat :=
  let rec go (i : Nat) (depth : Nat) : Option Nat :=
    match cs.get? i with
    | none => none
    | some c =>
      if c == '[' then go (i+1) (depth+1)
      else if c == ']' then
        if depth == 1 then some i
        else go (i+1) (depth-1)
      else if c == '(' then
        -- Skip parenthesized comment content too
        let rec skipParen (j : Nat) (pd : Nat) : Option Nat :=
          match cs.get? j with
          | none => none
          | some c' =>
            if c' == '(' then skipParen (j+1) (pd+1)
            else if c' == ')' then
              if pd == 1 then go (j+1) depth
              else skipParen (j+1) (pd-1)
            else skipParen (j+1) pd
        skipParen (i+1) 1
      else go (i+1) depth
  go from 1

/-- Skip ASCII whitespace starting at index `i`. -/
def skipWs (cs : List Char) (i : Nat) : Nat :=
  match cs.get? i with
  | some c => if c.isWhitespace then skipWs cs (i+1) else i
  | none => i

/-- Try to parse `(* ... *)` starting at `from`. Returns `(body, indexAfter)`. -/
partial def readComment (cs : List Char) (from : Nat) : Option (String × Nat) :=
  let i := skipWs cs from
  if cs.get? i != some '(' || cs.get? (i+1) != some '*' then none
  else
    let rec go (j : Nat) (content : List Char) : Option (String × Nat) :=
      match cs.get? j with
      | none => none
      | some c =>
        if c == '*' && cs.get? (j+1) == some ')' then
          some (String.mk content.reverse, j+2)
        else go (j+1) (c :: content)
    go (i+2) []

/-- Parse author/date from a comment body like `"_G. C. Greubel_, Jun 27 2018"`
or `"Harvey P. Dale, Aug 02 2015"`. Returns `(author, date)`. -/
private def parseCredit (credit : String) : String × String :=
  let s := credit.trimAscii.toString
  match s.splitOn "," with
  | [author, datePart] =>
    let a := author.replace "_" "" |>.trimAscii.toString
    let d := datePart.trimAscii.toString
    if d.any Char.isDigit then (a, d) else (a, "")
  | _ => (s, "")

/-- Parse one `LinearRecurrence[{...}, {...}, ...]` call at byte/char position
`start` in the text. Returns the formula and the index just past the call (or
past its trailing comment). -/
partial def parseOneCall (text : String) (start : Nat)
    (oeisName : String) (blockText : String) : Option (Formula × Nat) :=
  let cs := text.toList
  -- text[start..] starts with "LinearRecurrence["
  let afterName := start + "LinearRecurrence".length
  let i0 := skipWs cs afterName
  if cs.get? i0 != some '[' then none
  else
    let i1 := skipWs cs (i0 + 1)
    -- First brace group: coefficients
    match readBrace cs i1 with
    | none => none
    | some (coeffsStr, i2) =>
      let i3 := skipWs cs i2
      if cs.get? i3 != some ',' then none
      else
        let i4 := skipWs cs (i3 + 1)
        -- Second brace group: initial values
        match readBrace cs i4 with
        | none => none
        | some (initStr, i5) =>
          let i6 := skipWs cs i5
          -- Optional third argument (range) up to closing ']'
          let (rangeArg, afterRange) :=
            if cs.get? i6 == some ']' then ("", i6)
            else if cs.get? i6 != some ',' then ("", i6)
            else
              let j := skipWs cs (i6 + 1)
              match findCloseBracket cs j with
              | some endB =>
                let rangeChars := (cs.drop j).take (endB - j)
                (String.mk rangeChars |>.trimAscii.toString, endB)
              | none => ("", i6)
          if cs.get? afterRange != some ']' then none
          else
            let afterBracket := afterRange + 1
            -- Optional trailing (* ... *)
            let (author, date, afterCall) :=
              match readComment cs afterBracket with
              | some (body, endIdx) =>
                  let (a, d) := parseCredit body
                  (a, d, endIdx)
              | none => ("", "", afterBracket)
            match parseIntList coeffsStr, parseIntList initStr with
            | some coeffs, some init =>
              if coeffs.size != init.size || coeffs.size == 0 then none
              else
                let origChars := cs.drop start |>.take (afterCall - start)
                let originalText := String.mk origChars |>.trimAscii.toString
                let f : Formula := {
                  oeisName := oeisName
                  coeffs := coeffs
                  init := init
                  rangeArg := rangeArg
                  author := author
                  date := date
                  originalText := originalText
                  blockText := blockText
                }
                some (f, afterCall)
            | _, _ => none

/-- Extract all `LinearRecurrence[...]` calls from one %t block. -/
partial def parseBlock (oeisName : String) (blockText : String) :
    IO (Array Formula) := do
  let needle := "LinearRecurrence[".toList
  let cs := blockText.toList
  let mut results := #[]
  let mut fromByte := 0
  while true do
    match findSubstr cs needle fromByte with
    | none => break
    | some idx =>
      match parseOneCall blockText idx oeisName blockText with
      | some (f, nextIdx) =>
        let fh ← blake2b8 f.originalText
        let sh ← blake2b8 (f.blockText.trimAscii.toString)
        results := results.push { f with formulaHash := fh, sourceHash := sh }
        fromByte := nextIdx
      | none => fromByte := idx + needle.length
  return results

-- ---------------------------------------------------------------------------
-- .seq file scanning
-- ---------------------------------------------------------------------------

/-- Split `%<tag> <A-number> <content>` into `(tag, anum, content)`. -/
private def parseRecordLine (line : String) : Option (String × String × String) :=
  let line := line.trimAsciiEnd.toString
  match line.splitOn " " with
  | tag :: anum :: rest =>
    if tag.length == 2 && tag.startsWith "%" then
      some (tag, anum, (String.intercalate " " rest).trimAscii.toString)
    else none
  | _ => none

/-- Parse all %t blocks from a single .seq file. Returns array of
`(A-number, block-text)`. -/
private def parseSeqFile (contents : String) : Array (String × String) := Id.run do
  let mut blocks : Array (String × Array String) := #[]
  for rawLine in contents.splitOn "\n" do
    match parseRecordLine rawLine with
    | some ("%t", anum, content) =>
      match blocks.findIdx? (·.1 == anum) with
      | some i =>
        let (a, lines) := blocks[i]!
        blocks := blocks.set! i (a, lines.push content)
      | none => blocks := blocks.push (anum, #[content])
    | _ => pure ()
  blocks.filterMap fun (anum, lines) =>
    let text := (String.intercalate "\n" lines.toList).trimAscii.toString
    if text.isEmpty then none else some (anum, text)

/-- Metadata for one sequence parsed from a .seq file. -/
private structure SeqMeta where
  name : String
  title : String := ""
  offset : Int := 0
  terms : Array String := #[]

/-- Parse %N (title), %O (offset), %S/%T/%U (terms) from .seq contents. -/
private def parseSeqMeta (contents : String) : Array SeqMeta := Id.run do
  let mut titles : Array (String × String) := #[]
  let mut offsets : Array (String × String) := #[]
  let mut sTerms : Array (String × String) := #[]
  let mut tTerms : Array (String × String) := #[]
  let mut uTerms : Array (String × String) := #[]
  for rawLine in contents.splitOn "\n" do
    match parseRecordLine rawLine with
    | some ("%N", anum, content) =>
      unless titles.any (·.1 == anum) do titles := titles.push (anum, content)
    | some ("%O", anum, content) =>
      unless offsets.any (·.1 == anum) do offsets := offsets.push (anum, content)
    | some ("%S", anum, content) =>
      match sTerms.findIdx? (·.1 == anum) with
      | some i => let (a,v) := sTerms[i]!; sTerms := sTerms.set! i (a, v ++ content)
      | none => sTerms := sTerms.push (anum, content)
    | some ("%T", anum, content) =>
      match tTerms.findIdx? (·.1 == anum) with
      | some i => let (a,v) := tTerms[i]!; tTerms := tTerms.set! i (a, v ++ content)
      | none => tTerms := tTerms.push (anum, content)
    | some ("%U", anum, content) =>
      match uTerms.findIdx? (·.1 == anum) with
      | some i => let (a,v) := uTerms[i]!; uTerms := uTerms.set! i (a, v ++ content)
      | none => uTerms := uTerms.push (anum, content)
    | _ => pure ()
  -- Collect all A-numbers, deduplicated
  let allNames : Array String := Id.run do
    let mut arr : Array String := #[]
    for (n, _) in titles ++ offsets ++ sTerms ++ tTerms ++ uTerms do
      unless arr.contains n do arr := arr.push n
    arr.qsort (· < ·)
  allNames.filterMap fun anum =>
    let title := (titles.find? (·.1 == anum)).map Prod.snd |>.getD ""
    let offStr := (offsets.find? (·.1 == anum)).map Prod.snd |>.getD "0"
    let offset := ((offStr.splitOn ",").head? |>.bind String.toInt?).getD 0
    let st := (sTerms.find? (·.1 == anum)).map Prod.snd |>.getD ""
    let tt := (tTerms.find? (·.1 == anum)).map Prod.snd |>.getD ""
    let ut := (uTerms.find? (·.1 == anum)).map Prod.snd |>.getD ""
    let raw := st ++ "," ++ tt ++ "," ++ ut
    let terms := (raw.splitOn ",").filterMap fun s =>
      let t := s.trimAscii.toString
      if t.isEmpty then none else some t
    some { name := anum, title := title, offset := offset, terms := terms }

/-- Collect .seq file paths under `seqDir`. -/
partial def collectSeqFiles (seqDir : System.FilePath)
    (buckets : Array String) (seqs : Array String) : IO (Array System.FilePath) := do
  unless ← seqDir.pathExists do return #[]
  let mut files := #[]
  for bucketDir in (← seqDir.readDir).qsort (·.fileName < ·.fileName) do
    unless ← bucketDir.path.isDir do continue
    unless buckets.isEmpty || buckets.contains bucketDir.fileName do continue
    for f in (← bucketDir.path.readDir).qsort (·.fileName < ·.fileName) do
      if f.path.extension != some "seq" then continue
      -- Strip ".seq" from the filename to get the A-number stem
      let fname := f.fileName
      let stem := if fname.endsWith ".seq" then (fname.drop (fname.length - 4)).toString else fname
      unless seqs.isEmpty || seqs.contains (stem.toUpper) do continue
      files := files.push f.path
  return files

/-- Enrich formula metadata from parsed .seq metadata. -/
private def enrichFromMeta (f : Formula) (metas : Array SeqMeta) : Formula :=
  match metas.find? (·.name == f.oeisName) with
  | some m => { f with title := m.title, offset := m.offset, terms := m.terms }
  | none => f

/-- Scan all matching .seq files and return parsed LinearRecurrence formulas. -/
partial def scanFromSeqFiles (cfg : Config) : IO (Array Formula) := do
  let files ← collectSeqFiles cfg.seqDir cfg.buckets cfg.seqs
  IO.eprintln s!"Scanning {files.size} .seq files under {cfg.seqDir} ..."
  let mut all := #[]
  for path in files do
    let contents ← IO.FS.readFile path
    let metas := parseSeqMeta contents
    let blocks := parseSeqFile contents
    for (anum, blockText) in blocks do
      let formulas ← parseBlock anum blockText
      for f in formulas do
        all := all.push (enrichFromMeta f metas)
  return all

/-- Splits the JSON array text stored in the DB back into its elements. -/
private def parseJsonArray (s : String) : Array String := Id.run do
  let body := (s.trimAscii.toString.dropPrefix "[").toString.dropSuffix "]" |>.toString
  let mut out := #[]
  for piece in body.splitOn "," do
    let t := piece.trimAscii.toString
    let t := if t.startsWith "\"" && t.endsWith "\""
             then (t.drop 1).toString.dropEnd 1 |>.toString
             else t
    if !t.isEmpty then out := out.push t
  return out

/-- Query the `program` table for Mathematica blocks containing LinearRecurrence. -/
def scanFromDb (db : SQLite) (cfg : Config) : IO (Array Formula) := do
  let mut conds := #["p.language = ?1", "p.text LIKE '%LinearRecurrence%'"]
  let mut params : Array (Nat × String) := #[(1, "mathematica")]
  let mut paramIdx : Nat := 2
  unless cfg.seqs.isEmpty do
    let seqConds := String.intercalate " OR "
      (cfg.seqs.toList.map fun _ => "p.oeis_name = ?" ++ toString paramIdx)
    conds := conds.push ("(" ++ seqConds ++ ")")
    for s in cfg.seqs do
      params := params.push (paramIdx, s.toUpper)
      paramIdx := paramIdx + 1
  unless cfg.buckets.isEmpty do
    let buckConds := String.intercalate " OR "
      (cfg.buckets.toList.map fun _ => "substr(p.oeis_name,1,4) = ?" ++ toString paramIdx)
    conds := conds.push ("(" ++ buckConds ++ ")")
    for b in cfg.buckets do
      params := params.push (paramIdx, b)
      paramIdx := paramIdx + 1
  let sql :=
    "SELECT p.oeis_name, p.text, p.hash, s.title, s.\"offset\", s.data " ++
    "FROM program p JOIN sequence s ON s.name = p.oeis_name WHERE " ++
    String.intercalate " AND " conds.toList
  let stmt ← db.prepare sql
  for (idx, val) in params do
    stmt.bindText (Int32.ofNat idx) val
  let mut all := #[]
  while ← stmt.step do
    let anum ← stmt.columnText 0
    let text ← stmt.columnText 1
    let hash ← stmt.columnText 2
    let title ← stmt.columnText 3
    let offset : Int := (← stmt.columnInt64 4).toInt
    let dataStr ← stmt.columnText 5
    let terms := parseJsonArray dataStr
    let formulas ← parseBlock anum text
    for f in formulas do
      let srcHash := if hash.isEmpty then f.sourceHash else hash
      all := all.push { f with title := title, offset := offset,
                               terms := terms, sourceHash := srcHash }
  return all

-- ---------------------------------------------------------------------------
-- Lean code generation
-- ---------------------------------------------------------------------------

private def bucketOf (name : String) : String := (name.take 4).toString

private def argTypeStr (offset : Int) : String :=
  if offset == 0 then "Nat"
  else if offset == 1 then "PNat"
  else if offset > 1 then
    "{n : Nat // " ++ toString offset ++ " ≤ n}"
  else
    "{n : Int // " ++ toString offset ++ " ≤ n}"

private def formulaBody (offset : Int) : String :=
  if offset == 0 then "  fun n => linearrec.mkSol init n"
  else if offset == 1 then "  fun n => linearrec.mkSol init (n.val - 1)"
  else if offset > 1 then
    "  fun n => linearrec.mkSol init (n.val - " ++ toString offset ++ ")"
  else
    "  fun n => linearrec.mkSol init ((n.val - (" ++ toString offset ++ " : Int)).toNat)"

/-- The formula always returns Int; coerce the main def in the theorem. -/
private def formulaEqRhs (name : String) : String :=
  "(" ++ name ++ " n : Int)"

/-- Pair each element with its index starting at `startIdx`. -/
private def withIndexFrom {α : Type} (xs : List α) (startIdx : Nat) : List (Nat × α) :=
  (List.range' startIdx xs.length).zip xs

/-- Generate `| i => v` match arms for `Fin n → Int`. -/
private def finMatchArms (values : Array Int) (startIdx : Nat := 1) : String :=
  let arms := (withIndexFrom values.toList startIdx).map
    fun (i, v) => "    | " ++ toString i ++ " => " ++ toString v
  String.intercalate "\n" arms

private def sanitizeDoc (s : String) : String :=
  s.replace "-/" "- /" |>.replace "/-" "/ -"

private def templatePath : System.FilePath :=
  "Scripts" / "Templates" / "LinearRecurrenceWolfram.lean"

/-- Render the Equiv_<hash>.lean file for one formula. -/
def renderEquiv (f : Formula) (template : String) : String := Id.run do
  let order := f.coeffs.size
  let coeffRest := (f.coeffs.toList.drop 1).toArray
  let initRest := (f.init.toList.drop 1).toArray
  let coeffArms :=
    if order ≤ 1 then "    | _ => unreachable!"
    else finMatchArms coeffRest ++ "\n    | _ => unreachable!"
  let initArms :=
    if order ≤ 1 then "    | _ => unreachable!"
    else finMatchArms initRest ++ "\n    | _ => unreachable!"
  let sourceLines := String.intercalate "\n"
    (f.originalText.splitOn "\n" |>.map ("    " ++ sanitizeDoc ·))
  let replacements : List (String × String) := [
    ("__BUCKET__", bucketOf f.oeisName),
    ("__SEQNAME__", f.oeisName),
    ("__HASH__", f.formulaHash),
    ("__TITLE__", sanitizeDoc f.title),
    ("__ORDER__", toString order),
    ("__COEFF_0__", toString f.coeffs[0]!),
    ("__COEFF_MATCHES__", coeffArms),
    ("__INIT_0__", toString f.init[0]!),
    ("__INIT_MATCHES__", initArms),
    ("__ARG_TYPE__", argTypeStr f.offset),
    ("__FORMULA_BODY__", formulaBody f.offset),
    ("__FORMULA_EQ_RHS__", formulaEqRhs f.oeisName),
    ("__SOURCE__", sourceLines)
  ]
  replacements.foldl (fun acc (k, v) => acc.replace k v) template

/-- Literal expression for OEIS index `index`, given the sequence offset. -/
private def indexLiteral (offset : Int) (index : Int) : String :=
  if offset == 0 then "(" ++ toString index ++ " : Nat)"
  else if offset == 1 then "(" ++ toString index ++ " : PNat)"
  else if offset > 1 then
    "(⟨" ++ toString index ++ ", by norm_num⟩ : {n : Nat // "
      ++ toString offset ++ " ≤ n})"
  else
    "(⟨" ++ toString index ++ ", by norm_num⟩ : {n : Int // "
      ++ toString offset ++ " ≤ n})"

/-- Render the temporary Check module that `#eval`s `formula` against OEIS data. -/
def renderCheck (f : Formula) (batchId : Nat) (maxTerms : Nat) : String := Id.run do
  let bkt := bucketOf f.oeisName
  let ns := "Check.LinearRecurrence.B" ++ toString batchId ++ "."
           ++ f.oeisName ++ "_" ++ f.formulaHash
  let equivMod := "LOEIS." ++ bkt ++ "." ++ f.oeisName
                   ++ ".Equiv_" ++ f.formulaHash
  let count := min maxTerms f.terms.size
  let terms := f.terms.take count
  let args := (List.range count).map fun i =>
    indexLiteral f.offset (f.offset + (i : Int))
  let expected := String.intercalate ", "
    (terms.toList.map fun t =>
      if t.startsWith "-" then "(" ++ t ++ ")" else t)
  let actual := String.intercalate ",\n   "
    (args.map fun a => "((formula " ++ a ++ " : Int))")
  String.intercalate "\n" [
    "import Check.Basic",
    "import " ++ equivMod,
    "",
    "/-! Generated validation module; deleted once the batch is recorded. -/",
    "",
    "open " ++ f.oeisName ++ ".Equiv_" ++ f.formulaHash,
    "",
    "namespace " ++ ns,
    "",
    "#eval Oeis.Check.report \"" ++ f.oeisName ++ "\" (" ++ toString f.offset ++ ")",
    "  [" ++ expected ++ "]",
    "  [" ++ actual ++ "]",
    "",
    "end " ++ ns,
    ""
  ]

-- ---------------------------------------------------------------------------
-- lake build
-- ---------------------------------------------------------------------------

/-- Run `lake build <targets>` and return (success, full_output). -/
def lakeBuild (targets : Array String) (timeoutSecs : Nat) : IO (Bool × String) := do
  if targets.isEmpty then return (true, "")
  let pathEnv ← IO.getEnv "PATH"
  let home ← IO.getEnv "HOME"
  let elanPath := (home.getD "") ++ "/.elan/bin"
  let path := elanPath ++ ":" ++ pathEnv.getD ""
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["build"] ++ targets
    env := #[("PATH", path)]
  }
  let output := out.stdout ++ out.stderr
  return (out.exitCode == 0, output)

/-- Result of processing one formula. -/
inductive Result where
  | verified (f : Formula)
  | failed (f : Formula) (kind : String) (diags : String)

/-- Trim leading whitespace from a string. -/
private def ltrim (s : String) : String :=
  let cs := s.toList
  let rec go : List Char → String
    | [] => ""
    | c :: rest => if c.isWhitespace then go rest else String.mk (c :: rest)
  go cs

/-- Extract the file path from a lake error line `error: ./path.lean:line:col: msg`.
Takes everything up to the first `:` followed by a digit. -/
private partial def extractErrorPath (s : String) : String :=
  let cs := s.toList
  let rec go (acc : List Char) (rest : List Char) : String :=
    match rest with
    | [] => String.mk acc.reverse
    | ':' :: c :: _ => if c.isDigit then String.mk acc.reverse
                       else go (':' :: acc) (c :: rest.tail!)
    | c :: rest' => go (c :: acc) rest'
  go [] cs

/-- Parse lake build output and return per-file error diagnostics. -/
partial def collectErrors (output : String) : Std.HashMap String (Array String) :=
  Id.run do
    let mut perFile : Std.HashMap String (Array String) := Std.HashMap.empty
    let lines := output.splitOn "\n"
    let mut i := 0
    while i < lines.length do
      let line := lines[i]!
      let trimmed := ltrim line
      if trimmed.startsWith "error: " then
        let afterErr := (trimmed.drop "error: ".length).toString
        let pathPart := extractErrorPath afterErr
        unless pathPart.isEmpty do
          let existing := perFile.getD pathPart #[]
          perFile := perFile.insert pathPart (existing.push line)
          let mut j := i + 1
          while j < lines.length do
            let cont := lines[j]!
            if cont.isEmpty then break
            if ltrim cont == cont then break
            let existing2 := perFile.getD pathPart #[]
            perFile := perFile.insert pathPart (existing2.push cont)
            j := j + 1
          i := j
          continue
      i := i + 1
    return perFile

/-- Get errors for a file, trying both the full path and the basename. -/
private def errorsForFile (perFile : Std.HashMap String (Array String))
    (paths : Array String) : Array String :=
  let mut out := #[]
  for p in paths do
    let basename := (p.splitOn "/").reverse.headD p
    for key in #[p, "./" ++ p, basename] do
      match perFile[key]? with
      | some errs => out := out ++ errs
      | none => pure ()
  out

-- ---------------------------------------------------------------------------
-- Database persistence (mark STATUS_VERIFIED)
-- ---------------------------------------------------------------------------

/-- Insert a formalization batch row and return its rowid. -/
def createBatch (db : SQLite) (names : Array String) : IO Nat := do
  let stmt ← db.prepare
    "INSERT INTO formalization_batch
       (language, model, status, oeis_names, max_attempts, created_at, updated_at)
     VALUES ('mathematica', 'linearrecurrence-wolfram', 'BATCH_RUNNING', ?1, 1,
             datetime('now'), datetime('now'))"
  stmt.bindText 1 (Oeis.Json.strArray names)
  stmt.exec
  let q ← db.prepare "SELECT last_insert_rowid()"
  let _ ← q.step
  let id ← q.columnInt64 0
  return id.toInt.toNat

/-- Mark a formula as STATUS_VERIFIED. -/
def markVerified (db : SQLite) (batchId : Nat) (f : Formula)
    (leanFile checkFile : String) (verifiedUpto : Nat) (argKind : String) : IO Unit := do
  let notes :=
    if f.author.isEmpty && f.date.isEmpty then ""
    else "author=" ++ f.author ++ "; date=" ++ f.date
  let stmt ← db.prepare
    "INSERT INTO formalization_item
       (batch_id, oeis_name, language, source_hash, formula_hash, original_text,
        computable, arg_kind, lean_file, check_file, depends_on, status,
        verified_upto, attempt, notes, created_at, updated_at)
     VALUES (?1, ?2, 'mathematica', ?3, ?4, ?5, 1, ?6, ?7, ?8, '[]',
             'STATUS_VERIFIED', ?9, 1, ?10, datetime('now'), datetime('now'))
     ON CONFLICT(batch_id, oeis_name, formula_hash)
     DO UPDATE SET status='STATUS_VERIFIED', verified_upto=excluded.verified_upto,
                   lean_file=excluded.lean_file, updated_at=datetime('now')"
  stmt.bindInt64 1 (Int64.ofNat batchId)
  stmt.bindText 2 f.oeisName
  stmt.bindText 3 f.sourceHash
  stmt.bindText 4 f.formulaHash
  stmt.bindText 5 f.originalText
  stmt.bindText 6 argKind
  stmt.bindText 7 leanFile
  stmt.bindText 8 checkFile
  stmt.bindInt64 9 (Int64.ofNat verifiedUpto)
  stmt.bindText 10 notes
  stmt.exec

  let stmt2 ← db.prepare
    "UPDATE formula SET status='STATUS_VERIFIED', formalized_formula=?1
     WHERE oeis_name=?2 AND hash=?3"
  stmt2.bindText 1 f.originalText
  stmt2.bindText 2 f.oeisName
  stmt2.bindText 3 f.formulaHash
  stmt2.exec

/-- Mark a formula as failed. -/
def markFailed (db : SQLite) (batchId : Nat) (f : Formula)
    (leanFile : String) (diags : String) (failureKind : String) : IO Unit := do
  let stmt ← db.prepare
    "INSERT INTO formalization_item
       (batch_id, oeis_name, language, source_hash, formula_hash, original_text,
        computable, lean_file, depends_on, status, failure_kind, compiler_output,
        attempt, created_at, updated_at)
     VALUES (?1, ?2, 'mathematica', ?3, ?4, ?5, 1, ?6, '[]', ?7, ?8, ?9, 1,
             datetime('now'), datetime('now'))
     ON CONFLICT(batch_id, oeis_name, formula_hash)
     DO UPDATE SET status=excluded.status, failure_kind=excluded.failure_kind,
                   compiler_output=excluded.compiler_output, updated_at=datetime('now')"
  stmt.bindInt64 1 (Int64.ofNat batchId)
  stmt.bindText 2 f.oeisName
  stmt.bindText 3 f.sourceHash
  stmt.bindText 4 f.formulaHash
  stmt.bindText 5 f.originalText
  stmt.bindText 6 leanFile
  stmt.bindText 7 failureKind
  stmt.bindText 8 failureKind
  stmt.bindText 9 (diags.take 20000).toString
  stmt.exec

/-- Update the batch status when done. -/
def updateBatchStatus (db : SQLite) (batchId : Nat) (status : String) : IO Unit := do
  let stmt ← db.prepare
    "UPDATE formalization_batch SET status=?1, attempts=1, updated_at=datetime('now') WHERE id=?2"
  stmt.bindText 1 status
  stmt.bindInt64 2 (Int64.ofNat batchId)
  stmt.exec

-- ---------------------------------------------------------------------------
-- ArgKind derived from offset
-- ---------------------------------------------------------------------------

private def argKindForOffset (offset : Int) : String :=
  if offset == 0 then "Nat"
  else if offset == 1 then "PNat"
  else if offset > 1 then "NatSub"
  else "IntSub"

private def defsExists (loeisDir : System.FilePath) (name : String) : IO Bool :=
  (loeisDir / (name.take 4).toString / name / "Defs.lean").pathExists

-- ---------------------------------------------------------------------------
-- Main orchestration
-- ---------------------------------------------------------------------------

/-- Write Equiv + check files, build, and return per-formula results. -/
partial def processFormulas (cfg : Config) (formulas : Array Formula)
    (batchId : Nat) (template : String) : IO (Array Result) := do
  let batchCheckDir := cfg.checkDir / "LinearRecurrence" / ("B" ++ toString batchId)
  IO.FS.createDirAll batchCheckDir

  let mut items : Array (Formula × System.FilePath × System.FilePath) := #[]
  let mut targets : Array String := #[]
  for f in formulas do
    let equivName := "Equiv_" ++ f.formulaHash
    let equivPath := cfg.outDir / (bucketOf f.oeisName) / f.oeisName
                      / (equivName ++ ".lean")
    equivPath.parent.forM IO.FS.createDirAll
    IO.FS.writeFile equivPath (renderEquiv f template)

    let checkPath := batchCheckDir / (f.oeisName ++ "_" ++ f.formulaHash ++ ".lean")
    IO.FS.writeFile checkPath (renderCheck f batchId cfg.terms)

    let target := "Check.LinearRecurrence.B" ++ toString batchId ++ "."
                   ++ f.oeisName ++ "_" ++ f.formulaHash
    items := items.push (f, equivPath, checkPath)
    targets := targets.push target

  IO.eprintln s!"Building {targets.size} check module(s) ..."
  let (ok, output) ← lakeBuild targets cfg.timeout
  let perFile := collectErrors output
  let mismatch := output.contains "OEIS_CHECK_FAIL"

  let mut results : Array Result := #[]
  for (f, ep, _cp) in items do
    let diags := errorsForFile perFile #[ep.toString]
    if !diags.isEmpty || (mismatch && !ok) then
      let kind := if mismatch then "STATUS_EVAL_MISMATCH" else "STATUS_COMPILE_ERROR"
      IO.eprintln s!"FAIL {f.oeisName} Equiv_{f.formulaHash}: {kind}"
      IO.FS.removeFile ep
      let diagText := String.intercalate "\n" diags.toList
      results := results.push (.failed f kind diagText)
    else if !ok then
      IO.eprintln s!"FAIL {f.oeisName} Equiv_{f.formulaHash}: STATUS_COMPILE_ERROR"
      IO.FS.removeFile ep
      results := results.push (.failed f "STATUS_COMPILE_ERROR" output)
    else
      IO.eprintln s!"OK   {f.oeisName} Equiv_{f.formulaHash}"
      results := results.push (.verified f)
  return results

/-- Top-level run: scan, generate, build, persist. -/
partial def run (cfg : Config) : IO UInt32 := do
  let template ← IO.FS.readFile templatePath

  let formulas ←
    if ← cfg.dbPath.pathExists then
      try
        let db ← SQLite.«open» cfg.dbPath (busyTimeoutMs := 5000)
        let fs ← scanFromDb db cfg
        if fs.isEmpty && (← cfg.seqDir.pathExists) then
          IO.eprintln "No DB hits; falling back to .seq file scan ..."
          scanFromSeqFiles cfg
        else pure fs
      catch _ =>
        if ← cfg.seqDir.pathExists then
          IO.eprintln "Database not readable; scanning .seq files ..."
          scanFromSeqFiles cfg
        else
          throw <| IO.userError
            s!"neither {cfg.dbPath} nor {cfg.seqDir} is available"
    else if ← cfg.seqDir.pathExists then
      IO.eprintln "Database not available; scanning .seq files ..."
      scanFromSeqFiles cfg
    else
      throw <| IO.userError s!"neither {cfg.dbPath} nor {cfg.seqDir} is available"

  -- Deduplicate by (oeisName, formulaHash)
  let mut seenKeys : Array (String × String) := #[]
  let mut unique := #[]
  for f in formulas do
    let key := (f.oeisName, f.formulaHash)
    unless seenKeys.contains key do
      seenKeys := seenKeys.push key
      unique := unique.push f
  let formulas := if cfg.limit > 0 then unique.take cfg.limit else unique

  -- Filter to sequences that have Lean skeletons and terms
  let mut eligible := #[]
  let mut skipped := 0
  for f in formulas do
    if f.terms.isEmpty then skipped := skipped + 1
    else if !(← defsExists cfg.outDir f.oeisName) then skipped := skipped + 1
    else eligible := eligible.push f

  IO.eprintln s!"Found {formulas.size} LinearRecurrence call(s); \
    {eligible.size} eligible for formalization, \
    {skipped} skipped (no Defs.lean / no terms)."

  if cfg.dryRun then
    for f in eligible do
      IO.println ""
      IO.println s!"=== {f.oeisName}  Equiv_{f.formulaHash} ==="
      IO.println s!"  offset={f.offset}  order={f.coeffs.size}"
      let coeffs := "[" ++ String.intercalate ", " (f.coeffs.toList.map toString) ++ "]"
      let init := "[" ++ String.intercalate ", " (f.init.toList.map toString) ++ "]"
      IO.println s!"  coeffs={coeffs}"
      IO.println s!"  init={init}"
      unless f.author.isEmpty || f.date.isEmpty do
        IO.println s!"  author={f.author}  date={f.date}"
      IO.println s!"  source: {f.originalText}"
    return 0

  if eligible.isEmpty then
    IO.eprintln "Nothing to formalize."
    return 0

  let db? ← (try
      let db ← Db.openDb cfg.dbPath
      pure (some db)
    catch _ => pure none)
  let batchId ← match db? with
    | some db => createBatch db (eligible.map Formula.oeisName)
    | none => pure 0

  let results ← processFormulas cfg eligible batchId template

  let mut verified := 0
  let mut failed := 0
  for r in results do
    match r with
    | .verified f =>
      verified := verified + 1
      if let some db := db? then
        let equivPath := cfg.outDir / (bucketOf f.oeisName) / f.oeisName
                          / ("Equiv_" ++ f.formulaHash ++ ".lean")
        let checkPath := cfg.checkDir / "LinearRecurrence"
                          / ("B" ++ toString batchId)
                          / (f.oeisName ++ "_" ++ f.formulaHash ++ ".lean")
        let checkedUpto := min cfg.terms f.terms.size
        markVerified db batchId f (equivPath.toString) (checkPath.toString)
          checkedUpto (argKindForOffset f.offset)
    | .failed f kind diags =>
      failed := failed + 1
      if let some db := db? then
        let equivPath := cfg.outDir / (bucketOf f.oeisName) / f.oeisName
                          / ("Equiv_" ++ f.formulaHash ++ ".lean")
        markFailed db batchId f (equivPath.toString) diags kind

  if let some db := db? then
    let status :=
      if failed == 0 then "BATCH_OK"
      else if verified > 0 then "BATCH_PARTIAL"
      else "BATCH_FAILED"
    updateBatchStatus db batchId status

  unless cfg.keepCheckFiles do
    let batchCheckDir := cfg.checkDir / "LinearRecurrence" / ("B" ++ toString batchId)
    IO.FS.removeDirAll batchCheckDir

  IO.eprintln s!"Done. verified={verified} failed={failed} batch_id={batchId}"
  return if failed == 0 then 0 else 1

-- ---------------------------------------------------------------------------
-- CLI
-- ---------------------------------------------------------------------------

private def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--db" :: v :: rest, cfg => parseArgs rest { cfg with dbPath := ⟨v⟩ }
  | "--seq-dir" :: v :: rest, cfg => parseArgs rest { cfg with seqDir := ⟨v⟩ }
  | "--out" :: v :: rest, cfg => parseArgs rest { cfg with outDir := ⟨v⟩ }
  | "--check-dir" :: v :: rest, cfg => parseArgs rest { cfg with checkDir := ⟨v⟩ }
  | "--bucket" :: v :: rest, cfg =>
    parseArgs rest { cfg with buckets := cfg.buckets.push v }
  | "--seq" :: v :: rest, cfg =>
    parseArgs rest { cfg with seqs := cfg.seqs.push (v.toUpper) }
  | "--terms" :: v :: rest, cfg =>
    match v.toNat? with
    | some n => parseArgs rest { cfg with terms := n }
    | none => .error s!"--terms expects a number, got '{v}'"
  | "--timeout" :: v :: rest, cfg =>
    match v.toNat? with
    | some n => parseArgs rest { cfg with timeout := n }
    | none => .error s!"--timeout expects a number, got '{v}'"
  | "--limit" :: v :: rest, cfg =>
    match v.toNat? with
    | some n => parseArgs rest { cfg with limit := n }
    | none => .error s!"--limit expects a number, got '{v}'"
  | "--dry-run" :: rest, cfg => parseArgs rest { cfg with dryRun := true }
  | "--keep-check-files" :: rest, cfg =>
    parseArgs rest { cfg with keepCheckFiles := true }
  | arg :: _, _ => .error s!"unrecognized argument '{arg}'"

end Oeis.LinearRecurrenceWolfram

def main (args : List String) : IO UInt32 := do
  match Oeis.LinearRecurrenceWolfram.parseArgs args {} with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-linearrec [--seq-dir DIR] [--db PATH] \
      [--bucket A000]... [--seq A000001]... [--terms N] [--timeout SECONDS] \
      [--limit N] [--dry-run] [--keep-check-files]"
    return 1
  | .ok cfg => Oeis.LinearRecurrenceWolfram.run cfg
