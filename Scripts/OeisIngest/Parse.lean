import Scripts.OeisIngest.Json

/-!
Parser for the OEIS "internal format" `.seq` files shipped in `oeisdata/seq`.

Every line has the shape `%<tag> <A-number> <content>`. The tags used here:

* `%S`/`%T`/`%U` the terms of the sequence (comma separated, wrapped over lines)
* `%N` name / title of the sequence
* `%O` offset (`<offset>,<index of first term with absolute value > 1>`)
* `%K` keywords
* `%F` formulas
-/

namespace Oeis

private def trimStr (s : String) : String := s.trimAscii.toString
private def trimEndStr (s : String) : String := s.trimAsciiEnd.toString

/-- Everything the ingest step extracts from a single `.seq` file. -/
structure Entry where
  name : String
  title : String
  offset : Int
  /-- Second component of the `%O` line: index of the first term of absolute value > 1. -/
  offsetFirstBig : Option Int
  keywords : Array String
  terms : Array String
  formulas : Array String
  sourceFile : String
  deriving Inhabited

/-- Splits `%<tag> <A-number> <content>` into `("%<tag>", "<A-number>", "<content>")`. -/
def parseRecordLine (line : String) : Option (String × String × String) :=
  match line.splitOn " " with
  | tag :: anum :: rest =>
    if tag.length == 2 && tag.startsWith "%" then
      some (tag, anum, trimStr (String.intercalate " " rest))
    else
      none
  | _ => none

private def splitCommas (s : String) : Array String :=
  (s.splitOn ",").foldl (init := #[]) fun acc t =>
    let t := trimStr t
    if t.isEmpty then acc else acc.push t

/-- Parses the contents of one `.seq` file. Returns `none` if it holds no OEIS records. -/
def parseSeqFile (sourceFile : String) (fallbackName : String) (contents : String) :
    Option Entry := Id.run do
  let mut name := ""
  let mut title := ""
  let mut offsetLine := ""
  let mut keywords : Array String := #[]
  let mut sTerms := ""
  let mut tTerms := ""
  let mut uTerms := ""
  let mut formulas : Array String := #[]
  let mut sawAny := false
  for rawLine in contents.splitOn "\n" do
    match parseRecordLine (trimEndStr rawLine) with
    | none => pure ()
    | some (tag, anum, content) =>
      sawAny := true
      if name.isEmpty then name := anum
      match tag with
      | "%N" => if title.isEmpty then title := content
      | "%O" => if offsetLine.isEmpty then offsetLine := content
      | "%K" => keywords := keywords ++ splitCommas content
      | "%S" => sTerms := sTerms ++ content
      | "%T" => tTerms := tTerms ++ content
      | "%U" => uTerms := uTerms ++ content
      | "%F" => if !content.isEmpty then formulas := formulas.push content
      | _ => pure ()
  if !sawAny then
    return none
  let offsetParts := splitCommas offsetLine
  let offset := (offsetParts[0]?.bind String.toInt?).getD 0
  let offsetFirstBig := offsetParts[1]?.bind String.toInt?
  -- `%S`/`%T` lines usually already end with a comma; joining with one more and
  -- dropping empty tokens handles both conventions.
  let terms := splitCommas (String.intercalate "," [sTerms, tTerms, uTerms])
  return some {
    name := if name.isEmpty then fallbackName else name
    title, offset, offsetFirstBig, keywords, terms, formulas, sourceFile
  }

/-- Stable identifier of a formula: hex encoding of `String.hash` of its text. -/
def formulaHash (text : String) : String :=
  Json.toHex (String.hash text).toNat 16

end Oeis
