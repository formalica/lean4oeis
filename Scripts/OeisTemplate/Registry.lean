import SQLite
import Scripts.OeisIngest.Json

/-!
Shared plumbing for the generic template runner (`lake exe oeis-template`).

A *template* packages everything that is specific to one family of automatically-generated
OEIS sequences: an SQL predicate discovering its candidate sequences, and a `run` function
processing one sequence at a time. The runner (`Scripts/OeisTemplate.lean`) owns all the
common machinery — CLI parsing, selection, `.seq` file loading, reporting — and calls the
template function with the user-supplied arguments.

Requirements on templates are deliberately soft: the only mandatory pieces are `name`,
`selectWhere` and `run`; anything beyond that is a template-private concern.
-/

namespace Oeis.Template

open SQLite

/-- Common configuration plus everything the runner could not interpret itself; the latter
is passed through to the template verbatim. -/
structure Context where
  db : SQLite
  dbPath : System.FilePath
  outDir : System.FilePath
  seqDir : System.FilePath
  /-- Library name of the output tree (`LOEIS`). -/
  libName : String
  /-- Overwrite already-generated files. -/
  force : Bool
  /-- Do everything except writing files and touching the database. -/
  dryRun : Bool
  /-- Unrecognized command-line arguments, for template-private parameters. -/
  extras : List String

/-- One selected sequence, handed to `Template.run`. -/
structure SeqInput where
  name : String
  title : String
  offset : Int
  /-- Known terms (JSON-decoded `sequence.data`). -/
  terms : Array String
  /-- Raw contents of `oeisdata/seq/<bucket>/<name>.seq`. -/
  seqText : String

/-- Result of applying a template to one sequence. -/
inductive Outcome where
  /-- Processed successfully. -/
  | ok (msg : String)
  /-- Nothing was done, deliberately (already present without `--force`, not really a
  member of the family, ...). -/
  | skipped (msg : String)
  /-- Something went wrong; the sequence was NOT marked as formalized. -/
  | failed (msg : String)

/-- A named sequence-family processor. -/
structure Template where
  name : String
  descr : String
  /-- SQL condition over the `sequence` table picking out candidate sequences,
  e.g. `title LIKE '...'`. Used for `--all` / `--bucket`. -/
  selectWhere : String
  run : Context → SeqInput → IO Outcome

/-- Parses the JSON string arrays stored in the database back into elements. -/
def parseStrArray (s : String) : Array String := Id.run do
  let body := (s.trimAscii.toString.dropPrefix "[").toString.dropSuffix "]" |>.toString
  let mut out := #[]
  for piece in body.splitOn "," do
    let t := piece.trimAscii.toString
    let t := if t.startsWith "\"" && t.endsWith "\"" then
      (t.drop 1).toString.dropEnd 1 |>.toString else t
    if !t.isEmpty then out := out.push t
  return out

/-- Inserts/updates the `formula` row of a formalized formula or program snippet and
merges its hash into `sequence.formalized_formula_hashes`. `sourceTag` is `'F'` for `%F`
lines, `'T'` for the `%t` Wolfram section, `'O'` for `%o`, `'p'` for `%p`. Only call
after the formalization was actually verified against the data. -/
def markFormalized (ctx : Context) (seqName : String) (hash : String)
    (humanText formalized ftype status sourceTag : String)
    (verificationValues : Array String) (lineIndex : Option Int) : IO Unit := do
  unless ctx.dryRun do
    let ins ← ctx.db.prepare "
      INSERT INTO formula (hash, oeis_name, human_written_formula, formalized_formula,
                           type, status, verification_values, disproved_values,
                           additional_conditions, source_tag, line_index)
      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, '[]', '[]', ?8, ?9)
      ON CONFLICT(oeis_name, hash) DO UPDATE SET
        formalized_formula = excluded.formalized_formula,
        type = excluded.type,
        status = excluded.status,
        verification_values = excluded.verification_values;"
    ins.bindText 1 hash
    ins.bindText 2 seqName
    ins.bindText 3 humanText
    ins.bindText 4 formalized
    ins.bindText 5 ftype
    ins.bindText 6 status
    ins.bindText 7 (Json.strArray verificationValues)
    ins.bindText 8 sourceTag
    match lineIndex with
    | none => ins.bindNull 9
    | some v => ins.bindInt64 9 (Int64.ofInt v)
    ins.exec

    let sel ← ctx.db.prepare
      "SELECT formalized_formula_hashes FROM sequence WHERE name = ?1"
    sel.bindText 1 seqName
    let cur ← if ← sel.step then sel.columnText 0 else pure "[]"
    sel.reset
    let mut hashes := parseStrArray cur
    unless hashes.contains hash do
      hashes := hashes.push hash
    let upd ← ctx.db.prepare
      "UPDATE sequence SET formalized_formula_hashes = ?1 WHERE name = ?2"
    upd.bindText 1 (Json.strArray hashes)
    upd.bindText 2 seqName
    upd.exec

end Oeis.Template
