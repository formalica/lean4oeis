import SQLite
import Scripts.OeisTemplate.Registry
import Scripts.Templates.Registry

/-!
Generic template runner: applies named templates to families of OEIS sequences.

    lake exe oeis-template <template> --all
    lake exe oeis-template <template> --bucket A147
    lake exe oeis-template <template> --seq A147999 [--seq ...]

Only two things are mandatory: the template name and the sequences to apply it to.
Everything else has a default; unrecognized `--flags` are passed through to the template
as its private parameters. `--force` lets the template override files that already exist.

Each template's logic lives in its own module under `Scripts/Templates/` as a plain
function (`Oeis.Template.<name>.run`); this executable only does selection, plumbing and
reporting, then dispatches through `Oeis.Template.findTemplate?`.
-/

namespace Oeis.Template.Runner

open SQLite

structure Config where
  tpl : Option String := none
  dbPath : System.FilePath := "Metadata/oeis.db"
  outDir : System.FilePath := "LOEIS"
  seqDir : System.FilePath := "oeisdata/seq"
  seqs : Array String := #[]
  buckets : Array String := #[]
  all : Bool := false
  force : Bool := false
  dryRun : Bool := false
  limit : Option Nat := none
  extras : List String := []

def parseArgs (args : List String) : Except String Config := go args {}
where
  go : List String → Config → Except String Config
    | [], cfg =>
      match cfg.tpl with
      | none => .error "missing template name: `lake exe oeis-template <template> ...`"
      | some _ =>
        if cfg.all || !cfg.seqs.isEmpty || !cfg.buckets.isEmpty then .ok cfg
        else .error "nothing selected: pass --all, --bucket A147 or --seq A147999"
    | "--db" :: v :: rest, cfg => go rest { cfg with dbPath := v }
    | "--out" :: v :: rest, cfg => go rest { cfg with outDir := v }
    | "--seq-dir" :: v :: rest, cfg => go rest { cfg with seqDir := v }
    | "--seq" :: v :: rest, cfg => go rest { cfg with seqs := cfg.seqs.push v }
    | "--bucket" :: v :: rest, cfg => go rest { cfg with buckets := cfg.buckets.push v }
    | "--all" :: rest, cfg => go rest { cfg with all := true }
    | "--force" :: rest, cfg => go rest { cfg with force := true }
    | "--dry-run" :: rest, cfg => go rest { cfg with dryRun := true }
    | "--limit" :: v :: rest, cfg =>
        match v.toNat? with
        | some n => go rest { cfg with limit := some n }
        | none => .error s!"--limit expects a number, got '{v}'"
    | arg :: rest, cfg =>
        if arg.startsWith "-" then
          -- not a runner flag: hand it to the template (soft contract on templates)
          go rest { cfg with extras := cfg.extras ++ [arg] }
        else
          match cfg.tpl with
          | none => go rest { cfg with tpl := some arg }
          | some _ => .error s!"unexpected positional argument '{arg}' \
              (only one template at a time)"

private def rowToInput (stmt : Stmt) : IO SeqInput := do
  let name ← stmt.columnText 0
  let title ← stmt.columnText 1
  let offset := (← stmt.columnInt64 2).toInt
  let terms := parseStrArray (← stmt.columnText 3)
  return { name, title, offset, terms, seqText := "" }

private def drain (stmt : Stmt) : IO (Array SeqInput) := do
  let mut out := #[]
  while ← stmt.step do
    out := out.push (← rowToInput stmt)
  return out

/-- Fetches candidate rows for `--all` / `--bucket` using the template's discovery SQL. -/
private def fetchDiscovered (db : SQLite) (tpl : Template) (cfg : Config) :
    IO (Array SeqInput) := do
  let cond :=
    "(" ++ tpl.selectWhere ++ ")" ++
    if cfg.buckets.isEmpty then "" else
      " AND (" ++ String.intercalate " OR "
        (cfg.buckets.toList.map fun b => s!"name LIKE '{b}%'") ++ ")"
  let stmt ← db.prepare
    ("SELECT name, title, \"offset\", data FROM sequence WHERE " ++ cond ++ " ORDER BY name")
  drain stmt

private def fetchExplicit (db : SQLite) (name : String) : IO (Option SeqInput) := do
  let stmt ← db.prepare
    "SELECT name, title, \"offset\", data FROM sequence WHERE name = ?1"
  stmt.bindText 1 name
  if ← stmt.step then
    some <$> rowToInput stmt
  else
    return none

private def dedupByName (inputs : Array SeqInput) : Array SeqInput := Id.run do
  let mut seen : Array String := #[]
  let mut out : Array SeqInput := #[]
  for inp in inputs do
    unless seen.contains inp.name do
      seen := seen.push inp.name
      out := out.push inp
  return out

def run (cfg : Config) : IO UInt32 := do
  let tplName := cfg.tpl.getD ""
  let tpl ←
    match findTemplate? tplName with
    | some t => pure t
    | none =>
      IO.eprintln s!"error: unknown template '{tplName}'"
      IO.eprintln "available templates:"
      for t in templates do
        IO.eprintln s!"  {t.name}  — {t.descr}"
      return 1
  unless ← cfg.dbPath.pathExists do
    IO.eprintln s!"error: database not found: {cfg.dbPath} \
      (run `lake exe oeis-ingest` first)"
    return 1
  let db ← SQLite.«open» cfg.dbPath (busyTimeoutMs := 5000)
  db.exec "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;"
  -- gather inputs
  let mut inputs := #[]
  if cfg.all || !cfg.buckets.isEmpty then
    inputs := inputs ++ (← fetchDiscovered db tpl cfg)
  for name in cfg.seqs do
    match ← fetchExplicit db name with
    | none => IO.eprintln s!"warning: no such sequence in the database: {name}"
    | some inp => inputs := inputs.push inp
  let allInputs := dedupByName inputs
  let limited :=
    match cfg.limit with
    | some n => allInputs.take n
    | none => allInputs
  IO.println s!"Template '{tpl.name}': {limited.size} of {allInputs.size} selected \
    sequence(s){if cfg.dryRun then ", DRY RUN" else ""}"
  unless cfg.dryRun do
    db.exec "BEGIN;"
  let ctx : Context := {
    db, force := cfg.force, dryRun := cfg.dryRun, extras := cfg.extras,
    dbPath := cfg.dbPath, outDir := cfg.outDir, seqDir := cfg.seqDir,
    libName := cfg.outDir.fileName.getD "LOEIS" }
  let mut nOk := 0
  let mut nSkip := 0
  let mut nFail := 0
  for inp in limited do
    -- load the raw seq file for the %t section
    let bucket := (inp.name.take 4).toString
    let path := cfg.seqDir / bucket / s!"{inp.name}.seq"
    let inp ←
      if ← path.pathExists then do
        let seqText ← IO.FS.readFile path
        pure { inp with seqText }
      else
        pure inp
    let outcome ← try
      tpl.run ctx inp
    catch e =>
      pure (Outcome.failed (toString e))
    match outcome with
    | .ok msg => nOk := nOk + 1; IO.println s!"[{inp.name}] ok: {msg}"
    | .skipped msg => nSkip := nSkip + 1; IO.println s!"[{inp.name}] skipped: {msg}"
    | .failed msg =>
      nFail := nFail + 1; IO.eprintln s!"[{inp.name}] FAILED: {msg}"
  unless cfg.dryRun do
    db.exec "COMMIT;"
  IO.println s!"Done. ok={nOk} skipped={nSkip} failed={nFail}"
  return if nFail == 0 then 0 else 1

end Oeis.Template.Runner

def main (args : List String) : IO UInt32 := do
  match Oeis.Template.Runner.parseArgs args with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-template <template> (--all | [--bucket A147]... \
      [--seq A147999]...)"
    IO.eprintln "       [--db PATH] [--out DIR] [--seq-dir PATH] [--force] [--dry-run] \
      [--limit N] [<template-specific --params>]"
    return 1
  | .ok cfg => Oeis.Template.Runner.run cfg
