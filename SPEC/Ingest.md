# Ingest — `lake exe oeis-ingest`

Walks the OEIS internal-format files under `oeisdata/seq/<bucket>/<name>.seq`
and populates `Metadata/oeis.db` (schema in [Database.md](Database.md)).

Code: `Scripts/OeisIngest.lean` (CLI, directory walk, transaction batching),
`Parse.lean` (record parser, `Entry`, `formulaHash`), `Db.lean` (DDL,
prepared upserts), `Json.lean` (minimal JSON array/hex emitter).

CLI:

```
lake exe oeis-ingest [--seq-dir DIR] [--db PATH] [--limit N]
```

Defaults: `--seq-dir oeisdata/seq`, `--db Metadata/oeis.db`.

Record format: every line is `%<tag> <A-number> <content>`. Tags used:

- `%S` / `%T` / `%U` — terms, wrapped over lines; the three parts are
  concatenated and split on commas (empty tokens dropped), preserving order.
- `%N` — title (first occurrence wins).
- `%O` — `offset,offset_first_big`.
- `%K` — comma-separated keywords.
- `%F` — one formula per line; each non-empty line becomes a `formula` row,
  hashed with `formulaHash` over the line content (tag and A-number
  stripped, trimmed).

All other tags are ignored by ingest.

One parsed file yields one `Entry` (name, title, offset, offsetFirstBig,
keywords, terms, formulas, sourceFile) and upserts one `sequence` row plus
one `formula` row per `%F` line. Writes are batched in transactions.
Ingest never sets formalization columns (see refresh semantics in
[Database.md](Database.md)).
