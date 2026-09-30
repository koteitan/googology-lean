[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/DBMS/DBMS

DBMS → DBMS。`r + 1` 行が `r + 2` 行の中に入ること。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| DBMS どうし | `ZeroRow.lean` | `StepHom`、`Sim` | **DBMS の `r` 行が `r + 1` 行の中に入ること**。下に 0 の行を足す写像は、標準形に入り、括弧の番号を変えずに展開と可換で、単射で、階数を保つ（`dbmsL_homSucc`、`rank_dbmsL_homSucc`）。全射ではない（`dbmsToSucc_not_surjective`） |
