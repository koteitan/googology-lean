[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/DBMS/DBMS

DBMS → DBMS: `r + 1` rows inside `r + 2` rows.

## Files

| pair | file | structure | status |
|---|---|---|---|
| DBMS with itself | `ZeroRow.lean` | `StepHom`, `Sim` | **DBMS with `r` rows sits inside `r + 1` rows**: adding a row of zeros underneath lands in the standard forms, commutes with expansion without renumbering the brackets, is injective and keeps the rank (`dbmsL_homSucc`, `rank_dbmsL_homSucc`); it is not surjective (`dbmsToSucc_not_surjective`) |
