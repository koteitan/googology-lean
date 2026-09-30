[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/DBMS/ExBuchholz

DBMS → extended Buchholz ψ: one and two rows into the ordinals, and the table cells of one-row DBMS.

## Files

| pair | file | structure | status |
|---|---|---|---|
| DBMS, extended Buchholz's ψ | `OneRow.lean` | `StepHom` | the same for one-row DBMS, whose generators agree with BM4's there, including which matrices are standard |
| DBMS, BMS (pair sequences), extended Buchholz's ψ | `TwoRowBlock.lean`, `TwoRow.lean` | `Eval` | **the translation of two-row DBMS into the ordinals**: a standard form is a list of blocks that start with `(0,0)`, the rest of each block a pair sequence (`dreach2_iff_dform`); the value is `ω^o(M_0) + ω^o(M_1) + ...` (`dbmsL2OrdEval`). Injective, onto the ordinals below `ψ_0(Ω_ω)`, decreasing, equal to the rank, order-preserving (`dbmsL2OrdEval_injective`, `dbmsL2Ord_image`, `rank_dbmsL2_eq`, `ltPS_iff_dOrdL_lt`) |
