[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/DBMS/ExBuchholz

DBMS → 拡張ブーフホルツ ψ。1 行と 2 行の順序数、1 行 DBMS の表のセル。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| DBMS、拡張ブーフホルツ ψ | `OneRow.lean` | `StepHom` | 1 行の DBMS についての同じこと。1 行では生成元が BM4 と一致する。どの行列が標準形かも含む |
| DBMS、BMS（ペア数列）、拡張ブーフホルツ ψ | `TwoRowBlock.lean`、`TwoRow.lean` | `Eval` | **2 行の DBMS の順序数への翻訳写像**。標準形は `(0,0)` で始まるブロックの並びで、各ブロックの残りはペア数列（`dreach2_iff_dform`）。値は `w^o(M_0) + w^o(M_1) + ...`（`dbmsL2OrdEval`）。単射、`p0(W_w)` 未満への全射、展開で下がる、階数と一致、順序を保つ（`dbmsL2OrdEval_injective`、`dbmsL2Ord_image`、`rank_dbmsL2_eq`、`ltPS_iff_dOrdL_lt`） |
