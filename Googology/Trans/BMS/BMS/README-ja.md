[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/BMS

BMS → BMS。原始数列がペア数列の中に入ること、`r` 行が `r + 1` 行の中に入ること（下に 0 の行を足す）。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| BMS 自身 | `Embed.lean` | `StepHom` | **原始数列系がペア数列系の中に入ること** |
| BMS 自身 | `ZeroRow.lean` | `StepHom`, `Sim` | **それが行数によらず成り立つこと**。`r + 1` 行が `r + 2` 行の中に、`s ≥ r` なら `s + 1` 行の中に入る |
| BMS どうし | `ZeroRowSurj.lean` | — | BMS の `r` 行 → `r + 1` 行は全射でない。生成元 `(0,0)(1,1)` は像に無い（`bmsToSucc_not_surjective`） |
