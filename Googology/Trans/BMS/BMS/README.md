[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/BMS

BMS → BMS: the primitive sequences inside the pair sequences, and `r` rows inside `r + 1` rows (a row of zeros underneath).

## Files

| pair | file | structure | status |
|---|---|---|---|
| BMS with itself | `Embed.lean` | `StepHom` | **the primitive sequence system sits inside the pair sequence system** |
| BMS with itself | `ZeroRow.lean` | `StepHom`, `Sim` | **the same at every number of rows**: `r + 1` rows sit inside `r + 2`, and inside `s + 1` for any `s ≥ r` |
| BMS with itself | `ZeroRowSurj.lean` | — | BMS `r` rows → `r + 1` rows is not surjective: the generator `(0,0)(1,1)` is not in the image (`bmsToSucc_not_surjective`) |
