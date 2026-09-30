[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/common

Facts about BMS alone that two or more translations use: expansion written on the entries at every number of rows, zero rows, cutting and appending, and the cofinality of three-row expansion (`TrioCof/`).

## Files

| pair | file | structure | status |
|---|---|---|---|
| BMS with itself | `OneRow.lean` | — | that one-row expansion is the primitive sequence rule: keep the first `p` entries, repeat the next `s` of them `N + 1` times |
| BMS with itself | `Rows.lean` | — | that naming a parent pins the bad root down, whatever the number of rows |
| BMS with itself | `Entries.lean` | — | that an array and its entries expand the same way |
| BMS with itself | `TwoRow.lean` | — | two-row expansion: `m₀` is `0` or `1`, and at `1` row `0` takes an increment |
| BMS with itself | `Anc.lean` | — | the row-`0` ancestor relation read off the entries, computed and proved to match `BM4.anc` |
| BMS with itself | `EntriesR.lean` | — | **every Bashicu matrix expansion, written on the entries and shown to be `BM4.expand`** — so it runs, at any number of rows |
| BMS with itself | `AllL.lean` | `Sim` | the rule on **every** matrix, standard or not, as a system that runs, with the standard ones inside it |
| BMS with itself | `Zero.lean` | — | that a row of zeros underneath changes nothing: the two-row rule on it is the one-row rule |
| BMS with itself | `Embed.lean` | `StepHom` | **the primitive sequence system sits inside the pair sequence system** |
| BMS with itself | `ZeroRow.lean` | `StepHom`, `Sim` | **the same at every number of rows**: `r + 1` rows sit inside `r + 2`, and inside `s + 1` for any `s ≥ r` |
| BMS with itself | `ZeroRowSurj.lean` | — | BMS `r` rows → `r + 1` rows is not surjective: the generator `(0,0)(1,1)` is not in the image (`bmsToSucc_not_surjective`) |
| BMS with itself | `Append.lean` | — | **that expansion only looks at the last block**: a column whose row-`0` entry is `0` starts one, and no parent reaches back across it |
| BMS with itself | `Entries2.lean` | — | **two-row expansion written on the entries, that it is `BM4.expand`, and that a run of it ends** |
| BMS with itself | `Pair.lean` | — | the pair sequence system as a `Rewrite` whose step runs, with its generators |
| BMS with itself | `Agree.lean` | — | that the one-row, two-row and general rules agree, and the general system as a `Rewrite` with its generators |
| BMS with itself | `Same.lean` | `Equiv` | that the general system at one row **is** the primitive sequence system, and at two rows the pair sequence system |
| BMS with itself | `Cut.lean` | — | that the block recursion `expandL` is the textbook rule: drop the last column, repeat the bad part `N + 1` times |
| BMS at three rows | `TrioCof/`, `TrioCofinal.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **cofinality of trio expansion**: koteitan/trio's `trio_cofinality` and its 16 dependency files, with a proof that its expansion is this library's BMS expansion (`expandRL_toL`). For standard `b < a` there is `k` with `b ≤ a[k]` (`trio_cofinal`, `trioStd_cofinal`) |
