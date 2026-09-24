[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

Concrete translations. This is the only layer that imports two systems at
once.

## Rule

An unordered pair `{X, Y}` gets **one** file, placed under the alphabetically
earlier name:

```
Trans/BMS/DBMS.lean     everything about BMS and DBMS
Trans/BMS/Y.lean        everything about BMS and Y
```

One file per pair, not one per direction. Both simulations and the `Equiv`, if
there is one, live together; otherwise the `Equiv` has no clear home and the
two directions drift apart. The index below makes a pair findable from either
side.

Every system lives in [Notation](../Notation/README.md), so a translation from
a googological system into a proof-theoretic one is no different from any other
pair: `Trans/BMS/OTB.lean`, under the alphabetically earlier name.

One file per pair is the starting point, not a ceiling. A pair that grows —
`BMS` and extended Buchholz's ψ runs to several files — keeps its directory
and splits by what is being proved, and the index below lists each piece. A
file about one system alone, needed only because a translation uses it, goes
in the same directory and is listed as a pair with itself.

## What to build

Pick the weakest structure that does the job.

| structure | ask for | get |
|---|---|---|
| `Sim` | one step maps to one step | well-foundedness and termination transfer |
| `StepHom` | commutes with expansion, plus halting | becomes a `Sim` |
| `Equiv` | mutually inverse `Sim`s | both sides equivalent |
| `OrdHom` | order-preserving only | well-foundedness transfers |

`StepHom` carries a `reindex : Nat → Nat` for renumbering brackets. Pass `id`
when the numbering is unchanged.

## Calibration is not a theorem

Agreement with a reference implementation is a finite check (`#guard`,
`decide`), not a proof about all inputs. Keep it in its own file and do not
let it be read as one of the theorems above.

## Index

| pair | file | structure | status |
|---|---|---|---|
| BMS with itself | `BMS/OneRow.lean` | — | that one-row expansion is the primitive sequence rule: keep the first `p` entries, repeat the next `s` of them `N + 1` times |
| BMS with itself | `BMS/Rows.lean` | — | that naming a parent pins the bad root down, whatever the number of rows |
| BMS with itself | `BMS/Entries.lean` | — | that an array and its entries expand the same way |
| BMS with itself | `BMS/TwoRow.lean` | — | two-row expansion: `m₀` is `0` or `1`, and at `1` row `0` takes an increment |
| BMS with itself | `BMS/Anc.lean` | — | the row-`0` ancestor relation read off the entries, computed and proved to match `BM4.anc` |
| BMS with itself | `BMS/EntriesR.lean` | — | **every Bashicu matrix expansion, written on the entries and shown to be `BM4.expand`** — so it runs, at any number of rows |
| BMS with itself | `BMS/AllL.lean` | `Sim` | the rule on **every** matrix, standard or not, as a system that runs, with the standard ones inside it |
| BMS with itself | `BMS/Zero.lean` | — | that a row of zeros underneath changes nothing: the two-row rule on it is the one-row rule |
| BMS with itself | `BMS/Embed.lean` | `StepHom` | **the primitive sequence system sits inside the pair sequence system** |
| BMS with itself | `BMS/ZeroRow.lean` | `StepHom`, `Sim` | **the same at every number of rows**: `r + 1` rows sit inside `r + 2`, and inside `s + 1` for any `s ≥ r` |
| BMS with itself | `BMS/ZeroRowSurj.lean` | — | BMS `r` rows → `r + 1` rows is not surjective: the generator `(0,0)(1,1)` is not in the image (`bmsToSucc_not_surjective`) |
| BMS with itself | `BMS/Append.lean` | — | **that expansion only looks at the last block**: a column whose row-`0` entry is `0` starts one, and no parent reaches back across it |
| BMS with itself | `BMS/Entries2.lean` | — | **two-row expansion written on the entries, that it is `BM4.expand`, and that a run of it ends** |
| BMS with itself | `BMS/Pair.lean` | — | the pair sequence system as a `Rewrite` whose step runs, with its generators |
| BMS with itself | `BMS/Agree.lean` | — | that the one-row, two-row and general rules agree, and the general system as a `Rewrite` with its generators |
| BMS with itself | `BMS/Same.lean` | `Equiv` | that the general system at one row **is** the primitive sequence system, and at two rows the pair sequence system |
| BMS with itself | `BMS/Cut.lean` | — | that the block recursion `expandL` is the textbook rule: drop the last column, repeat the bad part `N + 1` times |
| BMS, extended Buchholz's ψ | `BMS/Calibrate.lean` | — | that below `ψ_0(Ω)` is exactly where the subscripts are all `0`, so the reading reaches every standard form there |
| BMS, extended Buchholz's ψ | `BMS/Eps0.lean` | — | **that one row names exactly the ordinals below `ε₀`**: `val` is onto there, by Cantor normal form, and `ψ_0(Ω)` is `ε₀`. It carries the same construction up to `ε₁`, where the leading term is `ψ_0(Ω + B)` |
| BMS, extended Buchholz's ψ | `BMS/EpsN.lean` | — | **that `val` is onto the ordinals below every `ε_n`, and so below `ε_ω`**, by induction on `n` with the `ε₁` construction as its step: `Ω·n + B` is a term, `ψ_0(Ω·(n+1) + B)` is the leading one, and `ψ_0(ψ_1(1))` is the limit |
| BMS, extended Buchholz's ψ | `BMS/Arg.lean`, `BMS/EpsBig.lean` | — | **that `val` is onto the ordinals below `ε_{ε₀}`**, a bijection onto them: `Ω·μ` is a term for every `μ < ε₀`, read off Cantor normal form with `ψ_1(e)` for `Ω·ω^e`, and the same leading-term construction runs over it at every level `δ < ε₀` |
| BMS, extended Buchholz's ψ | `BMS/Zeta.lean` | — | **that `val` is onto the ordinals below `ζ₀`**, and by exactly one standard form: the argument terms and the values are built by one induction, so an exponent that is itself an ε-number is named at the level its index gives. The general statement, onto `C_0(Λ)`, is `Notation.ExBuchholz.Term.Vals_eq`; these files say which term names which ordinal, which it does not |
| BMS at three rows, extended Buchholz's ψ | `BMS/Trio.lean` | [koteitan/trio](https://github.com/koteitan/trio) | the map from `ψ_0(Ω_α)` to the trio matrices, for `α < ε₀`, transcribed from the [algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md) and checked against the [table](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md) — a transcription and `#guard`s, not a theorem |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioStd.lean` | — | **the trio matrices are standard forms** (`α < ε₀`): the trio matrix of `ψ_0(Ω_α)` is the entries of a three-row array reached from a generator by finitely many expansions (`trioMatrix_std`) |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioMono.lean` | — | **the trio map preserves and reflects the order** (`α < ε₀`, lexicographic order of the columns, `omegaIndexMatrix_lt_iff`), so it is injective (`omegaIndexMatrix_injective`) |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioRules.lean`, `BMS/TrioRulesSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | the transcription of rules 1–10 for `ε₀ ≤ α < Λ` (`TrioRules.trioMatrixL`), checked by 875 `#guard`s — a transcription and `#guard`s, not a theorem |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioRulesE0.lean` | — | **the transcription of rules 1–10 agrees with `trioMatrix` below `ε₀`** for standard terms of depth at most 201 (`trioMatrixL_eq_trioMatrix'`). Fuel 200 is not enough for every `α < ε₀`: the tower of depth 203 disagrees (`#guard`) |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioRulesFuel.lean` | — | **rules 1–10 with fuel from the depth of the term agree with `trioMatrix` for every `α < ε₀`** (`trioMatrixD_eq_trioMatrix`); at fuel 200 it is the original `TrioRules.trioMatrixL` (`trioMatrixF_200`) |
| BMS at three rows | `BMS/TrioSheet41.lean`, [TRIO-SHEET-41.md](BMS/TRIO-SHEET-41.md) | [koteitan/trio](https://github.com/koteitan/trio) | the verdicts on the 41 rows where rules 1–10 and the table disagree. None is a transcription error. The rules are right on 17 rows, the table on 22, 1 is open and 1 is out of scope. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioRules2.lean`, `BMS/TrioRules2Sheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | rules 1–10 with four fixes: the table's matrix on the 22 rows where the table is right, the other standard rows unchanged; the 783 chosen matrices are in the order of their labels. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioSheet41Confirm.lean`, [TRIO-SHEET-4746.md](BMS/TRIO-SHEET-4746.md) | [koteitan/trio](https://github.com/koteitan/trio) | rows 4746, 4747, 4752 and 4753: the table is confirmed by order, the copied-block step and the level of the last term. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioRules3.lean`, `BMS/TrioRules3Sheet.lean`, [TRIO-SHEET-FIXES.md](BMS/TRIO-SHEET-FIXES.md) | [koteitan/trio](https://github.com/koteitan/trio) | Fix E: the matrix of the printed label of row 3552 (`u = Ω+1`, level `ω`); the new matrix is standard and in order, and no other row of the table changes. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioRulesNonLast.lean`, `BMS/TrioRulesNonLastSheet.lean`, [TRIO-NONLAST-LEAF.md](BMS/TRIO-NONLAST-LEAF.md) | [koteitan/trio](https://github.com/koteitan/trio) | Fix N: in the tower regimes, a leaf that is not last is upgraded at once; `Ω_{Ω_Ω}+Ω_{Ω_2}+1 < Ω_{Ω_Ω}·2`, and no row of the table changes. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioRulesAll.lean`, `BMS/TrioRulesAllSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | rules 1–10 with Fixes A–E and N merged; every check of the single-fix versions passes, and the 784 chosen matrices are in order. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioFixMulNormalize.lean`, `BMS/TrioFixMulNormalizeSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll`: `mul` and `power` write `ω^atom` as the atom (`mkExp`), and the `==` tests become patterns. Only the printed label of row 4369 changes (now `M(Ω_Ω)`); all sheet checks pass, and on 22 hand-made `ω^atom` labels the order disagreements drop from 62 to 0 ([TRIO-FIX-MUL-NORMALIZE.md](BMS/TRIO-FIX-MUL-NORMALIZE.md)) |
| BMS at three rows | `BMS/TrioFixFuel.lean`, `BMS/TrioFixFuelE0.lean`, `BMS/TrioFixFuelSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll`: the fuel 200 becomes `max 200 (depth of α)`. Nothing changes up to depth 200 (`MD_eq_MAll`); below `ε₀` the map is order-preserving and injective at every depth (`trioMatrixLD_lt_iff`, `trioMatrixLD_injective`); the collision at depths 206/207 is gone ([TRIO-FIX-FUEL.md](BMS/TRIO-FIX-FUEL.md)) |
| BMS at three rows | `BMS/TrioFixLastLeaf.lean`, `BMS/TrioFixLastLeafSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll` (Fix L): a last leaf `Ω_p` with `p` not a top of the tower regime gets a lifted copy of the block (cases L, K, K', D). The six targets after `Ω_{Ω_Ω}` are standard; on 151 last-leaf labels the disagreements go 555 → 0 and the non-standard ones 43 → 0; no sheet row changes ([TRIO-FIX-LASTLEAF.md](BMS/TRIO-FIX-LASTLEAF.md)) |
| BMS at three rows | `BMS/TrioFixStretch.lean`, `BMS/TrioFixStretchSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll` (Fix S): on the stretch from `Ω_ω·Ω+Ω_2` to `Ω_ω·Ω·2`, units laid after a leaf naming `Ω` get the leaf value and lifted copies (S1–S5). Sheet rows 3480, 3481, 3482 change and become standard (3480 → `c2`); on 69 labels of the stretch all are standard (54 were not) with 0 order disagreements ([TRIO-FIX-STRETCH.md](BMS/TRIO-FIX-STRETCH.md)) |
| BMS at three rows | `BMS/TrioFixOfTerm.lean`, `BMS/TrioFixOfTermSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on the term reader: `ψ_a(b_hi + b_lo)` is read as `ω^(P + b_lo)`, so `ψ_0(Ω+1)` becomes `ε₀·ω` (sheet row 2158). On 42 standard terms with sheet labels all matrices are right (the old reading: 25). The order theorem of `TrioTree` fails for the new map (`not_trioMatrixLFix_lt_iff`, because `strip` builds `ω^{ε₀·ω}` wrongly) ([TRIO-FIX-OFTERM.md](BMS/TRIO-FIX-OFTERM.md)) |
| BMS at three rows | `BMS/TrioFixStrip.lean`, `BMS/TrioFixStripTree.lean`, `BMS/TrioFixStripSheet*.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on Fix `ofterm`: rule 1's `strip` builds `ω^{ε₀·ω}` as `ψ_0(Ω+ψ_0(Ω+1))`. The tree map `trioE2` preserves the order, is injective and gives standard forms on terms with subscripts 0 and 1 (`trioE2_lt_iff`, `trioE2_injective`, `trioE2_std`); the rule map agrees with it if `CalibSt` holds (open; 0 differences on 9,782 terms). The sheets are in the separate library `GoogologySheets` ([TRIO-FIX-STRIP.md](BMS/TRIO-FIX-STRIP.md)) |
| BMS at three rows | `BMS/TrioFixStripCalib*.lean` | [koteitan/trio](https://github.com/koteitan/trio) | the rule map of Fix `strip` equals the tree map `trioE2` on terms with subscripts 0 and 1 whose reading depth `rdT` is at most 100 (`trioMatrixLSt_eq_trioE2`), so there it preserves the order, is injective and gives standard forms (`trioMatrixLSt_lt_iff`, `trioMatrixLSt_std`). Without a depth bound it is false: the fuel 200 makes the towers `T_202` and `T_203` get the same matrix (`not_calibSt`, `trioMatrixLSt_not_injective`) |
| BMS at three rows | `BMS/TrioFixU.lean`, `BMS/TrioFixUSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll` (Fix U): rule 9 for `ψ_u(w)` with `u = Ω+k` at level 1 and `w` starting with `ψ` is replaced. On 562 labels in its domain the non-standard matrices go 337 → 0; the claimed domain is too wide (three counterexamples where rule 9 itself fails) ([TRIO-FIX-U.md](BMS/TRIO-FIX-U.md)) |
| BMS at three rows | `BMS/TrioFixU2.lean`, `BMS/TrioFixU2Sheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on Fix U (Fix U2): rule 9 no longer moves an upgrade mark away from its parent column (Fix K), and for levels `L ≥ 2` with `Ω_Ω < w ≤ Ω_{Ω_L}` a new shift row is used. On 2,097 probe labels the rule-9 faults go 41 → 0 and 570 → 22, with no label becoming non-standard ([TRIO-FIX-U2.md](BMS/TRIO-FIX-U2.md)) |
| BMS at three rows | `BMS/TrioFixNonLastOther.lean`, `BMS/TrioFixNonLastOtherSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | patch on `TrioRulesAll`: leaves that are not last, outside the tower regimes (changes 1–3, Fixes G and M). On five families after `Ω_{Ω_ω}`, `Ω_{Ω_{ω+1}}`, `Ω_{Ω_2}`, `Ω_{Ω_Ω}`, `Ω_Ω` the order disagreements drop from thousands to 0–3. Outside those families Fix M, Fix G and change 1 break pairs that were right (e.g. `Ω_{Ω_2}+Ω_ω+Ω` vs `Ω_{Ω_2}+Ω+ω`); see the docstring |
| BMS at three rows | `BMS/TrioRow3480.lean`, [TRIO-ROW-3480.md](BMS/TRIO-ROW-3480.md) | [koteitan/trio](https://github.com/koteitan/trio) | the verdict on row 3480 (`Ω_ω·Ω+Ω_3`): both the table and the rules are wrong; the right matrix `c2` is standard (`trioStdL_c2`) and equals `M(Ω_ω·Ω+Ω_ω)[1]` |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioTree.lean`, `BMS/TrioTreeStd.lean`, `BMS/TrioTreeRules.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **on the countable standard terms whose subscripts are `0` or `1`** (all below `ψ_0(Ω_2)`), the structural map `trioE` gives standard forms (`trioE_std`) and preserves and reflects the order (`trioE_lt_iff`); at depth at most 200 rules 1–10 compute it (`trioMatrixL_eq_trioE`). 200 is tight: two terms at depths 206 and 207 get the same matrix (`#guard`) |
| BMS at three rows | `BMS/TrioCof/`, `BMS/TrioCofinal.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **cofinality of trio expansion**: koteitan/trio's `trio_cofinality` and its 16 dependency files, with a proof that its expansion is this library's BMS expansion (`expandRL_toL`). For standard `b < a` there is `k` with `b ≤ a[k]` (`trio_cofinal`, `trioStd_cofinal`) |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioCofPsi.lean` | — | **cofinality of trio expansion, stated with the ψ terms** (`α < ε₀`): the trio matrices lie in the trio fragment (`trioStdL_omegaIndexMatrix`); `ψ_0(Ω_β) < ψ_0(Ω_α)`, or `val` of it, gives `k` with `M(β) ≤ M(α)[k]` (`trioPsi_cofinal`, `trioPsi_cofinal_val`); at a limit `α` (`dom α = ω`), `ψ_0(Ω_α)[n] = ψ_0(Ω_{α[n]})` and the sequences `M(α)[k]` and `M(α[n])` are cofinal in each other, each `M(α)[k]` a prefix of some `M(α[n])` (`trioPsi_fs`, `trioPsi_expand_prefix`). At a successor `α` the members `ψ_0(ψ_α(⋯))` are outside the map's domain |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioSucc.lean` | — | **cofinality at a successor `α = β + 1`**: `ψ_0(Ω_α)[n] = ψ_0(ψ_β^{n+1}(0))`, and its trio matrix `towerMatrix β n` and `M(α)[k]` are cofinal in each other (`trioPsi_fs_succ`). For `β = 0` and a successor `β`, `towerMatrix` is an expansion of `M(α)` itself |
| BMS, extended Buchholz's ψ | `BMS/RankVal.lean` | — | **that the rank of the system is the value of the term**: the same measure by two definitions. It then computes the rank where no reading exists — the two-row generator, the successors, the block repetitions and the family `(0,0)(1,1)(1,0)ᵏ` |
| BMS, extended Buchholz's ψ | `BMS/Prim.lean` | `StepHom` | the primitive sequence system as a `Rewrite`, that it terminates, and its ordinal |
| BMS, extended Buchholz's ψ | `BMS/Cofinal.lean` | — | that below `ψ_0(Ω)` a term is the least upper bound of `X[0] < X[1] < ⋯` |
| BMS, extended Buchholz's ψ | `BMS/Bms.lean` | `StepHom` | **the ordinal a one-row Bashicu matrix names**, that it is below `ψ_0(Ω)`, and that one row terminates by translation |
| BMS, extended Buchholz's ψ | `BMS/Equiv.lean` | `Equiv` | **the primitive sequence system and the standard forms below `ψ_0(Ω)` are one system written two ways** |
| BMS, extended Buchholz's ψ | `BMS/Reach.lean` | — | **the standard one-row matrices are exactly the matrices whose term is standard** |
| DBMS with itself | `DBMS/Entries.lean` | — | DBMS on the entries at any number of rows, with its generators, and that it terminates |
| DBMS, extended Buchholz's ψ | `DBMS/OneRow.lean` | `StepHom` | the same for one-row DBMS, whose generators agree with BM4's there, including which matrices are standard |
| DBMS, BMS (primitive sequences) | `DBMS/OneRowL.lean` | `StepHom`, `Equiv` | **one-row DBMS on the matrices** (`dbmsL1`): the arrays map onto it by their entries, it is the primitive sequence system, and its ordinal is one to one, onto the ordinals below `ε₀`, equal to the rank and order-preserving |
| DBMS with itself | `DBMS/ZeroRow.lean` | `StepHom`, `Sim` | **DBMS with `r` rows sits inside `r + 1` rows**: adding a row of zeros underneath lands in the standard forms, commutes with expansion without renumbering the brackets, is injective and keeps the rank (`dbmsL_homSucc`, `rank_dbmsL_homSucc`); it is not surjective (`dbmsToSucc_not_surjective`) |
| DBMS, BMS (pair sequences), extended Buchholz's ψ | `DBMS/TwoRowBlock.lean`, `DBMS/TwoRow.lean` | `Eval` | **the translation of two-row DBMS into the ordinals**: a standard form is a list of blocks that start with `(0,0)`, the rest of each block a pair sequence (`dreach2_iff_dform`); the value is `ω^o(M_0) + ω^o(M_1) + ...` (`dbmsL2OrdEval`). Injective, onto the ordinals below `ψ_0(Ω_ω)`, decreasing, equal to the rank, order-preserving (`dbmsL2OrdEval_injective`, `dbmsL2Ord_image`, `rank_dbmsL2_eq`, `ltPS_iff_dOrdL_lt`) |
| DBMS with itself | `DBMS/Blocks.lean`, `DBMS/ThreeRow.lean` | `StepHom`, rank | **for every number of rows, a DBMS standard form is a list of blocks, and its rank is `ω^rank(M_0) + ... + ω^rank(M_k)`** (`rank_dbmsL_eq_sum`), each `M_i` in the content system generated by `(0,0,0)(1,1,0)(2,2,1)...`. At 3 rows, `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` has rank `ψ_0(Ω_ω)` (`rank_gen_three_three`); the later generators are open |
| DBMS, BMS | `DBMS/ContentLift.lean`, `DBMS/ThreeRowLift.lean` | — | **the generators of the content system `C_3` are lifted BMS generators** (`cgen_two_eq_lift`); lifting commutes with expansion (`expandRL_lift`). The 3-row DBMS generator `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` and the BMS `(0,0,0)(1,1,1)` have the same rank (`rank_genL_two_three_eq_bms`). The general case (3-row DBMS and BMS have the same ordinal) is a conjecture |
| DBMS, BMS | `DBMS/ThreeRowLower.lean` | — | **3-row BMS ≤ 3-row DBMS**: the lift never lowers the rank (`rkL_le_rkL_lift`), so `rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n+2))` for every n, and the ordinal of 3-row BMS is at most that of 3-row DBMS (`iSup_rank_bmsL_two_le_dbmsL`). The converse is open for n ≥ 2 |
| DBMS, BMS | `DBMS/ThreeRowUpper.lean`, `DBMS/ThreeRowUpperRefute.lean`, `DBMS/ThreeRowUpperComm.lean` | — | **toward 3-row DBMS ≤ BMS at n = 2**: the map `t3` (column 1 `(1,1,0)` → `(1,1,1)`) goes down lexicographically under expansion (`t3_expand_lt`); if the rank goes down under `t3` in the two non-commuting cases (`T3RankDescNC`, open), then `rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)` (`rkL_cgen_two_four_eq_of_NC`). "`t3 C` is trio-standard" is false (`not_t3Std`) |
| DBMS, BMS | `DBMS/ThreeRowUpperNC*.lean`, `DBMS/ThreeRowUpperRP*.lean`, `DBMS/ThreeRowUpperPushBMS.lean` | — | **n = 2 reduced to one statement about trio sequences**: with the nested raise `t3n`, the non-commuting cases are split by the raisable parent; the case of the column before the last and `RPLastShape` are proved, and `rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)` follows from `T3nPushStd` (open: `t3n C` trio-standard ⇒ `t3n (pushL C y)` trio-standard; 0 failures on about 1.6 million matrices) (`rkL_cgen_two_four_eq_of_push`). `T3nPushStd` is reduced further to `TrioPushStd`, which mentions only trio matrices: for trio-standard `S` whose last column has a row-2 parent `x`, and a row-1 ancestor `y > x` of it, the copy `pushS S y` is trio-standard (0 failures on 48,438 cases; false for `y = x`) (`rkL_cgen_two_four_eq_of_trioPush`) |
| DBMS with itself | `DBMS/BlocksStd.lean` | — | **which lists of blocks are standard** (any number of rows): in a standard form each content is reachable from the earlier ones and the ranks do not increase (`dchain_of_dstdL`, `drank_of_dstdL`); one block is always standard (`dstdL_blkR`); the converse follows from rank injectivity `RkInj` or from duplicating the last block `DupProp` (`dstdL_iff_drank_of_inj`, `dstdL_iff_dchain_of_dup`) |
| DBMS with itself | `DBMS/BlocksSuff.lean` | — | **the characterization of standard lists of blocks** (any number of rows): a list of blocks is standard iff each content is reachable from the earlier ones (`dstdL_iff_dchain`); the last block can always be duplicated (`dupProp`) |
| DBMS with itself | `DBMS/BlocksLex.lean` | — | **reachability and the lexicographic order** (any number of rows): one expansion step makes a list of columns lexicographically smaller (`expandRL_lt_self`), so reaching implies `≤`. Standard ⟺ contents lexicographically non-increasing holds iff `LexReach r` (`lexReach_iff_dstdL_iff_dlex`). |
| DBMS with itself | `DBMS/LexReachThree.lean` | — | **standard ⟺ contents lexicographically non-increasing** (any number of rows, `dstdL_iff_dlex`; 3 rows: `dstdL_three_iff_dlex`). Reaching is total on the contents, because `M[N+1]` reaches `M[N]` and the generators reach each other (`reachTotal`), so `LexReach r` holds for every `r` |
| BMS, extended Buchholz's ψ | `BMS/Commute.lean` | `StepHom`, eventually | that the reading turns expansion into `[ ]`, up to the reindexing `N ↦ N + 1` |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expand.lean`, `PSS/Terms.lean`, `PSS/Rank.lean` | — | **the translation of pair sequences into the ordinals**, through the `Trans` of koteitan/pss-proof: its expansion is `expand2L` (`oper_succ_eq_expand2L_of_ctps`), its Buchholz terms map onto the standard extended Buchholz terms below `ψ_0(Ω_ω)` (`toTerm_bijOn_TransRange`), and the rank of a pair sequence is `1 + val` of its term (`rank_pairL_eq`), with range the ordinals below `ψ_0(Ω_ω)` (`range_pairOrd`). See [PSS/README.md](PSS/README.md) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expansion.lean` | — | **pair sequences → extended Buchholz's ψ does not preserve expansion**: the generator `(0,0)(1,1)` with `[0]` is `(0,0)`, and no term of the fundamental sequence of `ψ_0(Ω_1)` is `1` (`pairOrdTerm_step_ne_fs`) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Steps.lean`, `Goals/PairReach.lean` | — | **one step goes to one or more steps on the ψ side**: "reached in one or more steps" is preserved and reflected by the map (`pairToExbOT_transGen_iff`, `pairToExb_transGen_iff`). `(0,0)(1,1)[0]` goes to `ψ_0(Ω_1) →[0] ω →[1] 1` |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/StepBound.lean`, `Goals/PairStepBound.lean` | — | **the number of ψ steps has no bound** (`pairToExb_steps_unbounded`): `(0,0)...(p,p)(p+1,p)[0]` goes from `ψ_0(ψ_p(ψ_p(0)))` to `ψ_0(ψ_p(0))` in exactly `p+1` steps (`pairToExb_min_steps`). For every index, one fundamental-sequence step lowers the subscript at the end of the rightmost path, `lastSub`, by exactly 1 (`lastSub_fs_idx`) |
| BMS, extended Buchholz's ψ | `BMS/Tables.lean`, `DBMS/Tables.lean` | `StepHom` | the smaller cells of the README tables: the order of primitive sequences is the order of their values, the translations of one row preserve the rank, and the primitive sequences embed injectively into the pair sequences |
| BMS, extended Buchholz's ψ | `BMS/ExBuchholz.lean` | `Sim`, eventually | the reading `read` for one row, that its terms are standard exactly when they descend, and that it is a bijection onto them |
