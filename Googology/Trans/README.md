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
| BMS at three rows | `BMS/TrioSheet41.lean`, [TRIO-SHEET-41.md](BMS/TRIO-SHEET-41.md) | [koteitan/trio](https://github.com/koteitan/trio) | the verdicts on the 41 rows where rules 1–10 and the table disagree. None is a transcription error. The rules are right on 17 rows, the table on 22, 1 is open and 1 is out of scope. Calibration by `#guard`, not a theorem |
| BMS at three rows | `BMS/TrioCof/`, `BMS/TrioCofinal.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **cofinality of trio expansion**: koteitan/trio's `trio_cofinality` and its 16 dependency files, with a proof that its expansion is this library's BMS expansion (`expandRL_toL`). For standard `b < a` there is `k` with `b ≤ a[k]` (`trio_cofinal`, `trioStd_cofinal`) |
| BMS at three rows, extended Buchholz's ψ | `BMS/TrioCofPsi.lean` | — | **cofinality of trio expansion, stated with the ψ terms** (`α < ε₀`): the trio matrices lie in the trio fragment (`trioStdL_omegaIndexMatrix`); `ψ_0(Ω_β) < ψ_0(Ω_α)`, or `val` of it, gives `k` with `M(β) ≤ M(α)[k]` (`trioPsi_cofinal`, `trioPsi_cofinal_val`); at a limit `α` (`dom α = ω`), `ψ_0(Ω_α)[n] = ψ_0(Ω_{α[n]})` and the sequences `M(α)[k]` and `M(α[n])` are cofinal in each other, each `M(α)[k]` a prefix of some `M(α[n])` (`trioPsi_fs`, `trioPsi_expand_prefix`). At a successor `α` the members `ψ_0(ψ_α(⋯))` are outside the map's domain |
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
| BMS, extended Buchholz's ψ | `BMS/Commute.lean` | `StepHom`, eventually | that the reading turns expansion into `[ ]`, up to the reindexing `N ↦ N + 1` |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expand.lean`, `PSS/Terms.lean`, `PSS/Rank.lean` | — | **the translation of pair sequences into the ordinals**, through the `Trans` of koteitan/pss-proof: its expansion is `expand2L` (`oper_succ_eq_expand2L_of_ctps`), its Buchholz terms map onto the standard extended Buchholz terms below `ψ_0(Ω_ω)` (`toTerm_bijOn_TransRange`), and the rank of a pair sequence is `1 + val` of its term (`rank_pairL_eq`), with range the ordinals below `ψ_0(Ω_ω)` (`range_pairOrd`). See [PSS/README.md](PSS/README.md) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expansion.lean` | — | **pair sequences → extended Buchholz's ψ does not preserve expansion**: the generator `(0,0)(1,1)` with `[0]` is `(0,0)`, and no term of the fundamental sequence of `ψ_0(Ω_1)` is `1` (`pairOrdTerm_step_ne_fs`) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Steps.lean`, `Goals/PairReach.lean` | — | **one step goes to one or more steps on the ψ side**: "reached in one or more steps" is preserved and reflected by the map (`pairToExbOT_transGen_iff`, `pairToExb_transGen_iff`). `(0,0)(1,1)[0]` goes to `ψ_0(Ω_1) →[0] ω →[1] 1` |
| BMS, extended Buchholz's ψ | `BMS/Tables.lean`, `DBMS/Tables.lean` | `StepHom` | the smaller cells of the README tables: the order of primitive sequences is the order of their values, the translations of one row preserve the rank, and the primitive sequences embed injectively into the pair sequences |
| BMS, extended Buchholz's ψ | `BMS/ExBuchholz.lean` | `Sim`, eventually | the reading `read` for one row, that its terms are standard exactly when they descend, and that it is a bijection onto them |
