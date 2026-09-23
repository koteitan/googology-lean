[← Back](README.md) | [English](results.md) | [Japanese](results-ja.md)

# The theorems proved

Names are written relative to `Googology`.

## The systems

| | |
|---|---|
| **Bashicu matrices terminate**, for any number of rows | `Notation.BMS.bms_terminates` |
| **expansion ends from any array at all**, standard or not | `Notation.BMS.terminates_any` |
| so the rule on every array is a system, well founded and with a rank | `Notation.BMS.bmsAll`, `Notation.BMS.bmsAll_wf`, `Notation.BMS.bmsAllEval` |
| and the same on the entries, where the step runs | `Trans.BMS.bmsAllL`, `Trans.BMS.bmsAllL_wf`, `Trans.BMS.bmsAllLEval` |
| the primitive, pair and trio sequences terminate | `Notation.BMS.primitive_terminates`, `Notation.BMS.pair_terminates`, `Notation.BMS.trio_terminates` |
| BMS carries an ordinal measure | `Notation.BMS.bmsEval` |
| **every Bashicu matrix expansion, written on the entries, is `BM4.expand`** — so it runs, at any number of rows | `Trans.BMS.entriesR_expand` |
| the one-row, two-row and general rules are one rule | `Trans.BMS.expandRL_one`, `Trans.BMS.expandRL_two` |
| and a row of zeros underneath changes nothing, for one row inside two | `Trans.BMS.expand2L_withZero` |
| **the primitive sequence system sits inside the pair sequence system** | `Trans.BMS.primHomPair`, `Trans.BMS.withZero_std` |
| so does `bmsL 0` inside `bmsL 1`, the first step of the hierarchy | `Trans.BMS.bmsL_zero_sim_one` |
| **and a row of zeros underneath changes nothing at every number of rows** | `Trans.BMS.expandRL_zeroRow` |
| so `r + 1` rows sit inside `r + 2`, standard matrices and all matrices | `Trans.BMS.bmsL_homSucc`, `Trans.BMS.bmsAllL_homSucc` |
| and iterating that, `r ≤ s` puts `r + 1` rows inside `s + 1` | `Trans.BMS.bmsL_simLe`, `Trans.BMS.bmsAllL_simLe` |
| **and the ordinal a matrix names does not change when the zero row is added** | `Trans.BMS.rank_zeroRow`, `StepHom.rank_map` |
| the systems on the entries, with their generators | `Trans.BMS.prim`, `Trans.BMS.pairL`, `Trans.BMS.bmsL` |
| the general system at one and two rows is the primitive and pair sequence system | `Trans.BMS.bmsEquivPrim`, `Trans.BMS.pairEquivBms` |
| from a generator, any expansion sequence ends | `Notation.BMS.bmsStd_terminates`, `Notation.DBMS.dbmsStd_terminates`, `Trans.BMS.bmsLStd_terminates` |
| **well-foundedness and termination are the same condition** | `Rewrite.wf_iff_terminates` |
| so every system here is well founded and expansion has a rank | `Trans.BMS.bmsL_wf`, `Trans.BMS.pairL_wf`, `Trans.BMS.prim_wf`, `Trans.BMS.bmsLRankEval` |
| DBMS is the same rule with other generators, and terminates too | `Notation.DBMS.dbms_terminates`, `Trans.DBMS.dbmsL_terminates` |
| the Y sequence as a system: the official program transcribed, and checked against it on 213 expansions | `Notation.Y.expand`, `Notation.Y.ySys` |
| **the Y sequence is well founded and terminates**, and carries an ordinal measure | `Notation.Y.ySys_wf`, `Notation.Y.ySys_terminates`, `Notation.Y.yStd_terminates`, `Notation.Y.yEval` |
| **and so on every legal sequence** (positive entries, first entry `1`), standard or not, and for `expand` on plain lists | `Notation.Y.yLegal_wf`, `Notation.Y.yLegal_terminates`, `Notation.Y.expand_terminates` |
| on a legal sequence the transcription is Phyrion's expansion, so the standard forms are Phyrion's generated sequences, well ordered by the lexicographic order | `Notation.Y.expand_eq_numeric`, `Notation.Y.yStd_iff_generated`, `Notation.Y.yStd_strictWellOrder` |

## Extended Buchholz's ψ

| | |
|---|---|
| **the standard forms are well ordered** | `Notation.ExBuchholz.Term.OTLt_wf` |
| distinct standard forms name distinct ordinals | `Notation.ExBuchholz.Term.val_inj_of_OT` |
| the notation system is correct: the term order matches the ordinal order | `Notation.ExBuchholz.Term.val_lt_val` |
| **every member of `C_0(Λ)` is the value of a standard form**, so `val` is an order isomorphism from the standard forms onto `C_0(Λ)`, and every ordinal below `ψ_0(Λ)` is named by exactly one standard form | `Notation.ExBuchholz.Term.Vals_eq`, `Notation.ExBuchholz.Term.valEquiv`, `Notation.ExBuchholz.Term.existsUnique_OT_of_lt_psi_Lam` |
| a standard form names a countable ordinal exactly when it names one below `ψ_0(Λ)` | `Notation.ExBuchholz.Term.val_lt_psi_Lam_iff` |
| **the standard forms below a countable standard form `X` are, in order, the ordinals below `val X`**, and the countable ones are the ordinals below `ψ_0(Λ)` — so the order type below `X` is the ordinal `X` names | `Notation.ExBuchholz.Term.belowEquiv`, `Notation.ExBuchholz.Term.countableEquiv` |
| the fundamental sequence descends | `Notation.ExBuchholz.Term.fs_lt` |
| **extended Buchholz terms terminate** | `Notation.ExBuchholz.Term.exbOT_terminates` |
| the fundamental sequence keeps a term standard — Buchholz's Lemma 3.3 | `Notation.ExBuchholz.Term.OTFS_thm` |
| **`ψ_0(a) = ω^a` below `ε₀`**, and `ψ_0(a) ≤ ω^a` always | `Notation.ExBuchholz.Ord.psi_zero_eq_opow`, `Notation.ExBuchholz.Ord.psi_zero_le_opow` |
| **`ψ_0(Ω) = ε₀`** | `Notation.ExBuchholz.Ord.psi_Omega_one` |
| **and `ψ_0(Ω + a) = ε₀·ω^a` below `ε₁`**, so `ψ_0(Ω + 1) = ε₀·ω` | `Notation.ExBuchholz.Ord.psi_Omega_add_eq`, `Notation.ExBuchholz.Ord.psi_Omega_add_one` |
| **and `ψ_0(Ω·2) = ε₁`**, which the term `ψ_0(Ω+Ω)` names | `Notation.ExBuchholz.Ord.psi_Omega_two`, `Trans.BMS.val_te1` |
| **and `ψ_0(Ω·(n+1)) = ε_n` at every finite `n`**, with `ψ_0(Ω·(n+1) + a) = ε_n·ω^a` below `ε_{n+1}` | `Notation.ExBuchholz.Ord.psi_OmegaMul`, `Notation.ExBuchholz.Ord.psi_OmegaMul_add` |
| **and `ψ_0(Ω·ω) = ε_ω`**, with `ψ_1(1) = Ω·ω` | `Notation.ExBuchholz.Ord.psi_Omega_omega`, `Notation.ExBuchholz.Ord.psi_one_one` |
| **and `ψ_0(Ω·(1+γ)) = ε_γ` at every `γ` below `ζ₀`**, with `ψ_0(Ω·(1+γ) + β) = ε_γ·ω^β` below `ε_{γ+1}` | `Notation.ExBuchholz.Ord.psi_Omega_mul_eps`, `Notation.ExBuchholz.Ord.psi_Omega_mul_add_eps` |
| **and `ψ_0(Ω·ζ₀) = ψ_0(Ω²) = ζ₀`** | `Notation.ExBuchholz.Ord.psi_Omega_mul_zeta0`, `Notation.ExBuchholz.Ord.psi_Omega_sq` |
| **and the same ladder at every subscript**: `ψ_v(Ω_{v+1}·(1+γ)) = ε^v_γ` | `Notation.ExBuchholz.Ord.psi_OmegaV_mul_eq`, `Notation.ExBuchholz.Ord.psi_OmegaV_mul_eq_nat` |
| `val` is onto the ordinals below `ζ₀`, by an explicit construction of the terms that came before the general theorem; `ζ₀` itself is `val (ψ_0(ψ_1(ψ_1(0))))` | `Trans.BMS.exists_OT_of_lt_zeta0`, `Trans.BMS.existsUnique_OT_of_lt_zeta0`, `Trans.BMS.val_tzeta0` |
| the map from `ψ_0(Ω_α)` to the three-row matrices, `α < ε₀` — transcribed from [koteitan/trio](https://github.com/koteitan/trio) and calibrated against its table, not a theorem | `Trans.BMS.omegaIndexMatrix` |
| an additively principal member of `C_v(a)` is below `Ω_v` or a collapse; and if `ψ_w(d)` is in `C_v(β)` with `v ≤ w` and `d` in its own closure, then `d` is in `C_v(β)` and below `β` — Buchholz's reading of the closure through `G`, which the normal form theorem rests on | `Notation.ExBuchholz.Ord.principal_mem_CSet`, `Notation.ExBuchholz.Ord.arg_mem_of_psi_mem`, `Notation.ExBuchholz.Term.G_lt_of_mem_CSet` |
| the standard forms reach those: `ψ_0(Ω+1)` names `ε₀·ω` and `ψ_0(Ω+Ω)` names `ε₁` | `Trans.BMS.OT_psi_Omega_add`, `Trans.BMS.val_tew`, `Trans.BMS.OT_te1` |

## One row: which ordinal a matrix names

| | |
|---|---|
| **expansion is the fundamental sequence** | `Trans.BMS.read_expandL` |
| **which ordinal a one-row Bashicu matrix names** | `Trans.BMS.bmsOrdEval` |
| it is below `ψ_0(Ω)` — the ceiling of the primitive sequence system | `Trans.BMS.read_lt_e0`, `Trans.BMS.bmsOrdEval_lt_e0` |
| and every standard form below `ψ_0(Ω)` is named by one | `Trans.BMS.exists_read`, `Trans.BMS.lt_e0_iff_allNil` |
| **and every ordinal below `ε₀` is named by one** — `ψ_0(Ω)` is `ε₀` | `Trans.BMS.exists_matrix_of_lt_eps0`, `Trans.BMS.val_te0` |
| so one row names those ordinals and no others | `Trans.BMS.val_read_lt_eps0` |
| `val` is onto the ordinals below `ε₀` | `Trans.BMS.exists_OT_of_lt_eps0` |
| **and onto the ordinals below `ε₁`** — the standard forms below `ψ_0(Ω+Ω)` name exactly those | `Trans.BMS.exists_OT_of_lt_eps1`, `Trans.BMS.exists_OT_lt_te1` |
| **so below `ε₁` `val` is a bijection**: one standard form per ordinal | `Trans.BMS.existsUnique_OT_lt_te1`, `Trans.BMS.existsUnique_OT_lt_te0` |
| **so the ordinal measure is a bijection onto `ε₀`** | `Trans.BMS.exists_bms_of_lt_eps0`, `Trans.BMS.bmsOrdEval_inj` |
| **the rank of the system is that same ordinal** — the two measures are one | `Trans.BMS.rank_prim_eq_val`, `Trans.BMS.rank_bms_eq_val` |
| **and the system's own ordinal is `ε₀`**: the ranks are cofinal in it and never reach it — on the entries, on the arrays, and for DBMS | `Trans.BMS.iSup_rank_prim`, `Trans.BMS.iSup_rank_bms`, `Trans.DBMS.iSup_rank_dbms` |
| the one-row generators name the towers of `ω`: `(0)` is `1`, `(0)(1)` is `ω` | `Trans.BMS.val_twr_succ`, `Trans.BMS.rank_primGen` |
| and small matrices can be read off: `(0)(1)(1)` is `ω²` and `(0)(1)(2)` is `ω^ω`, which settles two duplicated table entries | `Trans.BMS.val_read_one_one`, `Trans.BMS.val_read_one_two` |
| **the rank is the least ordinal measure** — any evaluation bounds it | `Eval.rank_le` |
| one row of DBMS names the same ordinals, and its rank agrees too | `Trans.DBMS.exists_dbms_of_lt_eps0`, `Trans.DBMS.rank_dbms_eq_val` |
| below `ψ_0(Ω)` a term is the least upper bound of its fundamental sequence | `Trans.BMS.fs_lub` |
| **the standard one-row matrices are exactly the matrices whose term is standard** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| **the primitive sequence system and the standard forms below `ψ_0(Ω)` are equivalent** | `Trans.BMS.primEquivE0` |
| a one-row matrix is determined by the ordinal it names, and is the least upper bound of its own expansions | `Trans.BMS.bmsOrdEval_inj`, `Trans.BMS.expandL_lub` |
| one row terminates, by translation rather than by labels | `Trans.BMS.bms_one_terminates`, `Trans.BMS.prim_terminates` |
| the same for one-row DBMS, whose termination is not otherwise proved here | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |

## Two rows and up: what the rank reaches

No reading of a two-row matrix is available, so the rank of the expansion
relation is the only ordinal these carry. It can still be computed where the
expansions are understood.

| | |
|---|---|
| **the two-row generator `(0,0)(1,1)` has rank `ε₀`** — two rows start where one row ends | `Trans.BMS.rank_pairGen` |
| and at every number of rows the generator is the limit of the previous row's generators | `Trans.BMS.rank_gen_eq_iSup`, `Trans.BMS.rank_gen_lt` |
| `(0,0)` has rank `1`, so a zero column at the end adds one: `(0,0)(1,1)(0,0)` has rank `ε₀ + 1` | `Trans.BMS.rank_zeroCol`, `Trans.BMS.rank_append_zeroCol`, `Trans.BMS.rank_succAll` |
| **expansion never reaches back across a block** — a column whose row-`0` entry is `0` | `Trans.BMS.expandRL_append` |
| **so the rank is additive over blocks**, and `n` copies of a block have `n` times its rank | `Trans.BMS.rank_appendState`, `Trans.BMS.rank_repNState` |
| **with `m₀ = 0` the expansion is a fixed part and a block repeated**, so the rank is multiplied by `ω` | `Trans.BMS.expandRL_of_m0_zero`, `Trans.BMS.rank_mul_omega0` |
| so `(0,0)(1,0)` has rank `ω`, `(0,0)(1,1)(1,0)` has `ε₀·ω`, and `(0,0)(1,1)(0,0)(1,0)` has `ε₀ + ω` | `Trans.BMS.rank_omegaCol`, `Trans.BMS.rank_omegaAll`, `Trans.BMS.rank_sumAll` |
| and it iterates: `(0,0)(1,1)(1,0)(1,0)` has rank `ε₀·ω²` | `Trans.BMS.rank_omegaSqAll` |
| **and every one of those ordinals has a name**: the ranks above are the values of `ψ_0(Ω)`, `ψ_0(1)`, `ψ_0(2)`, `ψ_0(Ω+1)`, `ψ_0(Ω+2)`, `ε₀+1` and `ε₀+ω` | `Trans.BMS.rank_genAll_val` and the five beside it |
| `rank_split_mul_omega0` takes the split directly, so a matrix of this shape costs three lines: `(0,0)(1,0)(1,0)` is `ω²` and `(0,0)(1,1)(0,0)(1,0)(1,0)` is `ε₀ + ω²` | `Trans.BMS.rank_split_mul_omega0`, `Trans.BMS.rank_omegaSqCol`, `Trans.BMS.rank_sumSqAll` |
| **a whole family**: `(0,0)(1,1)(1,0)ᵏ` has rank `ε₀·ω^k` | `Trans.BMS.rank_MkState` |
| **so the two-row system's ordinal is at least `ε₀·ω^ω`** — a crude bound, but one the rank gives with no reading | `Trans.BMS.eps0_mul_opow_omega0_le_iSup` |

What it does not reach: `(0,0)(1,1)(2,1)`, where `m₀` is `1` so the copies
are incremented and differ; `(0,0)(1,1)(2,0)`, which does repeat, but repeats
`(1,1)`, and a part that does not start a block carries no rank of its own;
and the later generators.

No `sorry`, and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
In `Googology.Core` the only declarations that use any axiom are the six that
conclude `Terminates`: `Rewrite.terminates_of_wf`,
`Rewrite.terminates_of_measure`, `Eval.terminates`, `Sim.terminates`,
`Sim.terminates_transfer` and `Equiv.terminates_iff`. They ask for a state
that halts, given only that no chain descends forever, and that step is
classical. Everything else in `Core` — the relation, well-foundedness, the
measures, and all four morphisms — depends on no axiom at all.
