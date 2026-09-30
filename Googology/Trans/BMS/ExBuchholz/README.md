[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/ExBuchholz

BMS → extended Buchholz ψ: which ordinal a matrix names. One row (below ε₀, ε-numbers, ζ₀, rank = value), and pair sequences (rank = 1 + val, `PSS/`).

- [PSS/](PSS/README.md): two rows (pair sequences).
- The other direction, extended Buchholz ψ → trio sequences, is in [../../ExBuchholz/BMS/](../../ExBuchholz/BMS/README.md).

## Files

| pair | file | structure | status |
|---|---|---|---|
| BMS, extended Buchholz's ψ | `Calibrate.lean` | — | that below `ψ_0(Ω)` is exactly where the subscripts are all `0`, so the reading reaches every standard form there |
| BMS, extended Buchholz's ψ | `Eps0.lean` | — | **that one row names exactly the ordinals below `ε₀`**: `val` is onto there, by Cantor normal form, and `ψ_0(Ω)` is `ε₀`. It carries the same construction up to `ε₁`, where the leading term is `ψ_0(Ω + B)` |
| BMS, extended Buchholz's ψ | `EpsN.lean` | — | **that `val` is onto the ordinals below every `ε_n`, and so below `ε_ω`**, by induction on `n` with the `ε₁` construction as its step: `Ω·n + B` is a term, `ψ_0(Ω·(n+1) + B)` is the leading one, and `ψ_0(ψ_1(1))` is the limit |
| BMS, extended Buchholz's ψ | `Arg.lean`, `EpsBig.lean` | — | **that `val` is onto the ordinals below `ε_{ε₀}`**, a bijection onto them: `Ω·μ` is a term for every `μ < ε₀`, read off Cantor normal form with `ψ_1(e)` for `Ω·ω^e`, and the same leading-term construction runs over it at every level `δ < ε₀` |
| BMS, extended Buchholz's ψ | `Zeta.lean` | — | **that `val` is onto the ordinals below `ζ₀`**, and by exactly one standard form: the argument terms and the values are built by one induction, so an exponent that is itself an ε-number is named at the level its index gives. The general statement, onto `C_0(Λ)`, is `Notation.ExBuchholz.Term.Vals_eq`; these files say which term names which ordinal, which it does not |
| BMS, extended Buchholz's ψ | `RankVal.lean` | — | **that the rank of the system is the value of the term**: the same measure by two definitions. It then computes the rank where no reading exists — the two-row generator, the successors, the block repetitions and the family `(0,0)(1,1)(1,0)ᵏ` |
| BMS, extended Buchholz's ψ | `Prim.lean` | `StepHom` | the primitive sequence system as a `Rewrite`, that it terminates, and its ordinal |
| BMS, extended Buchholz's ψ | `Cofinal.lean` | — | that below `ψ_0(Ω)` a term is the least upper bound of `X[0] < X[1] < ⋯` |
| BMS, extended Buchholz's ψ | `Bms.lean` | `StepHom` | **the ordinal a one-row Bashicu matrix names**, that it is below `ψ_0(Ω)`, and that one row terminates by translation |
| BMS, extended Buchholz's ψ | `Equiv.lean` | `Equiv` | **the primitive sequence system and the standard forms below `ψ_0(Ω)` are one system written two ways** |
| BMS, extended Buchholz's ψ | `Reach.lean` | — | **the standard one-row matrices are exactly the matrices whose term is standard** |
| BMS, extended Buchholz's ψ | `Commute.lean` | `StepHom`, eventually | that the reading turns expansion into `[ ]`, up to the reindexing `N ↦ N + 1` |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expand.lean`, `PSS/Terms.lean`, `PSS/Rank.lean` | — | **the translation of pair sequences into the ordinals**, through the `Trans` of koteitan/pss-proof: its expansion is `expand2L` (`oper_succ_eq_expand2L_of_ctps`), its Buchholz terms map onto the standard extended Buchholz terms below `ψ_0(Ω_ω)` (`toTerm_bijOn_TransRange`), and the rank of a pair sequence is `1 + val` of its term (`rank_pairL_eq`), with range the ordinals below `ψ_0(Ω_ω)` (`range_pairOrd`). See [PSS/README.md](../PoR/PSS/README.md) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Expansion.lean` | — | **pair sequences → extended Buchholz's ψ does not preserve expansion**: the generator `(0,0)(1,1)` with `[0]` is `(0,0)`, and no term of the fundamental sequence of `ψ_0(Ω_1)` is `1` (`pairOrdTerm_step_ne_fs`) |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/Steps.lean`, `../../../Goals/PairReach.lean` | — | **one step goes to one or more steps on the ψ side**: "reached in one or more steps" is preserved and reflected by the map (`pairToExbOT_transGen_iff`, `pairToExb_transGen_iff`). `(0,0)(1,1)[0]` goes to `ψ_0(Ω_1) →[0] ω →[1] 1` |
| BMS (pair sequences), extended Buchholz's ψ | `PSS/StepBound.lean`, `../../../Goals/PairStepBound.lean` | — | **the number of ψ steps has no bound** (`pairToExb_steps_unbounded`): `(0,0)...(p,p)(p+1,p)[0]` goes from `ψ_0(ψ_p(ψ_p(0)))` to `ψ_0(ψ_p(0))` in exactly `p+1` steps (`pairToExb_min_steps`). For every index, one fundamental-sequence step lowers the subscript at the end of the rightmost path, `lastSub`, by exactly 1 (`lastSub_fs_idx`) |
| BMS, extended Buchholz's ψ | `Tables.lean`, `../../DBMS/ExBuchholz/Tables.lean` | `StepHom` | the smaller cells of the README tables: the order of primitive sequences is the order of their values, the translations of one row preserve the rank, and the primitive sequences embed injectively into the pair sequences |
| BMS, extended Buchholz's ψ | `Basic.lean` | `Sim`, eventually | the reading `read` for one row, that its terms are standard exactly when they descend, and that it is a bijection onto them |
