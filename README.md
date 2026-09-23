[English](README.md) | [Japanese](README-ja.md)

# googology-lean

A Lean 4 library for googology: expansion systems, ordinal notation systems,
and the translations between them.

The question about a googological system — BMS, DBMS, the Y sequence — is
whether every expansion chain terminates. This library answers it once, for
all of them, and each system supplies only what is its own.

## What it proves

Names are written relative to `Googology`.

### The systems

| notation | expansion defined | termination, well-foundedness | termination from any array | ordinal measure (rank) | contains the system below | ordinal of a state | ordinal of the system |
|---|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| primitive sequences (BMS, 1 row) | ✅ | ✅ | ✅ | ✅ |  | ✅ | ✅ |
| pair sequences (BMS, 2 rows) | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| trio sequences (BMS, 3 rows) | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| BMS (any number of rows) | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| DBMS (1 row) | ✅ | ✅ | ✅ | ✅ |  | ✅ | ✅ |
| DBMS (any number of rows) | ✅ | ✅ | ✅ | ✅ |  |  |  |
| Y sequence (1-Y) | ✅ |  |  |  |  |  |  |
| extended Buchholz's ψ | ✅ | ✅ |  | ✅ |  | ✅ | ✅ |

- expansion defined: the expansion is a Lean function that runs. For BMS it is proved to be `BM4.expand`. For the Y sequence it is a transcription of the official program, checked against its output on 213 cases.
- termination, well-foundedness: every expansion sequence ends. That the two conditions are the same is proved as well.
- contains the system below: with a row of zeros underneath, the system with one row fewer sits inside.
- ordinal of a state: each state is given an ordinal. For primitive sequences and one-row DBMS it equals the rank of the expansion, and these are exactly the ordinals below `ε₀`. For extended Buchholz's ψ it is the value of the standard form, an order isomorphism onto `C_0(Λ)`; that it equals the rank is not proved.
- ordinal of the system: `ε₀` for primitive sequences and one-row DBMS; the countable standard forms of extended Buchholz's ψ have order type `ψ_0(Λ)`.
- The termination of the Y sequence is proved outside this library and only cited (`Googology/Notation/Y/README.md`).

### Extended Buchholz's ψ

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

### One row: which ordinal a matrix names

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

### Two rows and up: what the rank reaches

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

## Using it

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "googology"
git = "https://github.com/koteitan/googology-lean"
```

Then, for instance:

```lean
import Googology

open Googology Notation.BMS

-- Bashicu matrices with five rows terminate.
example : (bms 5).Terminates := bms_terminates 5
```

## The idea

An expansion system packages the state type itself as a field, so systems with
different state types share one proposition:

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

It is a `structure` and not a `class` on purpose: one state type carries
several expansion rules — BMS has BM4, 3.3, 2, 1.1 — and a class keyed on the
state type could hold only one of them.

### Proved once, for every system

| name | statement |
|---|---|
| `Rewrite.terminates_of_wf` | well-foundedness implies termination |
| `Rewrite.wf_of_measure` | a measure into any well-founded order implies well-foundedness |
| `Rewrite.terminates_of_measure` | a measure implies termination |
| `Rewrite.Std.of_terminates` | termination on all states implies it on standard forms |
| `OrdHom.wf` | a strictly monotone map transfers well-foundedness |
| `OrdHom.injective` | trichotomy plus irreflexivity gives injectivity |
| `Sim.wf`, `Sim.terminates` | a simulation transfers well-foundedness and termination |
| `Sim.terminates_transfer` | termination transfers backwards along a simulation |
| `StepHom.toSim` | commuting with expansion yields a simulation |
| `Equiv.wf_iff`, `Equiv.terminates_iff` | mutually inverse translations make both equivalent |
| `Eval.terminates` | an evaluation into a well-founded order gives termination |
| `Eval.compOrd` | an evaluation composed with an order-preserving map is an evaluation |
| `Eval.ofSim` | a simulation pulls an evaluation back to the source |
| `Rewrite.rankEval` | a well-founded system carries an ordinal measure of its own |

The last three are the spine: a translation plus a target evaluation gives
termination of the source, in one line.

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

## Adding a system

Give the three fields of `Rewrite`, and then, to prove termination, a measure:
a map into any type carrying a well-founded relation — `Nat`, an ordinal, a
term system of your own — that strictly decreases on every step. Everything
else is a theorem you inherit.

If your system already has a termination proof elsewhere, joining takes a few
lines; `Notation/BMS` is the worked example.

## What is in here

```
Googology/
  Core/            expansion systems, standard forms, translations
  Rank.lean        every well-founded system carries an ordinal measure
  Notation/        the systems themselves
    BMS/             Bashicu matrices, any number of rows
    ExBuchholz/      extended Buchholz's ψ
    DBMS/            BMS with other generators
    Y/               the Y sequence
  Trans/           translations between two systems
```

Each directory has its own README.

## Build

```sh
lake build
```

Lean 4 v4.30.0. Two dependencies: mathlib, and
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) for
the BMS termination proof. `Googology.Core` imports neither, so the
termination machinery can be read and used without mathlib.

## Sources

Material by others that this library uses, and where. Repositories of
koteitan's are linked where they are used and are not listed here.

| source | what is taken from it | where |
|---|---|---|
| [mathlib](https://github.com/leanprover-community/mathlib4) (Apache-2.0) | ordinals, cardinals and the rest of the library it is built on | a dependency, imported outside `Core` |
| BashicuHyudora, [BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81) | the Bashicu matrix system and its version BM4 | `Notation/BMS/`; the rule is implemented in the dependency koteitan/bms-elem-pattern |
| Maksudov's extended Buchholz ψ, as stated on the [Googology Wiki](https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function) | the definition of `ψ_v(a)` and `C_v(a)` | `Notation/ExBuchholz/Ord.lean` |
| p進大好きbot, [拡張Buchholz OCFに伴う順序数表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E6%8B%A1%E5%BC%B5Buchholz_OCF%E3%81%AB%E4%BC%B4%E3%81%86%E9%A0%86%E5%BA%8F%E6%95%B0%E8%A1%A8%E8%A8%98) | the terms, their order, `G`, `OT`, the evaluation, `dom` and `[ ]`, and the statement that `val` is an isomorphism onto `C_0(Λ)` | `Notation/ExBuchholz/` |
| W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207 | Lemmas 3.2–3.6, on which the fundamental sequences rest | `Notation/ExBuchholz/FS.lean`, `Closure.lean` |
| Yukito's Y sequence, and its official program [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js) of Naruyoko/YNySequence (revision `2de1397`) | the definition, transcribed statement by statement; the expected values of the checks | `Notation/Y/Yukito.lean`, `test/YCheck.lean` |
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) (Apache-2.0) | cited only, for the termination of 1-Y; nothing is copied or adapted | `Notation/Y/README.md` |
| the wiki articles [ペア数列数](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0) and [Y数列](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) | background and correspondence tables | `plan.md` |

The transcription in `Notation/Y/Yukito.lean` is a translation of `script.js`
into Lean. `Naruyoko/YNySequence` has no license file.

## License

MIT. See [LICENSE](LICENSE).

---

## For contributors

* [spec.md](spec.md) — how the library is laid out and how it is written,
  including the rules that govern these documents
* [plan.md](plan.md) — the whole argument and where the work has got to

Current state: `Core/` is complete. `Notation/ExBuchholz` is finished, as a
notation system and as an expansion system: its termination is proved with
nothing assumed. `Notation/BMS` terminates for every number of rows. `Trans/`
settles one row completely — as terms, as ordinals, and as the rank of the
system, which agree — and reaches a few two-row ordinals without a two-row
reading; `plan.md` says what is still missing.
