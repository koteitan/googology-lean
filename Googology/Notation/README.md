[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Notation

One directory per notation system. A notation system is a type of terms with
an order on them and, usually, fundamental sequences.

Everything lives here: the systems defined by the googology community (BMS,
DBMS, Y) and the systems from the proof-theory literature (Buchholz's `OT_B`,
Rathjen's `T(M)`). They are the same kind of object, so they are not split
apart.

## Rule

**A notation system never imports another notation system.** A directory here
knows only itself and `Googology/Core`. Everything that relates two systems
belongs in [Trans](../Trans/README.md).

This keeps the import graph a DAG. Were a translation to live under `BMS/`,
importing BMS would pull in every system it translates to, and eventually the
whole library.

## Suggested files per system

| file | contents |
|---|---|
| `Basic.lean` | the type of terms or states, and the order on them |
| `Expand.lean` | the expansion rule or fundamental sequences, as one `Rewrite` value per version |
| `Std.lean` | the standard forms and the generators (`Rewrite.Std`) |
| `Eval.lean` | the evaluation into an order, if there is one (`Eval`) |
| `WF.lean` | well-foundedness, when proved here rather than borrowed |

A system with several versions — BMS has BM4, 3.3, 2, 1.1 — defines one
`Rewrite` value per version on the same term type. That is why `Rewrite` is a
structure and not a class.

## Dependencies

`Googology/Core` needs nothing beyond core Lean. mathlib is imported **per
system**, by the systems that evaluate into the ordinals — not by this
directory as a whole. A system that only needs a syntactic order stays
mathlib-free.

## Index

| system | terms | order | standard forms | `Rewrite` | `Eval` |
|---|---|---|---|---|---|
| [ExBuchholz](ExBuchholz/README.md) | done | strict linear order | decidable, not calibrated | `exbOT` | `exbOTEval` |
| [BMS](BMS/README.md) | arrays | comparison in the package | reachable from a stair | `bms r` | `bmsEval` (the rank), and `Trans.BMS.bmsOrdEval` for `r = 1` |
| [DBMS](DBMS/README.md) | arrays | as BMS | reachable from `dstair` | `dbms r` | `Trans.DBMS.dbmsOrdEval` for `r = 1` |
