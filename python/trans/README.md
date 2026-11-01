[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# trans

`trans` converts a term of one notation into another, using Python ports of the
translation maps of this Lean library (`Googology/Trans/`).

```
python/trans/trans --from pss --to exb "(0,0)(1,1)(2,2)"     # p0(W_2)
python/trans/trans --from exb --to trio e0                   # (0,0,0)(1,1,0)
python/trans/trans --from prim --to dbms2 --path "0,1,2"     # path on stderr
python/trans/trans --from exb --to trio --wide "p0(W_W)"     # the rule program
python/trans/trans --from ssoss --to exb "(0,0,1,1)"         # p0(w)
python/trans/trans --from bms --to exb "(0)(1,1)"            # e0: N = 2 from the longest column
python/trans/trans --list                                    # the systems
python/trans/trans --maps                                    # the maps
```

Terms can also be given on stdin, one per line. `--lean` prints the Lean value
of the result instead of its ASCII form. `bms` and `dbms` without `N` read `N`
from the term, the length of its longest column; a shorter column is filled
with zeros at the bottom, so `(0)(1,1,1)` is `(0,0,0)(1,1,1)`. The ASCII notations are fixed in
[notations.md](notations.md).

## Maps

The routes are drawn in [trans.md](trans.md).

A conversion follows a path of maps. The paths are tried from the shortest, and
the first path whose maps all accept the input gives the result. Each map
refuses an input outside the domain where Lean proves it.

With `--wide`, two more maps are used: the rule program of the trio sheet,
which Lean checks by `#guard` but does not prove. Among paths of the same
length, a proved one is still tried first, so `trioE2` keeps its domain.

| map | from → to | Lean | accepted inputs |
|---|---|---|---|
| `zeroRow` (`toPairS` for one row) | `bmsN` → `bms(N+1)`, `dbmsN` → `dbms(N+1)` | `Googology/Trans/BMS/BMS/ZeroRow.lean:38`, `Googology/Trans/DBMS/DBMS/ZeroRow.lean:168` | any matrix |
| `l1ToPrim`, `primToL1` | `dbms1` ↔ `bms1` | `Googology/Trans/DBMS/BMS/OneRowL.lean:113`, `:116` | any |
| `read 0` | `bms1` → `exb` | `Googology/Trans/BMS/ExBuchholz/Basic.lean:49` | standard: `Col 0 l` and `read 0 l` is OT |
| `unread 0` | `exb` → `bms1` | `Googology/Trans/BMS/ExBuchholz/Basic.lean:197` | OT, every subscript 0 (below ε₀) |
| `pairOrdTerm` | `bms2` → `exb` | `Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean:344` | see below |
| `trioE2` | `exb` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStripTree.lean:113` | `p0(W_a)` with `a` OT, `0 < a < W`, every subscript of `a` 0 or 1 |
| `trioMatrixLSt` (`--wide`) | `exb` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:422` | `p0(W_a)` with `a` OT, `a ≠ 0` |
| `trioRuleMatrixSt` (`--wide`) | `ord` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:410` | a nonzero sheet label `a`, read as `p0(W_a)` |
| `o` | `ssoss` → `exb` | `Googology/Notation/SSOSS/SequenceOrdinal.lean:17` | see below |
| `phi.py` | `bms2` → `por1` | `Googology/Trans/BMS/PoR/PSS/por/phi.py` | as the program |
| `tr.py` (= `trNode`) | `bms2` → `wilken1` | `Googology/Trans/BMS/PoR/PSS/por/tr.py` | as the program |
| `phi3def2.py` | `bms3` → `por2` | `Googology/Trans/BMS/PoR/Trio/por/phi3def2.py` | as the program |
| `tr3.py` | `bms3` → `wilken2` | `Googology/Trans/BMS/PoR/Trio/por/tr3.py` | as the program |

Every map into `exb` gives the usual value of the matrix: `(0)(1)` = `w`,
`(0,0)(1,1)` = `e0`, `(0,0)(1,1)(2,2)` = `p0(W_2)`. In Lean,
`pairOrdTerm (withZero l) = read 0 l` holds on every standard one-row `l`
tested.

`trioE2 a` is the trio matrix of ψ₀(Ω_a). Lean proves it standard, injective
and order-preserving on the domain above (`trioE2_std`, `trioE2_injective`,
`trioE2_lt_iff`). The four programs of the last rows run as they are, in a
subprocess.

`o` is the value of a strong second-order searching sequence (SSOSS) below
`(0,0,2)`: `o (0,0) ⌢ Y = 2 + vs (parse Y)`, with `val z = 1` and
`val (b u) = w^(1 + vs u)`. It is noncomputable in Lean; the port computes it
as a Cantor normal form, written as an `exb` term with every subscript 0.
Lean proves that `o` equals the rank of one step on the standard forms
(`ssoss_rank`).

### What is not checked

- **Standard pair sequences.** `pairOrdTerm` is proved on the standard pair
  sequences (`CTPS`), but neither Lean nor pss-proof has a computable test of
  `CTPS`. `trans` checks only what every standard one satisfies: the first
  column is `(0,0)`, and the value is a standard form below `p0(W_w)`.
- **Standard matrices with two or more rows** in general, for `zeroRow` and the
  programs.
- **Standard SSOSS sequences.** Lean has no computable test of `Standard`.
  `trans` checks only that every entry is 0 or 1 and that a sequence of length
  2 or more starts with (0,0), the fragment on which `o` has its meaning.

### The `--wide` maps

`trioMatrixLSt` and `trioRuleMatrixSt` are what `--wide` adds. They are the
rule program of rules 1–10 with the fixes merged in `TrioRulesAll`, the
reading `ofTermFix` and the strip patch. Lean proves that it equals `trioE2`
on the terms with subscripts 0 and 1 of reading depth at most 100
(`trioMatrixLSt_eq_trioE2`), and that it is not injective beyond depth 200
(the towers `T_202` and `T_203`, `trioMatrixLSt_not_injective`). On wider
families its matrices can be out of order or not standard
(`Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-STRIP.md`). The other fixes
(U, U2, nonlast2, lastleaf, stretch, mul-normalize, fuel) are separate
patches on `TrioRulesAll` and are not ported.

### Not reachable

- `inacc`, `y`, `omegay`: no map in the library reaches them. Their parsers and
  printers exist.
- `exb` → `bms2`: Lean proves that `pairTerm` is a bijection
  (`toTerm_bijOn_TransRange_OT`), but defines no inverse function.
- `dbms2` → `exb`: Lean has only the ordinal-valued `dbmsL2OrdEval`, no term.
- `bms3` → `exb`: no map in Lean.

## Files

| file | contents |
|---|---|
| `trans` | the command |
| `notations.md` | the ASCII notations |
| `trans.md` | the routes, as a diagram |
| `notation/` | parsers and printers: `matrix`, `seq`, `ssoss`, `exb`, `label` (`ord`), `inacc`; `exb_std` (`Term.cmp`, `isOT`) |
| `maps/bms.py` | `zeroRow`, `read`, `unread` |
| `maps/pss.py` | `pairTerm`, `pairOrdTerm`, and the part of [pss-proof](https://github.com/koteitan/pss-proof) they need (`PSS.Trans`, `Red`, `Adm`, …) |
| `maps/trio.py` | `trioE2`, `trioE`, `omegaIndexMatrix` |
| `maps/trio_rules.py` | `trioMatrixLSt`, `trioRuleMatrixSt`, `ofTermFix` (the rule program) |
| `maps/ssoss.py` | `Seq.fs`, `parse`, `flat`, `encode` and the value `o` of SSOSS |
| `maps/por.py` | the four PoR programs |
| `maps/__init__.py` | the graph of maps and the path search |
| `tests/` | unit tests, and the generators of the Lean checks |

## Checks

Unit tests, in `python/trans`:

```
python3 -m unittest discover -s tests
```

Agreement with Lean: each generator writes a Lean file of `#guard`s that
compare the Lean function with the Python one. Run each file with
`leanman check -C <this Lean project> FILE`.

| generator | what | guards |
|---|---|---|
| `tests/gen_lean_check.py` | `ord` labels (158), `exb` shorthands, `inacc`; `read`, `unread`, `zeroRow` on every `Col 0` list up to length 7 (626) | 2047 |
| `tests/gen_lean_pss.py` | `pairTerm`, `pairOrdTerm` on 1297 standard pair sequences; `pairOrdTerm (withZero l) = read 0 l` on 84 one-row `l` | 2762 |
| `tests/gen_lean_ssoss.py` | `Seq.fs` (k = 1, 2, 3) and `encode (parse (S.drop 2)) = S` on 180 standard SSOSS sequences | 718 |
| `tests/gen_lean_trio.py OUTDIR` | `Term.cmp`, `isOT` (600); `trioE2` on all 2398 terms of `smallFrag 7` and 150 outside the domain; `trioE`; `omegaIndexMatrix` | 4008 |
| `tests/gen_lean_trio_rules.py OUTDIR` | `trioRuleMatrixOfSt` on every string literal of `Googology/Trans/ExBuchholz/BMS/Trio/` (6160); `trioMatrixLSt`, `ofTermFix` on `smallFrag 7` (2398), on the four wide families of `TRIO-FIX-STRIP.md` (2089) and on 402 more terms; the towers `T_190`–`T_212` and the depth limits around fuel 200 | 16080 |

All five pass (`leanman` exit 0). A false `#guard` added on purpose fails
(exit 2).
