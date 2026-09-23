[English](TRIO-FIX-STRIP.md) | [Japanese](TRIO-FIX-STRIP-ja.md)

# Patch "strip": rule 1 on an exponent whose head is not an atom

Files: [TrioFixStrip.lean](TrioFixStrip.lean) (the patch),
[TrioFixStripSheet.lean](TrioFixStripSheet.lean) (the checks: summary and first piece; the
other pieces are `TrioFixStripSheet1b`–`1h`, `TrioFixStripSheet2`, `TrioFixStripSheet9`,
`TrioFixStripSheet9Frag7`, `TrioFixStripSheet9Wide`, split so each checks in minutes),
[TrioFixStripTree.lean](TrioFixStripTree.lean) (order and standard forms on the fragment).
The patch sits on top of [TrioFixOfTerm.lean](TrioFixOfTerm.lean) (the reading `ofTermFix`)
and `TrioRulesAll` (rules 1–10 with Fixes A–E, N).

## The problem

With the reading `ofTermFix`, the order theorem of `TrioTree` failed
(`TrioFixOfTerm.not_trioMatrixLFix_lt_iff`):

    α = ψ_0(ψ_1(ψ_0(Ω)))              = ε_{ε₀}
    β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))   = ε_{ε₀^{ε₀^ω}}
    α < β, but M(β) < M(α)

The builder lays a summand ω^δ as a column whose children spell `strip δ`, the
argument Y with ω^δ = ψ_v(Y). `strip` looks at the head h·c of δ = h·c + ρ:

| head h | children | why |
|---|---|---|
| ψ_v(X) | X + ψ_v(X)·(c-1) + ρ | ω^δ = ψ_v(X + …) |
| Ω_v | Ω_v·(c-1) + ρ | ω^δ = ψ_v(Ω_v·(c-1) + ρ) |
| ω^e (not an atom) | δ | right only if the chain of leading exponents of δ ends in 0 or in Ω_v |

In β the exponent is ω^(ε₀·ω) = ψ_0(Ω + ψ_0(Ω+1)), and ε₀·ω = ω^(ε₀+1) has the head
ω^(ε₀+1), whose chain ends in the atom ε₀ = ψ_0(Ω). `strip` gave ε₀·ω, the tree of
ψ_0(ψ_0(Ω+1)) (a non-standard term, equal to ε₀ in Buchholz's system), instead of
Ω + ε₀·ω, the tree of ψ_0(Ω + ψ_0(Ω+1)).

## The change

`chainAtom h`: follow the leading exponents of h until an atom (or 0).

- `stripSt δ`: the first two rows unchanged. In the third row, if `chainAtom h = ψ_v(X)`,
  the children are **X + δ** (ψ_v(X + δ) = ω^(ψ_v(X) + δ) = ω^δ); otherwise δ as before.
- `uncollapses e` in place of `headIsPsi (ato e)` (the `arg` flag of the children):
  true when `chainAtom` of the head is a ψ atom. Same as before on an atom head; true
  in the new case, since the children again start with the argument X.

For merging: replace the body of `TrioRules.strip` by `stripSt`, and each
`headIsPsi (ato e)` by `uncollapses e` (in `blockF`, `blockF2`, `blockN` and the copies
in the other patches). Nothing else changes. The patch copies `tailBlockF`, `tailBlock`,
`unitTailLevel`, `tailLevel`, `blockN`, `restate`, `placeUnitsN`, `finishN`,
`MstepAll` with only these two substitutions.
`stripSt_eq_strip`, `uncollapses_eq`: the old and new rule agree unless the head is not an
atom and its chain ends in a ψ atom. Below ε₀ there is no ψ atom, so nothing changes there.

Proved in Lean: `trioMatrixLSt_tβ` (β now gets the tree of the term), `trioMatrixLSt_tα_lt_tβ`
(M(α) < M(β)).

## Checks (`TrioFixStripSheet*.lean`, all `#guard`, 968 in total)

| check | patched (`trioMatrixLSt`) | before (`trioMatrixLFix`) |
|---|---|---|
| every guard of `TrioRulesAllSheet.lean` (sheet rows, order of 783 / 784, Fixes A–E, N, interactions, one-step comparison) | all hold | all hold |
| labels of the corpus (1,225) changed | 0 | – |
| 42 terms with a sheet row: matrix = sheet, disagreements vs 784 | 42, 0 | 42, 0 |
| (ε₀·ω)[n] = ε₀·(n+1), n = 0..3 | yes | yes |
| smallFrag 6 (610): disagreements, collisions | 0, 0 | 0, 0 |
| ≤ 7 ψ, subscripts 0/1 (2,397): disagreements, collisions | **0, 0** | 127, 0 |
| terms of that family whose matrix changed | only β | – |
| subscripts 0,1,2 (491) | 75, 8 | 75, 8 |
| α < Ω_2, subscripts 0,1 (524) | 0, 0 | 0, 0 |
| α < Ω_Ω, subscripts 0,1,ω (537) | 63, 11 | 63, 11 |
| α < Ω_{Ω_Ω}, subscripts 0,1,Ω (537) | 137, 29 | 137, 29 |

On the four wider families the patch changes no matrix, so their failures are other
defects of the builder.

Standard forms (yaBMS `bms -s`, outside Lean): all 2,397 matrices of the 7-ψ family are
standard (before: all but β's). Wider families as before: subscripts 0,1,2: 2 of 483
distinct not standard; α < Ω_2: 0 of 524; 0,1,ω: 30 of 527; 0,1,Ω: 59 of 512.

## Order and standard forms on the fragment (`TrioFixStripTree.lean`)

`trioE2` is the patched map written as a structural recursion, like `TrioTree.trioE`.
Only the digits of an add unit ψ_0(b) change. With b = h + l (h = the ψ_1 summands,
l = the ψ_0 summands ψ_0(g_1) + ψ_0(g_2) + …):

    ψ_0(b) = ω^(ψ_0(h) + l)
    digits: ψ_0(h) (dropped if h < g_1, then ψ_0(h) + l = l), then one digit per ψ_0(g_j)
    the digit of ψ_0(g) is the tree of expoT(g), with ψ_0(g) = ω^expoT(g):
      expoT(g) = g                    if g has no Ω
               = ψ_0(hi g) + lo g     otherwise (lo g alone if hi g < first argument of lo g)

(The old map had one digit, the tree of ψ_0(b).)

Proved, for standard α, β < Ω with every subscript 0 or 1:

- `trioE2_lt_iff`: trioE2 α < trioE2 β ↔ α < β; `trioE2_injective`.
- `trioE2_std`: trioE2 α is a standard form of 3-row BMS.

Key steps: `expoT_lt` (expoT keeps the order on the arguments that occur), `good_of_OT`,
`OT_psi_hiPart` (ψ_0 of the Ω part of a standard argument of ψ_0 is standard), and
`TrioTreeStd.reach_units`.

## What is still wrong / not proved

1. **The program is not proved to compute `trioE2`.** `trioMatrixLSt α = trioE2 α` is
   checked on the 2,398 terms of `smallFrag 7` (`#guard`) and proved for α, β above. The
   old proof `TrioTreeRules.trioMatrixL_eq_trioE` is about rules 1–10 and `ofTerm`; a new
   one would need the merged builder (Fixes A–E, N) with `ofTermFix` and `stripSt`
   (the program's comparisons on the new exponents, absorption in `add`, and the
   simulation of `placeUnitsN` with no regime). So the order and standard-form theorems
   for `trioMatrixLSt` itself rest on that calibration. It is stated as the open `Prop`
   `CalibSt` (∀ α, OT α → α < Ω → Sub01 α → trioMatrixLSt α = trioE2 α), and
   `trioMatrixLSt_lt_iff_of_calib`, `trioMatrixLSt_std_of_calib` are proved from it.
2. **Larger subscripts.** The failures with subscripts 0,1,2 / 0,1,ω / 0,1,Ω are
   unchanged (75 / 63 / 137 disagreements). They are other defects, not this one.
