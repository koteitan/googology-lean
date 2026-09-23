[← Back](../README.md) | [English](TRIO-FIX-MUL-NORMALIZE.md) | [Japanese](TRIO-FIX-MUL-NORMALIZE-ja.md)

# Patch: `ω^atom = atom` in `mul` and `power`

This is a separate patch on top of [`TrioRulesAll.lean`](TrioRulesAll.lean), which has rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N. The code is in
[`TrioFixMulNormalize.lean`](TrioFixMulNormalize.lean). The checks are in
[`TrioFixMulNormalizeSheet.lean`](TrioFixMulNormalizeSheet.lean).

## The defect

This is a side finding of [TRIO-SHEET-41.md](TRIO-SHEET-41.md). `mul` builds the exponent of `ω^3·Ω` as
`ω^(3+Ω)` = `.o [(.W 1, 1)]`, which is the normal form `Ω` wrapped as an exponent. It should be the atom
`.W 1`. The two forms are the same ordinal, and `cmp_ord` says `Ω_{ω^3·Ω} = Ω_Ω`. But the builder
reads the shape. It sends `Ω_{ω^3·Ω}` through `placeUnits` at the level `ω^Ω`, and it sends `Ω_Ω`
through rule 2. So the printed label of row 4369, `W_(w^3*W)`, gets a different matrix from `W_W`.
`power` has the same defect: `ω^Ω` is written `ω^(ω^Ω)`.

## The change

1. `mkExp [(x, 1)] = x` when `x` is an atom (`Ω_v` or `ψ_v(X)`). In every other case,
   `mkExp a = .o a`.
2. `mulM`: this is `mul`, with `.o (addExp e1 e)` replaced by `mkExp (addExp e1 e)`.
3. `powerM`: this is `power`, with `mulM` in place of `mul` and `wpowM b = [(mkExp b, 1)]` in place of `wpow b`.
4. `parseM`: this is the label reader, with `mulM` and `powerM`. No other part of the rules calls `mul` or `power`.
5. `MstepFix`: this is `MstepAll`, with the test `alpha == [(.W v, 1)]` replaced by the pattern
   `alpha = [(.W _, 1)]`. It computes the same result.

In 2 and 3, the tests `== .o []` and `== one` also become pattern matches. The derived `==` on `Ex` does
not reduce inside proofs, not even for `Ex.W v == Ex.o []`. That is why points 2, 3 and 5 use patterns.

The following are proved: `ato (mkExp a) = a`; `mkExp` never writes `.o [(atom, 1)]`;
`mulM (ω^3) Ω = Ω`; `powerM ω Ω = Ω`; `MstepFix Mf Ω_w = MOmega2 Mf w` (rule 2 for every `w`); and
`MstepFix = MstepAll` on countable `α` and on `ψ_{Ω_u}(X)`. A theorem that compares `mulM` with `mul`
is not possible, because `mul` uses the derived `==`. The guards check it instead.

## Checks

| check | result |
|---|---|
| guards of `TrioRulesAllSheet.lean` (Parts 1–7) | all hold, with one intended change |
| distinct labels whose reading changes | 1 of 1,209: the printed label of row 4369 |
| distinct labels whose matrix changes | the same single label: it now gets `M(Ω_Ω)` |
| `parseM` outputs in normal form | 1,209 of 1,209 (`parse`: 1,208) |
| order check, 785 labels (both printed labels) | 0 disagreements (without the patch: 1) |
| Part 7 counts (step vs rules 1–10) | unchanged: 171/0, 32/6, 152/7, 870/257 |
| 22 hand-made `ω^atom` labels | patched matrix = the matrix of the normal form; all standard (yaBMS `bms -s`); 0 order disagreements against the 784 chosen matrices |
| the same 22 without the patch | 17 differ from the normal form, 5 are not standard, 62 order disagreements |

The corrected label of row 4369, `Ω_{ω^3}·Ω`, keeps its matrix.

## Still open

- The Python reference program [`tools/probe_eps_range.py`](https://github.com/koteitan/trio/blob/main/tools/probe_eps_range.py)
  has the same `mul` and `power`. It needs the same smart constructor, so that the two stay equal.
- The builder itself still reads the shape of its input. A `.o [(atom, 1)]` built by some other route
  would still be handled wrongly. After this patch, the label reader is the only source of ordinals, and
  on all 1,209 labels it makes normal forms (guarded).
