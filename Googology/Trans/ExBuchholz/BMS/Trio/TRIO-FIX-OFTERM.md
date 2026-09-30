[English](TRIO-FIX-OFTERM.md) | [Japanese](TRIO-FIX-OFTERM-ja.md)

# Patch "ofTerm": how a term ψ_a(b) is read

Files: [TrioFixOfTerm.lean](TrioFixOfTerm.lean) (the patch),
[TrioFixOfTermSheet.lean](TrioFixOfTermSheet.lean) (the checks).
The patch sits on top of `TrioRulesAll` and changes **no definition of the builder**.
It only changes the reading of a term of the extended Buchholz notation into the
normal form of the rules (`TrioRules.ofTerm`).

## The problem

`ofTerm` reads every ψ_a(b) with b ≠ 0 as one atom ψ_a(b).
The atoms of the rules are fixed points of x ↦ ω^x
([algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md), "Atoms").
On the [sheet](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv),
every ψ atom has an argument whose summands are all ≥ Ω_{a+1}.
So ψ_0(Ω+1) = ε₀·ω was read as the atom `psi(W+1)`.
The rules lay that out like the label ε₀^{ε₀^ω} (row 2163), not like ε₀·ω (row 2158).

## The reading (change 1)

Split the argument: b = b_hi + b_lo.

- b_hi = the summands ψ_c(d) with c > a (each ≥ Ω_{a+1})
- b_lo = the summands ψ_c(d) with c ≤ a (each < Ω_{a+1})

Then

    ψ_a(b_hi + b_lo) = ω^(P + b_lo)
    P = ψ_a(b_hi)  if b_hi ≠ 0
    P = Ω_a        if b_hi = 0, a ≠ 0
    P = 0          if b_hi = 0, a = 0

With b_lo = 0 this is the old atom. With a = 0, b_hi = 0 it is the old ω^b.
Examples:

| term | value | sheet label |
|---|---|---|
| ψ_0(Ω+1) | ω^(ε₀+1) = ε₀·ω | `psi(W)*w` |
| ψ_0(Ω+ψ_0(Ω)) | ω^(ε₀·2) = ε₀^2 | `psi(W)^2` |
| ψ_1(1) | ω^(Ω+1) = Ω·ω | `W*w` |
| ψ_1(ψ_0(Ω)) | ω^(Ω+ε₀) = Ω·ε₀ | `W*psi(W)` |
| ψ_1(Ω) | ω^(Ω·2) = Ω^2 | `W^2` |

Proved in Lean: `val_psi_Omega_add`: ψ_0(Ω+t) = ε₀·ω^t = ω^(ε₀+t) for t < ε₁
(from `Ord.psi_Omega_add_eq`). The general identity (ψ_a is continuous in the part
below Ω_{a+1}) is not proved.

## Change 2: an infinite subscript

The sheet writes a collapse at an infinite level c with the cardinal Ω_{c+1}:
`psi_W_(w+1)(W_(w+1))` = ψ_ω(Ω_{ω+1}), `psi_W_(W+1)(W_(W+1))` = ψ_Ω(Ω_{Ω+1}).
It writes the index form `psi_c` only for finite c.
`ofTerm` wrote `psi_c` for every c. For c = Ω this is the program's cardinal form
ψ_{Ω_1}, a collapse below Ω. So `psiAtom` writes an infinite c as `psi_{Ω_{c+1}}`.
Change 2 can be dropped on its own (`psiAtom cf X := .psi cf X`).

## For merging

- `ofTermFix` replaces the body of `TrioRules.ofTerm`.
- `trioMatrixLFix α = trioRuleMatrixAll (ofTermFix α)` replaces `trioMatrixL`.
- `ofTermFix_allNil`: below ε₀ nothing changes (proved).

## Checks (`TrioFixOfTermSheet.lean`, all `#guard`)

| check | new reading | old reading |
|---|---|---|
| label map, order of the 783 and 784 chosen matrices | unchanged, 0 | 0 |
| 42 terms with a sheet row: normal form = label | 42 | 14 |
| same: matrix = sheet row | 42 | 25 |
| those 42 against the 784 chosen: order disagreements | 0 | 710 |
| (ε₀·ω)[n] = ε₀·(n+1), n = 0..3 (BMS expansion) | yes | no (goes to ε₀^{ε₀^n}) |
| smallFrag 6 (610 terms): disagreements, collisions | 0, 0 | 0, 0 |
| ≤ 7 ψ, subscripts 0/1 (2397): disagreements | 127 | 0 |
| subscripts 0,1,2 countable (491) | 75, 8 | 75, 8 |
| α < Ω_2, subscripts 0,1 (524) | 0, 0 | 0, 0 |
| α < Ω_Ω, subscripts 0,1,ω (537) | 63, 11 | 0, 0 |
| α < Ω_{Ω_Ω}, subscripts 0,1,Ω (537) | 137, 29 | 58277, 2743 |
| the reading's own order (cmpOrd), all families | 0 | 0 |

The ψ_0-only version of change 1 gets 21 of the 42 labels.

Expansions do not separate the two maps on smallFrag 6 (run outside the sheet):
for each of the 448 nonzero limits α and n ≤ 2, some step m ≤ 6 of the BMS
expansion of M(α) reaches M(α[n]) (Buchholz fundamental sequence `fs`/`idx`),
and every step is below M(α). Both maps pass on all 448.
So the sheet rows and (ε₀·ω)[n] = ε₀·(n+1) are what decide the reading.

Standard forms (yaBMS `bms -s`, outside Lean):
smallFrag 6 new: all 610. ≤ 7 ψ new: 2396 of 2397 (all but β below).
Subscripts 0,1,2: 481 of 483 with either reading. α < Ω_2: all 524.
Subscripts 0,1,ω: new 30 of 527 not standard, old 61 of 537.
Subscripts 0,1,Ω: new 59 of 512, old 46 of 291.

## What is still wrong

1. **TrioTree's theorems are about the old map.** They stay true as stated
   (`trioMatrixL_eq_trioE`, `trioMatrixL_std`, `trioMatrixL_lt_iff`,
   `trioMatrixL_injective` in TrioTreeRules.lean).
   With the new map in place of the old one, the order theorem is false.
   Proved in Lean (`trioMatrixLFix_order_fails`, `not_trioMatrixLFix_lt_iff`):

       α = ψ_0(ψ_1(ψ_0(Ω)))              = ε_{ε₀}
       β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))   = ε_{ε₀^{ε₀^ω}}
       α, β standard, < Ω, subscripts 0/1, dep ≤ 200, α < β
       new: M(β) < M(α)        old: M(α) < M(β)

   The new map keeps the order on smallFrag 6 (610 terms, `#guard`),
   and on 7 ψs every failure (127 pairs) involves β.
   Standard forms: all of smallFrag 6, and 2396 of 2397 with 7 ψs (only β fails;
   yaBMS, re-run for this report). Not proved in Lean.
2. **The one failure up to 7 ψs is a builder defect.**
   β = ψ_0(ψ_1(ψ_0(Ω+ψ_0(Ω+1)))) = ψ_0(Ω·ε₀^{ε₀^ω}), label `psi(W*psi(W)^psi(W)^w)`.
   Its matrix `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)(5,0,0)(6,0,0)(7,1,0)(7,0,0)`
   is not standard, and lies below the matrix of ε_{ε₀} = `psi(W*psi(W))`.
   The builder writes ω^{ε₀·ω} as the tree of ψ_0(ψ_0(Ω+1)).
   The right tree is ψ_0(Ω+ψ_0(Ω+1)): rule 1's `strip` uncollapses an exponent only
   when its head is a ψ atom, but ω^{ε₀+1} has head ω^{…}.
   With β's matrix replaced by the tree of the term, the 127 disagreements become 0.
   No sheet row reaches this case.
3. **Larger subscripts.** With subscripts 0,1,ω the new map has 63 order
   disagreements (old: 0). None of them is between two ordinals that both have a
   sheet row. These are builder defects off the sheet, which the old reading did not
   reach because it read those terms as atoms.
   With subscripts 0,1,Ω the new map has 137 disagreements and 29 collisions
   (old: 58277 and 2743). These 137 are not checked against the sheet.
