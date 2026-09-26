/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeMH.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMD
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredBoundary

set_option backward.do.legacy false

/-!
# (MH) holds

`MHHolds` (`CopyShape.lean`, fact `FactMH` of `CopyShapeItems.lean`): for a reached clean item
with `b = 0` in a copied column of a block `i ≥ 1`, `h_ρ ≤ h_q + g`, where `ρ` is the top of the
root column in the source region and `q` the top of the output boundary column `c_r + w·i` in
the target region. This file proves the stronger `h_ρ ≤ h_q` (`mhHolds`).

The proof has two parts.

* **Source equals target** (`reach_good`). Every reached item `it` satisfies `Good`: its source
  and target regions are equal, or it is a gap copy (`b = 1`), or it is plain and the root
  column has no node in its source region. By induction over the items (`good_child`):
  - case 1 keeps the slot index (`S[j] ↦ T[j]`), and a region without root node has none in
    its slots;
  - cases 2 and 4: below the root slot and at the root slot the index is kept; the other
    children are gap copies, or (case 2) lifted slots `S[σ]` whose index `σ` is above the root
    height `h_ρ`, where the root column has no node since `ρ` is its top in `S`;
  - case 3: gap copies, or slots `S[j - h_q]` with `j > h_q + h_ρ`, again above `h_ρ`.
  So a clean item with `b = 0` has source = target (it is neither a gap copy nor plain).
* **The boundary column has the row of `ρ`** (`Recon.CutPredMD.boundaryRootRowsHolds`,
  proved): the output column `c_r + w·i` has a node at every official row of the root column
  below `τ`. The row of `ρ` lies in the region `S = T`, which is below `τ` (`reach_below`), so the
  top `q` of the boundary column in `T` is at or above it, and `h_q ≥ h_ρ`.

No fact about `M(s)` beyond these is used; in particular (MA), which is false
(`CopyShapeMAFalse.lean`), is not used.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.MHProof

open Canonical Reserve Official Descent Classification Proofs

/-! ## Regions without a node of a column -/

theorem topIn_eq_none {M : Mountain} {c d : Nat} {S : Row}
    (h : ∀ p ∈ realNodes M c, inRegion d S (official p.2.row) = false) : topIn M c d S = none := by
  unfold topIn
  rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
  intro p hp
  simp [h p hp]

theorem topIn_slot_none {M : Mountain} {c d : Nat} {S : Row} {j : Nat}
    (h : topIn M c (d + 2) S = none) : topIn M c (d + 1) (slot (d + 2) S j) = none := by
  apply topIn_eq_none
  intro p hp
  have hn := Recon.RowLaw.topIn_none h p hp
  cases hs : inRegion (d + 1) (slot (d + 2) S j) (official p.2.row) with
  | false => rfl
  | true =>
      rw [(Recon.RowLaw.inRegion_slot_iff.mp hs).1] at hn
      cases hn

/-- Along a column of a valid mountain, a higher index has a higher row. -/
theorem row_le_of_index {M : Mountain} (hV : MountainValid M) {c : Nat} {p q : Ref × Cell}
    (hp : p ∈ realNodes M c) (hq : q ∈ realNodes M c) (h : p.1.index ≤ q.1.index) :
    p.2.row ≤ q.2.row := by
  obtain ⟨hpc, _, hpcell⟩ := Classification.mem_realNodes hp
  obtain ⟨hqc, _, hqcell⟩ := Classification.mem_realNodes hq
  have hp' : cell? M ⟨c, p.1.index⟩ = some p.2 := by rw [← hpc]; exact hpcell
  have hq' : cell? M ⟨c, q.1.index⟩ = some q.2 := by rw [← hqc]; exact hqcell
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · exact (ChainCorr.cell_row_lt hV hp' hq' hlt).le
  · rw [heq] at hp'
    rw [Option.some.inj (hp'.symm.trans hq')]

/-- A slot strictly above the slot of the top `ρ` of column `c` in `S` has no node of `c`. -/
theorem topIn_slot_above {M : Mountain} (hV : MountainValid M) {c d : Nat} {S : Row}
    {ρr : Ref} {ρc : Cell} (hρ : topIn M c (d + 2) S = some (ρr, ρc)) {σ : Nat}
    (hσ : height (d + 2) (official ρc.row) < σ) :
    topIn M c (d + 1) (slot (d + 2) S σ) = none := by
  apply topIn_eq_none
  intro p hp
  cases hs : inRegion (d + 1) (slot (d + 2) S σ) (official p.2.row) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨hpS, hpσ⟩ := Recon.RowLaw.inRegion_slot_iff.mp hs
      obtain ⟨hρmem, hρreg, hmax⟩ := Recon.RowLaw.topIn_spec hρ
      have hρreg' : inRegion (d + 2) S (official ρc.row) = true := hρreg
      have hidx : p.1.index ≤ ρr.index := hmax p hp hpS
      have hle : p.2.row ≤ ρc.row := row_le_of_index hV hp hρmem hidx
      obtain ⟨_, hp1, hpcell⟩ := Classification.mem_realNodes hp
      have h1 : (1 : Row) ≤ p.2.row := one_le_row hV hpcell hp1
      have hco : (official p.2.row).coeff d ≤ (official ρc.row).coeff d :=
        Recon.RowLaw.coeff_le_of_inRegion hpS hρreg' (Recon.official_mono h1 hle)
      have hh : height (d + 2) (official ρc.row) = (official ρc.row).coeff d := rfl
      omega

/-! ## The invariant -/

/-- An item whose source and target regions are equal, or a gap copy, or a plain item whose
source region has no node of the root column. -/
def Good (M : Mountain) (cr d : Nat) (it : Item) : Prop :=
  it.source = it.target ∨ it.cutBottom = true ∨
    (it.clean = none ∧ topIn M cr d it.source = none)

/-- **The children of a `Good` item are `Good`** (blocks `i ≥ 1`). -/
theorem good_child {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (hV : MountainValid ctx.source) (hblk : 1 ≤ ctx.block)
    (h : childItems ctx (d + 2) it = .ok cs) (hg : Good ctx.source ctx.rootColumn (d + 2) it) :
    ∀ c ∈ cs, Good ctx.source ctx.rootColumn (d + 1) c := by
  intro c hc
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
      rw [Recon.childItems_none h hx] at hc
      cases hc
  | some a =>
      obtain ⟨b, hb⟩ := Recon.childItems_asc h hx
      cases b with
      | false =>
          obtain ⟨j, rfl⟩ := Recon.CutPredMD.childItems_case1_eq h hx hb c hc
          rcases hg with hst | hcut | ⟨_, hnone⟩
          · left
            show slot (d + 2) it.source j = slot (d + 2) it.target j
            rw [hst]
          · exfalso
            have := (Recon.childItems_case1 h hx hb).2.1
            rw [hcut] at this
            cases this
          · right; right
            exact ⟨rfl, topIn_slot_none hnone⟩
      | true =>
          cases hr : topIn ctx.source ctx.rootColumn (d + 2) it.source with
          | none =>
              rw [hr] at hb
              simp [ascends, pure, Except.pure] at hb
          | some ρ =>
              obtain ⟨ρr, ρc⟩ := ρ
              rw [hr] at hb
              have hst_or : it.source = it.target ∨ it.cutBottom = true := by
                rcases hg with h1 | h1 | ⟨_, h1⟩
                · exact Or.inl h1
                · exact Or.inr h1
                · rw [hr] at h1; cases h1
              have habove : ∀ σ, height (d + 2) (official ρc.row) < σ →
                  topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) it.source σ) = none :=
                fun σ hσ => topIn_slot_above hV hr hσ
              cases hcl : it.clean with
              | none =>
                  cases hcb : it.cutBottom with
                  | false =>
                      have hst : it.source = it.target := by
                        rcases hst_or with h1 | h1
                        · exact h1
                        · rw [hcb] at h1; cases h1
                      rw [Recon.childItems_case2 h hcl hcb hx hr hb] at hc
                      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
                      unfold Recon.c2
                      have he0 : (0 : Int) ≤ (if d + 2 = 2 then (1 : Int) else 0) := by
                        split_ifs <;> omega
                      generalize (if d + 2 = 2 then (1 : Int) else 0) = e at he0 ⊢
                      split_ifs with h1 h2
                      · left
                        show slot (d + 2) it.source j = slot (d + 2) it.target j
                        rw [hst]
                      · by_cases h3 : height (d + 2) (official ρc.row) < j
                        · right; left
                          simp [h3]
                        · left
                          have hj : j = height (d + 2) (official ρc.row) := by omega
                          subst hj
                          show slot (d + 2) it.source _ = slot (d + 2) it.target _
                          rw [hst]
                      · by_cases h4 : ctx.block ≠ 0 ∧ (j : Int) =
                            (height (d + 2) (official ρc.row) : Int) +
                              (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2)
                                it.source) : Nat) : Int) -
                                ((height (d + 2) (official ρc.row) : Nat) : Int)) *
                                (ctx.block : Int)
                        · right; left
                          simp only
                          exact decide_eq_true h4
                        · right; right
                          refine ⟨rfl, habove _ ?_⟩
                          have hne : (j : Int) ≠ (height (d + 2) (official ρc.row) : Int) +
                              (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2)
                                it.source) : Nat) : Int) -
                                ((height (d + 2) (official ρc.row) : Nat) : Int)) *
                                (ctx.block : Int) := by
                            intro he
                            exact h4 ⟨by omega, he⟩
                          omega
                  | true =>
                      rw [Recon.childItems_case3 h hcl hcb hx hr hb] at hc
                      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
                      have hRj : height (d + 2) (official ρc.row) ≤ j := by
                        have := (List.mem_filter.mp hj).2
                        simpa using this
                      unfold Recon.c3
                      have he0 : (0 : Int) ≤ (if d + 2 = 2 then (1 : Int) else 0) := by
                        split_ifs <;> omega
                      generalize (if d + 2 = 2 then (1 : Int) else 0) = e at he0 ⊢
                      split_ifs with h1
                      · right; left; rfl
                      · by_cases h5 : j = heightOf (d + 2)
                            (topIn ctx.result ctx.boundary (d + 2) it.target) +
                            height (d + 2) (official ρc.row)
                        · right; left
                          simp [h5]
                        · right; right
                          refine ⟨rfl, habove _ ?_⟩
                          omega
              | some C =>
                  obtain ⟨_, _, _, _, _, _, hcs⟩ := Recon.childItems_case4 h hcl hx hr hb
                  rw [hcs] at hc
                  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
                  unfold Recon.c4
                  split_ifs with h1 h2
                  · right; left; rfl
                  · have hst : it.source = it.target := by
                      rcases hst_or with h' | h'
                      · exact h'
                      · exact absurd h' h1
                    left
                    show slot (d + 2) it.source j = slot (d + 2) it.target j
                    rw [hst]
                  · have hst : it.source = it.target := by
                      rcases hst_or with h' | h'
                      · exact h'
                      · exact absurd h' h1
                    by_cases h3 : height (d + 2) (official ρc.row) < j
                    · right; left
                      simp [h3]
                    · left
                      have hj : j = height (d + 2) (official ρc.row) := by omega
                      subst hj
                      show slot (d + 2) it.source _ = slot (d + 2) it.target _
                      rw [hst]

/-- **Every reached item is `Good`** (blocks `i ≥ 1`). -/
theorem reach_good {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    (hblk : 1 ≤ ctx.block) {d : Nat} {it : Item} (h : Reach ctx τ d it) :
    Good ctx.source ctx.rootColumn d it := by
  induction h with
  | top hmem =>
      obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
      simp only [Prod.mk.injEq] at hk
      obtain ⟨_, rfl⟩ := hk
      exact Or.inl rfl
  | child _ hch hc ih => exact good_child hV hblk hch ih _ hc

/-- A reached clean item with `b = 0` has equal source and target regions. -/
theorem reach_clean_eq {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    (hblk : 1 ≤ ctx.block) {d : Nat} {it : Item} (h : Reach ctx τ d it) {C : Row}
    (hC : it.clean = some C) (hcb : it.cutBottom = false) : it.source = it.target := by
  rcases reach_good hV hblk h with h1 | h1 | ⟨h1, _⟩
  · exact h1
  · rw [hcb] at h1; cases h1
  · rw [hC] at h1; cases h1

/-! ## (MH) -/

/-- **(MH) holds**, in the strong form `h_ρ ≤ h_q` (then `h_ρ ≤ h_q + g` for every `g`). -/
theorem mhHolds : MHHolds := by
  intro s n D M out ρ R t hS i hi0 hi y hy d it C hRe hC hcb csRef cs g _ _
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hst := reach_clean_eq (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
    (y + (ρ.x0 - ρ.cr) * i)) hV hi0 hRe hC hcb
  have hbel := (reach_below hRe).1
  -- the context, read off
  show heightOf (d + 2) (topIn M ρ.cr (d + 2) it.source) ≤
    heightOf (d + 2) (topIn (R.extract 0 (y + (ρ.x0 - ρ.cr) * i))
      (ρ.cr + (ρ.x0 - ρ.cr) * i) (d + 2) it.target) + g
  rw [topIn_extract' (by omega)]
  cases hρ : topIn M ρ.cr (d + 2) it.source with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨ρr, ρc⟩ := p
      obtain ⟨hρmem, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
      have hlt : official ρc.row < official t.row := hbel _ hρreg
      obtain ⟨col, root, hcol, ht, htl, _, hcr, hx0⟩ := splice_root hS
      have hcx : root.column < M.size - 1 := by
        rw [← hcr, ← hx0]
        exact lt_of_lt_of_le hcy ‹y ≤ ρ.x0›
      have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
        rw [build_size hS.canon]
        exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run
          hS.splice.root hS.splice.copies
      have hBR := Recon.CutPredMD.boundaryRootRowsHolds s n R hS.run M col t root
        hS.splice.build hcol ht htl hcx i hi0
      have hBlt : root.column + (M.size - 1 - root.column) * i < R.size := by
        rw [← hcr, ← hx0, hRs]
        have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
          rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      have hρmem' : (ρr, ρc) ∈ realNodes M root.column := by rw [← hcr]; exact hρmem
      obtain ⟨q0, hq0, hq0row⟩ := hBR hBlt (ρr, ρc) hρmem' hlt
      rw [← hcr, ← hx0] at hq0
      -- `q0` is a node of the boundary column in `T = S`
      have hq0reg : inRegion (d + 2) it.target (official q0.2.row) = true := by
        rw [← hst, hq0row]; exact hρreg
      cases hq : topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) (d + 2) it.target with
      | none =>
          have := Recon.RowLaw.topIn_none hq q0 hq0
          rw [hq0reg] at this
          cases this
      | some qq =>
          obtain ⟨hqmem, hqreg, hqmax⟩ := Recon.RowLaw.topIn_spec hq
          have hidx := hqmax q0 hq0 hq0reg
          have hle : q0.2.row ≤ qq.2.row := row_le_of_index hVR hq0 hqmem hidx
          obtain ⟨_, hq01, hq0cell⟩ := Classification.mem_realNodes hq0
          have h1 : (1 : Row) ≤ q0.2.row := one_le_row hVR hq0cell hq01
          have hco := Recon.RowLaw.coeff_le_of_inRegion hq0reg hqreg (Recon.official_mono h1 hle)
          rw [hq0row] at hco
          obtain ⟨qr, qc⟩ := qq
          show (official ρc.row).coeff d ≤ (official qc.row).coeff d + g
          have : (official ρc.row).coeff d ≤ (official qc.row).coeff d := hco
          omega

/-- **`CopyEmitted`, `CopyFirst` from MA alone** (MD and MH are proved). MA is false
(`CopyShapeMAFalse.lean`), so these give nothing; `CopyShapeNoMA.lean` proves `CopyEmitted` and
`CopyFirst` without MA (`NoMA.copyEmitted`, `NoMA.copyFirst`). `CopyOrder` is false. -/
theorem copyEmitted_of_MA (hMA : MAHolds) : ChainCorr.CopyEmitted :=
  copyEmitted_of_facts hMA mdHolds mhHolds

theorem copyFirst_of_MA (hMA : MAHolds) : ChainCorr.CopyFirst :=
  copyFirst_of_facts hMA mdHolds mhHolds

end OmegaY.Official.Classification.Proofs.CopyShape.MHProof

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MHProof.reach_good
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MHProof.mhHolds
