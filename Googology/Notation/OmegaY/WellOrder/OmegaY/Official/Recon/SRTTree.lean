/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/SRTTree.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CPNBase

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The boundary column stays below a lifted copy of a root-parent node (`SRT`, tree part)

Setting: a copied column `ctx` of a block `i ≥ 1` (here any context with the facts of one), the
boundary column `B = Bc` read by it, and an emit `p` of the lower part of `ctx` whose origin
`z⁺` has an official row `ρ_z` strictly above a row `rr`. The claim `claim` follows the path of
`p` in the tree of `ctx` downwards, through plain items `A` whose root top `ρ` (the top of the
root column in the source region of `A`) has the official row `rr`:

* in case 2 (no cut bottom; the top of `B` in the target of `A` is at height `h_ρ + Δ`), the
  child of `p` is a lifted plain child (a copy of the root row would copy the row `rr < ρ_z`, a
  child below `h_ρ` has its source below `rr`); if its slot is above `h_ρ + Δ`, every node of `B`
  in the target of `A` is in a lower slot; otherwise it is the cut-bottom child at the slot
  `h_ρ + Δ`, and the claim goes down;
* in case 3 (cut bottom), the lifted children map the slot `σ ≥ h_ρ` to `σ - h_ρ + h_B`, where
  `h_B` is the height of the top of `B` in the target of `A`; if `σ > h_ρ`, `p` is above every
  node of `B` in the target; otherwise it is the cut-bottom child at the slot `h_B`, and the
  claim goes down.

At level `2` the slots are single rows, so `σ = h_ρ` would put `ρ_z = rr`; the recursion ends.
The invariant carried down: every node of `B` below `τ` is in the target of the item or below
`p`.
-/

namespace OmegaY.Official.Recon.LRC.SRT

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- A node of `B` in a region below a node of `B` at the top of the region. -/
theorem coeff_le_top {Bc d : Nat} {T : Row} (hVR : MountainValid R) {q : Ref × Cell}
    (hq : q ∈ realNodes R Bc) (hin : inRegion (d + 2) T (official q.2.row) = true) :
    ∃ qt, topIn R Bc (d + 2) T = some qt ∧
      (official q.2.row).coeff d ≤ (official qt.2.row).coeff d := by
  cases htop : topIn R Bc (d + 2) T with
  | none =>
    have := RowLaw.topIn_none htop q hq
    rw [hin] at this; cases this
  | some qt =>
    refine ⟨qt, rfl, ?_⟩
    have hle := topIn_row_max' hVR htop hq hin
    obtain ⟨rt, ct⟩ := qt
    exact RowLaw.coeff_le_of_inRegion hin (Classification.topIn_inRegion htop) hle

/-- Rows of two slots of one region. -/
theorem lt_of_slot {d : Nat} {T G r : Row} {j : Nat}
    (hG : inRegion (d + 2) T G = true) (hGj : G.coeff d < j)
    (hr : inRegion (d + 1) (slot (d + 2) T j) r = true) : G < r :=
  Inner.slot_rows_lt (j := G.coeff d) (RowLaw.inRegion_slot_iff.mpr ⟨hG, rfl⟩) hr hGj

/-- **The claim along the path of `p`.** -/
theorem claim {ctx : Context} (rX : RunCtx s ctx t root) (hblk : ctx.block ≠ 0)
    (hsrc : ctx.source = M) (hrc : ctx.rootColumn = root.column)
    {Bc : Nat} (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R Bc d T)
    (hVR : MountainValid R)
    (hMD : Proofs.CopyShape.FactMD ctx (official t.row))
    (hMH : Proofs.CopyShape.FactMH ctx (official t.row))
    {p : Emit × Origin} {cz : Cell} (hcz : cell? M p.2.src = some cz) {rr : Row}
    (hrz : rr < official cz.row) :
    ∀ d A, InTree ctx (official t.row) (d + 2) A →
      Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) A → A.clean = none →
      ∀ ρr ρc, topIn M root.column (d + 2) A.source = some (ρr, ρc) → official ρc.row = rr →
      (A.cutBottom = false → ascends ctx (some (ρr, ρc)) = .ok true ∧
        ∃ q, topIn R Bc (d + 2) A.target = some q ∧
          (((official q.2.row).coeff d : Nat) : Int) = ((height (d + 2) rr : Nat) : Int) +
            (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) A.source) : Nat) : Int) -
              ((height (d + 2) rr : Nat) : Int)) * (ctx.block : Int)) →
      (∀ q ∈ realNodes R Bc, official q.2.row < official t.row →
        inRegion (d + 2) A.target (official q.2.row) = true ∨ official q.2.row < p.1.row) →
      ∀ TA, runItemT ctx (d + 2) A = .ok TA → p ∈ TA →
      ∀ q ∈ realNodes R Bc, official q.2.row < official t.row → official q.2.row < p.1.row := by
  have hV : MountainValid ctx.source := build_valid_of_success rX.top.build
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro A hA hinv hcl ρr ρc hρ hρr hcase hINV TA hTA hp
  obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTA
  obtain ⟨hlenF, hgetF⟩ := forall₂_getElem hF
  obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
  obtain ⟨j, hjo, rfl⟩ := List.getElem_of_mem hL'
  have hj : j < cs.length := by omega
  have hcT : InTree ctx (official t.row) (d + 1) cs[j] :=
    LowerLeftProof.inTree_snoc hA hcs (List.getElem_mem hj)
  have hAOK := (LowerLeftProof.inTree_itemOK rX hA).2
  obtain ⟨hcOK, hctgt⟩ := child_itemOK rX hAOK hcs j hj
  have hpreg := runItemT_region rX (by omega) hcOK (hgetF j hj hjo) p hpL'
  rw [hctgt] at hpreg
  have hinvc := (Inner.childItems_order hcs hinv).1 cs[j] (List.getElem_mem hj)
  have hEOK := (Proofs.CopyShape.NoMA.runItemT_shapeW ctx (official t.row) R Bc hV
    (by omega) hbnd hMD hMH d cs[j] outs[j] (hgetF j hj hjo) (reach_of_inTree hcT) hinvc).1 p hpL'
  obtain ⟨_, _, c', hc', hsreg, hsclean, _⟩ := hEOK
  have hc'' : cell? M p.2.src = some c' := by
    have : cell? ctx.source p.2.src = some c' := hc'
    rw [hsrc] at this; exact this
  have ec : cz = c' := Option.some.inj (hcz.symm.trans hc'')
  subst ec
  -- the rows `rr` and `ρ_z`
  have hrrS : inRegion (d + 2) A.source rr = true := by
    rw [← hρr]; exact Classification.topIn_inRegion hρ
  have hρ' : topIn ctx.source ctx.rootColumn (d + 2) A.source = some (ρr, ρc) := by
    rw [hsrc, hrc]; exact hρ
  have hhR : height (d + 2) (official ρc.row) = rr.coeff d := by
    rw [hρr]; show rr.coeff (d + 2 - 2) = rr.coeff d; rfl
  -- the top of `x` in the source region
  obtain ⟨ax, hax⟩ : ∃ ax, topIn ctx.source ctx.x (d + 2) A.source = some ax := by
    cases h : topIn ctx.source ctx.x (d + 2) A.source with
    | none =>
      have := childItems_none hcs h
      rw [this] at hj; simp at hj
    | some ax => exact ⟨ax, rfl⟩
  -- the rows of `B` in the target region
  have hBtop : ∀ q ∈ realNodes R Bc, inRegion (d + 2) A.target (official q.2.row) = true →
      ∃ qt, topIn R Bc (d + 2) A.target = some qt ∧
        (official q.2.row).coeff d ≤ (official qt.2.row).coeff d :=
    fun q hq hin => coeff_le_top hVR hq hin
  -- the source slot of `p` is at least `h_ρ`
  have hσge : ∀ σ, inRegion (d + 1) (slot (d + 2) A.source σ) (official cz.row) = true →
      rr.coeff d ≤ σ := by
    intro σ hσ
    obtain ⟨hzS, hzσ⟩ := RowLaw.inRegion_slot_iff.mp hσ
    rw [← hzσ]
    exact RowLaw.coeff_le_of_inRegion hrrS hzS hrz.le
  -- no copy of the root row
  have hnoC : cs[j].clean ≠ some rr := by
    intro h
    have := hsclean _ h
    exact absurd (lt_of_lt_of_le hrz this) (lt_irrefl _)
  -- a child at a slot above the top of `B`
  have hdone : ∀ hb : Nat, (∀ q ∈ realNodes R Bc, inRegion (d + 2) A.target (official q.2.row) = true →
      (official q.2.row).coeff d ≤ hb) → hb < j →
      ∀ q ∈ realNodes R Bc, official q.2.row < official t.row → official q.2.row < p.1.row := by
    intro hb hbnd' hbj q hq hqτ
    rcases hINV q hq hqτ with hin | hlt
    · exact lt_of_slot hin (lt_of_le_of_lt (hbnd' q hq hin) hbj) hpreg
    · exact hlt
  -- the cut-bottom child at the slot `hb` of the top of `B`
  have hdown : ∀ hb : Nat, (∀ q ∈ realNodes R Bc, inRegion (d + 2) A.target (official q.2.row) = true →
      (official q.2.row).coeff d ≤ hb) → j = hb → 1 ≤ d →
      cs[j].source = slot (d + 2) A.source (rr.coeff d) → cs[j].clean = none →
      cs[j].cutBottom = true →
      ∀ q ∈ realNodes R Bc, official q.2.row < official t.row → official q.2.row < p.1.row := by
    intro hb hbnd' hjb hd1 hcsrc hccl hccb
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hρc : topIn M root.column (d' + 2) cs[j].source = some (ρr, ρc) := by
      rw [hcsrc]
      have := Inner.topIn_slot hρ
      rw [hρr] at this
      exact this
    refine IH d' (by omega) cs[j] hcT hinvc hccl ρr ρc hρc hρr (fun h => by rw [hccb] at h; cases h)
      ?_ outs[j] (hgetF j hj hjo) hpL'
    intro q hq hqτ
    rw [hctgt]
    rcases hINV q hq hqτ with hin | hlt
    · have hle := hbnd' q hq hin
      rcases Nat.lt_or_eq_of_le hle with hlt' | heq
      · exact Or.inr (lt_of_slot hin (by omega) hpreg)
      · left
        exact RowLaw.inRegion_slot_iff.mpr ⟨hin, by omega⟩
    · exact Or.inr hlt
  have hhr : height (d + 2) rr = rr.coeff d := rfl
  cases hcb : A.cutBottom with
  | false =>
    obtain ⟨hasc, qB, hqB, hqBco⟩ := hcase hcb
    obtain ⟨_, hget⟩ := kids2 hcs hcl hcb hax hρ' hasc
    rw [hρr] at hget
    generalize hLift : (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) A.source) :
      Nat) : Int) - ((height (d + 2) rr : Nat) : Int)) * (ctx.block : Int) = lift at hget hqBco
    rw [hhr] at hget hqBco
    have hbndB : ∀ q ∈ realNodes R Bc, inRegion (d + 2) A.target (official q.2.row) = true →
        (official q.2.row).coeff d ≤ (official qB.2.row).coeff d := by
      intro q hq hin
      obtain ⟨qt, hqt, hle⟩ := hBtop q hq hin
      rw [hqB] at hqt
      obtain rfl := Option.some.inj hqt
      exact hle
    have hcj := hget j hj
    rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := ctx.block)
      (hR := rr.coeff d) (lift := lift) (C := rr) j with ⟨hjlt, hk⟩ | ⟨_, _, hk⟩ |
        ⟨_, hge2, hks, hkc, hkb⟩
    · rw [hcj, hk] at hsreg
      have := hσge j hsreg
      omega
    · exact absurd (by rw [hcj, hk]) hnoC
    · rw [hcj, hks] at hsreg
      have hσ := hσge _ hsreg
      by_cases hjeq : (j : Int) = (rr.coeff d : Int) + lift
      · -- the cut-bottom child
        have hd1 : 1 ≤ d := by
          by_contra hd0
          have : d = 0 := by omega
          subst this
          simp only [if_true] at hge2
          omega
        refine hdown ((official qB.2.row).coeff d) hbndB (by omega) hd1 ?_ ?_ ?_
        · rw [hcj, hks]
          congr 1
          omega
        · rw [hcj]; exact hkc
        · rw [hcj, hkb]
          simp only [decide_eq_true_eq]
          exact ⟨hblk, hjeq⟩
      · exact hdone ((official qB.2.row).coeff d) hbndB (by omega)
  | true =>
    have hasc : ascends ctx (some (ρr, ρc)) = .ok true := by
      have := asc_true_of_kind hcs hax (Or.inr hcb)
      rw [hρ'] at this; exact this
    obtain ⟨_, hget⟩ := kids3 hcs hcl hcb hblk hax hρ' hasc
    rw [hbnd, hρr, hhr] at hget
    generalize hhB : heightOf (d + 2) (topIn R Bc (d + 2) A.target) = hB at hget
    have hbndB : ∀ q ∈ realNodes R Bc, inRegion (d + 2) A.target (official q.2.row) = true →
        (official q.2.row).coeff d ≤ hB := by
      intro q hq hin
      obtain ⟨qt, hqt, hle⟩ := hBtop q hq hin
      rw [← hhB, hqt]
      exact hle
    have hcj := hget j hj
    rcases c3_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := rr.coeff d) (hB := hB) (C := rr) (j + rr.coeff d) with ⟨_, hk⟩ | ⟨hge2, hk⟩
    · exact absurd (by rw [hcj, hk]) hnoC
    · rw [hcj, hk] at hsreg
      have hσ := hσge _ hsreg
      by_cases hjeq : j = hB
      · have hd1 : 1 ≤ d := by
          by_contra hd0
          have : d = 0 := by omega
          subst this
          simp only [if_true] at hge2
          omega
        refine hdown hB hbndB hjeq hd1 ?_ ?_ ?_
        · rw [hcj, hk]
          simp only
          congr 1
          omega
        · rw [hcj, hk]
        · rw [hcj, hk]
          simp only [decide_eq_true_eq]
          omega
      · exact hdone hB hbndB (by omega)

end OmegaY.Official.Recon.LRC.SRT

#print axioms OmegaY.Official.Recon.LRC.SRT.claim
