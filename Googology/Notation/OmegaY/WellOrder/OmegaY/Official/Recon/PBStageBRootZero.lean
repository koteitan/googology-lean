/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBRootZero.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `rootShadowZero` the `simp` proving `hcb` is followed by `rfl`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBRootPos
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBBnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawAscend
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBGenLeg

set_option backward.do.legacy false

/-!
# `RootShadowZero` holds (stage B)

`RootShadowZero` (`PBStageBRoot.lean`): `RootShadowOut` for the root column `c_r = 0`.

## Proof

* The first column has only its bottom node (`col0_only`), so the root is that node, with the
  official row `0`, and the top row is `τ = ω^J` (`tau_shape`, from `topBump`). There is one first
  region `L = [0, ω^J)` (level `J + 1`), and `0 ∈ L`; every region containing `0` has the root top
  `0` at height `0`.
* The copy of `x` ascends at the root (`ascends_of_root_leg`, from the node whose leg is the root
  column), unless the emit `e` is the plain copy of the bottom node of `x`, at the row `0`
  (`Ψ_zero`), and then there is nothing to show.
* So in `L` the copy of `x` is in case 2 with `h_ρ = 0`: every child is a clean copy of the root
  row, a gap copy, or a cut-bottom item, up to the slot `L_X = h_κ·i`. These items emit every row
  of the boundary column in their target (`coverAll`).
* The boundary column is the copy of `x₀` in block `i - 1`; its rows in `L` are in the slots
  `≤ h_κ + h_κ·(i - 1) = h_κ·i` (`bnd_slot`).
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve
open Classification.Proofs Classification.Proofs.CopyShape.PBStageB
open Classification.Proofs.CopyShape Classification.Proofs.CopyShape.InnerRow

/-! ## The first column and the top row -/

theorem col0_row {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {p : Ref × Cell} (hp : p ∈ realNodes M 0) : official p.2.row = 0 := by
  obtain ⟨hc, hi, hcell⟩ := Classification.mem_realNodes hp
  have hp1 : p.1 = ⟨0, p.1.index⟩ := by rw [← hc]
  rw [hp1] at hcell
  have h1 := col0_only hb hcell hi
  rw [h1] at hcell
  exact bottom_official hb hcell

theorem tau_shape {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) (h0 : root.column = 0) :
    ∃ J, ∀ k, (official t.row).coeff k = if k = J then 1 else 0 := by
  obtain ⟨rc, a, J, hrc, hri, hτ, hag, _⟩ := topBump hTop
  have hmem : (root, rc) ∈ realNodes M root.column :=
    CopyShape.mem_realNodes_of_cell' (p := root) hrc hri
  rw [h0] at hmem
  have hr0 := col0_row hTop.build hmem
  refine ⟨J, fun k => ?_⟩
  rw [hτ]
  rcases Nat.lt_trichotomy k J with hk | rfl | hk
  · rw [Recon.RowLaw.bump_coeff_low hk, if_neg (by omega)]
  · rw [Recon.RowLaw.bump_coeff_at, if_pos rfl, hag k le_rfl]
    simp only at hr0
    rw [hr0, Row.coeff_zero]
  · rw [Recon.RowLaw.bump_coeff_high hk, if_neg (by omega), hag k hk.le]
    simp only at hr0
    rw [hr0, Row.coeff_zero]

theorem Ψ_zero (E : Env) (top : Nat → Row → Option (Ref × Cell)) :
    ∀ (d : Nat) (S : Row), inRegion (d + 1) S 0 = true → Ψ E top false (d + 1) S S 0 = 0
  | 0, S, h => by rw [Ψ_one]; exact (inRegion_one h).symm
  | d + 1, S, h => by
      have hs : inRegion (d + 1) (slot (d + 2) S ((0 : Row).coeff d)) 0 = true := slot_mem h
      cases ht : top (d + 2) S with
      | none =>
          rw [ΨF_none ht]
          exact Ψ_zero E top d _ hs
      | some p =>
          obtain ⟨ρr, ρc⟩ := p
          rw [ΨF_low ht (Row.zero_le _)]
          exact Ψ_zero E top d _ hs

/-! ## The setting -/

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
  {X i x : Nat} {lo us : List (Emit × Origin)}

/-- **The copy of `x` ascends at the root, or `e` is at the row `0`.** -/
theorem ascZero (hD : ColData s n R M t root X i x lo us) (hi1 : 1 ≤ i) (h0 : root.column = 0)
    {e : Emit × Origin} (he : e ∈ lo ++ us) (hlc : e.1.leftColumn = some root.column) :
    (∀ ρ : Ref × Cell, official ρ.2.row = 0 →
      ascends (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) (some ρ) =
        .ok true) ∨ e.1.row = 0 := by
  have hb := hD.top.build
  have hVM := build_valid_of_success hb
  have hxg := hD.xgt
  obtain ⟨rc, _, _, hrc, hri, _, _, _⟩ := topBump hD.top
  have hrmem : (root, rc) ∈ realNodes M root.column :=
    CopyShape.mem_realNodes_of_cell' (p := root) hrc hri
  have hr0 : official rc.row = 0 := by
    have := hrmem; rw [h0] at this; exact col0_row hb this
  -- ascension from a node of `x` whose leg is the root column
  have hasc : ∀ (q : Ref × Cell), q ∈ realNodes M x → official q.2.row ≠ 0 →
      leftColumn q.2 = .ok root.column →
      ∀ ρ : Ref × Cell, official ρ.2.row = 0 →
        ascends (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) (some ρ) =
          .ok true := by
    intro q hq hθ hl ρ hρ
    have hps : JumpLaw.HighestBelow (RowLaw.rowsOf M root.column) (official q.2.row) 0 := by
      refine ⟨?_, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨(root, rc), hrmem, hr0⟩
      · exact lt_of_le_of_ne (Row.zero_le _) (Ne.symm hθ)
      · intro r hr _
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        rw [h0] at hp
        rw [col0_row hb hp]
    have h1 := JumpLaw.ascends_of_root_leg hb (ctxX := ctxAt M R x i root.column
      (M.size - 1 - root.column) (M.size - 1) X) rfl hq hθ hl hps hrmem (le_of_eq hr0)
    rw [CopyShape.PBStageB.ascends_row (ctx := ctxAt M R x i root.column
      (M.size - 1 - root.column) (M.size - 1) X) (a := ρ) (b := (root, rc)) (by rw [hρ, hr0])]
    exact h1
  rcases List.mem_append.mp he with hel | heu
  · obtain ⟨k, co, hsrc, hk, hco, hleft⟩ := lowerT_src hD.hlo hel
    change cell? M ⟨x, k⟩ = some co at hco
    obtain ⟨l, hl, hlc2⟩ : ∃ l : Ref, co.left = some l ∧ e.1.leftColumn = some l.column := by
      rcases hleft with h | ⟨hn, _⟩
      · exact h
      · rw [hn] at hlc; cases hlc
    have hlr : l.column = root.column := by rw [hlc2] at hlc; exact Option.some.inj hlc
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- the bottom node of `x`
      have hk1' : k = 1 := by omega
      subst hk1'
      have hco0 : official co.row = 0 := bottom_official hb hco
      have hcoe : cell? M e.2.src = some co := by rw [hsrc]; exact hco
      cases hcut : cutO e.2 with
      | true =>
          left
          obtain ⟨_, _, _, _, _, _, ⟨d0, S0, ρ0, _, hρ0row, hρ0asc⟩⟩ :=
            CopyShape.ProfileLeg.lowerT_cut hD.run hD.top hi1 hD.iln hD.bctx hD.hlo e hel hcut co
              hcoe
          intro ρ hρ
          rw [CopyShape.PBStageB.ascends_row (a := ρ) (b := ρ0) (by rw [hρ, hρ0row, hco0])]
          exact hρ0asc
      | false =>
          right
          obtain ⟨q, hq, hqin, hrow⟩ := CopyShape.ProfileLeg.lowerT_formula hD.run hD.top hi1
            hD.iln hD.bctx hD.hlo e hel hcut co hcoe
          obtain ⟨kk, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
          rw [hkj] at hqin hrow
          rw [hco0] at hqin hrow
          rw [hrow]
          exact Ψ_zero _ _ kk _ hqin
    · left
      obtain ⟨cl, J', _, _, hrow⟩ := below_bump hb hk2 hco
      have hθ : official co.row ≠ 0 := by
        rw [hrow]; exact ne_of_gt (lt_of_le_of_lt (Row.zero_le _) (Row.lt_bump _ _))
      refine hasc (⟨x, k⟩, co) (CopyShape.mem_realNodes_of_cell' (p := ⟨x, k⟩) hco
        (by omega)) hθ ?_
      rw [← hlr]
      exact Recon.leftColumn_of hl
  · left
    obtain ⟨k, c, hk, hc, _, hrow, hτc, l, hl, hlc2⟩ := (upperT_spec hD.hus).1 e heu
    rw [upperColumn_ctxAt] at hc
    have hlr : l.column = root.column := by rw [hlc2] at hlc; exact Option.some.inj hlc
    have hxx : x ≠ M.size - 1 := by
      intro hx0
      rw [if_pos hx0] at hc
      have := left_lt hVM hc hl
      omega
    rw [if_neg hxx] at hc
    have hθ : official c.row ≠ 0 := by
      intro h
      rw [h] at hτc
      exact hD.top.real (le_antisymm hτc (Row.zero_le _))
    refine hasc (⟨x, k⟩, c) (CopyShape.mem_realNodes_of_cell' (p := ⟨x, k⟩) hc hk)
      hθ ?_
    rw [← hlr]
    exact Recon.leftColumn_of hl

/-! ## The first region -/

theorem first_item {τ : Row} {J : Nat} (hJ : ∀ k, τ.coeff k = if k = J then 1 else 0)
    {q0 : Nat × Item} (hq0 : q0 ∈ lowerItems τ) :
    q0 = (J + 1, ⟨slot (J + 2) τ 0, slot (J + 2) τ 0, none, 0, false⟩) := by
  obtain ⟨k, j, _, hj, rfl⟩ := Recon.RowLaw.mem_lowerItems hq0
  rw [hJ k] at hj
  by_cases hk : k = J
  · subst hk
    have : j = 0 := by simp at hj; omega
    subst this; rfl
  · rw [if_neg hk] at hj; omega

theorem zero_in {τ : Row} {J : Nat} (hJ : ∀ k, τ.coeff k = if k = J then 1 else 0) :
    inRegion (J + 1) (slot (J + 2) τ 0) 0 = true := by
  refine Recon.RowLaw.inRegion_slot_iff.mpr ⟨?_, Row.coeff_zero _⟩
  rw [Recon.RowLaw.inRegion_iff']
  intro q hq
  rw [Row.coeff_zero, hJ q, if_neg (by omega)]

/-- **The rows of the boundary column in the first region are in the slots `≤ h_κ·i`.** -/
theorem bnd_slot (hD : ColData s n R M t root X i x lo us) (hi1 : 1 ≤ i)
    (h0 : root.column = 0) {J : Nat}
    (hJ : ∀ k, (official t.row).coeff k = if k = J then 1 else 0) {d : Nat} (hJd : J = d + 1)
    (hqR : root.column + (M.size - 1 - root.column) * i < R.size) {kz : Nat}
    (hkz : kz < (R[root.column + (M.size - 1 - root.column) * i]'hqR).size) (hkz1 : 1 ≤ kz)
    (hzτ : official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row <
      official t.row) :
    (official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row).coeff d ≤
      heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0)) * i := by
  have hcr := hD.top.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨i', x', loA, usA, hDA⟩ := colData hD.run hD.top hD.ci hD.inv hqR (by omega)
  obtain ⟨hx', hii⟩ := CutPredMD.boundary_source hcr (by omega) hDA.xb hDA.Xeq.symm
  -- the emit of `z`
  obtain ⟨hk', hrow, _⟩ := hDA.node hkz hkz1
  have hrow' : official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row =
      (loA ++ usA)[kz - 1].1.row := by rw [hrow, official_stored']
  have hlo : kz - 1 < loA.length := by
    by_contra hn
    have hmem : (loA ++ usA)[kz - 1] ∈ usA := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := hDA.us_ge _ hmem
    rw [← hrow'] at this
    exact absurd hzτ (not_lt.mpr this)
  have hpmem : (loA ++ usA)[kz - 1] ∈ loA := by
    rw [List.getElem_append_left hlo]; exact List.getElem_mem _
  set pA := (loA ++ usA)[kz - 1] with hpA
  -- the first item of `pA`
  have hlA := hDA.hlo
  unfold lowerT at hlA
  simp only [bind, Except.bind, pure, Except.pure] at hlA
  split at hlA
  · cases hlA
  · rename_i outsA houtsA
    cases hlA
    obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hpmem
    obtain ⟨q0, hq0, hq0out⟩ := mem_of_mapM houtsA hout
    have hq0e := first_item hJ hq0
    subst hq0e
    rw [hJd] at hq0out
    simp only at hq0out
    obtain ⟨csA, outsA', hchA, hmA, rfl⟩ := CopyShape.PBStageB.runItemT_step' hq0out
    obtain ⟨out', hout', hpo'⟩ := List.mem_flatten.mp hpo
    obtain ⟨cA, hcA, hcAout⟩ := mem_of_mapM hmA hout'
    have htA := CopyShape.PBStageB.runItemT_target _ d cA out' hcAout pA hpo'
    have hcase := CopyShape.PBStageB.childItems_cases hchA
    have hslot : ∀ j, cA.target = slot (d + 2) (slot (d + 3) (official t.row) 0) j →
        (official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row).coeff d
          = j := by
      intro j hj
      rw [hj] at htA
      rw [hrow']
      exact (Recon.RowLaw.inRegion_slot_iff.mp htA).2
    have hxA : (ctxAt M R x' i' root.column (M.size - 1 - root.column) (M.size - 1)
        (root.column + (M.size - 1 - root.column) * i)).x = M.size - 1 := hx'
    cases hcase with
    | none _ => simp at hcA
    | case1 a ha _ _ _ _ =>
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcA
        rw [hslot j rfl]
        have hj' := List.mem_range.mp hj
        simp only [ctxAt] at ha
        rw [hx'] at ha
        have : height (d + 2) (official a.2.row) =
            heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0)) := by
          rw [ha]; rfl
        have hle : heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0))
            ≤ heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0)) * i :=
          Nat.le_mul_of_pos_right _ hi1
        omega
    | case2 a ha ρr ρc hρ _ _ _ LA eA hLA _ =>
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcA
        have htg : (ChainCorr.CopyMonoProof.c2 (slot (d + 3) (official t.row) 0)
            (slot (d + 3) (official t.row) 0) (official ρc.row) d
            (height (d + 2) (official ρc.row)) LA eA
            (ctxAt M R x' i' root.column (M.size - 1 - root.column) (M.size - 1)
              (root.column + (M.size - 1 - root.column) * i)).block j).target =
            slot (d + 2) (slot (d + 3) (official t.row) 0) j := by
          unfold ChainCorr.CopyMonoProof.c2; split_ifs <;> rfl
        rw [hslot j htg]
        have hρm := (Recon.RowLaw.topIn_spec hρ).1
        simp only [ctxAt] at hρm
        rw [h0] at hρm
        have hR0 : height (d + 2) (official ρc.row) = 0 := by
          show (official ρc.row).coeff d = 0
          rw [col0_row hD.top.build hρm]; exact Row.coeff_zero _
        simp only [ctxAt] at ha
        rw [hx'] at ha
        have hHa : height (d + 2) (official a.2.row) =
            heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0)) := by
          rw [ha]; rfl
        have hj' := List.mem_range.mp hj
        rw [hHa, hLA, hR0] at hj'
        simp only [ctxAt] at hj'
        set hC := heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0))
        have e1 : ((hC : Int) - ((0 : Nat) : Int)) * (i' : Int) = ((hC * i' : Nat) : Int) := by
          rw [Int.natCast_mul]; simp
        have e2 : hC * i = hC * i' + hC := by rw [← hii, Nat.mul_succ]
        rw [e1] at hj'
        omega
    | case3 _ _ _ _ _ _ _ hcb _ _ => simp at hcb
    | case4 _ _ _ _ _ _ _ hcl _ _ _ _ _ _ => simp at hcl

/-! ## The theorem -/

/-- **`RootShadowZero` holds.** -/
theorem rootShadowZero : RootShadowZero := by
  intro s n R M t root X i x lo us hD hi1 h0 e he hlc q hq hqR kz hkz hkz1 hzτ hze
  subst hq
  have hb := hD.top.build
  have hVM := build_valid_of_success hb
  obtain ⟨_, _, _, _, hBR⟩ := run_basic hD.run
  have hVR : MountainValid R := hBR.valid
  have hxg := hD.xgt
  have hxl := hD.xle
  obtain ⟨J, hJ⟩ := tau_shape hD.top h0
  rcases ascZero hD hi1 h0 he hlc with hasc | he0
  swap
  · rw [he0] at hze; exact absurd hze (not_lt.mpr (Row.zero_le _))
  -- the first region
  obtain ⟨k0, j0, hmem0, hin0⟩ := CutPredMD.lowerItems_cover hzτ
  have hfi := first_item hJ hmem0
  have hk0 : k0 = J := by have := congrArg Prod.fst hfi; simp only at this; omega
  subst hk0
  have hsl : slot (k0 + 2) (official t.row) j0 = slot (k0 + 2) (official t.row) 0 := by
    have := congrArg (fun p : Nat × Item => p.2.source) hfi; simpa using this
  rw [hsl] at hin0
  rw [hfi] at hmem0
  -- the node of `z`
  have hzB : ((⟨root.column + (M.size - 1 - root.column) * i, kz⟩ : Ref),
      (R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz) ∈
        realNodes R (root.column + (M.size - 1 - root.column) * i) :=
    CopyShape.mem_realNodes_of_cell' (p := ⟨root.column + (M.size - 1 - root.column) * i, kz⟩)
      (by simp [cell?, Array.getElem?_eq_getElem hqR, Array.getElem?_eq_getElem hkz]) hkz1
  -- the bottom node of `x`
  have hxs : x < M.size := by have := hD.top.lt; omega
  have hxsz := (hVM x hxs).size_ge_two
  have hcb : cell? M ⟨x, 1⟩ = some (M[x]'hxs)[1] := by
    simp [cell?, Array.getElem?_eq_getElem hxs, Array.getElem?_eq_getElem (show 1 < M[x].size by omega)]
    rfl
  have hcb0 : official ((M[x]'hxs)[1]).row = 0 := bottom_official hb hcb
  have hXb : XNode M x 0 :=
    ⟨(⟨x, 1⟩, (M[x]'hxs)[1]), CopyShape.mem_realNodes_of_cell' (p := ⟨x, 1⟩) hcb le_rfl, hcb0⟩
  -- the run of the copy of `x` on the first region
  have hlX := hD.hlo
  unfold lowerT at hlX
  simp only [bind, Except.bind, pure, Except.pure] at hlX
  split at hlX
  · cases hlX
  · rename_i outs houts
    cases hlX
    obtain ⟨out0, hout0, hrun0⟩ := CopyShape.PBStageB.mapM_ok_of_mem' houts hmem0
    have hsub : ∀ p ∈ out0, p ∈ outs.flatten := fun p hp => List.mem_flatten.mpr ⟨out0, hout0, hp⟩
    cases k0 with
    | zero =>
        -- the region is the row `0`
        have h1 : levelOneT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
            ⟨slot 2 (official t.row) 0, slot 2 (official t.row) 0, none, 0, false⟩ = .ok out0 := by
          simpa [runItemT] using hrun0
        have h00 : (0 : Row) = slot 2 (official t.row) 0 := inRegion_one (zero_in hJ)
        have hn : ∃ q, nodeAt M x (slot 2 (official t.row) 0) = some q := by
          rw [← h00]
          obtain ⟨p, hp⟩ := Recon.RowLaw.nodeAt_of_mem
            (CopyShape.mem_realNodes_of_cell' (p := ⟨x, 1⟩) hcb le_rfl)
          rw [hcb0] at hp
          exact ⟨p, hp⟩
        obtain ⟨p, hp, hpr⟩ := levelOne_emits_target h1 hn
        refine ⟨p, hsub p hp, ?_⟩
        rw [hpr]
        exact (inRegion_one hin0).symm
    | succ d =>
        obtain ⟨cs, outs', hch, hm, rfl⟩ := CopyShape.PBStageB.runItemT_step' hrun0
        have hcase := CopyShape.PBStageB.childItems_cases hch
        -- the root top and the top of `x` in the first region
        have hL0 := zero_in hJ
        obtain ⟨rc, _, _, hrc, hri, _, _, _⟩ := topBump hD.top
        have hrmem : (root, rc) ∈ realNodes M root.column :=
          CopyShape.mem_realNodes_of_cell' (p := root) hrc hri
        have hr0 : official rc.row = 0 := by
          have := hrmem; rw [h0] at this; exact col0_row hb this
        cases hcase with
        | none hn =>
            have := topIn_ne_none_of_node (p := ⟨x, 1⟩) rfl le_rfl hcb (by rw [hcb0]; exact hL0)
            exact absurd hn this
        | case1 a ha hasc1 _ _ _ =>
            obtain ⟨ρ, hρ⟩ : ∃ ρ, topIn M root.column (d + 1 + 1)
                (slot (d + 1 + 2) (official t.row) 0) = some ρ := by
              cases h' : topIn M root.column (d + 1 + 1) (slot (d + 1 + 2) (official t.row) 0) with
              | none => exact absurd h' (topIn_ne_none_of_node (p := root) rfl hri hrc
                  (by rw [hr0]; exact hL0))
              | some ρ => exact ⟨ρ, rfl⟩
            have hρ0 : official ρ.2.row = 0 := by
              have hm := (Recon.RowLaw.topIn_spec hρ).1
              rw [h0] at hm; exact col0_row hb hm
            have hρ' : topIn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
                X).source (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
                X).rootColumn (d + 1 + 1) (slot (d + 1 + 2) (official t.row) 0) = some ρ := hρ
            rw [hρ', hasc ρ hρ0] at hasc1
            cases hasc1
        | case3 _ _ _ _ _ _ _ hcb' _ _ => simp at hcb'
        | case4 _ _ _ _ _ _ _ hcl _ _ _ _ _ _ => simp at hcl
        | case2 a ha ρr ρc hρ hascX _ _ LX eX hLX heX =>
            simp only [ctxAt] at hρ
            have hρm := (Recon.RowLaw.topIn_spec hρ).1
            rw [h0] at hρm
            have hρ0 : official ρc.row = 0 := col0_row hb hρm
            have hR0 : height (d + 2) (official ρc.row) = 0 := by
              show (official ρc.row).coeff d = 0
              rw [hρ0]; exact Row.coeff_zero _
            have hRe : Reach (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
                (official t.row) (d + 2)
                ⟨slot (d + 3) (official t.row) 0, slot (d + 3) (official t.row) 0, none, 0, false⟩ :=
              Reach.top hmem0
            have hMD := CopyShape.Found.factMD_of_bctx hD.top hD.bctx d _ hRe ρr ρc hρ hascX
            have hbs := bnd_slot hD hi1 h0 hJ rfl hqR hkz hkz1 hzτ
            set hC := heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 3) (official t.row) 0))
            have hMD' : 0 < hC := by
              have : heightOf (d + 2) (some (ρr, ρc)) = height (d + 2) (official ρc.row) := rfl
              simp only [ctxAt] at hMD
              omega
            have hLX' : LX = ((hC * i : Nat) : Int) := by
              rw [hLX, hR0]; simp only [ctxAt]; push_cast; simp; exact Or.inl rfl
            set jz := (official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row).coeff d
            have he01 : 0 ≤ eX ∧ eX ≤ 1 := by rw [heX]; split <;> omega
            have hblk : (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X).block
                ≠ 0 := by show i ≠ 0; omega
            have hrt : ChainCorr.CopyMonoProof.rootTop
                (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
                (d + 2) (slot (d + 3) (official t.row) 0) = some (official ρc.row) :=
              rootTop_of_topIn (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
                (M.size - 1) X) (M := M) (cr := root.column) rfl rfl hρ
            have hrts := ChainCorr.CopyMonoProof.rootTop_slot hrt
            have htps := ChainCorr.Inner.topIn_slot hρ
            have hXρ : XNode M x (official ρc.row) := by rw [hρ0]; exact hXb
            have hC0q : ∀ q, (official ρc.row).coeff q = 0 := by
              intro q; rw [hρ0]; exact Row.coeff_zero _
            let c := ChainCorr.CopyMonoProof.c2 (slot (d + 3) (official t.row) 0)
              (slot (d + 3) (official t.row) 0) (official ρc.row) d
              (height (d + 2) (official ρc.row)) LX eX
              (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X).block jz
            generalize hP : hC * i = P at hbs hLX'
            have hct : c.target = slot (d + 2) (slot (d + 3) (official t.row) 0) jz := by
              show (ChainCorr.CopyMonoProof.c2 _ _ _ _ _ _ _ _ _).target = _
              unfold ChainCorr.CopyMonoProof.c2; split_ifs <;> rfl
            have hInv : InvCov (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
                M root.column (d + 1) c := by
              show InvCov _ M root.column (d + 1) (ChainCorr.CopyMonoProof.c2 _ _ _ _ _ _ _ _ _)
              unfold ChainCorr.CopyMonoProof.c2
              rw [if_neg (by omega)]
              by_cases h2 : (jz : Int) < (height (d + 2) (official ρc.row) : Int) + LX + eX
              · rw [if_pos h2]
                by_cases hz0 : jz = 0
                · have hd : decide (height (d + 2) (official ρc.row) < jz) = false :=
                    decide_eq_false (by omega)
                  rw [hd]
                  exact Or.inr (Or.inr ⟨official ρc.row, rfl, rfl, hC0q, hrts, hXρ⟩)
                · have hd : decide (height (d + 2) (official ρc.row) < jz) = true :=
                    decide_eq_true (by omega)
                  rw [hd]
                  exact Or.inl ⟨official ρc.row, rfl, rfl, hrts, hXρ,
                    fun _ _ _ _ _ => Nat.zero_le _⟩
              · rw [if_neg h2]
                have hjz : jz = P := by omega
                have hidx : ((jz : Int) - LX).toNat = (official ρc.row).coeff d := by
                  rw [hρ0, Row.coeff_zero]; omega
                refine Or.inr (Or.inl ⟨rfl, decide_eq_true ⟨hblk, by rw [hR0]; omega⟩,
                  (ρr, ρc), ?_, hXρ⟩)
                show topIn M root.column (d + 1)
                  (slot (d + 2) (slot (d + 3) (official t.row) 0) ((jz : Int) - LX).toNat) = _
                rw [hidx]; exact htps
            have hzt : inRegion (d + 1) c.target
                (official ((R[root.column + (M.size - 1 - root.column) * i]'hqR)[kz]'hkz).row) =
                  true := by
              rw [hct]; exact slot_mem hin0
            have hbnd : ∀ d' T, topIn (ctxAt M R x i root.column (M.size - 1 - root.column)
                (M.size - 1) X).result (ctxAt M R x i root.column (M.size - 1 - root.column)
                (M.size - 1) X).boundary d' T =
                topIn R (root.column + (M.size - 1 - root.column) * i) d' T := by
              intro d' T
              exact CopyShape.Found.topIn_congr hD.bctx.bnd
            obtain ⟨outc, houtc, hcout⟩ := CopyShape.PBStageB.mapM_ok_of_mem' hm
              (List.mem_map.mpr ⟨jz, List.mem_range.mpr (by omega), rfl⟩)
            obtain ⟨p, hp, hpr⟩ := coverAll hVM hVR rfl rfl hblk hbnd d c outc hcout hInv _ hzB hzt
            exact ⟨p, hsub p (List.mem_flatten.mpr ⟨outc, houtc, hp⟩), hpr⟩

/-- **`RootShadowOut` holds** for `c_r = 0` (`rootShadowZero`); with `BoundaryPos` for `c_r ≥ 1`. -/
theorem rootShadowOut_of_boundaryPos' (hBP : BoundaryPos) : RootShadowOut :=
  rootShadowOut_of_boundaryPos CopyShape.PBStageB.cutLeg hBP rootShadowZero

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.rootShadowZero
