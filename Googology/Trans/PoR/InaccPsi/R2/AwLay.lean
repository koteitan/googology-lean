import Googology.Trans.PoR.InaccPsi.R2.AwImg

/-!
# AwLay: UPPER, LOWER, CapV AT EVERY RANGE RESTART BELOW `ι(Ω₂)`

The term system `Aw.awSys` of the code bound `K_{j+1}` (`AwH`, from `Aw.aw_Rd_lt`, `Aw.aw_pkg`, `Aw.aw_rs`) gives UPPER, LOWER, CapV
below `ι(ω^{K_{j+1}}·ω)`, and `P(Ω₂) ≤ sup_j P(K_{j+1} + W)` (`Zr.zrPv_le_sup`).

* `aw_H` (**THE HYPOTHESIS `AwH` AT `K_{j+1}`**), `aw_UV_K`, `aw_UV` (**EVERY RANGE RESTART BELOW `ι(Ω₂)`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zr
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- A restart index gives a strongly critical `υ`-point. -/
theorem aw_ri_SC (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    UpsPt (upsilon l) ∧ upsilon l < Om1 ∧ SC (upsilon l) := by
  have hU : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  have h1 : upsilon l < Om1 := ups_lt_Om1 l hl1
  exact ⟨hU, h1, aw_ups_SC S hU h1⟩

/-- `awNx (awNx (υ_l)) < υ_{l+ω+1}`. -/
theorem aw_mm_lt (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    awNx (awNx (upsilon l)) < upsilon (l + ω + 1) := by
  obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Gg.gg_one_lt_of_SC hSC).trans h1
  have hl' : l + 1 < Om1 := Om1_add_lt hl1 h1Ω
  have hU' : UpsPt (upsilon (l + 1)) := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one l))
  have hS2 : SC (upsilon (l + 1)) := aw_ups_SC S hU' (ups_lt_Om1 _ hl')
  rw [aw_Nx_ups hSC h1, aw_Nx_ups hS2 (ups_lt_Om1 _ hl')]
  refine upsilon_normal.strictMono ?_
  rw [add_assoc l 1 1, add_assoc l ω 1]
  refine (add_lt_add_iff_left l).2 (lt_of_lt_of_le ?_ le_self_add)
  rw [one_add_one_eq_two]
  exact_mod_cast natCast_lt_omega0 2

/-- **THE HYPOTHESIS `AwH` AT `K_{j+1}`.** -/
theorem aw_H (j : ℕ) : AwH S (zrK S (j + 1)) := by
  have hV : zrK S (j + 1) < awV S := zrK_lt_V _
  refine ⟨hV.le, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Gg.ggE_le (eN_E _) (lt_eN _)).trans_lt (Go.go_eN_lt_SC (zrK_SC j) (zrK_gt_Om1 j))
  · intro l hl hl1
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    have hcode : GxCl (upsilon l) (awAt S (upsilon l)) (zrK S (j + 1)) := GxCl.atom (aw_K_mem _ j)
    exact (aw_Rd_lt hSC h1 hcode).trans (aw_mm_lt S hl hl1)
  · intro l hl hl1 c hc1 hcT hcc R
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    refine aw_pkg R hSC hcc (hcT.trans hV) ?_
    exact (Order.one_le_iff_pos.2 hSC.1).trans (aw_val_ge (by rw [← Rj.rj_Om1]; exact h1.le) hc1)
  · intro l hl hl1 R
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    refine aw_pkg R hSC (GxCl.atom (aw_K_mem _ j)) hV ?_
    exact (Order.one_le_iff_pos.2 hSC.1).trans (aw_val_ge (by rw [← Rj.rj_Om1]; exact h1.le) (zrK_gt_Om1 j).le)
  · intro l hl hl1 c hc1 hcT hcc
    exact aw_rs hl1 (hcT.trans hV) hcc

/-- **UPPER, LOWER, CapV below `ι(K_{j+1}·ω)`.** -/
theorem aw_UV_K (j : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (zrK S (j + 1) * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hTE : ω ^ zrK S (j + 1) = zrK S (j + 1) := Low.opow_eq_self_of_SC (zrK_SC j)
  exact awUV (aw_H j) hTE (fun Z => GxCl.atom (aw_K_mem Z j)) hr (by rw [hTE]; exact hl)

/-- Every index below `ι(Ω₂)` lies below some `ι(K_{j+1}·ω)`. -/
theorem aw_below_K {l : Ordinal.{0}} (hl : l < iota S (Om (1 + 1))) : ∃ j, l < iota S (zrK S (j + 1) * ω) := by
  have hρ : upsilon l < Pv S (Om (1 + 1)) := by
    rw [zrIota_ri.2]; exact upsilon_normal.strictMono hl
  obtain ⟨j, hj⟩ := (lt_ciSup_iff zrSig_bdd).1 (hρ.trans_le zrPv_le_sup)
  have hle : zrK S (j + 1) + W ≤ zrK S (j + 1) * ω := by
    have hW : W < zrK S (j + 1) := Lw.lw_W_lt_SC (zrK_SC j) (zrK_gt_Om1 j)
    calc zrK S (j + 1) + W ≤ zrK S (j + 1) + zrK S (j + 1) := add_le_add le_rfl hW.le
      _ = zrK S (j + 1) * 2 := (mul_two_eq _).symm
      _ ≤ zrK S (j + 1) * ω := mul_le_mul_right (by exact_mod_cast (natCast_lt_omega0 2).le) _
  refine ⟨j, lt_of_lt_of_le ?_ (iota_mono _ _ hle)⟩
  have : upsilon l < upsilon (iota S (zrK S (j + 1) + W)) := by
    rw [ups_iota]; exact hj
  exact upsilon_normal.strictMono.lt_iff_lt.1 this

/-- **UPPER, LOWER, CapV AT EVERY RANGE RESTART BELOW `ι(Ω₂)`.** -/
theorem aw_UV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (Om (1 + 1))) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  obtain ⟨j, hj⟩ := aw_below_K hl
  exact aw_UV_K j hr hj

end Googology.Trans.PoR.InaccPsi.R2.Aw
