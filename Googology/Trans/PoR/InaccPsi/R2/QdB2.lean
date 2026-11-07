import Googology.Trans.PoR.InaccPsi.R2.QdLvD

/-!
# QdB2: `B₂ = Hᵛ_{E₂}(0)` — ITS DATA AND READING; THE READINGS BELOW `B₂` ARE BELOW IT

`B₂ = Uc.ucB` is fixed by every visible `Hᵛ_γ = H_γ`, `γ < E₂` (`Uc.ucB_spec` through `S`), and `Hᵛ_{E₂}` does not fix
it (`Us.us_fix_iff` at `E₂`, as in `Qd.qd_B2_lt_B3`): its level is `E₂` (`qd_B2_lev`).  Its index is `0`: `Hᵛ_{E₂}(0)`
is strongly critical above `Ω₁` and fixed by every visible lower level, so it has no normal form of `R2.UcDat` and is
`≥ B₂` (`qd_B2_idx`).  So `B₂` is a fixed point of `Γ` read `ϑˣ(Ω₁·(Ω₁ + E₂(x))) = ϑˣ(Ω₁·ε_{Ω₁+1})` (`qd_B2_read`),
with gate `0`.  Every code `c < B₂` with its gate below `x` reads below a generic-level point (`qd_low_bd`, from the
digit system at a fixed point `H_{γ_n}(0) > c` of `Qc.qcF_cof`), so below `ϑˣ(Ω₁·ε_{Ω₁+1})` (`qd_low_lt`).

* `qd_low_fix`, `qd_E2_noFix`, `qd_E2_mem`, `qd_B2_lev` (**the level of `B₂` is `E₂`**), `qd_B2_idx` (**its index is
  `0`**), `qd_B2_H`, `qd_B2_fix`, `qd_B2_gate`, `qd_B2_read` (**`B₂` reads `ϑˣ(Ω₁·ε_{Ω₁+1})`**);
* `qd_low_bd` (**every reading below `B₂` is `QcBd`**), `qd_gE_lt_gg`, `qd_low_lt` (**below `ϑˣ(Ω₁·ε_{Ω₁+1})`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Qc Googology.Trans.PoR.InaccPsi.R2.Vd
  Googology.Trans.PoR.InaccPsi.R2.Ul

theorem qd_one_lt_B2 : (1 : Ordinal.{0}) < ucB :=
  (show (1 : Ordinal.{0}) < Om1 by rw [Rj.rj_Om1]; exact Nm.one_lt_Om1).trans ucB_gt

variable (S : InaccSeq.{0})
include S

/-- **`B₂` is fixed by every visible level below `E₂`.** -/
theorem qd_low_fix {γ : Ordinal.{0}} (hγ : γ < ucE) (hC : qdFold id γ < ucB) : qdH γ ucB = ucB := by
  rw [qd_uc_H S hγ]; exact ucB_spec hγ ((qd_uc_vis S hγ ucB_SC ucB_gt).1 hC)

/-- **`Hᵛ_{E₂}` does not fix `B₂`.** -/
theorem qd_E2_noFix : qdH ucE ucB ≠ ucB := by
  rw [qdH_eq_ul S qd_E_lt_G2]
  intro hfix
  have hs : (1 : Ordinal.{0}) < ω := vd_one_lt_omega
  have hown : ucE ∈ S.CSet ucE (S.psi ucE (Om (1 + 1))) := by
    have h := Ui.ui_E_mem (S := S) hs ucE (S.psi ucE (Om (1 + 1))); rwa [Ui.ui_one_E] at h
  have hE0 : (ucE : Ordinal.{0}) ≠ 0 := (ucE_gt.trans' uc_SC_Om2.1).ne'
  have hEV : ucE < (Om (1 + 1 + 1) : Ordinal.{0}) := vd_E_lt_V
  rw [← uc_psiE_eq_B (S := S)] at hfix
  have hd := ((Us.us_fix_iff hs hown hE0 hEV).1 hfix).1
  have hle := Ordinal.le_of_dvd hE0 hd
  have hlt : ucE < Om (1 + 1) ^ (ucE + 1) :=
    (right_le_opow ucE (Ui.ui_one_lt_SC (Ui.ui_SC_W 1))).trans_lt
      ((opow_lt_opow_iff_right (Ui.ui_one_lt_SC (Ui.ui_SC_W 1))).2 (lt_add_one _))
  exact absurd hle (not_le.2 hlt)

theorem qd_E2_mem : ucE ∈ qdLevSet ucB :=
  ⟨qd_E_lt_G2, (qdFold_lt_iff ucB_SC.1 ucE).2 fun d hd => by rw [qdComps_E2 d hd]; exact qd_one_lt_B2,
    qd_E2_noFix S⟩

/-- **The level of `B₂` is `E₂`.** -/
theorem qd_B2_lev : qdLev ucB = ucE := by
  refine le_antisymm (csInf_le' (qd_E2_mem S)) ?_
  have hm : qdLev ucB ∈ qdLevSet ucB := csInf_mem ⟨_, qd_E2_mem S⟩
  by_contra hlt
  push Not at hlt
  exact hm.2.2 (qd_low_fix S hlt hm.2.1)

/-- **The index of `B₂` is `0`.** -/
theorem qd_B2_idx : qdI ucE ucB = 0 := by
  have hne : (qdLevSet ucB).Nonempty := ⟨_, qd_E2_mem S⟩
  obtain ⟨hnf, -⟩ := qd_nf ucB_SC ucB_gt hne
  rw [qd_B2_lev S] at hnf
  by_contra h0
  have hf₀ : qdH ucE 0 < ucB := by rw [← hnf]; exact (qdH_lt_iff _).2 (pos_iff_ne_zero.2 h0)
  have hS : SC (qdH ucE 0) := qdH_SC _ _
  have hO : Om1 < qdH ucE 0 := qdH_gt _ _
  obtain ⟨hl, hC, hne', -, -⟩ := ucLev_spec hS hO (uc_nf_of_lt hS hO hf₀)
  apply hne'
  rw [← qd_uc_H S hl]
  exact ucG_fix_lower hl ⟨0, rfl⟩ ((qd_uc_vis S hl hS hO).2 hC)

theorem qd_B2_H : qdH ucE 0 = ucB := by
  have h := (qd_nf ucB_SC ucB_gt ⟨_, qd_E2_mem S⟩).1
  rwa [qd_B2_lev S, qd_B2_idx S] at h

/-- **`B₂` is a fixed point of `Γ`.** -/
theorem qd_B2_fix : YhAt ucB ∧ ¬ yhJ ucB < ucB ∧ gamma ucB = ucB := by
  have h1E : (1 : Ordinal.{0}) < ucE := qd_one_lt_Om2.trans ucE_gt
  have hC1 : qdFold id 1 < ucB := by rw [qdFold_small id qd_one_lt_Om2]; exact qd_one_lt_B2
  have h1 : qdH 1 ucB = ucB := by
    rw [← qd_B2_H S]; exact ucG_fix_lower h1E ⟨0, rfl⟩ (by rw [qd_B2_H S]; exact hC1)
  have hfix : gamma ucB = ucB := qd_P_gamma S one_ne_zero h1
  refine ⟨⟨ucB_SC, ucB_gt⟩, ?_, hfix⟩
  have h := yhJ_gcG ucB; rw [vs_gcG_fix hfix ucB_gt] at h; rw [h]; exact lt_irrefl _

/-- **The gate of `B₂` is `0`.** -/
theorem qd_B2_gate : qdGt ucB = 0 := by
  obtain ⟨hA, hi, -⟩ := qd_B2_fix S
  have hB3 := qd_B2_lt_B3 S
  have hN : qdI (qdLev ucB) ucB < ucB := by rw [qd_B2_lev S, qd_B2_idx S]; exact ucB_SC.1
  rw [qdGt_base qd_B2_E le_rfl hB3, qdQEt_fix le_rfl hB3 hA hi hN, qd_B2_lev S, qd_B2_idx S]
  have hK : qdKQ ucE 0 = 0 := by
    unfold qdKQ; rw [if_neg (by rintro ⟨f, -, hf⟩; exact absurd hf (not_lt.2 zero_le))]
    unfold qdQt; rw [if_pos omega0_pos]
  have hF : qdFold (fun d => if d < ucB then qdQt d else 0) ucE < 1 :=
    (qdFold_lt_iff' _ zero_lt_one ucE).2 fun d hd => by
      rw [qdComps_E2 d hd, if_pos qd_one_lt_B2]
      unfold qdQt; rw [if_pos one_lt_omega0]; exact zero_lt_one
  rw [hK, Order.lt_one_iff.1 hF, max_self]

/-- **`B₂` reads `ϑˣ(Ω₁·ε_{Ω₁+1})`.** -/
theorem qd_B2_read (x : Ordinal.{0}) : qdA ucB x = vt x (Om1 * ggE) := by
  obtain ⟨hA, hi, -⟩ := qd_B2_fix S
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  rw [qdA_fix S hA hi le_rfl (qd_B2_lt_B3 S) x, qd_B2_lev S, qd_B2_idx S]
  have hlv : qdLvx ucB ucE x = ggE := by
    unfold qdLvx; exact qdLv_E2 _ (by simp only [if_pos qd_one_lt_B2, vD_one])
  have hK : qdRK ucE 0 x = 0 := by
    unfold qdRK; rw [if_neg (by rintro ⟨f, -, hf⟩; exact absurd hf (not_lt.2 zero_le)), vD_zero]
  rw [hlv, hK, add_zero, add_eq_right_iff_mul_omega0_le.2 (hgE.mul_lt hOE (omega0_lt_inE hgE)).le]

/-! ## The readings below `B₂` -/

/-- **Every code below `B₂` with its gate below `x` reads below a generic-level point.** -/
theorem qd_low_bd {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < ucB) (hg : qcG c < x) :
    QcBd x (vQ c x) := by
  obtain ⟨n, hn⟩ := qcF_cof hc
  have hFS : SC (qcF n) := ucH_SC _ _
  have hFE : InE (qcF n) := Low.opow_eq_self_of_SC hFS
  obtain ⟨-, hBF, hFB, -⟩ := qcF_facts S n
  obtain ⟨M, hME, hEg, hV, hR, hG, -, -⟩ := qsGood_all (qcF n) hFE hBF hFB
  obtain ⟨h1, hE, hcd⟩ := qcTw_facts n
  have hcomp : ∀ d ∈ ucComps (qcTw n), qcG d < x := fun d hd => by
    rcases (hcd d hd).lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, qcG_zero]; exact hx.pos
    · rw [h, show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans (omega0_lt_inE hx)
  have hgF : qcG (qcF n) < x := qc_H_gate hx (one_le_iff_ne_zero.1 h1) hE (lt_of_le_of_lt zero_le (ucH_gt _ _))
    hFB hcomp (by rw [qcG_zero]; exact hx.pos)
  have hQ : qcQE (qcF n) < x := by rw [← qcG_base' hFE (gl_G0_le hFS (ucH_gt _ _)) hFB]; exact hgF
  have hEgx : M.Eg < x := by rw [hEg]; exact max_lt (omega0_lt_inE hx) hQ
  have hcM : c < M.E := by rw [hME]; exact hn
  have hGc : M.G c < x := by
    rcases eq_or_ne c 0 with rfl | h0
    · rw [M.G0]; exact hx.pos
    · rw [hG c hn h0]; exact max_lt hEgx hg
  have hlt := M.lt c x hx hx1 hcM hGc
  rw [hR c hn x hx hx1 hGc] at hlt
  exact qcBd_mono hlt.le (M.V_T x hx hx1 hEgx).2.2.2

omit S in
theorem qd_gE_lt_gg : (ggE : Ordinal.{0}) < ggGam :=
  lt_of_le_of_ne ggE_le_ggGam fun h => by
    have h1 := tfDat_E; rw [h, tfDat_gg] at h1; exact zero_ne_one h1

omit S in
/-- **A reading under `QcBd` is below `ϑˣ(Ω₁·ε_{Ω₁+1})`.** -/
theorem qd_low_lt {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : QcBd x v) : v < vt x (Om1 * ggE) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  refine h4.trans ?_
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have hdE : tfDat ggE < x := by rw [tfDat_E]; exact lu_one_lt_E hx
  obtain ⟨-, -, hpos, -⟩ := qd_bd_pt hx hx1 hOE.le qd_gE_lt_gg hdE
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h := tfVt_lt hx hx1 hOE.le (qd_gE_lt_gg.trans tf_gg_lt_BG) h2.le
    (by rw [tfDat_eq_rj N h2]; exact mem_T_of_le hx hx1 h3.le) h0T h0Ω (mem_T_of_le hx hx1 hdE.le) h0T h0Ω
    (by rw [add_zero, add_zero]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 h2)
    (by rw [add_zero, tfDat_eq_rj N h2]; exact h3.trans_le hpos) (by rw [add_zero]; exact hx.pos.trans_le hpos)
  rwa [add_zero, add_zero] at h

end Googology.Trans.PoR.InaccPsi.R2.Qd
