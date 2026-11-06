import Googology.Trans.PoR.InaccPsi.R2.QdR
import Googology.Trans.PoR.InaccPsi.R2.VdCit

/-!
# QdAgr: THE VEBLEN LEVELS ARE THE LIFTED LEVELS BELOW `Γ_{Ω₂+1}`; `B₂ < B₃ ≤ θ`

`B₂ = Uc.ucB = ψ_{Ω₂}(E₂)`, `B₃ = Qd.qdB`, `θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `Hˡ_γ = Ul.ulH S 1 γ`, `vdLev` the level of
the normal form `z = Hˡ_λ(y)` of `R2.VdNF`.  For a Veblen level `γ < Γ_{Ω₂+1}`, `Hᵛ_γ = Hˡ_γ` (`Qd.qdH_eq_ul`) and the
leaves of `γ` are below a strongly critical `z > Ω₁` iff `γ` is visible at `z` (`Qd.qd_K_iff`).  So the levels of
`R2.QdDat` are the lifted levels below `Γ_{Ω₂+1}`, and:

* `qd_vis`, `qdLevSet_vd` (**`qdLevSet z` is `vdLevSet S z` below `Γ_{Ω₂+1}`**), `qd_lev_vd` (**a strongly critical
  `z ∈ (Ω₁, θ)` with `vdLev z < Γ_{Ω₂+1}` has a normal form, and `qdLev z = vdLev z`**), `qd_vd_of_nf`;
* `qd_G2_le_psi3`, `qd_G2_lt_Om3`, `qd_E_lt_G2`;
* `qd_th_noNF`, `qd_B3_le_th` (**`B₃ ≤ θ`**: `θ` is a fixed point of every visible level `γ < ψ_{Ω₃}(Ω_ω)`, by
  `Us.us_fix_iff` at the own argument `Ω_ω`), `qd_B2_lt_B3` (**`B₂ < B₃`**: below `B₂` the level is `ucLev z < E₂`,
  at `B₂` the level `E₂` does not fix it, `Us.us_fix_iff` at `E₂`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Vd

variable {S : InaccSeq.{0}}

/-- **The leaves of a Veblen level are below `z` iff it is visible at `z`.** -/
theorem qd_vis {γ z : Ordinal.{0}} (hγ : γ < qdG2) (hz : SC z) (h1 : Om1 < z) :
    qdFold id γ < z ↔ ulD S 1 γ < z := by
  rw [qdFold_lt_iff hz.1, qd_K_iff hz h1 hγ, ul_vis hz]

theorem qd_G2_le_psi3 (a : Ordinal.{0}) : qdG2 ≤ S.psi a (Om (1 + 1 + 1)) :=
  qdG2_le (SC_psi (InR_Om_succ (1 + 1)) a) (by rw [uc_Om2_eq]; exact (psiS_bounds (S := S) a (1 + 1)).1)

theorem qd_G2_lt_Om3 (S : InaccSeq.{0}) : qdG2 < (Om (1 + 1 + 1) : Ordinal.{0}) :=
  (qd_G2_le_psi3 (S := S) 0).trans_lt (psi_lt (InR_Om_succ (1 + 1)) 0)

theorem qd_E_lt_G2 : ucE < qdG2 := by
  rw [uc_E_eq_veblen]
  exact qdG2_spec.1.2 1 (Gg.gg_one_lt_of_SC qdG2_spec.1) _ (qdG2_spec.1.isSuccLimit.add_one_lt qdG2_spec.2)

/-- **The levels of `R2.QdDat` are the lifted levels below `Γ_{Ω₂+1}`.** -/
theorem qdLevSet_vd {z : Ordinal.{0}} (hz : SC z) (h1 : Om1 < z) (γ : Ordinal.{0}) :
    γ ∈ qdLevSet z ↔ γ < qdG2 ∧ γ ∈ vdLevSet S z := by
  rw [vdLevSet_eq]
  constructor
  · rintro ⟨hγ, hd, hne⟩
    exact ⟨hγ, hγ.trans (qd_G2_lt_Om3 S), (qd_vis hγ hz h1).1 hd, by rw [← qdH_eq_ul S hγ]; exact hne⟩
  · rintro ⟨hγ, -, hd, hne⟩
    exact ⟨hγ, (qd_vis hγ hz h1).2 hd, by rw [qdH_eq_ul S hγ]; exact hne⟩

/-- **A strongly critical `z ∈ (Ω₁, θ)` whose lifted level is a Veblen level has a normal form with that level.** -/
theorem qd_lev_vd {z : Ordinal.{0}} (hz : SC z) (h1 : Om1 < z) (hzθ : z < ConjT.th S) (hlt : vdLev S z < qdG2) :
    (qdLevSet z).Nonempty ∧ qdLev z = vdLev S z := by
  have h1' : Om 1 < z := by rw [← Rj.rj_Om1]; exact h1
  have hne := vd_nf_ex hz h1' hzθ
  have hm : vdLev S z ∈ vdLevSet S z := csInf_mem hne
  have hq : vdLev S z ∈ qdLevSet z := (qdLevSet_vd hz h1 _).2 ⟨hlt, hm⟩
  refine ⟨⟨_, hq⟩, le_antisymm (csInf_le' hq) (le_csInf ⟨_, hq⟩ fun γ hγ => csInf_le' ((qdLevSet_vd hz h1 γ).1 hγ).2)⟩

/-- **With a normal form, the lifted level is the Veblen level.** -/
theorem qd_vd_of_nf {z : Ordinal.{0}} (hz : SC z) (h1 : Om1 < z) (hzθ : z < ConjT.th S)
    (hne : (qdLevSet z).Nonempty) : vdLev S z < qdG2 ∧ qdLev z = vdLev S z := by
  have hm : qdLev z ∈ qdLevSet z := csInf_mem hne
  have hle : vdLev S z ≤ qdLev z := csInf_le' ((qdLevSet_vd hz h1 _).1 hm).2
  have hlt := hle.trans_lt hm.1
  exact ⟨hlt, (qd_lev_vd hz h1 hzθ hlt).2⟩

/-- **`θ` has no normal form over the Veblen levels**: it is a fixed point of every visible `γ < ψ_{Ω₃}(Ω_ω)`. -/
theorem qd_th_noNF : ConjT.th S ∈ qdNoNF := by
  have hθS : SC (ConjT.th S) := ConjT.SC_th S
  have hθ1 : Om1 < ConjT.th S := by rw [Rj.rj_Om1]; exact (psiS_bounds (S := S) _ 1).1
  refine ⟨hθS, hθ1, fun ⟨γ, hγ, hd, hne⟩ => hne ?_⟩
  rw [qdH_eq_ul S hγ]
  have hown : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := Ui.ui_OmW_own
  have hOw : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have hB0 : (Om ω : Ordinal.{0}) ≠ 0 := hOw.1.ne'
  have hγV : γ < Om (1 + 1 + 1) := hγ.trans (qd_G2_lt_Om3 S)
  have h3w : (Om (1 + 1 + 1) : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have : (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) := by norm_num
    rw [this]; exact natCast_lt_omega0 3)
  have h2w : (Om (1 + 1) : Ordinal.{0}) < Om ω := (Om_lt_Om.2 (lt_add_one _)).trans h3w
  have hγw : γ + 1 < Om ω := hOw.isSuccLimit.add_one_lt (hγV.trans h3w)
  refine (Us.us_fix_iff vd_one_lt_omega hown hB0 hγV).2 ⟨?_, hγ.trans_le (qd_G2_le_psi3 _), ?_⟩
  · have hOwE : ω ^ (Om ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hOw
    have h2E : ω ^ (Om (1 + 1) : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC (SC_Om (by simp))
    rw [← h2E, ← opow_mul]
    conv_rhs => rw [← hOwE]
    exact opow_dvd_opow ω ((show InE (Om ω : Ordinal.{0}) from Low.opow_eq_self_of_SC hOw).mul_lt h2w hγw).le
  · exact (ul_vis hθS).1 ((qd_vis hγ hθS hθ1).1 hd)

/-- **`B₃ ≤ θ`.** -/
theorem qd_B3_le_th : qdB ≤ ConjT.th S := qdB_le qd_th_noNF

/-- **`B₂ < B₃`.** -/
theorem qd_B2_lt_B3 (S : InaccSeq.{0}) : ucB < qdB := by
  have hBθ : ucB < ConjT.th S := ul_B_lt_th
  have key : ∀ z, SC z → Om1 < z → z ≤ ucB → (qdLevSet z).Nonempty := by
    intro z hz h1 hzB
    have hzθ := hzB.trans_lt hBθ
    refine (qd_lev_vd hz h1 hzθ ?_).1
    rcases hzB.lt_or_eq with hlt | rfl
    · have h1' : Om 1 < z := by rw [← Rj.rj_Om1]; exact h1
      rw [(vdLev_eq_uc (S := S) hz h1' hlt).1]
      exact (ucLev_spec hz h1 (uc_nf_of_lt hz h1 hlt)).1.trans qd_E_lt_G2
    · -- the level `E₂` does not fix `B₂`
      have hs : (1 : Ordinal.{0}) < ω := vd_one_lt_omega
      have hown : ucE ∈ S.CSet ucE (S.psi ucE (Om (1 + 1))) := by
        have h := Ui.ui_E_mem (S := S) hs ucE (S.psi ucE (Om (1 + 1))); rwa [Ui.ui_one_E] at h
      have hE0 : (ucE : Ordinal.{0}) ≠ 0 := (ucE_gt.trans' uc_SC_Om2.1).ne'
      have hEV : ucE < (Om (1 + 1 + 1) : Ordinal.{0}) := vd_E_lt_V
      have hEK : UlK S 1 ucB ucE := by
        rw [uc_E_eq_veblen, uc_Om2_eq]
        exact UlK.phi UlK.one (UlK.add (UlK.om (UlK.add UlK.one UlK.one)) UlK.one)
      have hmem : ucE ∈ vdLevSet S ucB := by
        rw [vdLevSet_eq]
        refine ⟨hEV, (ul_vis hz).2 hEK, fun hfix => ?_⟩
        rw [← uc_psiE_eq_B (S := S)] at hfix
        have hd := ((Us.us_fix_iff hs hown hE0 hEV).1 hfix).1
        have hle := Ordinal.le_of_dvd hE0 hd
        have hlt : ucE < Om (1 + 1) ^ (ucE + 1) :=
          (right_le_opow ucE (Ui.ui_one_lt_SC (Ui.ui_SC_W 1))).trans_lt
            ((opow_lt_opow_iff_right (Ui.ui_one_lt_SC (Ui.ui_SC_W 1))).2 (lt_add_one _))
        exact absurd hle (not_le.2 hlt)
      exact (csInf_le' hmem).trans_lt qd_E_lt_G2
  by_contra h
  exact qdB_mem.2.2 (key qdB qdB_SC qdB_gt (not_lt.1 h))

end Googology.Trans.PoR.InaccPsi.R2.Qd
