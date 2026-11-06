import Googology.Trans.PoR.InaccPsi.R2.QcAtS
import Googology.Trans.PoR.InaccPsi.R2.VaFixS

/-!
# QcFr: ONE FORM OF THE READING OF EVERY FIXED POINT OF `Γ` BELOW `B₂`

A fixed point `e = H_λ(y)` of `Γ` from `X` on reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + K(x))`, `K = Qc.qcK λ y` (`Qc.vQ_fix`).
Below `X` it is `F_β(z)` read by `Va.vR` as `ϑˣ(Ω₁·(Ω₁ + β(x)) + vK β z x)` (`Va.vA_atom_fix`).  The two agree:
`ucLev e = tlLev e` (`qc_lev_low`), `z = s_β + y` with `s_β = Uc.ucS β` the start of `H_β` in `F_β`
(`qc_idx_low`), `s_β = y₀(β)` below `X` (`qc_ucS_low`: no `β ∈ (Ω₁, X)` has `F_β(0) = β`), the fixed points of
`F_β` above `Ω₁` below `z` are those of `H_β` below `y` (`qc_fix_sets`), so `vK β z x = qcK β y x`
(`qc_vK_low`).

* `qc_ucS_low`, `qc_lev_low`, `qc_idx_low`, `qc_fix_sets`, `qc_vK_low`;
* `qs_fixRd` (**every fixed point `e ∈ (Ω₁, B₂)` of `Γ` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + qcK λ y x)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The start of `H_β` in `F_β` is `y₀(β)` below `X`.** -/
theorem qc_ucS_low {β : Ordinal.{0}} (hβX : β < tlX) : ucS β = glY0 β := by
  rcases lt_trichotomy β Om1 with hβ | rfl | hβ
  · rw [glY0_lt hβ]
    have hmax : max Om1 β = Om1 := max_eq_left hβ.le
    refine le_antisymm (ucS_le ?_) (not_lt.1 fun h => ?_)
    · rw [hmax]
      calc Om1 = rhF β Om1 := (tl_rhF_Om1 hβ).symm
        _ < rhF β (Om1 + 1) := (rhF_lt β).2 (lt_add_one _)
    · have hs := ucS_spec β
      rw [hmax] at hs
      have h1 : ucS β ≤ Om1 := Order.lt_add_one_iff.1 h
      have h2 := (rhF_le β).2 h1
      rw [tl_rhF_Om1 hβ] at h2
      exact absurd hs (not_lt.2 h2)
  · rw [glY0_eq]
    have hmax : max Om1 Om1 = (Om1 : Ordinal.{0}) := max_self _
    refine le_antisymm (ucS_le ?_) (not_lt.1 fun h => ?_)
    · rw [hmax]; exact (rhF_left_le Om1 0).trans_lt ((rhF_lt Om1).2 zero_lt_one)
    · have hs := ucS_spec Om1
      rw [hmax, Order.lt_one_iff.1 h] at hs
      exact absurd hs (not_lt.2 vs_rhF_Om1_zero)
  · rw [glY0_gt hβ]
    have hmax : max Om1 β = β := max_eq_right hβ.le
    refine le_antisymm (ucS_le ?_) zero_le
    rw [hmax]
    refine lt_of_le_of_ne (rhF_left_le β 0) fun h => ?_
    exact absurd (tlX_le (show tlG β = β from h.symm) hβ) (not_le.2 hβX)

/-- **Below `X` the level of a strongly critical `e > Ω₁` is `tlLev e`.** -/
theorem qc_lev_low {e : Ordinal.{0}} (hSC : SC e) (hO : Om1 < e) (heX : e < tlX) : ucLev e = tlLev e := by
  have hmem := uc_nf_lt_X hSC hO heX
  refine le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_)
  have hm : ucLev e ∈ ucLevSet e := csInf_mem ⟨_, hmem⟩
  obtain ⟨hl, -, hlow⟩ := tlLev_spec hSC hO heX
  have hγ2 : ucLev e < OmTwo := (hlt.trans hl).trans (heX.trans tlX_lt_OmTwo)
  have hF := hlow _ hlt
  exact hm.2.2 ((ucH_fix_iff_F hγ2 (max_lt hO (hlt.trans hl))).2 hF)

/-- **The index in `F_β` is `s_β` plus the index in `H_β`.** -/
theorem qc_idx_low {β e : Ordinal.{0}} (hβ2 : β < OmTwo) (hβe : max Om1 β < e) (he : e ∈ range (rhF β)) :
    ucS β + ucI β e = tlI β e := by
  have hH : e ∈ range (ucH β) := (uc_range_F hβ2 hβe).2 he
  have h1 := ucI_spec hH
  rw [ucH_eq_F hβ2] at h1
  obtain ⟨z, rfl⟩ := he
  rw [tlI_rhF]
  exact (rhF_normal β).strictMono.injective h1

/-- **The fixed points of `F_β` above `Ω₁` below `s_β + y` are those of `H_β` below `y`** (`0 < β < Ω₂`). -/
theorem qc_fix_sets {β y : Ordinal.{0}} (hβ0 : β ≠ 0) (hβ2 : β < OmTwo) :
    {f | rhF β f = f ∧ Om1 < f ∧ f < ucS β + y} = {f | ucH β f = f ∧ f < y} := by
  ext f
  constructor
  · rintro ⟨hf, hOf, hfz⟩
    have hβf : β < f := rhF_lt_fix hβ0 hf
    have hmax : max Om1 β < f := max_lt hOf hβf
    have hSC : SC f := by rw [← hf]; exact rhF_SC β f
    refine ⟨(ucH_fix_iff_F hβ2 hmax).2 hf, not_le.1 fun hyf => ?_⟩
    have hS : ucS β + f = f := (isPrincipal_add_iff_add_left_eq_self.1 hSC.isPrincipal) _ (ucS_lt hmax hSC)
    have := (add_le_add_iff_left (ucS β)).2 hyf
    rw [hS] at this
    exact absurd hfz (not_lt.2 this)
  · rintro ⟨hf, hfy⟩
    have hOf : Om1 < f := by rw [← hf]; exact ucH_gt β f
    have hβf : β < f := by
      have h := ucH_C_lt β f; rw [hf, ucC_small hβ2] at h; exact h
    exact ⟨(ucH_fix_iff_F hβ2 (max_lt hOf hβf)).1 hf, hOf, hfy.trans_le le_add_self⟩

/-- **The index readings agree below `X`.** -/
theorem qc_vK_low {β y : Ordinal.{0}} (hβ0 : β ≠ 0) (hβX : β < tlX) (hyX : ucS β + y < tlX) (hne : ucH β y ≠ y)
    (x : Ordinal.{0}) :
    vK β (ucS β + y) x = qcK β y x := by
  have hβ2 : β < OmTwo := hβX.trans tlX_lt_OmTwo
  have hsets := qc_fix_sets (y := y) hβ0 hβ2
  have hyX : y < tlX := le_add_self.trans_lt hyX
  have hFiff : VaFixL β (ucS β + y) ↔ QcFixH β y := by
    constructor
    · rintro ⟨f, h1, h2, h3⟩
      have : f ∈ {f | ucH β f = f ∧ f < y} := hsets ▸ (show f ∈ {f | rhF β f = f ∧ Om1 < f ∧ f < ucS β + y}
        from ⟨h1, h2, h3⟩)
      exact ⟨f, this.1, this.2⟩
    · rintro ⟨f, h1, h2⟩
      have : f ∈ {f | rhF β f = f ∧ Om1 < f ∧ f < ucS β + y} := hsets.symm ▸ (show f ∈ {f | ucH β f = f ∧ f < y}
        from ⟨h1, h2⟩)
      exact ⟨f, this.1, this.2.1, this.2.2⟩
  have hp : vaFpL β (ucS β + y) = qcFpH β y := by unfold vaFpL qcFpH; rw [hsets]
  unfold vK qcK
  by_cases hF : QcFixH β y
  · rw [if_pos (hFiff.2 hF), if_pos hF, hp]
    obtain ⟨hpf, hpO, hpy⟩ := qc_fpH_mem hne hF
    have hSC : SC (qcFpH β y) := by rw [← hpf]; exact ucH_SC _ _
    have hβp : β < qcFpH β y := by have h := ucH_C_lt β (qcFpH β y); rw [hpf, ucC_small hβ2] at h; exact h
    have hS : ucS β + qcFpH β y = qcFpH β y :=
      (isPrincipal_add_iff_add_left_eq_self.1 hSC.isPrincipal) _ (ucS_lt (max_lt hpO hβp) hSC)
    have hsub : ucS β + y - (qcFpH β y + 1) = y - (qcFpH β y + 1) := by
      set p := qcFpH β y with hpdef
      obtain ⟨t, ht⟩ := exists_add_of_le (Order.add_one_le_of_lt hpy)
      rw [ht, ← add_assoc, ← add_assoc, hS, Ordinal.add_sub_cancel]
    have hpX : qcFpH β y < tlX := hpy.trans hyX
    rw [hsub, vQ_low hpX, vQ_low ((Ordinal.sub_le_self _ _).trans_lt hyX)]
  · rw [if_neg (fun h => hF (hFiff.1 h)), if_neg hF, qc_ucS_low hβX, Ordinal.add_sub_cancel, vQ_low hyX]

/-- **Every fixed point `e ∈ (Ω₁, B₂)` of `Γ` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + qcK λ y x)`**, `λ = ucLev e`,
`y = ucI λ e`. -/
theorem qs_fixRd {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hB : e < ucB) (x : Ordinal.{0}) :
    vQ e x = vt x (Om1 * (Om1 + qcLvx e (ucLev e) x) + qcK (ucLev e) (ucI (ucLev e) e) x) := by
  rcases lt_or_ge e tlX with hX | hX
  · obtain ⟨h1, hlc, hyc, hnf, -⟩ := vs_fix_data hA hi hX
    have hE : InE e := Low.opow_eq_self_of_SC hA.1
    have hGe : gcG 0 ≤ e := gl_G0_le hA.1 hA.2
    have hlev := qc_lev_low hA.1 hA.2 hX
    have hβ0 : tlLev e ≠ 0 := one_le_iff_ne_zero.1 h1
    have hβX : tlLev e < tlX := hlc.trans hX
    have hβ2 : tlLev e < OmTwo := hβX.trans tlX_lt_OmTwo
    have hidx := qc_idx_low hβ2 (max_lt hA.2 hlc) ⟨_, hnf⟩
    have hlv : qcLvx e (tlLev e) x = vQ (tlLev e) x := by
      unfold qcLvx; rw [qcLv_small _ hβ2, if_pos hlc]
    have hne : ucH (tlLev e) (ucI (tlLev e) e) ≠ ucI (tlLev e) e := by
      have hH : e ∈ range (ucH (tlLev e)) := (uc_range_F hβ2 (max_lt hA.2 hlc)).2 ⟨_, hnf⟩
      rw [ucI_spec hH]
      exact ne_of_gt (le_add_self.trans_lt (hidx ▸ hyc))
    rw [vQ_low hX, vR_base hE hGe, vA_atom_fix hA hi ⟨hlc, hyc⟩, hlev, hlv, vQ_low hβX, ← hidx,
      qc_vK_low hβ0 hβX (by rw [hidx]; exact hyc.trans hX) hne]
    simp only [ywV, mul_one]
  · exact vQ_fix hA hi (qc_fix_data hA hi hX hB).2.2.2.1 hX hB x

end Googology.Trans.PoR.InaccPsi.R2.Qc
