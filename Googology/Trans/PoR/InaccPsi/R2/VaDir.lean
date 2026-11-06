import Googology.Trans.PoR.InaccPsi.R2.VaCu

/-!
# VaDir: `ZbDirect S Γ_{B_Γ+1}` — THE WHOLE LAYER `c = B_Γ`, UNCONDITIONAL

`Γ_{B_Γ+1}` is the supremum of the tower `a₀ = B_Γ + 1`, `a_{n+1} = φ(a_n, 0)` (`Ordinal.gamma_succ_eq_nfp`), whose
members are codes over `K` (gate below `K`, `Va.va_gate`); the step of the system `Va.VaGood (a_{n+1})` gives
`ZbDirect S ε_{a_{n+1}+1}` (`Zm.ZmDS.direct`).

* `vaU_nfp`, `vaTw`, `vaTw_iter`, `vaTw_lt`, `vaTw_cof`, `vaTw_cl`;
* `vaDirectU` (**`ZbDirect S Γ_{B_Γ+1}`, UNCONDITIONAL**), `vaUVU` (**UPPER ∧ LOWER ∧ CapV at every range restart
  below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < Γ_{B_Γ+1}`**), `vaLayBG` (**the conclusions of `skLayLoFix` and `skLayHiFix`
  at the layer `c = B_Γ`**).

No new axiom.  New definition: `vaTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **`Γ_{B_Γ+1}` is the least fixed point of `α ↦ φ(α, 0)` above `B_Γ + 1`.** -/
theorem vaU_nfp : vaU = nfp (fun a => veblen a 0) (tfBG + 1) := by
  have hBE : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have e : Om1 + 1 + (tfBG + 1) = tfBG + 1 := by rw [← add_assoc, gl_absorb hBE tfBG_gt]
  unfold vaU
  rw [tf_gcG, e, ← Order.succ_eq_add_one, gamma_succ_eq_nfp, tfBG_fix]

/-- **The tower** `B_Γ + 1, φ(B_Γ+1, 0), φ(φ(B_Γ+1, 0), 0), …`. -/
noncomputable def vaTw : ℕ → Ordinal.{0}
  | 0 => tfBG + 1
  | n + 1 => veblen (vaTw n) 0

theorem vaTw_iter : ∀ n : ℕ, (fun a => veblen a 0)^[n] (tfBG + 1) = vaTw n
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', vaTw_iter n]; rfl

theorem vaTw_lt : ∀ n, vaTw n < vaU
  | 0 => (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))).add_one_lt va_BG_lt_U
  | n + 1 => (gcG_SC _).2 _ (vaTw_lt n) 0 (gcG_SC _).1

theorem vaTw_cof {B : Ordinal.{0}} (hB : B < vaU) : ∃ n, B < vaTw n := by
  rw [vaU_nfp] at hB
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hB
  exact ⟨n, by rw [← vaTw_iter]; exact hn⟩

theorem vaTw_gt : ∀ n, tfBG < vaTw n
  | 0 => lt_add_one _
  | n + 1 => (vaTw_gt n).trans_le (left_le_veblen _ _)

theorem vaTw_cl {Z : Ordinal.{0}} (hZ : 0 < Z) : ∀ n, TlCl Z (vaTw n)
  | 0 => TlCl.add (zbBG_tl hZ) (TlCl.one hZ)
  | n + 1 => TlCl.phi (vaTw_cl hZ n) (TlCl.zero hZ)

/-- **`ZbDirect S Γ_{B_Γ+1}`, UNCONDITIONAL.** -/
theorem vaDirectU (S : InaccSeq.{0}) : ZbDirect S vaU := by
  intro B hB1 hB2
  obtain ⟨n, hn⟩ := vaTw_cof hB2
  set e := vaTw (n + 1) with hedef
  have hne : vaTw n < e := by
    show vaTw n < veblen (vaTw n) 0
    refine lt_of_le_of_ne (left_le_veblen _ _) fun h => ?_
    -- a fixed point `a = φ(a, 0)` above `Ω₁` is strongly critical, so it is not below `Γ_{B_Γ+1}`
    have hSC : SC (vaTw n) := gl_SC_of_fix h.symm ((Rj.rj_Om1_pos.trans tfBG_gt).trans (vaTw_gt n))
    rcases va_atom_cases (vaTw_gt n).le (vaTw_lt n) with h1 | h1
    · exact absurd h1 (vaTw_gt n).ne'
    · exact h1 ⟨hSC, tfBG_gt.trans (vaTw_gt n)⟩
  have he1 : (1 : Ordinal.{0}) ≤ vaTw n := (one_le_iff_ne_zero.2 (lt_of_le_of_lt zero_le (vaTw_gt n)).ne')
  have heE : InE e := luP_E he1 (luP_veblen _ _)
  have heB : tfBG ≤ e := (vaTw_gt (n + 1)).le
  have heU : e < vaU := vaTw_lt (n + 1)
  obtain ⟨M, hE, hEg, -, -, -⟩ := vaGood_all e heE heB heU
  have hK : SC (Td.tdK S) := Td.tdK_SC
  have hK1 : Td.tdK S ≤ Om1 := by rw [Br.Om1_eq]; exact (Td.tdK_lt_Om1 (S := S)).le
  have hge : yrG e < Td.tdK S := va_gate hK hK1 e (vaTw_cl hK.1 (n + 1)) heU
  have hgK : M.step.Eg < Td.tdK S := by
    rw [ZmDS.step_Eg, hEg]
    refine max_lt (omega0_lt_inE (Low.opow_eq_self_of_SC hK)) ?_
    rw [← yrG_base heE (va_G_le_BG.trans heB)]; exact hge
  have hBM : B < M.step.E := by
    show B < eN M.E
    rw [hE]; exact (hn.trans hne).trans (lt_eN e)
  have hGM : tfBG < M.step.E := by
    show tfBG < eN M.E
    rw [hE]; exact heB.trans_lt (lt_eN e)
  exact M.step.direct S hGM hgK M.step_gc0 B hB1 hBM

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < Γ_{B_Γ+1}`
(UNCONDITIONAL).** -/
theorem vaUVU (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < vaU) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (vaDirectU S) l hr B hB hl

/-- **THE WHOLE LAYER `c = B_Γ`**: the conclusions of `skLayLoFix` and `skLayHiFix` at `c = B_Γ`. -/
theorem vaLayBG (S : InaccSeq.{0}) :
    ∀ l, CdRange S l → (∃ ℓ, ℓ < gcG (tfBG + 1) ∧ l < iota S (gcG (veblen ℓ (gcG tfBG + 1)) * ω)) →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbLay_of_direct (vaDirectU S)

end Googology.Trans.PoR.InaccPsi.R2.Va
