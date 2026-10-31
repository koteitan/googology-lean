import Googology.Trans.PoR.InaccPsi.R2.WnLv

/-!
# WnSucc: `G` AS A BASE OF EVERY LEVEL BELOW `G`; THE SUCCESSOR STEP `ℓ ↦ ℓ + Ω₁` OF REGION (A2)

`Wh.whGW` makes `G` a base of level `L + Ω₁` only when the reading stays below `ε_{x+1}` (`Wh.WhNB`), which fails at
every level `ℓ ≥ ε_{Ω₁+1}` (there `glR ℓ x ≥ ε_{x+1}`).  Here the outer low field of `G` is
`Z_o(x) = hdNx (Γ_{x+1}+1) (Γ_{x+1})` (the next fixed point of `φ(Γ_{x+1}, ·)` above `Γ_{x+1}`, below `Γ_{x+2}`), which
lies above `φ(a, Γ_{x+1}+1)` for EVERY `a < Γ_{x+1}`; so the base needs no bound on the level.

* `wnZo`, `wnZo_G1`, `wn_S_Zo`, `wnGW Λ` (**`G` AS A BASE OF LEVEL `L + Ω₁` FOR EVERY BAND LEVEL DATUM**),
  `wnGU_shape` (the union over `wnGW Λ` started at a start over it is a start over `wnGW Λ.succ`),
  `wnU_shape` (**`Hg.hgU` is a start over `wnGW Hn.hnL1`**);
* `WnAt` (**AN ENTRY AT A LEVEL `ℓ < G`**: package at `ℓ` read `glR ℓ x`, gate `≤ glG ℓ`, system over `G` with the
  bound `φ(ℓ, G+1)`, a start over `wnGW` at the package), `wnAt_base`;
* `wnSuccV`, `wnSucc_at`, `wnSucc_ext`, `wnSucc_ext_lt` (**THE SUCCESSOR STEP of region (A2)**).

The extension statement is `Wh.WhExt`.  No new axiom.  New definitions: `wnZo`, `wnGW`, `WnAt`, `wnSuccV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wn

open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## The outer low field -/

/-- **The outer low field of `G`**: the next fixed point of `φ(Γ_{x+1}, ·)` above `Γ_{x+1}` (`Γ_{x+1}` replaced by
`max ω Γ_{x+1}` in the level, so that the field is a fixed point of `φ(2, ·)` at every `x`). -/
noncomputable def wnZo (x : Ordinal.{0}) : Ordinal.{0} := hdNx (max ω (lgG x) + 1) (lgG x)

theorem wn_lgG_max {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : max ω (lgG x) = lgG x :=
  max_eq_right ((omega0_lt_inE hx).trans (lgG_facts hx hx1).2.1).le

theorem wnZo_fix (x : Ordinal.{0}) : veblen 2 (wnZo x) = wnZo x := by
  unfold wnZo
  refine hdNx_fix ?_ _
  calc (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  _ ≤ max ω (lgG x) := le_max_left _ _
  _ < max ω (lgG x) + 1 := lt_add_one _

theorem wnZo_E (x : Ordinal.{0}) : InE (wnZo x) := hdNx_E (by simp) _

/-- **`Z_o(x) < Γ_{x+2}`.** -/
theorem wnZo_G1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : wnZo x < gq 1 x := by
  unfold wnZo
  rw [wn_lgG_max hx hx1, hdNx_succ]
  have hl : IsSuccLimit (gq 1 x) := ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2
  exact he_N_lt1 hx hx1 (hl.add_one_lt (mg_lgG_lt_G1 hx hx1)) (mg_lgG_lt_G1 hx hx1)

/-- **`hdNx a (Γ_{x+1}) < Z_o(x)` for every `1 ≤ a < Γ_{x+1}`.** -/
theorem wn_S_Zo {x a : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : 1 ≤ a) (ha : a < lgG x) :
    hdNx a (lgG x) < wnZo x := by
  rw [hdNx_fixP (hjG_fix hx hx1 h1 ha)]
  have haZ : a < max ω (lgG x) + 1 := by rw [wn_lgG_max hx hx1]; exact ha.trans (lt_add_one _)
  have hfix : veblen a (wnZo x) = wnZo x := hdNx_fix haZ _
  have hlt : lgG x + 1 < wnZo x := (ev_isSuccLimit_of_inE (wnZo_E x)).add_one_lt (hdNx_gt _ _)
  rw [← hfix]
  exact (isNormal_veblen a).strictMono hlt

/-! ## `G` as a base of level `L + Ω₁` -/

section GW

variable (Λ : HnLv)

/-- **`G` AS A BASE OF LEVEL `L + Ω₁`** for every band level datum (code gate `0`, reading gate `g`, reading
`Γ_{x+1}`, outer low field `Z_o`). -/
noncomputable def wnGW : HnWB Λ where
  F := gcG 0
  Fr := lgG
  γ := 0
  γR := Λ.g
  Zo := wnZo
  γ_lt := gv_Om1_pos
  γR_lt := Λ.g_lt
  γ_le := zero_le
  lg := le_rfl
  γR_cl := fun _ _ _ _ h => h
  F_P := ⟨gcG 0, hnG_FP Λ⟩
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Λ.L + Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (Λ.succ.L_lt 1)
    have h2 := (isNormal_veblen (Λ.L + Om1)).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rw [hdNx_fixP (hnG_FP Λ)]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  S_mem := fun S a b ha hb => by
    rw [hdNx_fixP (hnG_FP Λ)]
    exact CSet.phi_mem (Λ.succ.L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => hnG_q Λ hx hx1
  Fr_P := fun hx hx1 _ => ⟨lgG _, hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1)⟩
  S_Zo := fun {x} hx hx1 _ => wn_S_Zo hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1)
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  S_pi := fun hB hg => hjG_S_pi hB (Λ.succ.l_pi _ _ hB hg) (hnG_one Λ hB.2.1) (hnG_q Λ hB.2.1 hB.2.2.2)
    (hnG_one Λ hB.1) (hnG_q Λ hB.1 (hB.2.2.1.trans hB.2.2.2))

theorem wnGW_γR : (wnGW Λ).γR = Λ.g := rfl

/-- **The union over `G` with a package at `Λ` starts the next package at `Λ.succ`.** -/
theorem wnGU_shape (St0 : HnVStTy Λ 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h))
    (S0 : HgVD) (hS0 : HnWShape (wnGW Λ) 0 S0) :
    HnWShape (wnGW Λ.succ) 0 (hnwU (wnGW Λ) St0 h0 S0 hS0) := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hdNx (Λ.L + Om1) (gcG 0) = veblen (Λ.succ.L + 0) (gcG 0 + 1)
    rw [add_zero, hdNx_fixP (hnG_FP Λ)]; rfl
  · show Λ.g < x ↔ max Λ.g 0 < x
    rw [max_eq_left zero_le]
  · show hdNx (Λ.l x + x) (lgG x) = veblen (Λ.succ.l x + 0) (lgG x + 1)
    rw [add_zero, hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]; rfl
  · show hnwUZ (wnGW Λ) x = if max Λ.g 0 < x then evZ (veblen (Λ.succ.l x + 0) (lgG x + 1))
      else (wnGW Λ.succ).hnwZo x
    unfold hnwUZ
    rw [max_eq_left zero_le]
    by_cases hg : Λ.g < x
    · rw [if_pos (show (wnGW Λ).γR < x from hg), if_pos hg, add_zero]
      show evZ (hdNx (Λ.l x + x) (lgG x)) = evZ (veblen (Λ.l x + x) (lgG x + 1))
      rw [hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]
    · rw [if_neg (show ¬ (wnGW Λ).γR < x from hg), if_neg hg,
        (wnGW Λ.succ).hnwZo_low (show ¬ (wnGW Λ.succ).γR < x from hg)]
      rfl

end GW

/-- **`Hg.hgU` IS A START OVER `wnGW Hn.hnL1` AT THE LEVEL `Ω₁ + 0`.** -/
theorem wnU_shape : HnWShape (wnGW hnL1) 0 hgU := by
  refine ⟨by show veblen Om1 (gcG 0 + 1) = veblen (Om1 + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max (0 : Ordinal.{0}) 0 < x
    rw [max_self]
  · show veblen x (lgG x + 1) = veblen (x + 0) (lgG x + 1)
    rw [add_zero]
  · show evZ (hcBR x) = if max 0 0 < x then evZ (veblen (x + 0) (lgG x + 1))
      else (wnGW hnL1).hnwZo x
    rw [max_self, if_pos hx.pos, add_zero]; rfl

/-! ## Entries of region (A2) -/

/-- **AN ENTRY AT THE LEVEL `ℓ < G`**: the package `K` at `ℓ` (read `glR ℓ x` above its gate `g ≤ glG ℓ`, every
`ε`-number above `g` is above `glG ℓ`) and a system `V` over `G` with the bound `φ(ℓ, G+1)` and base gate
`≤ glG ℓ` that is a START over `wnGW` at `K`. -/
def WnAt (ℓ : Ordinal.{0}) (K : HnPk) (V : HgVD) : Prop :=
  K.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → K.Λ.g < x → K.Λ.l x = glR ℓ x) ∧
    V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ glG ℓ ∧ K.Λ.g ≤ glG ℓ ∧
    (∀ x, InE x → x < Om1 → K.Λ.g < x → glG ℓ < x) ∧ HnWShape (wnGW K.Λ) 0 V

/-- **THE ENTRY AT THE LEVEL `Ω₁`**: `Hn.hnPk1` and `Hg.hgU`. -/
theorem wnAt_base : WnAt Om1 hnPk1 hgU := by
  have hgO : glG Om1 = 1 := by rw [glG_low Om1_lt_eW, (rdc_Om1 0).2]
  refine ⟨rfl, fun x _ _ _ => ?_, hgU_B, ?_, ?_, fun x hx _ _ => ?_, wnU_shape⟩
  · rw [wh_hnPk1_l, glR_low Om1_lt_eW, (rdc_Om1 x).1]
  · rw [hgU_γ]; exact zero_le
  · show (0 : Ordinal.{0}) ≤ _; exact zero_le
  · rw [hgO]; exact one_lt_omega0.trans (omega0_lt_inE hx)

/-! ## The successor step -/

section Succ

variable {ℓ' : Ordinal.{0}} {K' : HnPk} {V' : HgVD}

/-- **The next system**: the union over `G` of the levels `ℓ' + κ`, `κ < Ω₁`, started at `V'`. -/
noncomputable def wnSuccV (hat : WnAt ℓ' K' V') : HgVD :=
  hnwU (wnGW K'.Λ) K'.St0 K'.h0 V' hat.2.2.2.2.2.2

theorem wnSuccV_B (hat : WnAt ℓ' K' V') : (wnSuccV hat).B = veblen (ℓ' + Om1) (gcG 0 + 1) := by
  show hdNx (K'.Λ.L + Om1) (gcG 0) = _
  rw [hdNx_fixP (hnG_FP K'.Λ), hat.1]

/-- **The next entry is an entry at `ℓ' + Ω₁`.** -/
theorem wnSucc_at (h2 : Om1 ∣ ℓ') (h3 : ℓ' < gcG 0) (hat : WnAt ℓ' K' V') :
    WnAt (ℓ' + Om1) K'.succ (wnSuccV hat) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, hsh⟩ := hat
  have hga := (wn_glR_add_Om1 ℓ' h3 h2 0).2
  refine ⟨by show K'.Λ.L + Om1 = _; rw [e1], fun x hx hx1 hg => ?_, wnSuccV_B _, ?_, ?_,
    fun x hx hx1 hg => wn_glG_add_Om1_lt hx h3 (e6 x hx hx1 hg), wnGU_shape K'.Λ K'.St0 K'.h0 V' _⟩
  · show K'.Λ.l x + x = _
    rw [e2 x hx hx1 hg, (wn_glR_add_Om1 ℓ' h3 h2 x).1]
  · show K'.Λ.g ≤ _; exact e5.trans hga
  · show K'.Λ.g ≤ _; exact e5.trans hga

/-- **The next entry extends the entry at `ℓ'`.** -/
theorem wnSucc_ext (hat : WnAt ℓ' K' V') : WhExt K' V' K'.succ (wnSuccV hat) := by
  set hsh := hat.2.2.2.2.2.2
  refine ⟨?_, ?_, fun c x hc => ⟨hnwU_R0 _ _ _ _ hsh hc x, hnwU_g0 _ _ _ _ hsh hc⟩⟩
  · intro hg' hL' hl' Q U hU c x hc
    have hsh' := hnw_shape_dn Q (K'.h0 Q.dn U hU)
    exact ⟨hnwU_R0 Q.toW K'.St0 K'.h0 _ hsh' hc x, hnwU_g0 Q.toW K'.St0 K'.h0 _ hsh' hc⟩
  · rw [wnSuccV_B hat, hat.2.2.1]
    exact hd_veb_left_lt (lt_add_of_pos_right _ wh_Om1_pos) _

/-- **The next entry extends every entry that the entry at `ℓ'` extends.** -/
theorem wnSucc_ext_lt (h2 : Om1 ∣ ℓ') (h3 : ℓ' < gcG 0) (hat : WnAt ℓ' K' V') {ℓ'' : Ordinal.{0}}
    (hlt : ℓ'' < ℓ') (hd'' : Om1 ∣ ℓ'') {K'' : HnPk} {V'' : HgVD}
    (hat'' : WnAt ℓ'' K'' V'') (hext : WhExt K'' V'' K' V') : WhExt K'' V'' K'.succ (wnSuccV hat) := by
  obtain ⟨n1, n2, -, -, -, n6, -⟩ := hat''
  obtain ⟨s1, s2, s3⟩ := wnSucc_ext hat
  have e1 := hat.1
  have e2 := hat.2.1
  have e6 := hat.2.2.2.2.2.1
  obtain ⟨x1, x2, x3⟩ := hext
  refine ⟨?_, x2.trans s2, fun c x hc => ?_⟩
  · intro hg' hL' hl' Q U hU c x hc
    have hsh' := hnw_shape_dn Q (K'.h0 Q.dn U hU)
    have hLa : K''.Λ.L + Om1 ≤ K'.Λ.L := by rw [n1, e1]; exact wh_lev_succ_le hd'' h2 hlt
    have hla : ∀ x, InE x → x < Om1 → K'.Λ.g < x → K''.Λ.l x + x ≤ K'.Λ.l x := fun x hx hx1 hgx => by
      have hgx'' : K''.Λ.g < x := hg'.trans_lt hgx
      rw [n2 x hx hx1 hgx'', e2 x hx hx1 hgx]
      exact wn_glR_step hx hx1 hd'' h2 hlt h3 (n6 x hx hx1 hgx'') (e6 x hx hx1 hgx)
    have hc0 : c < (K'.St0 Q.dn U hU).B := by
      rw [(K'.h0 Q.dn U hU).B]
      rw [(K''.h0 _ U hU).B] at hc
      exact hc.trans_le (hdNx_mono (add_le_add (le_self_add.trans hLa) le_rfl) _)
    obtain ⟨r1, g1⟩ := x1 hg' hLa hla Q.dn U hU c x hc
    exact ⟨(hnwU_R0 Q.toW K'.St0 K'.h0 _ hsh' hc0 x).trans r1, (hnwU_g0 Q.toW K'.St0 K'.h0 _ hsh' hc0).trans g1⟩
  · obtain ⟨r1, g1⟩ := s3 c x (hc.trans x2)
    obtain ⟨r2, g2⟩ := x3 c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

end Succ

end Googology.Trans.PoR.InaccPsi.R2.Wn
