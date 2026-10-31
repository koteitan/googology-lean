import Googology.Trans.PoR.InaccPsi.R2.WhLeaf

/-!
# WhGW: `G` AS A TWO-GATE BASE OF EVERY LEVEL BELOW `ε_{Ω₁+1}`; `Hg.hgU` IS A START AT THE LEVEL `Ω₁`

PORT of `Hn.hnGW` / `Hn.hnGU_shape` (the same proofs) to every level datum whose reading stays below `ε_{x+1}`.
What differs from `Hn.hnGW`: the outer low field of `G` is `φ(ε_{x+1}, Γ_{x+1}+1)` (one field for every level below
`ε_{Ω₁+1}`) in place of `φ(x·x·2, Γ_{x+1}+1)`, so the base asks the bound `WhNB Λ` (`ℓ(x) + x < ε_{x+1}` above the
gate) in place of `Hn.HnNB Λ` (`ℓ(x) + x < x·x·2`).

* `WhNB`, `whZo`, `whZo_G1`, `whGW Λ hN` (**`G` AS A BASE OF LEVEL `L + Ω₁`**), `whGU_shape` (**the union over
  `whGW Λ` started at a start over it is a start over `whGW Λ.succ`**);
* `wh_hnL1_NB`, `whU_shape` (**`Hg.hgU` IS A START OVER `G` AT THE LEVEL `Ω₁ + 0`**).

No new axiom.  New definitions: `WhNB`, `whZo`, `whGW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wh

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

/-- **The outer-field bound of a level datum below `ε_{Ω₁+1}`**: `ℓ(x) + x < ε_{x+1}` above the gate. -/
def WhNB (Λ : HnLv) : Prop := ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x + x < eN x

/-- **The outer low field of `G`**: `φ(ε_{x+1}, Γ_{x+1}+1)` (`x` replaced by `ω` below `ω`). -/
noncomputable def whZo (x : Ordinal.{0}) : Ordinal.{0} := veblen (eN (max ω x)) (lgG x + 1)

theorem wh_eN_lt_lgG {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < lgG x := gT_lt_lgG hx hx1 0

theorem wh_one_le_eN (x : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ eN x :=
  Order.one_le_iff_pos.2 (eN_E x).pos

/-- **`φ(ε_{x+1}, Γ_{x+1}+1) < Γ_{x+2}`.** -/
theorem whZo_G1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : whZo x < gq 1 x := by
  unfold whZo; rw [max_eq_right (omega0_lt_inE hx).le]
  rw [← hdNx_fixP (hjG_fix hx hx1 (wh_one_le_eN x) (wh_eN_lt_lgG hx hx1))]
  exact hjG_lt1 hx hx1 (wh_one_le_eN x) (wh_eN_lt_lgG hx hx1)

theorem whZo_fix (x : Ordinal.{0}) : veblen 2 (whZo x) = whZo x := by
  unfold whZo
  refine veblen_veblen_of_lt ?_ _
  calc (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  _ ≤ max ω x := le_max_left _ _
  _ < eN (max ω x) := lt_eN _

section GW

variable (Λ : HnLv)

/-- **`G` AS A BASE OF LEVEL `L + Ω₁`** (code gate `0`, reading gate `g`, reading `Γ_{x+1}`, outer low field
`φ(ε_{x+1}, Γ_{x+1}+1)`). -/
noncomputable def whGW (hN : WhNB Λ) : HnWB Λ where
  F := gcG 0
  Fr := lgG
  γ := 0
  γR := Λ.g
  Zo := whZo
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
  S_Zo := fun {x} hx hx1 hg => by
    show hdNx (Λ.l x + x) (lgG x) < veblen (eN (max ω x)) (lgG x + 1)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]
    exact hd_veb_left_lt (hN x hx hx1 hg) _
  Zo_fix := whZo_fix
  Zo_G1 := fun _ hx hx1 => whZo_G1 hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  S_pi := fun hB hg => hjG_S_pi hB (Λ.succ.l_pi _ _ hB hg) (hnG_one Λ hB.2.1) (hnG_q Λ hB.2.1 hB.2.2.2)
    (hnG_one Λ hB.1) (hnG_q Λ hB.1 (hB.2.2.1.trans hB.2.2.2))

theorem whGW_γ (hN : WhNB Λ) : (whGW Λ hN).γ = 0 := rfl

theorem whGW_γR (hN : WhNB Λ) : (whGW Λ hN).γR = Λ.g := rfl

theorem whGW_F (hN : WhNB Λ) : (whGW Λ hN).F = gcG 0 := rfl

/-- **The union over `G` with a package at `Λ` starts the next package at `Λ.succ`.** -/
theorem whGU_shape (hN : WhNB Λ) (hN' : WhNB Λ.succ) (St0 : HnVStTy Λ 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h))
    (S0 : HgVD) (hS0 : HnWShape (whGW Λ hN) 0 S0) :
    HnWShape (whGW Λ.succ hN') 0 (hnwU (whGW Λ hN) St0 h0 S0 hS0) := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hdNx (Λ.L + Om1) (gcG 0) = veblen (Λ.succ.L + 0) (gcG 0 + 1)
    rw [add_zero, hdNx_fixP (hnG_FP Λ)]; rfl
  · show Λ.g < x ↔ max Λ.g 0 < x
    rw [max_eq_left zero_le]
  · show hdNx (Λ.l x + x) (lgG x) = veblen (Λ.succ.l x + 0) (lgG x + 1)
    rw [add_zero, hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]; rfl
  · show hnwUZ (whGW Λ hN) x = if max Λ.g 0 < x then evZ (veblen (Λ.succ.l x + 0) (lgG x + 1))
      else (whGW Λ.succ hN').hnwZo x
    unfold hnwUZ
    rw [max_eq_left zero_le]
    by_cases hg : Λ.g < x
    · rw [if_pos (show (whGW Λ hN).γR < x from hg), if_pos hg, add_zero]
      show evZ (hdNx (Λ.l x + x) (lgG x)) = evZ (veblen (Λ.l x + x) (lgG x + 1))
      rw [hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]
    · rw [if_neg (show ¬ (whGW Λ hN).γR < x from hg), if_neg hg,
        (whGW Λ.succ hN').hnwZo_low (show ¬ (whGW Λ.succ hN').γR < x from hg)]
      rfl

end GW

/-! ## The start: `Hg.hgU` at the level `Ω₁ + 0` -/

theorem wh_hnL1_g : hnL1.g = 0 := rfl

/-- **The level datum `Ω₁` has the outer-field bound** `x + x < ε_{x+1}`. -/
theorem wh_hnL1_NB : WhNB hnL1 := fun x hx _ _ => by
  show x + x < eN x
  exact (eN_E x |> inE_indec).add_lt (lt_eN x) (lt_eN x)

/-- **`Hg.hgU` IS A START OVER `G` AT THE LEVEL `Ω₁ + 0`.** -/
theorem whU_shape : HnWShape (whGW hnL1 wh_hnL1_NB) 0 hgU := by
  refine ⟨by show veblen Om1 (gcG 0 + 1) = veblen (Om1 + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max (0 : Ordinal.{0}) 0 < x
    rw [max_self]
  · show veblen x (lgG x + 1) = veblen (x + 0) (lgG x + 1)
    rw [add_zero]
  · show evZ (hcBR x) = if max 0 0 < x then evZ (veblen (x + 0) (lgG x + 1))
      else (whGW hnL1 wh_hnL1_NB).hnwZo x
    rw [max_self, if_pos hx.pos, add_zero]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Wh
