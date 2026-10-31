import Googology.Trans.PoR.InaccPsi.R2.HnQU

/-!
# HnWG: `G` AS A TWO-GATE BASE OF EVERY BAND LEVEL `L + Ω₁`; THE FIRST BAND SYSTEM `φ(Ω₁·Ω₁ + Ω₁, G+1)`

PORT of `Hl.HlWG` (`Hl.hlGW`, `Hl.hlGU_shape`) to the band level datum `Hn.HnLv`.  What differs: the outer low field of
`G` is `φ(x·x·2, Γ_{x+1}+1)` (the reading of the next union `Ω₁·Ω₁·2`) in place of `φ(x·x, Γ_{x+1}+1)`, so the base asks
the hypothesis `HnNB Λ` (`ℓ(x) + x < x·x·2` above the gate) in place of the field `ℓ(x) + x < x·x` of `Hl.HlLv`; the
start of the band recursion is `Hl.hlU` (bound `φ(Ω₁·Ω₁, G+1)`) at the datum `hnSqLv`, in place of `Hg.hgU`.

* `HnNB`, `hnGW Λ hN` (**`G` AS A BASE OF LEVEL `L + Ω₁`**), `hnGU_shape`;
* `hnSqNB`, `hnU_shape` (**`Hl.hlU` IS A START OVER `G` AT THE LEVEL `Ω₁·Ω₁ + 0`**);
* `hnS1` (**THE SYSTEM AT `φ(Ω₁·Ω₁ + Ω₁, G+1)`**: the union over `G` of the levels `Ω₁·Ω₁ + κ`, `κ < Ω₁`, started at
  `Hl.hlU`, with the steps of the package `hnPkSq`), `hnS1_B`, `hnS1_γ`, `hnS1_loc` (**LOCATED**), `hnS1_blk`,
  `hnS1_enum`, `hnS1_capV`, `hnS1_road`.

No new axiom.  New definitions: `HnNB`, `hnGW`, `hnS1`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## `G` as a base of level `L + Ω₁`, with two gates -/

theorem hn_sq2_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x * x * 2 < lgG x :=
  InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (hl_sq_lt hx hx1)
    ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
      ((omega0_lt_inE hx).trans (lgG_facts hx hx1).2.1))

theorem hn_sq2_one {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ x * x * 2 :=
  ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le).trans (le_mul_of_one_le_right' one_le_two)

/-- **`φ(x·x·2, Γ_{x+1}+1) < Γ_{x+2}`.** -/
theorem hn_sq2_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (x * x * 2) (lgG x + 1) < gq 1 x := by
  rw [← hdNx_fixP (hjG_fix hx hx1 (hn_sq2_one hx) (hn_sq2_lt hx hx1))]
  exact hjG_lt1 hx hx1 (hn_sq2_one hx) (hn_sq2_lt hx hx1)

/-- **The outer-field bound of a band level datum**: `ℓ(x) + x < x·x·2` above the gate. -/
def HnNB (Λ : HnLv) : Prop := ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x + x < x * x * 2

section GW

variable (Λ : HnLv)

theorem hnG_one {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ Λ.l x + x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans le_add_self

theorem hnG_q {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x < lgG x := Λ.succ.l_lt x hx hx1

theorem hnG_q2 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x + x < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hnG_q Λ hx hx1) (lgG_facts hx hx1).2.1

theorem hnG_FP : veblen (Λ.L + Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) Λ.succ.L_G

/-- **`G` AS A BASE OF LEVEL `L + Ω₁`** (code gate `0`, reading gate `g`, reading `Γ_{x+1}`, outer low field
`φ(x·x·2, Γ_{x+1}+1)`). -/
noncomputable def hnGW (hN : HnNB Λ) : HnWB Λ where
  F := gcG 0
  Fr := lgG
  γ := 0
  γR := Λ.g
  Zo := fun x => veblen (max ω x * max ω x * 2) (lgG x + 1)
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
    show hdNx (Λ.l x + x) (lgG x) < veblen (max ω x * max ω x * 2) (lgG x + 1)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]
    exact hd_veb_left_lt (hN x hx hx1 hg) _
  Zo_fix := fun x => veblen_veblen_of_lt ((show (2 : Ordinal.{0}) < ω from by
    exact_mod_cast natCast_lt_omega0 2).trans_le ((le_mul_of_one_le_right' (one_lt_omega0.le.trans
      (le_max_left ω x)) |>.trans' (le_max_left ω x)).trans (le_mul_of_one_le_right' one_le_two))) _
  Zo_G1 := fun x hx hx1 => by
    show veblen (max ω x * max ω x * 2) (lgG x + 1) < gq 1 x
    rw [max_eq_right (omega0_lt_inE hx).le]
    exact hn_sq2_lt1 hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  S_pi := fun hB hg => hjG_S_pi hB (Λ.succ.l_pi _ _ hB hg) (hnG_one Λ hB.2.1) (hnG_q Λ hB.2.1 hB.2.2.2)
    (hnG_one Λ hB.1) (hnG_q Λ hB.1 (hB.2.2.1.trans hB.2.2.2))

theorem hnGW_γ (hN : HnNB Λ) : (hnGW Λ hN).γ = 0 := rfl

theorem hnGW_γR (hN : HnNB Λ) : (hnGW Λ hN).γR = Λ.g := rfl

/-- **The union over `G` with a package at `Λ` starts the next package at `Λ.succ`.** -/
theorem hnGU_shape (hN : HnNB Λ) (hN' : HnNB Λ.succ) (St0 : HnVStTy Λ 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h))
    (S0 : HgVD) (hS0 : HnWShape (hnGW Λ hN) 0 S0) :
    HnWShape (hnGW Λ.succ hN') 0 (hnwU (hnGW Λ hN) St0 h0 S0 hS0) := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hdNx (Λ.L + Om1) (gcG 0) = veblen (Λ.succ.L + 0) (gcG 0 + 1)
    rw [add_zero, hdNx_fixP (hnG_FP Λ)]; rfl
  · show Λ.g < x ↔ max Λ.g 0 < x
    rw [max_eq_left zero_le]
  · show hdNx (Λ.l x + x) (lgG x) = veblen (Λ.succ.l x + 0) (lgG x + 1)
    rw [add_zero, hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]; rfl
  · show hnwUZ (hnGW Λ hN) x = if max Λ.g 0 < x then evZ (veblen (Λ.succ.l x + 0) (lgG x + 1))
      else (hnGW Λ.succ hN').hnwZo x
    unfold hnwUZ
    rw [max_eq_left zero_le]
    by_cases hg : Λ.g < x
    · rw [if_pos (show (hnGW Λ hN).γR < x from hg), if_pos hg, add_zero]
      show evZ (hdNx (Λ.l x + x) (lgG x)) = evZ (veblen (Λ.l x + x) (lgG x + 1))
      rw [hdNx_fixP (hjG_fix hx hx1 (hnG_one Λ hx) (hnG_q Λ hx hx1))]
    · rw [if_neg (show ¬ (hnGW Λ hN).γR < x from hg), if_neg hg,
        (hnGW Λ.succ hN').hnwZo_low (show ¬ (hnGW Λ.succ hN').γR < x from hg)]
      rfl

end GW

/-! ## The start: `Hl.hlU` at the level `Ω₁·Ω₁ + 0` -/

/-- **The band datum `Ω₁·Ω₁` has the outer-field bound**: `x·x + x < x·x·2`. -/
theorem hnSqNB : HnNB hnSqLv := fun _ hx _ _ => Hm.hmSq_next_bound hx

/-- **`Hl.hlU` IS A START OVER `G` AT THE LEVEL `Ω₁·Ω₁ + 0`.** -/
theorem hnU_shape : HnWShape (hnGW hnSqLv hnSqNB) 0 hlU := by
  refine ⟨by show veblen (Om1 * Om1) (gcG 0 + 1) = veblen (Om1 * Om1 + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max (0 : Ordinal.{0}) 0 < x
    rw [max_self]
  · show veblen (x * x) (lgG x + 1) = veblen (x * x + 0) (lgG x + 1)
    rw [add_zero]
  · show evZ (hlBR x) = if max 0 0 < x then evZ (veblen (x * x + 0) (lgG x + 1))
      else (hnGW hnSqLv hnSqNB).hnwZo x
    rw [max_self, if_pos hx.pos, add_zero]; rfl

/-! ## The first band system `φ(Ω₁·Ω₁ + Ω₁, G+1)` -/

/-- **THE SYSTEM AT `φ(Ω₁·Ω₁ + Ω₁, G+1)`**: the union over `G` of all levels `Ω₁·Ω₁ + κ`, `κ < Ω₁`, started at
`Hl.hlU`, with the steps of the package `hnPkSq`. -/
noncomputable def hnS1 : HgVD := hnwU (hnGW hnSqLv hnSqNB) hnPkSq.St0 hnPkSq.h0 hlU hnU_shape

theorem hnS1_B : hnS1.B = veblen (Om1 * Om1 + Om1) (gcG 0 + 1) := by
  show hdNx (Om1 * Om1 + Om1) (gcG 0) = _
  exact hdNx_fixP (hnG_FP hnSqLv)

theorem hnS1_γ : hnS1.γ = 0 := rfl

theorem hnS1_b (x : Ordinal.{0}) : hnS1.b x = hdNx (x * x + x) (lgG x) := rfl

/-- **`hnS1` extends `Hl.hlU`.** -/
theorem hnS1_ext {c : Ordinal.{0}} (hc : c < hlU.B) (x : Ordinal.{0}) : hnS1.R c x = hlU.R c x ∧ hnS1.g c = hlU.g c :=
  ⟨hnwU_R0 _ _ _ _ hnU_shape hc x, hnwU_g0 _ _ _ _ hnU_shape hc⟩

section Loc

variable (S : InaccSeq.{0})

theorem hnS1_γK : hnS1.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁·Ω₁ + Ω₁, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁·Ω₁ + Ω₁, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem hnS1_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hnS1.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG hnS1.B * ω) ∧ Pv S (gcG hnS1.B * ω) < Nc.ncL S 0 :=
  hgV_locD hnS1 S (hnS1_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·Ω₁ + Ω₁, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hnS1_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hnS1.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum hnS1 S (hnS1_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·Ω₁ + Ω₁, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hnS1_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hnS1.B * ω)) : CdCapV S l :=
  hgV_locD_capV hnS1 S (hnS1_γK S) hr hl

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Hn
