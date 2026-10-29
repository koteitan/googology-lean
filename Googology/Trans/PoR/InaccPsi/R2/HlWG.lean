import Googology.Trans.PoR.InaccPsi.R2.HlWP
import Googology.Trans.PoR.InaccPsi.R2.HkFr

/-!
# HlWG: `G` AS A TWO-GATE BASE OF EVERY GATED LEVEL `L + Ω₁`

PORT of the first part of `Hj.HjWG` (`Hj.hjG_fix`, `hjG_glA`, `hjG_lt1`, `hjG_S_pi` are imported; the systems
`Hj.hjGU n` and their frontier are not ported).  `hlGW Λ`: code gate `0`, reading gate `Λ.g`, outer low field
`φ(x·x, Γ_{x+1}+1)` (independent of `Λ`; `Hj.hjGW` has `hdNx (ℓ(x)+x+x) Γ_{x+1}`); `hlgU_shape` (`Hg.hgU` starts
the recursion at the level `Ω₁`).

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definition: `hlGW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

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

section GW

variable (Λ : HlLv)

theorem hlG_one {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ Λ.l x + x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans le_add_self

theorem hlG_q {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x < lgG x := Λ.succ.l_lt x hx hx1

theorem hlG_q2 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x + x < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hlG_q Λ hx hx1) (lgG_facts hx hx1).2.1

theorem hlG_FP : veblen (Λ.L + Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) Λ.succ.L_G

/-- **`G` AS A BASE OF LEVEL `L + Ω₁`** (gate `0`, reading `Γ_{x+1}`, outer low field `hdNx (ℓ(x)+x+x) (Γ_{x+1})`). -/
noncomputable def hlGW : HlWB Λ where
  F := gcG 0
  Fr := lgG
  γ := 0
  γR := Λ.g
  Zo := fun x => veblen (max ω x * max ω x) (lgG x + 1)
  γ_lt := gv_Om1_pos
  γR_lt := Λ.g_lt
  γ_le := zero_le
  lg := le_rfl
  γR_cl := fun _ _ _ _ h => h
  F_P := ⟨gcG 0, hlG_FP Λ⟩
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Λ.L + Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (Λ.succ.L_lt 1)
    have h2 := (isNormal_veblen (Λ.L + Om1)).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rw [hdNx_fixP (hlG_FP Λ)]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  S_mem := fun S a b ha hb => by
    rw [hdNx_fixP (hlG_FP Λ)]
    exact CSet.phi_mem (Λ.succ.L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => hlG_q Λ hx hx1
  Fr_P := fun hx hx1 _ => ⟨lgG _, hjG_fix hx hx1 (hlG_one Λ hx) (hlG_q Λ hx hx1)⟩
  S_Zo := fun {x} hx hx1 hg => by
    show hdNx (Λ.l x + x) (lgG x) < veblen (max ω x * max ω x) (lgG x + 1)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP (hjG_fix hx hx1 (hlG_one Λ hx) (hlG_q Λ hx hx1))]
    exact hd_veb_left_lt (Λ.l_lt2 x hx hx1 hg) _
  Zo_fix := fun x => veblen_veblen_of_lt ((show (2 : Ordinal.{0}) < ω from by
    exact_mod_cast natCast_lt_omega0 2).trans_le (le_mul_of_one_le_right' (one_lt_omega0.le.trans
      (le_max_left ω x)) |>.trans' (le_max_left ω x))) _
  Zo_G1 := fun x hx hx1 => by
    show veblen (max ω x * max ω x) (lgG x + 1) < gq 1 x
    rw [max_eq_right (omega0_lt_inE hx).le]
    have hq : x * x < lgG x := InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 (lgG_facts hx hx1).2.1
    have h1 : (1 : Ordinal.{0}) ≤ x * x := (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le
    rw [← hdNx_fixP (hjG_fix hx hx1 h1 hq)]
    exact hjG_lt1 hx hx1 h1 hq
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  S_pi := fun hB hg => hjG_S_pi hB (Λ.succ.l_pi _ _ hB hg) (hlG_one Λ hB.2.1) (hlG_q Λ hB.2.1 hB.2.2.2)
    (hlG_one Λ hB.1) (hlG_q Λ hB.1 (hB.2.2.1.trans hB.2.2.2))

theorem hlGW_γ : (hlGW Λ).γ = 0 := rfl

theorem hlGW_γR : (hlGW Λ).γR = Λ.g := rfl

/-- **The union over `G` with a package at `Λ` starts the next package at `Λ.succ`.** -/
theorem hlGU_shape (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h)) (S0 : HgVD)
    (hS0 : HlWShape (hlGW Λ) 0 S0) : HlWShape (hlGW Λ.succ) 0 (hlwU (hlGW Λ) St0 h0 S0 hS0) := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hdNx (Λ.L + Om1) (gcG 0) = veblen (Λ.succ.L + 0) (gcG 0 + 1)
    rw [add_zero, hdNx_fixP (hlG_FP Λ)]; rfl
  · show Λ.g < x ↔ max Λ.g 0 < x
    rw [max_eq_left zero_le]
  · show hdNx (Λ.l x + x) (lgG x) = veblen (Λ.succ.l x + 0) (lgG x + 1)
    rw [add_zero, hdNx_fixP (hjG_fix hx hx1 (hlG_one Λ hx) (hlG_q Λ hx hx1))]; rfl
  · show hlwUZ (hlGW Λ) x = if max Λ.g 0 < x then evZ (veblen (Λ.succ.l x + 0) (lgG x + 1))
      else (hlGW Λ.succ).hlwZo x
    unfold hlwUZ
    rw [max_eq_left zero_le]
    by_cases hg : Λ.g < x
    · rw [if_pos (show (hlGW Λ).γR < x from hg), if_pos hg, add_zero]
      show evZ (hdNx (Λ.l x + x) (lgG x)) = evZ (veblen (Λ.l x + x) (lgG x + 1))
      rw [hdNx_fixP (hjG_fix hx hx1 (hlG_one Λ hx) (hlG_q Λ hx hx1))]
    · rw [if_neg (show ¬ (hlGW Λ).γR < x from hg), if_neg hg,
        (hlGW Λ.succ).hlwZo_low (show ¬ (hlGW Λ.succ).γR < x from hg)]
      rfl

end GW

/-- **`Hg.hgU` is a start over `G` at the level `Ω₁ + 0`.** -/
theorem hlgU_shape : HlWShape (hlGW hlL1) 0 hgU := by
  refine ⟨by show veblen Om1 (gcG 0 + 1) = veblen (Om1 + 0) (gcG 0 + 1); rw [add_zero], fun x _ _ => ?_,
    fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max (0 : Ordinal.{0}) 0 < x
    rw [max_self]
  · show veblen x (lgG x + 1) = veblen (x + 0) (lgG x + 1)
    rw [add_zero]
  · show evZ (hcBR x) = if max 0 0 < x then evZ (veblen (x + 0) (lgG x + 1)) else (hlGW hlL1).hlwZo x
    rw [max_self, if_pos hx.pos, add_zero]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Hl
