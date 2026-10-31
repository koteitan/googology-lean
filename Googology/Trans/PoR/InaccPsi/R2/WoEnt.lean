import Googology.Trans.PoR.InaccPsi.R2.WoA1

/-!
# WoEnt: THE FAMILY AS ENTRIES OF THE OLD INDUCTION (`Wh.WhAt`, `Wm.WmExtE`), WITH NO HYPOTHESIS

* `woEnt ℓ` (**the package `Wo.woPkOf ℓ (woF ℓ)` and the system `Wo.woV ℓ` over `G`**);
* `woEnt_at` (**EVERY ENTRY IS A `Wh.WhAt` ENTRY**), `woEnt_ext` (**EVERY PAIR EXTENDS IN THE CORRECTED SENSE
  `Wm.WmExtE`**, so in the old sense too), `woFamW2` (**THE FAMILY OF `Wm` ON ALL LEVELS BELOW `ε_{Ω₁+1}`**: the
  conclusion of `Wm.wmFam` at `ε_{Ω₁+1}` with no hypothesis; it replaces the remaining case `Wm.WmOm1Step`);
* `wo_gate_ge` (**REFUTE-FIRST FINDING on `Wm.WmOm1Step`**: every `Wh.WhAt` entry at `Ω₁·x`, `x` an `ε`-number, has
  gate `≥ x`; so at a pseudo-base with gate `γ < x` an arbitrary member at `Ω₁·x` has no lowered step,
  `wo_noLowr`, and a step for arbitrary coherent families must build those members itself).

No new axiom.  New definitions: `woEnt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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

open Classical in
/-- **THE ENTRY AT `ℓ`**: the package of the family and the system over `G`. -/
noncomputable def woEnt (ℓ : Ordinal.{0}) : WmEnt :=
  if h : WmLev ℓ then (woPkOf ℓ h (woF ℓ) (woFam ℓ h).1, ULift.up (woV ℓ)) else (hnPk1, ULift.up hgU)

theorem woEnt_eq {ℓ : Ordinal.{0}} (h : WmLev ℓ) :
    woEnt ℓ = (woPkOf ℓ h (woF ℓ) (woFam ℓ h).1, ULift.up (woV ℓ)) := by
  unfold woEnt; rw [dif_pos h]

/-- **EVERY ENTRY IS A `Wh.WhAt` ENTRY.** -/
theorem woEnt_at {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) : WhAt ℓ (woEnt ℓ).1 (woEnt ℓ).2.down := by
  rw [woEnt_eq hℓ]
  obtain ⟨sB, ⟨-, sγ2⟩, sγ, sb, sZ, shi⟩ := woV_sh hℓ
  have hmx : ∀ x : Ordinal.{0}, max woG.γ (gtc ℓ) < x ↔ max (gtc ℓ) 0 < x := fun x => by
    show max (0 : Ordinal.{0}) (gtc ℓ) < x ↔ _
    rw [max_eq_right zero_le, max_eq_left zero_le]
  have hN : WhNB (woLv ℓ hℓ) := fun x hx hx1 hg => by
    rw [woLv_l hℓ hx hg]
    exact (inE_indec (eN_E x)).add_lt (rdc_lt_eN hx ℓ hg) (lt_eN x)
  refine ⟨rfl, fun x hx _ hg => woLv_l hℓ hx hg, woV_B hℓ, woV_γ hℓ, le_rfl, fun _ _ _ h => h, hN,
    ?_, fun x hx hx1 => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, fun c σ h1 h2 hσ hσ1 h3 => ?_⟩
  · show (woV ℓ).B = veblen (ℓ + 0) (gcG 0 + 1)
    rw [add_zero]; exact woV_B hℓ
  · show (woV ℓ).γ < x ↔ max (gtc ℓ) 0 < x
    rw [sγ x hx hx1]; exact hmx x
  · have hk' : max woG.γ (gtc ℓ) < x := (hmx x).2 hk
    show (woV ℓ).b x = veblen (whRd ℓ x + 0) (lgG x + 1)
    have hg : gtc ℓ < x := (max_lt_iff.1 hk).1
    rw [sb x hx hx1 hk', add_zero, whRd_eq hx hℓ.1 hℓ.2.2 hg]
    exact hdNx_fixP (hjG_fix hx hx1 (wo_one_le_rdc hℓ hx) (wo_rdc_lt_lgG hℓ hx hx1 hg))
  · show (woV ℓ).Z x = if max (gtc ℓ) 0 < x then evZ (veblen (whRd ℓ x + 0) (lgG x + 1))
      else (whGW (woLv ℓ hℓ) hN).hnwZo x
    rw [sZ x hx hx1]
    by_cases hk : max (gtc ℓ) 0 < x
    · have hg : gtc ℓ < x := (max_lt_iff.1 hk).1
      rw [if_pos ((hmx x).2 hk), if_pos hk, add_zero, whRd_eq hx hℓ.1 hℓ.2.2 hg]
      show evZ (hdNx (rdc ℓ x) (lgG x)) = evZ (veblen (rdc ℓ x) (lgG x + 1))
      rw [hdNx_fixP (hjG_fix hx hx1 (wo_one_le_rdc hℓ hx) (wo_rdc_lt_lgG hℓ hx hx1 hg))]
    · rw [if_neg (fun h => hk ((hmx x).1 h)), if_neg hk,
        (whGW (woLv ℓ hℓ) hN).hnwZo_low (show ¬ (whGW (woLv ℓ hℓ) hN).γR < x from
          fun h => hk (by rw [max_eq_left zero_le]; exact h))]
      rfl
  · exact shi c σ h1 h2 hσ hσ1 h3

/-- **EVERY PAIR OF ENTRIES EXTENDS IN THE CORRECTED SENSE `Wm.WmExtE`.** -/
theorem woEnt_ext {ℓ' ℓ : Ordinal.{0}} (hℓ' : WmLev ℓ') (hℓ : WmLev ℓ) (hlt : ℓ' < ℓ) :
    WmExtE (woEnt ℓ') (woEnt ℓ) := by
  rw [woEnt_eq hℓ', woEnt_eq hℓ]
  have hE := (woFam ℓ hℓ).2 ℓ' hlt hℓ'
  refine ⟨fun Q hg hL hl U hU c x hc => ?_, ?_, fun c x hc => ?_⟩
  · have e1 : (woPkOf ℓ' hℓ' (woF ℓ') (woFam ℓ' hℓ').1).St0 (wmLowr Q (woPkOf ℓ' hℓ' (woF ℓ')
        (woFam ℓ' hℓ').1).Λ hg hL hl) U hU = woF ℓ' (woQR Q) (woSt1 hℓ Q U hU) := rfl
    have e2 : (woPkOf ℓ hℓ (woF ℓ) (woFam ℓ hℓ).1).St0 Q U hU = woF ℓ (woQR Q) (woSt1 hℓ Q U hU) := rfl
    rw [e1] at hc
    rw [e1, e2]
    exact hE (woQR Q) _ (woGood_Q hℓ Q) (woSt1_sh hℓ Q U hU) c x hc
  · show (woV ℓ').B < (woV ℓ).B
    rw [(woV_sh hℓ').1, (woV_sh hℓ).1]
    exact wo_N_lt hℓ (woGood_G hℓ).F_P hlt
  · exact hE woG hgU (woGood_G hℓ) woSh_hgU c x hc

/-- **THE FAMILY OF `Wm` ON ALL LEVELS BELOW `ε_{Ω₁+1}`, WITH NO HYPOTHESIS** (the conclusion of `Wm.wmFam` at
`ε_{Ω₁+1}`). -/
theorem woFamW2 : ∀ ℓ, WmLev ℓ → WhAt ℓ (woEnt ℓ).1 (woEnt ℓ).2.down ∧
    ∀ ℓ', ℓ' < ℓ → WmLev ℓ' → WmExtE (woEnt ℓ') (woEnt ℓ) := fun ℓ hℓ =>
  ⟨woEnt_at hℓ, fun ℓ' h h' => woEnt_ext h' hℓ h⟩

/-! ## The refute-first finding on `Wm.WmOm1Step` -/

theorem wo_gtc_Om1_mul {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : gtc (Om1 * x) = x := by
  have h := wm_gtc_term (e := 1) (d := x) (gf_one_lt_Om1.trans Om1_lt_eW) hx.pos.ne' hx1
  rw [opow_one, (rdc_const gf_one_lt_Om1 0).2] at h
  rw [h]; exact max_eq_right (wo_one_lt_inE hx).le

/-- **EVERY `Wh.WhAt` ENTRY AT `Ω₁·x` (`x` AN `ε`-NUMBER) HAS GATE `≥ x`.** -/
theorem wo_gate_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {K : HnPk} {V : HgVD}
    (h : WhAt (Om1 * x) K V) : x ≤ K.Λ.g := by
  by_contra hlt
  have := h.2.2.2.2.2.1 x hx hx1 (not_le.1 hlt)
  rw [wo_gtc_Om1_mul hx hx1] at this
  exact lt_irrefl x this

/-- **No lowered step**: an entry at `Ω₁·x` cannot be lowered to a pseudo-base whose gate is below `x`. -/
theorem wo_noLowr {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {K : HnPk} {V : HgVD}
    (h : WhAt (Om1 * x) K V) {Λ : HnLv} (Q : HnVQ Λ 0) (hγ : Q.γ < x) : ¬ K.Λ.g ≤ Q.γ :=
  fun hg => absurd ((wo_gate_ge hx hx1 h).trans hg) (not_le.2 hγ)

end Googology.Trans.PoR.InaccPsi.R2.Wo
