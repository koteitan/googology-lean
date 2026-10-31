import Googology.Trans.PoR.InaccPsi.R2.HnLow
import Googology.Trans.PoR.InaccPsi.R2.HlU

/-!
# HnQW: THE LEVEL `Ω₁·Ω₁` AS A BAND LEVEL DATUM; A PSEUDO-BASE OF IT IS A TWO-GATE BASE OF EVERY LEVEL `Ω₁·q`

* `hnSqLv` (**the band level datum `Ω₁·Ω₁`**, read `x·x`, gate `0`; band `u = Ω₁`, `q = 0`);
* `hnq_lt` (`L + Ω₁ + 1 < Ω₁·Ω₁` for every `Hl.HlLv`), `hnq_lle` (`ℓ(x) + x ≤ x·x` above the gate);
* `hnQW Q Λ` (**A PSEUDO-BASE `Q` OF LEVEL `Ω₁·Ω₁ + 0` IS A TWO-GATE BASE `Hl.HlWB Λ` OF EVERY `Hl.HlLv` `Λ`**: the same
  point, reading and outer low field, code gate `Q.γ`, reading gate `max Q.γ Λ.g`; this is `Hl.hlGW` with `G`
  replaced by `Q.F` and the reading gate raised to the level gate);
* `hnQ1` (the same pseudo-base read at the level `Ω₁ + 0`: an `Hl.HlVQ Hl.hlL1 0`), `hnQ1_shape` (a system with the
  specification of level `Ω₁ + 0` at `hnQ1 Q` is a start over `hnQW Q Hl.hlL1`).

No new axiom.  New definitions: `hnSqLv`, `hnQW`, `hnQ1`.
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

/-! ## The band level datum `Ω₁·Ω₁` -/

theorem hn_le_sq (x : Ordinal.{0}) : x ≤ x * x := by
  rcases eq_or_ne x 0 with rfl | h
  · rw [mul_zero]
  · exact le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 h)

/-- **THE BAND LEVEL DATUM `Ω₁·Ω₁`**, read `x·x`, gate `0` (band `Ω₁·Ω₁ + Ω₁·0`). -/
noncomputable def hnSqLv : HnLv where
  L := Om1 * Om1
  l := fun x => x * x
  u := Om1
  q := 0
  g := 0
  g_lt := gv_Om1_pos
  q_lt := gv_Om1_pos
  OL := le_mul_of_one_le_right' hg_one_lt_Om1.le
  L_G := hl_OO_lt_G 0
  L_eq := by rw [mul_zero, add_zero, Br.Om1_eq]
  g_cl := fun _ _ hZ _ _ _ _ => hZ.1
  L_mem := fun S a b _ _ => hl_OO_mem S a b
  l_ge := hn_le_sq
  l_lt := fun _ hx hx1 => hl_sq_lt hx hx1
  l_pi := fun _ _ hB _ => pi_sq hB

theorem hnSqLv_L : hnSqLv.L = Om1 * Om1 := rfl

theorem hnSqLv_l (x : Ordinal.{0}) : hnSqLv.l x = x * x := rfl

theorem hnSqLv_g : hnSqLv.g = 0 := rfl

/-! ## Every `Hl.HlLv` lies below `Ω₁·Ω₁` -/

/-- **`L + Ω₁ + 1 < Ω₁·Ω₁`** for every `Hl.HlLv`. -/
theorem hnq_lt (Λ : HlLv) : Λ.L + Om1 + 1 < Om1 * Om1 := by
  have h := Λ.succ.L_add_lt (ν := 1) (by rw [← Br.Om1_eq]; exact hg_one_lt_Om1)
  rw [← Br.Om1_eq] at h
  exact h

theorem hnq_le (Λ : HlLv) : Λ.L + Om1 ≤ hnSqLv.L + 0 := by
  rw [add_zero]; exact (lt_add_one _).le.trans (hnq_lt Λ).le

theorem hnq_lt0 (Λ : HlLv) : Λ.L + Om1 < hnSqLv.L + 0 := by
  rw [add_zero]; exact (lt_add_one _).trans (hnq_lt Λ)

/-- **`ℓ(x) + x ≤ x·x + 0`** above the gate. -/
theorem hnq_lle (Λ : HlLv) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : Λ.g < x) :
    Λ.l x + x ≤ hnSqLv.l x + 0 := by
  rw [add_zero]; exact (Λ.l_lt2 x hx hx1 hg).le

theorem hnq_llt (Λ : HlLv) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : Λ.g < x) :
    Λ.l x + x < hnSqLv.l x + 0 := by
  rw [add_zero]; exact Λ.l_lt2 x hx hx1 hg

/-! ## A pseudo-base of level `Ω₁·Ω₁` as a two-gate base of every lower level -/

section QW

variable (Q : HnVQ hnSqLv 0) (Λ : HlLv)

theorem hnq_Ffix : veblen (Λ.L + Om1) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt (hnq_lt0 Λ) a

theorem hnq_S_lt : hdNx (Λ.L + Om1) Q.F < hdNx (hnSqLv.L + 0) Q.F := by
  refine (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx ?_)
  rw [add_zero]; exact hnq_lt Λ

theorem hnq_rfix {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (hg : Λ.g < x) :
    veblen (Λ.l x + x) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (hnq_llt Λ hx hx1 hg) a

/-- **Lemma EXACT for `hdNx (ℓ(ρ)+ρ) (F(ρ))`** above both gates. -/
theorem hnq_S_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Q.γ < σ) (hg : Λ.g < σ) :
    hdNx (Λ.l ρ + ρ) (Q.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + ρ) (Q.Fr ρ)) = hdNx (Λ.l σ + σ) (Q.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
  have hgρ : Λ.g < ρ := hg.trans hB.2.2.1
  obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
  have h := hlv_glA_pi Λ.succ hB hg hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
  have hfρ : veblen (Λ.succ.l ρ + 0) (Q.Fr ρ) = Q.Fr ρ := by
    rw [add_zero]; exact hnq_rfix Q Λ hB.2.1 hρ1 hγρ hgρ
  have hfσ : veblen (Λ.succ.l σ + 0) (Q.Fr σ) = Q.Fr σ := by
    rw [add_zero]; exact hnq_rfix Q Λ hB.1 hσ1 hγ hg
  have hgtρ : Λ.succ.l ρ + 0 < Q.Fr ρ := by
    rw [add_zero]; exact (hnq_lle Λ hB.2.1 hρ1 hgρ).trans_lt (Q.Fr_gt hB.2.1 hρ1 hγρ)
  have hgtσ : Λ.succ.l σ + 0 < Q.Fr σ := by
    rw [add_zero]; exact (hnq_lle Λ hB.1 hσ1 hg).trans_lt (Q.Fr_gt hB.1 hσ1 hγ)
  rw [f2, hlv_glA_fixP Λ.succ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) hfρ hgtρ (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
    hlv_glA_fixP Λ.succ hB.1 hσ1 hB.1.pos hfσ hgtσ (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
  simpa only [HlLv.succ_l, add_zero] using h

/-- **A PSEUDO-BASE OF LEVEL `Ω₁·Ω₁ + 0` IS A TWO-GATE BASE OF EVERY `Hl.HlLv` `Λ`** (level `L + Ω₁`): the same point,
reading and outer low field; code gate `Q.γ`, reading gate `max Q.γ Λ.g`. -/
noncomputable def hnQW : HlWB Λ where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  γR := max Q.γ Λ.g
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  γR_lt := max_lt Q.γ_lt Λ.g_lt
  γ_le := le_max_left _ _
  lg := le_max_right _ _
  γR_cl := fun _ _ _ h1 h2 => max_lt h1 h2
  F_P := hd_LuP_mono (hnq_le Λ) Q.F_P
  G_le := Q.G_lt.le
  S_lt1 := (hnq_S_lt Q Λ).trans Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (hnq_Ffix Q Λ)]
    exact CSet.phi_mem (Λ.succ.L_mem S _ _ ha ((le_max_right _ _).trans_lt hb))
      (CSet.succ_mem (Q.F_mem S ha ((le_max_left _ _).trans_lt hb)))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans (hnq_S_lt Q Λ))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (hnq_S_lt Q Λ))
  S_cl := fun Z hZ hZ1 h => Q.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (hnq_S_lt Q Λ)
  Fr_gt := fun hx hx1 hγ =>
    (hnq_lle Λ hx hx1 ((le_max_right _ _).trans_lt hγ)).trans_lt (Q.Fr_gt hx hx1 ((le_max_left _ _).trans_lt hγ))
  Fr_P := fun hx hx1 hγ =>
    hd_LuP_mono (hnq_lle Λ hx hx1 ((le_max_right _ _).trans_lt hγ)) (Q.Fr_P hx hx1 ((le_max_left _ _).trans_lt hγ))
  S_Zo := fun hx hx1 hγ => (hdNx_mono (hnq_lle Λ hx hx1 ((le_max_right _ _).trans_lt hγ)) _).trans_lt
    (Q.S_Zo hx hx1 ((le_max_left _ _).trans_lt hγ))
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := fun hB hγ => Q.Fr_pi hB ((le_max_left _ _).trans_lt hγ)
  S_pi := fun hB hγ => hnq_S_pi Q Λ hB ((le_max_left _ _).trans_lt hγ) ((le_max_right _ _).trans_lt hγ)

theorem hnQW_F : (hnQW Q Λ).F = Q.F := rfl

theorem hnQW_Fr : (hnQW Q Λ).Fr = Q.Fr := rfl

theorem hnQW_γ : (hnQW Q Λ).γ = Q.γ := rfl

theorem hnQW_γR : (hnQW Q Λ).γR = max Q.γ Λ.g := rfl

theorem hnQW_Zo : (hnQW Q Λ).Zo = Q.Zo := rfl

/-- **The outer low field of `hnQW Q Λ` below the reading gate is `Q.Zo`.** -/
theorem hnQW_Zo_low {x : Ordinal.{0}} (h : ¬ max Q.γ Λ.g < x) : (hnQW Q Λ).hlwZo x = Q.Zo x :=
  (hnQW Q Λ).hlwZo_low h

end QW

/-! ## The same pseudo-base at the level `Ω₁ + 0` -/

section Q1

variable (Q : HnVQ hnSqLv 0)

theorem hnq1_fix : veblen (hlL1.L + 0) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]
  exact veblen_veblen_of_lt ((add_zero _).trans_lt ((lt_add_of_pos_right _ gv_Om1_pos).trans (hnq_lt0 hlL1))) a

theorem hnq1_S_lt : hdNx (hlL1.L + 0) Q.F < hdNx (hnSqLv.L + 0) Q.F :=
  (hdNx_mono (by rw [add_zero]; exact le_self_add) _).trans_lt (hnq_S_lt Q hlL1)

theorem hnq1_lle {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : hlL1.l x + 0 ≤ hnSqLv.l x + 0 := by
  rw [add_zero]; exact le_self_add.trans (hnq_lle hlL1 hx hx1 hx.pos)

theorem hnq1_rfix {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    veblen (hlL1.l x + 0) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]
  refine veblen_veblen_of_lt ?_ a
  rw [add_zero]; exact (lt_add_of_pos_right _ hx.pos).trans (hnq_llt hlL1 hx hx1 hx.pos)

/-- **A pseudo-base of level `Ω₁·Ω₁ + 0` is an `Hl.HlVQ` of level `Ω₁ + 0`** (the same point, reading and outer low
field; a port of `Hl.HlVQ.lowr` across the two level-datum types). -/
noncomputable def hnQ1 : HlVQ hlL1 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := zero_le
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (by rw [add_zero, add_zero]; exact le_self_add.trans ((hnq_le hlL1).trans_eq (add_zero _)))
    Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (hnq1_S_lt Q).trans Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (hnq1_fix Q)]
    exact CSet.phi_mem (hlv_L_mem hlL1 S ha (zero_le.trans_lt hb) (zero_le.trans_lt hb))
      (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans (hnq1_S_lt Q))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (hnq1_S_lt Q))
  S_cl := fun Z hZ hZ1 h => Q.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (hnq1_S_lt Q)
  Fr_gt := fun hx hx1 hγ => (hnq1_lle hx hx1).trans_lt (Q.Fr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (hnq1_lle hx hx1) (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono (hnq1_lle hx hx1) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := hlv_glA_pi hlL1 hB hB.1.pos hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [f2, hlv_glA_fixP hlL1 hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (hnq1_rfix Q hB.2.1 hρ1 hγρ)
      ((hnq1_lle hB.2.1 hρ1).trans_lt (Q.Fr_gt hB.2.1 hρ1 hγρ)) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
      hlv_glA_fixP hlL1 hB.1 hσ1 hB.1.pos (hnq1_rfix Q hB.1 hσ1 hγ)
      ((hnq1_lle hB.1 hσ1).trans_lt (Q.Fr_gt hB.1 hσ1 hγ)) (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem hnQ1_PB : hlVPB (hnQ1 Q) = hnVPB Q := rfl

/-- **A system with the specification of level `Ω₁ + 0` at `hnQ1 Q` is a start over `hnQW Q Hl.hlL1`.** -/
theorem hnQ1_shape {U T : HgVD} (h : HlVSpec (hnQ1 Q) U T) : HlWShape (hnQW Q hlL1) 0 T := by
  have hmx : ∀ x : Ordinal.{0}, max (max Q.γ hlL1.g) 0 < x ↔ Q.γ < x := fun x => by
    rw [max_eq_left zero_le]; show max Q.γ 0 < x ↔ _; rw [max_eq_left zero_le]
  have hB : T.B = hdNx (hlL1.L + 0) Q.F := h.B
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · rw [hB]; exact hdNx_fixP (hnq1_fix Q)
  · change T.γ < x ↔ max (max Q.γ hlL1.g) 0 < x
    rw [h.γ, hmx]; rfl
  · change max (max Q.γ hlL1.g) 0 < x at hγ
    rw [hmx] at hγ
    change T.b x = veblen (hlL1.l x + 0) (Q.Fr x + 1)
    rw [h.b x hx hx1 hγ]; exact hdNx_fixP (hnq1_rfix Q hx hx1 hγ)
  · rw [h.Z x hx hx1]
    show (if Q.γ < x then evZ (hdNx (hlL1.l x + 0) (Q.Fr x)) else Q.Zo x) =
      if max (max Q.γ hlL1.g) 0 < x then evZ (veblen (hlL1.l x + 0) (Q.Fr x + 1)) else (hnQW Q hlL1).hlwZo x
    by_cases hγ : Q.γ < x
    · rw [if_pos hγ, if_pos ((hmx x).2 hγ), hdNx_fixP (hnq1_rfix Q hx hx1 hγ)]
    · rw [if_neg hγ, if_neg (fun h' => hγ ((hmx x).1 h')), hnQW_Zo_low Q hlL1 (fun h' => hγ (by
        have : max Q.γ hlL1.g = Q.γ := max_eq_left zero_le
        rwa [this] at h'))]
  · refine h.high c σ hFc ?_ hσ hσ1 hg
    show c < hdNx (hlL1.L + 0) Q.F
    rw [← hB]; exact hc

end Q1

end Googology.Trans.PoR.InaccPsi.R2.Hn
