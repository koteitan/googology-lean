import Googology.Trans.PoR.InaccPsi.R2.WhSucc

/-!
# WmLow: THE EXTENSION STATEMENT THAT LOWERS BY THE PSEUDO-BASE GATE

`Hn.HnkExt K' K` compares the step of `K` at a pseudo-base `Q` with the step of `K'` at `Q` lowered by
`Hn.HnVQ.lowr`, and it asks `K'.g ≤ K.g`.  Across a gate drop (`K'.g > K.g`) it says nothing.  The lowering itself
only needs `K'.g ≤ Q.γ` (the gate of the pseudo-base): `wmLowr` is `Hn.HnVQ.lowr` with that hypothesis and with the
reading comparison asked only above `Q.γ`.

* `wmLowr` (**a pseudo-base of level `L' + 0` is one of every lower level `L + 0` with `g ≤ γ`**), `wmLowr_PB`,
  `wmLowr_lowr` (lowering twice is lowering once), `wm_lowr_eq` (`Hn.HnVQ.lowr` is a case of `wmLowr`);
* `WmExt K' K` (**THE EXTENSION STATEMENT, lowering by the pseudo-base gate**: at every pseudo-base `Q` of the level
  of `K` with `K'.g ≤ Q.γ`), `wmExt_old` (`WmExt ⇒ Hn.HnkExt`), `wmExt_trans` (**transitivity through a middle
  package whose gate is below the larger outer gate**);
* `wmSucc_ext` (**`WmExt K K.succ` for every package**), `wmLev_step` (the level and reading comparisons of two
  entries `Wh.WhAt`), `wmSucc_ext_lt` (**the successor entry extends, in the new sense, every entry that the entry
  at `ℓ'` extends**).

No new axiom.  New definitions: `wmLowr`, `WmExt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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

/-! ## Lowering by the pseudo-base gate -/

section Low

variable {Λ' : HnLv} (Q : HnVQ Λ' 0) (Λ : HnLv) (hg : Λ.g ≤ Q.γ) (hL : Λ.L + Om1 ≤ Λ'.L)
  (hl : ∀ x, InE x → x < Om1 → Q.γ < x → Λ.l x + x ≤ Λ'.l x)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x)
include hl hx hx1 hγ

theorem wm_lle : Λ.l x + 0 ≤ Λ'.l x + 0 := by rw [add_zero, add_zero]; exact le_self_add.trans (hl x hx hx1 hγ)

theorem wm_llt : Λ.l x + 0 < Λ'.l x + 0 := by
  rw [add_zero, add_zero]; exact ((lt_add_iff_pos_right _).2 hx.pos).trans_le (hl x hx hx1 hγ)

theorem wm_rfix : veblen (Λ.l x + 0) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (wm_llt Q Λ hl hx hx1 hγ) a

end Base

include hg in
/-- **A PSEUDO-BASE OF LEVEL `L' + 0` IS ONE OF EVERY LOWER LEVEL `L + 0` WHOSE GATE IS AT MOST ITS GATE**
(`L + Ω₁ ≤ L'`, `ℓ(x) + x ≤ ℓ'(x)` above `γ`; the same point, reading, gate and outer low field). -/
noncomputable def wmLowr : HnVQ Λ 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := hg
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (HnVQ.lw_le Λ hL) Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (Q.lw_S_lt Λ hL).trans Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (Q.lw_fix Λ hL)]
    exact CSet.phi_mem (hnv_L_mem Λ S ha (hg.trans_lt hb) (zero_le.trans_lt hb))
      (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  S_cl := fun Z hZ hZ1 h => Q.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (Q.lw_S_lt Λ hL)
  Fr_gt := fun hx hx1 hγ => (wm_lle Q Λ hl hx hx1 hγ).trans_lt (Q.Fr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (wm_lle Q Λ hl hx hx1 hγ) (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono (wm_lle Q Λ hl hx hx1 hγ) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := hnv_glA_pi Λ hB (hg.trans_lt hγ) hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [f2, hnv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (wm_rfix Q Λ hl hB.2.1 hρ1 hγρ)
      ((wm_lle Q Λ hl hB.2.1 hρ1 hγρ).trans_lt (Q.Fr_gt hB.2.1 hρ1 hγρ)) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
      hnv_glA_fixP Λ hB.1 hσ1 hB.1.pos (wm_rfix Q Λ hl hB.1 hσ1 hγ)
      ((wm_lle Q Λ hl hB.1 hσ1 hγ).trans_lt (Q.Fr_gt hB.1 hσ1 hγ)) (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem wmLowr_PB : hnVPB (wmLowr Q Λ hg hL hl) = hnVPB Q := rfl

theorem wmLowr_F : (wmLowr Q Λ hg hL hl).F = Q.F := rfl

theorem wmLowr_γ : (wmLowr Q Λ hg hL hl).γ = Q.γ := rfl

end Low

/-- **`Hn.HnVQ.lowr` is the case `g ≤ g'` of `wmLowr`.** -/
theorem wm_lowr_eq {Λ' : HnLv} (Q : HnVQ Λ' 0) (Λ : HnLv) (hg : Λ.g ≤ Λ'.g) (hL : Λ.L + Om1 ≤ Λ'.L)
    (hl : ∀ x, InE x → x < Om1 → Λ'.g < x → Λ.l x + x ≤ Λ'.l x) :
    Q.lowr Λ hg hL hl = wmLowr Q Λ (hg.trans Q.lg) hL (fun x hx hx1 hγ => hl x hx hx1 (Q.lg.trans_lt hγ)) := rfl

/-- **Lowering twice is lowering once.** -/
theorem wmLowr_lowr {Λ'' Λ' : HnLv} (Q : HnVQ Λ'' 0) (Λ : HnLv) (hg' : Λ'.g ≤ Q.γ) (hL' : Λ'.L + Om1 ≤ Λ''.L)
    (hl' : ∀ x, InE x → x < Om1 → Q.γ < x → Λ'.l x + x ≤ Λ''.l x) (hg : Λ.g ≤ (wmLowr Q Λ' hg' hL' hl').γ)
    (hL : Λ.L + Om1 ≤ Λ'.L) (hl : ∀ x, InE x → x < Om1 → (wmLowr Q Λ' hg' hL' hl').γ < x → Λ.l x + x ≤ Λ'.l x)
    (hg2 : Λ.g ≤ Q.γ) (hL2 : Λ.L + Om1 ≤ Λ''.L) (hl2 : ∀ x, InE x → x < Om1 → Q.γ < x → Λ.l x + x ≤ Λ''.l x) :
    wmLowr (wmLowr Q Λ' hg' hL' hl') Λ hg hL hl = wmLowr Q Λ hg2 hL2 hl2 := rfl

/-! ## The extension statement -/

/-- **THE EXTENSION STATEMENT, LOWERING BY THE PSEUDO-BASE GATE**: at every pseudo-base `Q` of the level `L + 0` of
`K` whose gate is at least the gate of `K'` (and the level / reading of `K'` are below those of `K` by `Ω₁` / `x`
above `Q.γ`), the step of `K` at `Q` agrees with the step of `K'` at `Q` lowered, below the bound of the latter. -/
def WmExt (K' K : HnPk) : Prop :=
  ∀ (Q : HnVQ K.Λ 0) (hg : K'.Λ.g ≤ Q.γ) (hL : K'.Λ.L + Om1 ≤ K.Λ.L)
    (hl : ∀ x, InE x → x < Om1 → Q.γ < x → K'.Λ.l x + x ≤ K.Λ.l x)
    (U : HgVD) (hU : HgSStart (hnVPB Q) U) (c x : Ordinal.{0}),
    c < (K'.St0 (wmLowr Q K'.Λ hg hL hl) U hU).B →
    (K.St0 Q U hU).R c x = (K'.St0 (wmLowr Q K'.Λ hg hL hl) U hU).R c x ∧
    (K.St0 Q U hU).g c = (K'.St0 (wmLowr Q K'.Λ hg hL hl) U hU).g c

/-- **The new extension statement implies the old one** (`Hn.HnkExt`). -/
theorem wmExt_old {K' K : HnPk} (h : WmExt K' K) : HnkExt K' K := by
  intro hg hL hl Q U hU c x hc
  exact h Q (hg.trans Q.lg) hL (fun x hx hx1 hγ => hl x hx hx1 (Q.lg.trans_lt hγ)) U hU c x hc

/-- **The bound of a step** (from its specification). -/
theorem wm_St0_B (K : HnPk) (Q : HnVQ K.Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U) :
    (K.St0 Q U hU).B = hdNx (K.Λ.L + 0) Q.F := (K.h0 Q U hU).B

/-- **TRANSITIVITY** of the extension statement through a middle package `B` whose gate is at most the larger of the
two outer gates, with the level and reading comparisons `A < B < C`. -/
theorem wmExt_trans {A B C : HnPk} (hAB : WmExt A B) (hBC : WmExt B C) (hLAB : A.Λ.L + Om1 ≤ B.Λ.L)
    (hLBC : B.Λ.L + Om1 ≤ C.Λ.L) (hgB : B.Λ.g ≤ max A.Λ.g C.Λ.g)
    (hlAB : ∀ x, InE x → x < Om1 → max A.Λ.g C.Λ.g < x → A.Λ.l x + x ≤ B.Λ.l x)
    (hlBC : ∀ x, InE x → x < Om1 → max A.Λ.g C.Λ.g < x → B.Λ.l x + x ≤ C.Λ.l x) : WmExt A C := by
  intro Q hg hL hl U hU c x hc
  have hmax : max A.Λ.g C.Λ.g ≤ Q.γ := max_le hg Q.lg
  have hgB' : B.Λ.g ≤ Q.γ := hgB.trans hmax
  have hlBC' : ∀ x, InE x → x < Om1 → Q.γ < x → B.Λ.l x + x ≤ C.Λ.l x := fun x hx hx1 hγ =>
    hlBC x hx hx1 (hmax.trans_lt hγ)
  set QB := wmLowr Q B.Λ hgB' hLBC hlBC'
  have hlAB' : ∀ x, InE x → x < Om1 → QB.γ < x → A.Λ.l x + x ≤ B.Λ.l x := fun x hx hx1 hγ =>
    hlAB x hx hx1 (hmax.trans_lt hγ)
  have hcB : c < (B.St0 QB U hU).B := by
    have h1 := wm_St0_B A (wmLowr Q A.Λ hg hL hl) U hU
    rw [h1] at hc
    rw [wm_St0_B B QB U hU]
    refine hc.trans_le (hdNx_mono ?_ _)
    rw [add_zero, add_zero]; exact le_self_add.trans hLAB
  obtain ⟨r1, g1⟩ := hBC Q hgB' hLBC hlBC' U hU c x hcB
  obtain ⟨r2, g2⟩ := hAB QB hg hLAB hlAB' U hU c x hc
  exact ⟨r1.trans r2, g1.trans g2⟩

/-! ## The successor step in the new sense -/

/-- **`WmExt K K.succ` for every package** (the next step starts at the step of `K` at the lowered pseudo-base). -/
theorem wmSucc_ext (K : HnPk) : WmExt K K.succ := by
  intro Q hg hL hl U hU c x hc
  have hsh' := hnw_shape_dn Q (K.h0 Q.dn U hU)
  exact ⟨hnwU_R0 Q.toW K.St0 K.h0 _ hsh' hc x, hnwU_g0 Q.toW K.St0 K.h0 _ hsh' hc⟩

/-- **The level and reading comparisons of two entries** at levels `ℓ'' < ℓ'`. -/
theorem wmLev_step {ℓ'' ℓ' : Ordinal.{0}} {K'' K' : HnPk} {V'' V' : HgVD} (hat'' : WhAt ℓ'' K'' V'')
    (hat' : WhAt ℓ' K' V') (hd'' : Om1 ∣ ℓ'') (hd' : Om1 ∣ ℓ') (hlt : ℓ'' < ℓ') (hW : ℓ' < gfE) :
    K''.Λ.L + Om1 ≤ K'.Λ.L ∧
    ∀ x, InE x → x < Om1 → K''.Λ.g < x → K'.Λ.g < x → K''.Λ.l x + x ≤ K'.Λ.l x := by
  refine ⟨by rw [hat''.1, hat'.1]; exact wh_lev_succ_le hd'' hd' hlt, fun x hx hx1 h1 h2 => ?_⟩
  rw [hat''.2.1 x hx hx1 h1, hat'.2.1 x hx hx1 h2]
  exact wh_rdc_step hx hd'' hd' hlt hW (hat''.2.2.2.2.2.1 x hx hx1 h1) (hat'.2.2.2.2.2.1 x hx hx1 h2)

/-- **The successor entry extends, in the new sense, every entry that the entry at `ℓ'` extends.** -/
theorem wmSucc_ext_lt {ℓ'' ℓ' : Ordinal.{0}} {K'' K' : HnPk} {V'' V' : HgVD} (hat'' : WhAt ℓ'' K'' V'')
    (hat' : WhAt ℓ' K' V') (hd'' : Om1 ∣ ℓ'') (hd' : Om1 ∣ ℓ') (hlt : ℓ'' < ℓ') (hW : ℓ' < gfE)
    (hext : WmExt K'' K') : WmExt K'' K'.succ := by
  obtain ⟨hL, hl⟩ := wmLev_step hat'' hat' hd'' hd' hlt hW
  refine wmExt_trans hext (wmSucc_ext K') hL le_rfl (le_max_right _ _) (fun x hx hx1 h => ?_)
    (fun x _ _ _ => le_rfl)
  have h' : max K''.Λ.g K'.Λ.g < x := h
  exact hl x hx hx1 (max_lt_iff.1 h').1 (max_lt_iff.1 h').2

end Googology.Trans.PoR.InaccPsi.R2.Wm
