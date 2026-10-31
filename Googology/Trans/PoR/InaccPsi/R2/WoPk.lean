import Googology.Trans.PoR.InaccPsi.R2.WoDat

/-!
# WoPk: A PSEUDO-BASE OF A LEVEL READ AT `Ω₁ + 0`; THE PACKAGE OF A FAMILY OF SYSTEMS OVER RAW DATA

* `woQ1 Q` (**a pseudo-base `Q` of the level `ℓ` as a pseudo-base of the level `Ω₁ + 0`**, an `Hn.HnVQ Hn.hnL1 0`
  with the same data), `woSt1 Q U h` (**the step of the level `Ω₁ + 0` at it**, `Hn.hnSt1`), `woSt1_sh` (**it has the
  shape at `Ω₁`**), `woSt1_B`;
* `woSpecOf` (**a system with the shape at `ℓ` over `Q` that extends the step at `Ω₁` has the specification
  `Hn.HnVSpec` of the level `ℓ + 0` at `Q`**);
* `woPk ℓ E hE` (**THE PACKAGE OF A FAMILY `E` OF SYSTEMS OVER RAW DATA**: level datum `whLv ℓ`, step at `Q` =
  `E (woQR Q) (woSt1 Q U h)`).

No new axiom.  New definitions: `woQ1`, `woSt1`, `woPk`.
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

theorem wo_lev_Om1 : WmLev Om1 := ⟨le_rfl, dvd_refl _, Om1_lt_eW⟩

theorem wo_one_lt_inE {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) < x :=
  one_lt_omega0.trans (omega0_lt_inE hx)

theorem wo_gtc_Om1 : gtc Om1 = 1 := (rdc_Om1 0).2

/-- `max γ (gtc Ω₁) < x ↔ γ < x` at an `ε`-number `x`. -/
theorem wo_cut1 {γ x : Ordinal.{0}} (hx : InE x) : max γ (gtc Om1) < x ↔ γ < x := by
  rw [max_lt_iff, wo_gtc_Om1]; exact ⟨fun h => h.1, fun h => ⟨h, wo_one_lt_inE hx⟩⟩

section Q1

variable {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) (Q : HnVQ (woLv ℓ hℓ) 0)

theorem wo_Q_FP : LuP ℓ Q.F := by have := Q.F_P; rwa [add_zero] at this

/-- **A PSEUDO-BASE OF THE LEVEL `ℓ` AS ONE OF THE LEVEL `Ω₁ + 0`.** -/
noncomputable def woQ1 : HnVQ hnL1 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := zero_le
  γ_lt := Q.γ_lt
  F_P := by show LuP (Om1 + 0) Q.F; rw [add_zero]; exact ((woGood_Q hℓ Q).mono wo_lev_Om1 hℓ.1).F_P
  G_lt := Q.G_lt
  S_lt1 := by show hdNx (Om1 + 0) Q.F < _; rw [add_zero]; exact ((woGood_Q hℓ Q).mono wo_lev_Om1 hℓ.1).S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    show hdNx (Om1 + 0) Q.F ∈ _
    rw [add_zero]
    rcases hℓ.1.lt_or_eq with hlt | heq
    · rw [hdNx_fixP (wo_fix_of_LuP (wo_Q_FP hℓ Q) hlt)]
      exact CSet.phi_mem (hnL1.L_mem S _ _ ha (zero_le.trans_lt hb)) (CSet.succ_mem (Q.F_mem S ha hb))
    · have := Q.S_mem S ha hb
      rw [wo_Q_N hℓ Q] at this
      have e : hdNx Om1 Q.F = hdNx ℓ Q.F := by rw [heq]
      rw [e]; exact this
  F_code := fun Z hZ hZ1 y hy hQy hyZ => ((woGood_Q hℓ Q).mono wo_lev_Om1 hℓ.1).F_code Z hZ hZ1 y hy hQy
    (by rw [add_zero] at hyZ; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => ((woGood_Q hℓ Q).mono wo_lev_Om1 hℓ.1).F_cl Z hZ hZ1 y hy hQy
    (by rw [add_zero] at hyZ; exact hyZ)
  S_cl := fun Z hZ hZ1 hc => ((woGood_Q hℓ Q).mono wo_lev_Om1 hℓ.1).S_cl Z hZ hZ1
    (by rw [add_zero] at hc; exact hc)
  Fr_gt := fun {x} hx hx1 hγ => by
    show x + 0 < Q.Fr x
    have := (((woGood_Q hℓ Q).rd Om1 wo_lev_Om1 hℓ.1 x hx hx1 ((wo_cut1 hx).2 hγ))).2.1
    rw [(rdc_Om1 x).1] at this; rw [add_zero]; exact this
  Fr_P := fun {x} hx hx1 hγ => by
    show LuP (x + 0) (Q.Fr x)
    have := (((woGood_Q hℓ Q).rd Om1 wo_lev_Om1 hℓ.1 x hx hx1 ((wo_cut1 hx).2 hγ))).1
    rw [(rdc_Om1 x).1] at this; rw [add_zero]; exact this
  S_Zo := fun {x} hx hx1 hγ => by
    show hdNx (x + 0) (Q.Fr x) < Q.Zo x
    have := (((woGood_Q hℓ Q).rd Om1 wo_lev_Om1 hℓ.1 x hx hx1 ((wo_cut1 hx).2 hγ))).2.2
    rw [(rdc_Om1 x).1] at this; rw [add_zero]; exact this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    show hdNx (ρ + 0) (Q.Fr ρ) ∈ _ ∧ pi σ ρ (hdNx (ρ + 0) (Q.Fr ρ)) = hdNx (σ + 0) (Q.Fr σ)
    have := (woGood_Q hℓ Q).S_pi Om1 wo_lev_Om1 hℓ.1 σ ρ hB ((wo_cut1 hB.1).2 hγ)
    rw [(rdc_Om1 ρ).1, (rdc_Om1 σ).1] at this; rw [add_zero, add_zero]; exact this

/-- **The step of the level `Ω₁ + 0` at `Q`** (`Hn.hnSt1` at `woQ1 Q`). -/
noncomputable def woSt1 (U : HgVD) (h : HgSStart (hnVPB Q) U) : HgVD := hnSt1 (woQ1 hℓ Q) U h

theorem woSt1_spec (U : HgVD) (h : HgSStart (hnVPB Q) U) : HnVSpec (woQ1 hℓ Q) U (woSt1 hℓ Q U h) :=
  hnSt1_spec (woQ1 hℓ Q) U h

/-- **The step of the level `Ω₁ + 0` has the shape at `Ω₁`.** -/
theorem woSt1_sh (U : HgVD) (h : HgSStart (hnVPB Q) U) : WoSh (woQR Q) Om1 (woSt1 hℓ Q U h) := by
  have s := woSt1_spec hℓ Q U h
  refine ⟨?_, ⟨?_, ?_⟩, fun x hx _ => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_,
    fun c σ h1 h2 => s.high c σ h1 (by rw [← s.B]; exact h2)⟩
  · rw [s.B]; show hdNx (Om1 + 0) Q.F = _; rw [add_zero]; rfl
  · rw [s.γ]; exact le_rfl
  · rw [s.γ]; exact le_max_left _ _
  · rw [s.γ]; exact (wo_cut1 hx).symm
  · rw [s.b x hx hx1 ((wo_cut1 hx).1 hk), (rdc_Om1 x).1]
    show hdNx (x + 0) (Q.Fr x) = hdNx x (Q.Fr x); rw [add_zero]
  · rw [s.Z x hx hx1, (rdc_Om1 x).1]
    show (if Q.γ < x then evZ (hdNx (x + 0) (Q.Fr x)) else Q.Zo x) =
      if max Q.γ (gtc Om1) < x then evZ (hdNx x (Q.Fr x)) else Q.Zo x
    by_cases hk : Q.γ < x
    · rw [if_pos hk, if_pos ((wo_cut1 hx).2 hk), add_zero]
    · rw [if_neg hk, if_neg (fun h' => hk ((wo_cut1 hx).1 h'))]

/-- The bound of the start `U` is `F`. -/
theorem wo_U_B {U : HgVD} (h : HgSStart (hnVPB Q) U) : U.B = Q.F := by
  rw [U.B_ix, h.ix]
  show veblen 1 Q.F = Q.F
  exact wo_fix_of_LuP (wo_Q_FP hℓ Q) ((wh_one_lt_Om1).trans_le hℓ.1)

/-- **A SYSTEM WITH THE SHAPE AT `ℓ` OVER `Q` EXTENDING THE STEP AT `Ω₁` HAS THE SPECIFICATION OF `ℓ + 0` AT `Q`.** -/
theorem woSpecOf (U : HgVD) (h : HgSStart (hnVPB Q) U) {T : HgVD} (hT : WoSh (woQR Q) ℓ T)
    (hext : ∀ c x, c < (woSt1 hℓ Q U h).B → T.R c x = (woSt1 hℓ Q U h).R c x ∧ T.g c = (woSt1 hℓ Q U h).g c) :
    HnVSpec Q U T := by
  dsimp only [WoSh, woQR] at hT
  have s := woSt1_spec hℓ Q U h
  have hg : max Q.γ (gtc ℓ) = Q.γ := max_eq_left (wo_Q_g hℓ Q)
  have hS1B : (woSt1 hℓ Q U h).B = hdNx Om1 Q.F := by rw [s.B]; show hdNx (Om1 + 0) Q.F = _; rw [add_zero]
  have hFS1 : Q.F < (woSt1 hℓ Q U h).B := by rw [hS1B]; exact hdNx_gt _ _
  have hUS1 : ∀ c, c < U.B → c < (woSt1 hℓ Q U h).B := fun c hc =>
    hc.trans (by rw [wo_U_B hℓ Q h]; exact hFS1)
  obtain ⟨hB, ⟨hγ1, hγ2⟩, -, hb, hZ, hhi⟩ := hT
  refine ⟨?_, ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, fun c x hc => ?_, fun c hc => ?_,
    fun c σ h1 h2 => hhi c σ h1 (by rw [hB]; rw [wo_Q_N hℓ Q] at h2; exact h2), fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_⟩
  · rw [hB]; exact (wo_Q_N hℓ Q).symm
  · exact le_antisymm (by rw [hg] at hγ2; exact hγ2) hγ1
  · rw [hb x hx hx1 (by rw [hg]; exact hk), ← wo_Q_l hℓ Q hx hk]
  · rw [hZ x hx hx1, hg]
    by_cases hk : Q.γ < x
    · rw [if_pos hk, if_pos hk, ← wo_Q_l hℓ Q hx hk]
    · rw [if_neg hk, if_neg hk]
  · rw [(hext c x (hUS1 c hc)).1]; exact s.extR c x hc
  · rw [(hext c 0 (hUS1 c hc)).2]; exact s.extg c hc
  · rw [(hext Q.F x hFS1).1]; exact s.RF x hx hx1 hk
  · rw [(hext Q.F 0 hFS1).2]; exact s.gF x hx hx1

end Q1

/-! ## The package of a family of systems over raw data -/

/-- **THE PACKAGE OF A FAMILY `E` OF SYSTEMS OVER RAW DATA**: level datum `whLv ℓ`, step at a pseudo-base `Q` with
start `U`: `E (woQR Q) (woSt1 Q U h)`. -/
noncomputable def woPk (ℓ : Ordinal.{0}) (hℓ : WmLev ℓ) (E : WoR → HgVD → HgVD)
    (hE : ∀ (Q : HnVQ (woLv ℓ hℓ) 0) U (h : HgSStart (hnVPB Q) U), HnVSpec Q U (E (woQR Q) (woSt1 hℓ Q U h))) :
    HnPk := ⟨woLv ℓ hℓ, fun Q U h => E (woQR Q) (woSt1 hℓ Q U h), hE⟩

theorem woPk_St0 (ℓ : Ordinal.{0}) (hℓ : WmLev ℓ) (E : WoR → HgVD → HgVD) (hE) (Q : HnVQ (woLv ℓ hℓ) 0) (U : HgVD)
    (h : HgSStart (hnVPB Q) U) : (woPk ℓ hℓ E hE).St0 Q U h = E (woQR Q) (woSt1 hℓ Q U h) := rfl

end Googology.Trans.PoR.InaccPsi.R2.Wo
