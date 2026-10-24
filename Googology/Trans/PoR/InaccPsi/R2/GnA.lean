import Googology.Trans.PoR.InaccPsi.R2.GmQ3

/-!
# THE NEXT `ε`-NUMBER AFTER `Γ_{x+1}` AND LEMMA EXACT FOR THE POWERS `ω^X`, `Γ_{ρ+1} ≤ X < ε_{Γ_{ρ+1}+1}`

* `gn_eNG` (**`ε_{Γ_{x+1}+1} = ϑˣ(Ω₁ + Γ_{x+1})`**, by `Gl.glA_min`), `gn_eNG_lt1` (**`ε_{Γ_{x+1}+1} < Γ_{x+2}`**,
  [W07a] Lemma 3.30 as `lgVt_lt_low`), `gn_eNG_T`;
* `gn_eNG_pi` (**`π(ε_{Γ_{ρ+1}+1}) = ε_{Γ_{σ+1}+1}`** at every pair of bases, `Gl.glA_pi`);
* `gn_GAtom_pi` (**Lemma EXACT for the atom `ω^{Γ_{ρ+1}+β}`** for every `β ∈ Tᵖ[σ]` with `Γ_{ρ+1} + β < ε_{Γ_{ρ+1}+1}`:
  it is `ϑᵖ(Γ_{ρ+1} + β')`, [W07a] Lemma 4.2 through `vt_ps`, and `π(ϑᵖ(ξ)) = ϑ^σ(π ξ)`), `gn_opowG_pi`
  (**`π(ω^X) = ω^{π X}` for every `X ∈ Tᵖ[σ] ∩ [Γ_{ρ+1}, ε_{Γ_{ρ+1}+1})`** at every pair of bases).

No new axiom, no new definition.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ε_{Γ_{x+1}+1} = ϑˣ(Ω₁ + Γ_{x+1})`.** -/
theorem gn_eNG : eN (lgG x) = glA 1 (lgG x) x := by
  obtain ⟨hGT, hxG, hG1, hGE, -⟩ := lgG_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hGT hG1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (lgG x)) := by
    have h := vzP_one.2 (eN_E (lgG x)); unfold VzP at h; rwa [Nat.cast_one] at h
  have h1G : (1 : Ordinal.{0}) < lgG x := one_lt_omega0.trans (omega0_lt_inE hGE)
  refine glA_min hx hx1 le_rfl h1T h11 hGT hG1 hP1 (hxG.trans (lt_eN _)) (lt_eN _)
    (h1G.trans (lt_eN _)) (fun σ hσ => ?_)
  exact (glA_lt_G hx hx1 h1G hσ).trans (lt_eN _)

/-- **`ε_{Γ_{x+1}+1} < Γ_{x+2}`.** -/
theorem gn_eNG_lt1 : eN (lgG x) < gq 1 x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hG := mg_lgG_lt_G1 hx hx1
  have h1q : (1 : Ordinal.{0}) < gq 1 x := (one_lt_omega0.trans (omega0_lt_inE (gm1_facts hx hx1).2.2.2))
  rw [gn_eNG hx hx1]
  exact lgVt_lt_low hx hx1 h1T h11 hGT hG1 h1T h11 h1q hG

/-- Every ordinal below `ε_{Γ_{x+1}+1}` lies in `Tˣ ∩ Ω₁`. -/
theorem gn_eNG_T {v : Ordinal.{0}} (hv : v < eN (lgG x)) : v ∈ Tset x ∧ v < Om1 :=
  gm1_T hx hx1 (hv.trans (gn_eNG_lt1 hx hx1))

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(ε_{Γ_{ρ+1}+1}) = ε_{Γ_{σ+1}+1}`** at every pair of bases. -/
theorem gn_eNG_pi : eN (lgG ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (lgG ρ)) = eN (lgG σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := mg_lgG_pi hB
  have hG1 : lgG ρ < Om1 := (lgG_facts hB.2.1 hρ1).2.2.1
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 g1 hG1
  rw [o2, g2, ← gn_eNG hB.2.1 hρ1, ← gn_eNG hB.1 hσ1] at h
  exact h

/-- `π` maps `Tᵖ[σ] ∩ ε_{Γ_{ρ+1}+1}` below `ε_{Γ_{σ+1}+1}`. -/
theorem gn_pi_lt_eNG {β : Ordinal.{0}} (hβ : β ∈ TB ρ σ) (hβe : β < eN (lgG ρ)) : pi σ ρ β < eN (lgG σ) := by
  obtain ⟨e1, e2⟩ := gn_eNG_pi hB
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

/-- **Lemma EXACT for the atom `ω^{Γ_{ρ+1}+β}`** (`β ∈ Tᵖ[σ]`, `Γ_{ρ+1} + β < ε_{Γ_{ρ+1}+1}`) at every pair of
bases. -/
theorem gn_GAtom_pi {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβe : lgG ρ + β < eN (lgG ρ)) :
    ω ^ (lgG ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (lgG ρ + β)) = ω ^ (lgG σ + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := mg_lgG_pi hB
  obtain ⟨-, hρG, he1, heE, -⟩ := lgG_facts hB.2.1 hρ1
  obtain ⟨-, hσG, hes1, hseE, -⟩ := lgG_facts hB.1 hσ1
  have hN1 : eN (lgG ρ) < Om1 := (gn_eNG_lt1 hB.2.1 hρ1).trans (gm1_facts hB.2.1 hρ1).2.2.1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ lgG ρ = lgG ρ := heE
    have h2 : ω ^ lgG σ = lgG σ := hseE
    rw [pi_lt hB hB.1.pos, add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ1 : β < Om1 := (lt_of_le_of_lt le_add_self hβe).trans hN1
  have hβ'T : β' ∈ TB ρ σ ∧ 1 + pi σ ρ β' = pi σ ρ β := by
    rcases lt_or_ge β ω with hω | hω
    · have hβσ : β < σ := hω.trans (omega0_lt_inE hB.1)
      have hβ'σ : β' < σ := lt_of_le_of_lt (sub_le_self β 1) hβσ
      refine ⟨mem_TB_of_lt hB hβ'σ, ?_⟩
      rw [pi_lt hB hβ'σ, pi_lt hB hβσ, hb]
    · have e : β' = β := by
        have h := Ordinal.add_sub_cancel 1 β
        rw [one_add_of_omega0_le hω] at h
        rw [hβ']; exact h
      rw [e]
      refine ⟨hβTB, one_add_of_omega0_le ?_⟩
      rcases lt_or_ge β σ with hβσ | hσβ
      · rw [pi_lt hB hβσ]; exact hω
      · exact (omega0_lt_inE hB.1).le.trans (pi_ge hB hβTB hσβ)
  obtain ⟨hβ'TB, hπ1⟩ := hβ'T
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB hβ'TB
  rw [hpe] at hpξ
  -- the bounds at `ρ` and at `σ`
  have hξ1 : lgG ρ + β' < Om1 := lt_of_le_of_lt (add_le_add le_rfl (sub_le_self β 1)) (hβe.trans hN1)
  have hbρ : lgG ρ + 1 + β' < eN (lgG ρ) := by rw [add_assoc, hb]; exact hβe
  have hsum : lgG ρ + β ∈ TB ρ σ ∧ pi σ ρ (lgG ρ + β) = lgG σ + pi σ ρ β := by
    obtain ⟨s1, s2⟩ := pi_add hB heTB hβTB
    exact ⟨s1, by rw [s2, hpe]⟩
  have hbσ : lgG σ + 1 + pi σ ρ β' < eN (lgG σ) := by
    rw [add_assoc, hπ1, ← hsum.2]; exact gn_pi_lt_eNG hB hsum.1 hβe
  have hξ1' : lgG σ + pi σ ρ β' < Om1 :=
    lt_of_le_of_lt (add_le_add le_rfl le_add_self) (by
      rw [hπ1, ← hsum.2]
      exact (gn_pi_lt_eNG hB hsum.1 hβe).trans ((gn_eNG_lt1 hB.1 hσ1).trans (gm1_facts hB.1 hσ1).2.2.1))
  have hv := vt_ps hB.2.1 hρ1 heE hρG hbρ hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hv' := vt_ps hB.1 hσ1 hseE hσG hbσ hξ1'
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **`π(ω^X) = ω^{π X}`** for every `X ∈ Tᵖ[σ]` with `Γ_{ρ+1} ≤ X < ε_{Γ_{ρ+1}+1}`, at every pair of bases. -/
theorem gn_opowG_pi {X : Ordinal.{0}} (hX : X ∈ TB ρ σ) (hGX : lgG ρ ≤ X) (hXe : X < eN (lgG ρ)) :
    ω ^ X ∈ TB ρ σ ∧ pi σ ρ (ω ^ X) = ω ^ (pi σ ρ X) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨heTB, hpe⟩ := mg_lgG_pi hB
  have hX1 : X < Om1 := hXe.trans ((gn_eNG_lt1 hB.2.1 hρ1).trans (gm1_facts hB.2.1 hρ1).2.2.1)
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hX hGX hX1
  have e : lgG ρ + (X - lgG ρ) = X := Ordinal.add_sub_cancel_of_le hGX
  have hle : lgG σ ≤ pi σ ρ X := by
    rw [← hpe]; exact ((pi_bijOn hB).2.le_iff_le heTB hX).2 hGX
  obtain ⟨h1, h2⟩ := gn_GAtom_pi hB hβTB (by rw [e]; exact hXe)
  rw [e] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, hpβ, hpe, Ordinal.add_sub_cancel_of_le hle]

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gn
