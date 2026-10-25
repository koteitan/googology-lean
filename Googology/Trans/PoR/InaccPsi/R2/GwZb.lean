import Googology.Trans.PoR.InaccPsi.R2.GwImg

/-!
# THE BASE DATA AT `ζ_{G+1}`: `ζ_{Γ_{x+1}+1} = ϑˣ(Ω₁·2 + Γ_{x+1})`, Lemma EXACT for it, `ε_{ζ+1} = ϑˣ(Ω₁ + ζ)`

A union at the index `ζ_{G+1}` has to read its own index (`Gw.gw_wall`): its base reading is `ζ_{Γ_{x+1}+1}`.  The
base data such a union needs, as far as they are facts about ordinals, hold:

* `gw_LuP2` (`ζ_{τ+1}` is a fixed point of every `φ(b, ·)`, `b < 2`), `gw_glA2_eq` (**`ϑˣ(Ω₁·2 + Γ_{x+1}) =
  ζ_{Γ_{x+1}+1}`**: `≤` by the minimality `Gl.glA_min`, `≥` because the left side is an `ε`-fixed point above
  `Γ_{x+1}`), `gw_Z_pi` (**Lemma EXACT: `π_{σ,ρ}(ζ_{Γ_{ρ+1}+1}) = ζ_{Γ_{σ+1}+1}`**, from `Gl.glA_pi`);
* `gw_eNZ` (**`ε_{ζ_{Γ_{x+1}+1}+1} = ϑˣ(Ω₁ + ζ_{Γ_{x+1}+1})`**: every `ϑˣ(Ω₁ + σ)`, `σ < ζ`, is below `ζ`, by
  `Gl.glA_lt_G` below `Γ_{x+1}` and `Gw.gw_glA_eq` above), `gw_eNZ_pi` (**Lemma EXACT for `ε_{ζ_{Γ_{ρ+1}+1}+1}`**).

What fails is not a fact about ordinals but the field `b_Z` (and `R_lt_Z`) of `Gv.GvD`: `ε_{ζ+1} < ζ` is false.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- `ζ_{τ+1}` lies in the range of `φ(2, ·)`. -/
theorem gw_LuP2 (τ : Ordinal.{0}) : LuP 2 (evZ τ) := by
  unfold LuP
  rw [mem_range_veblen two_ne_zero]
  intro b hb
  rcases lt_or_ge b 1 with h0 | h1
  · rw [Order.lt_one_iff] at h0
    rw [h0, veblen_zero_apply]; exact evZ_E τ
  · have hb1 : b = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hb)) h1
    rw [hb1]; exact epsilon_evZ τ

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gw_two_T : (2 : Ordinal.{0}) ∈ Tset x ∧ (2 : Ordinal.{0}) < Om1 := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact gm1_T hx hx1 ((show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hq))

/-- **`ϑˣ(Ω₁·2 + Γ_{x+1}) = ζ_{Γ_{x+1}+1}`.** -/
theorem gw_glA2_eq : glA 2 (lgG x) x = evZ (lgG x) := by
  obtain ⟨hGT, hxG, hG1, hGE, -⟩ := lgG_facts hx hx1
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  refine le_antisymm ?_ ?_
  · have h2G : (2 : Ordinal.{0}) < lgG x :=
      (show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hGE)
    refine glA_min hx hx1 h12 h2T h21 hGT hG1 (gw_LuP2 _) (hxG.trans (lt_evZ _)) (lt_evZ _)
      (h2G.trans (lt_evZ _)) (fun σ hσ => (glA_lt_G hx hx1 h2G hσ).trans (lt_evZ _))
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h12 h2T h21 hGT hG1
    obtain ⟨i, hi⟩ := glA_P hx hx1 h12 h2T h21 hGT hG1
    have hfix : Ordinal.epsilon (glA 2 (lgG x) x) = glA 2 (lgG x) x := by
      rw [← hi]; exact veblen_veblen_of_lt one_lt_two i
    exact evZ_le hta hfix

theorem gw_Z_T : evZ (lgG x) ∈ Tset x ∧ evZ (lgG x) < Om1 := gm1_T hx hx1 (gn_evZG_lt1 hx hx1)

/-- **`ε_{ζ_{Γ_{x+1}+1}+1} = ϑˣ(Ω₁ + ζ_{Γ_{x+1}+1})`.** -/
theorem gw_eNZ : eN (evZ (lgG x)) = glA 1 (evZ (lgG x)) x := by
  obtain ⟨hGT, hxG, hG1, hGE, -⟩ := lgG_facts hx hx1
  obtain ⟨hZT, hZ1⟩ := gw_Z_T hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hZT hZ1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (evZ (lgG x))) := by
    have h := vzP_one.2 (eN_E (evZ (lgG x))); unfold VzP at h; rwa [Nat.cast_one] at h
  have hZ := lt_evZ (lgG x)
  have h1G : (1 : Ordinal.{0}) < lgG x := one_lt_omega0.trans (omega0_lt_inE hGE)
  refine glA_min hx hx1 le_rfl h1T h11 hZT hZ1 hP1 ((hxG.trans hZ).trans (lt_eN _)) (lt_eN _)
    ((h1G.trans hZ).trans (lt_eN _)) (fun σ hσ => ?_)
  refine lt_trans ?_ (lt_eN _)
  rcases lt_or_ge σ (lgG x) with hσG | hσG
  · exact (glA_lt_G hx hx1 h1G hσG).trans hZ
  · obtain ⟨ν, rfl⟩ := exists_add_of_le hσG
    have hν : ν < evZ (lgG x) := lt_of_le_of_lt le_add_self hσ
    rw [gw_glA_eq hx hx1 hν]
    exact evA_lt_evZ hGE (add_lt_evZ (one_lt_omega0.trans (omega0_lt_inE (evZ_E _))) hν)

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for `ζ_{Γ_{ρ+1}+1}`**: `π_{σ,ρ}(ζ_{Γ_{ρ+1}+1}) = ζ_{Γ_{σ+1}+1}`. -/
theorem gw_Z_pi : evZ (lgG ρ) ∈ TB ρ σ ∧ pi σ ρ (evZ (lgG ρ)) = evZ (lgG σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h2σ : (2 : Ordinal.{0}) < σ := (show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hB.1)
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [pi_lt hB h2σ, g2, gw_glA2_eq hB.2.1 hρ1, gw_glA2_eq hB.1 hσ1] at h
  exact h

/-- **Lemma EXACT for `ε_{ζ_{Γ_{ρ+1}+1}+1}`.** -/
theorem gw_eNZ_pi : eN (evZ (lgG ρ)) ∈ TB ρ σ ∧ pi σ ρ (eN (evZ (lgG ρ))) = eN (evZ (lgG σ)) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨z1, z2⟩ := gw_Z_pi hB
  obtain ⟨o1, o2⟩ := one_TB hB
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 z1 (gw_Z_T hB.2.1 hρ1).2
  rw [o2, z2, ← gw_eNZ hB.2.1 hρ1, ← gw_eNZ hB.1 hσ1] at h
  exact h

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gw
