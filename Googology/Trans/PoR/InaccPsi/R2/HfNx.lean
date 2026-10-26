import Googology.Trans.PoR.InaccPsi.R2.HeGate

/-!
# HfNx: THE READINGS AT A COUNTABLE LEVEL `ω ≤ μ < Ω₁` READ THROUGH A GATE

`Hd.HdLvl μ` asks `ω ≤ μ < ε₀`, so that the level lies below every `ε`-number base and is read as itself.  Here a
level is any countable `ω ≤ μ < Ω₁` (`HfLvl μ`), and the readings `ϑˣ(Ω₁·μ + t)` are taken only at bases `x > μ`
(above a gate `≥ μ`).  At such a base:

* `hfm_glA_P` (`ϑˣ(Ω₁·μ + t)` is a point of `range φ(μ, ·)`), `hfm_glA_succ`
  (**`ϑˣ(Ω₁·μ + t + 1) = Hd.hdNx μ (ϑˣ(Ω₁·μ + t))`**), `hfm_glA_fixP`, `hfm_lvglAV` (**the closed form
  `ϑˣ(Ω₁·μ + P + r) = φ(μ, i₀ + r)` below `N_μ(P)`**), `hfm_glA_lt`;
* `hfm_glA_pi` (Lemma EXACT for `ϑᵖ(Ω₁·μ + t)` at every base pair with `μ < σ`, from `He.he_glA_pi`).

No new axiom.  New definition: `HfLvl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Hd
  Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A countable level**: `ω ≤ μ < Ω₁` (read through a gate `≥ μ`). -/
def HfLvl (μ : Ordinal.{0}) : Prop := ω ≤ μ ∧ μ < Om1

namespace HfLvl

variable {μ : Ordinal.{0}} (hμ : HfLvl μ)
include hμ

theorem ne : μ ≠ 0 := (omega0_pos.trans_le hμ.1).ne'

theorem one_le : 1 ≤ μ := one_lt_omega0.le.trans hμ.1

theorem one_lt : 1 < μ := one_lt_omega0.trans_le hμ.1

theorem two_lt : 2 < μ := (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans_le hμ.1

theorem lt_Om : μ < Om 1 := by rw [← Br.Om1_eq]; exact hμ.2

theorem succ : HfLvl (μ + 1) :=
  ⟨hμ.1.trans le_self_add, gl_Om1_lim.add_one_lt hμ.2⟩

theorem lt_G : μ < gcG 0 := hμ.lt_Om.trans (gcG_Om1_lt 0)

theorem fix1 {v : Ordinal.{0}} (hv : LuP μ v) : veblen 1 v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt hμ.one_lt a

theorem fix2 {v : Ordinal.{0}} (hv : LuP μ v) : veblen 2 v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt hμ.two_lt a

theorem fixk {v : Ordinal.{0}} (hv : LuP μ v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans_le hμ.1) a

end HfLvl

section Base

variable {μ : Ordinal.{0}} (hμ : HfLvl μ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hμx : μ < x)
include hμ hx hx1 hμx

theorem hfm_lev_q : μ < gq 1 x := hμx.trans (gm1_facts hx hx1).2.1

theorem hfm_lev_T : μ ∈ Tset x ∧ μ < Om1 := gm1_T hx hx1 (hfm_lev_q hμ hx hx1 hμx)

theorem hfm_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP μ (glA μ t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hμT, hμ1⟩ := hfm_lev_T hμ hx hx1 hμx
  exact glA_P hx hx1 hμ.one_le hμT hμ1 htT ht1

theorem hfm_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    x < glA μ t x ∧ glA μ t x < Om1 ∧ t < glA μ t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hμT, hμ1⟩ := hfm_lev_T hμ hx hx1 hμx
  obtain ⟨-, hxa, ha1, -, -, hta⟩ := glA_facts hx hx1 hμ.one_le hμT hμ1 htT ht1
  exact ⟨hxa, ha1, hta⟩

/-- **`ϑˣ(Ω₁·μ + t + 1) = hdNx μ (ϑˣ(Ω₁·μ + t))`** at a base `x > μ`. -/
theorem hfm_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) : glA μ (t + 1) x = hdNx μ (glA μ t x) := by
  obtain ⟨i, hi⟩ := hfm_glA_P hμ hx hx1 hμx ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 hμ.one_le (hfm_lev_q hμ hx hx1 hμx) ht hi.symm, ← hdNx_veb, hi]

/-- **`ϑˣ(Ω₁·μ + P) = hdNx μ P`** at a fixed point `P ∈ (x, Γ_{x+2})` of `φ(μ, ·)`. -/
theorem hfm_glA_fixP {P : Ordinal.{0}} (hP : veblen μ P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    glA μ P x = hdNx μ P := by
  rw [hdNx_fixP hP]
  exact hc_glA_fixG hx hx1 hμ.one_le (hfm_lev_q hμ hx hx1 hμx) hP (hμx.trans hxP) hxP hPq

/-- **THE CLOSED FORM BELOW `N_μ(P)`** at a base `x > μ`. -/
theorem hfm_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA μ P x = hdNx μ P) (hPq : P < gq 1 x)
    (hNq : hcN μ P < gq 1 x) (hi0 : veblen μ i0 = hdNx μ P) (hr : r < hcN μ P) :
    glA μ (P + r) x = veblen μ (i0 + r) := by
  have hNE := hcN_E μ P
  have hSN : hdNx μ P < hcN μ P := hdNx_lt_N (hcN_gt μ P)
  have hi0H : i0 < hcN μ P := (right_le_veblen μ i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcN μ P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen μ (i0 + r) < hcN μ P := by
    have := (isNormal_veblen μ).strictMono hir; rwa [hcN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen μ i0 := by rw [hi0]; exact hdNx_gt μ P
  exact hc_glAV hx hx1 hμ.one_le (hfm_lev_q hμ hx hx1 hμx) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixG hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·μ + P + r) < N_μ(P)`** for `r < N_μ(P)`, at a base `x > μ`. -/
theorem hfm_glA_lt {P r : Ordinal.{0}} (hP0 : glA μ P x = hdNx μ P) (hPq : P < gq 1 x) (hNq : hcN μ P < gq 1 x)
    (hr : r < hcN μ P) : glA μ (P + r) x < hcN μ P := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP μ P
  rw [hfm_lvglAV hμ hx hx1 hμx hP0 hPq hNq hi0 hr]
  have hNE := hcN_E μ P
  have hi0H : i0 < hcN μ P := (right_le_veblen μ i0).trans_lt (by rw [hi0]; exact hdNx_lt_N (hcN_gt μ P))
  have hir : i0 + r < hcN μ P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen μ).strictMono hir; rwa [hcN_fix] at this

end Base

/-- **Lemma EXACT for `ϑᵖ(Ω₁·μ + t)`** at every base pair with `μ < σ`, from Lemma EXACT for `t`. -/
theorem hfm_glA_pi {μ σ ρ t : Ordinal.{0}} (hμσ : μ < σ) (hB : Bases σ ρ) (ht : t ∈ TB ρ σ) (htq : t < gq 1 ρ) :
    glA μ t ρ ∈ TB ρ σ ∧ pi σ ρ (glA μ t ρ) = glA μ (pi σ ρ t) σ := he_glA_pi hμσ hB ht htq

end Googology.Trans.PoR.InaccPsi.R2.Hf
