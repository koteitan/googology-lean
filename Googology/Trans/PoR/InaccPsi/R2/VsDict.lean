import Googology.Trans.PoR.InaccPsi.R2.VsLex
import Googology.Trans.PoR.InaccPsi.R2.VpNF

/-!
# The ψ-side of the dictionary `D(s)`: the three forms on `(Ω_s, Ω_{s+1})`, the level bound, the parts

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite, `s ≥ 1`), `ψ_π = S.psi · π`, `Hˡ⁽ˢ⁾_γ = Ul.ulH S s γ`, `K⁽ⁱ⁾_q = Ul.UlK S i q`.
The dictionary `D(s)` of `R2.CitedUz` / `R2.CitedVp` reads the `ϑ_s`-terms of `[Ω_s, θ_s)` as (C) `ω^g`, `g ≥ Ω_s` not
an `ε`-number, (V) `φ(a, c)`, `1 ≤ a`, `a, c < φ(a, c)`, (H) the atoms `Hˡ⁽ˢ⁾_λ(y)`, `λ < V`, `y < Hˡ⁽ˢ⁾_λ(y)`.  The
Lean half (`ϑ_s` is not a Lean object):

* `vsShape` (**every `ξ ∈ (Ω_s, ψ_W(A))` has exactly one of the three forms**: not an `ε`-number with `Ω_s ≤ log ξ <
  ξ`; an `ε`-number `φ(a, c)` with `1 ≤ a`, `a, c < ξ`, not strongly critical; strongly critical with the normal form
  `ξ = Hˡ⁽ˢ⁾_λ(y)`, `λ = Vp.vpLev S s ξ < V` visible at `ξ` (`λ ∈ K⁽ˢ⁾_ξ`), `y = Vp.vpI S s λ ξ < ξ`; it is the
  only pair `(γ, y)` with `γ < V`, `y < ξ = Hˡ⁽ˢ⁾_γ(y)`, by `Vp.vpLev_H`);
* `vs_B0_ne` (**a value `ψ(B)` of `Hˡ⁽ˢ⁾_γ`, `γ ≠ 0`, has `B ≠ 0`**), `vs_lev_bound` (**an atom `Hˡ⁽ˢ⁾_γ(y) < ψ_W(E)`
  has `γ < ψ_V(E)`, and `Ω_{s+1} < E` when `γ ≠ 0`**);
* `vs_atom_parts` (**the parts of an atom**: `Hˡ⁽ˢ⁾_γ(y) ∈ K⁽ⁱ⁾_q ⇔ γ, y ∈ K⁽ⁱ⁾_q` for `i < s`, `q ≤ Ω_{i+1}`, and
  `γ ∈ K⁽ˢ⁾_{Hˡ⁽ˢ⁾_γ(y)}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **A value `ψ_W(B)` of `Hˡ⁽ˢ⁾_γ`, `γ ≠ 0`, has `B ≠ 0`.** -/
theorem vs_B0_ne (hs : s < ω) {B γ c : Ordinal.{0}} (hγ0 : γ ≠ 0) (hB : ulH S s γ c = S.psi B (Om (s + 1))) :
    B ≠ 0 := by
  rintro rfl
  have hv : ulH S s γ c = ulH S s 0 0 := by rw [hB, Us.us_psi0 hs]
  have hf : ulH S s 0 (ulH S s γ c) = ulH S s γ c :=
    ucG_fix_lower (pos_iff_ne_zero.2 hγ0) ⟨c, rfl⟩ ((ulD_le_self 0).trans_lt (ulH_SC γ c).1)
  rw [hv] at hf
  exact Us.us_val0_ne hf

/-- **The level bound**: an atom `Hˡ⁽ˢ⁾_γ(y) < ψ_W(E)` (`γ < V`, `y < Hˡ⁽ˢ⁾_γ(y)`) has `γ < ψ_V(E)`, and `Ω_{s+1} <
E` if `γ ≠ 0`. -/
theorem vs_lev_bound (hs : s < ω) {γ y E : Ordinal.{0}} (hγ : γ < Om (s + 1 + 1)) (hy : y < ulH S s γ y)
    (hE : ulH S s γ y < S.psi E (Om (s + 1))) :
    γ < S.psi E (Om (s + 1 + 1)) ∧ (γ ≠ 0 → Om (s + 1) < E) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  obtain ⟨B, c, D, hown, hc, hcD, hcond, -⟩ := Vp.vp_dec (S := S) (s := s) hs hy hE
  have hDy : D ≤ y := by rw [← hcD]; exact le_add_self
  have hzW : ulH S s γ y < Om (s + 1) := hE.trans (Ui.ui_psi_lt (s := s) E)
  have hDW : D < Om (s + 1) := (hDy.trans_lt hy).trans hzW
  obtain ⟨hψe, -⟩ := Vp.vp_run (S := S) (s := s) hs hγ hown hc hDW hcond
  rw [hcD] at hψe
  have heE : B + Om (s + 1) ^ γ * D < E := by
    by_contra hc'
    push Not at hc'
    have h1 := (psi_mono (S := S) hκ hc').1
    rw [hψe] at h1
    exact absurd hE (not_lt.2 h1)
  have hBE : B < E := lt_of_le_of_lt le_self_add heE
  have hγψ : γ ≤ S.psi B (Om (s + 1 + 1)) := Us.us_val_le hs hown hc
  refine ⟨hγψ.trans_lt (Ui.ui_psi_lt_of_own (s := s + 1) (Vp.vp_ownV hown) hBE), fun hγ0 => ?_⟩
  have hB0 : B ≠ 0 := vs_B0_ne hs hγ0 hc
  have hdvd : Om (s + 1) ^ γ ∣ B := Us.us_dvd_val hs hown hc
  have h1 : Om (s + 1) ≤ Om (s + 1) ^ γ := by
    have := opow_le_opow_right (Ui.ui_SC_W s).1 (one_le_iff_ne_zero.2 hγ0)
    rwa [opow_one] at this
  exact (h1.trans (Ordinal.le_of_dvd hB0 hdvd)).trans_lt hBE

/-- **The parts of an atom**: for `i < s`, `q ≤ Ω_{i+1}` strongly critical, `Hˡ⁽ˢ⁾_γ(y) ∈ K⁽ⁱ⁾_q ⇔ γ, y ∈ K⁽ⁱ⁾_q`
(`γ < V`, `y < Hˡ⁽ˢ⁾_γ(y) < W`); and `γ ∈ K⁽ˢ⁾_{Hˡ⁽ˢ⁾_γ(y)}`. -/
theorem vs_atom_parts (hs : s < ω) {i q γ y : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγ : γ < Om (s + 1 + 1)) (hy : y < ulH S s γ y) (hW : ulH S s γ y < Om (s + 1)) :
    (UlK S i q (ulH S s γ y) ↔ UlK S i q γ ∧ UlK S i q y) ∧ UlK S s (ulH S s γ y) γ :=
  ⟨Uz.uz_L1 hs his hq hqL hγ hW (ne_of_gt hy), (ul_vis (ulH_SC γ y)).1 (ulH_D_lt γ y)⟩

/-- **The three forms on `(Ω_s, ψ_W(A))`.** -/
theorem vsShape (hs : s < ω) (hs1 : 1 ≤ s) {ξ A : Ordinal.{0}} (h1 : Om s < ξ) (hA : ξ < S.psi A (Om (s + 1))) :
    (ω ^ ξ ≠ ξ ∧ Om s ≤ log ω ξ ∧ log ω ξ < ξ) ∨
    (ω ^ ξ = ξ ∧ ¬ SC ξ ∧ 1 ≤ invVeblen₁ ξ ∧ invVeblen₁ ξ < ξ ∧ invVeblen₂ ξ < ξ ∧
      veblen (invVeblen₁ ξ) (invVeblen₂ ξ) = ξ) ∨
    (SC ξ ∧ ulH S s (Vp.vpLev S s ξ) (Vp.vpI S s (Vp.vpLev S s ξ) ξ) = ξ ∧
      Vp.vpI S s (Vp.vpLev S s ξ) ξ < ξ ∧ Vp.vpLev S s ξ < Om (s + 1 + 1) ∧ UlK S s ξ (Vp.vpLev S s ξ)) := by
  have hO1 : Om1 < ξ := by
    rw [Rj.rj_Om1]; exact (Om_le_Om.2 hs1).trans_lt h1
  have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  by_cases hE : ω ^ ξ = ξ
  · by_cases hI : invVeblen₁ ξ < ξ
    · right; left
      refine ⟨hE, fun hSC => ?_, ?_, hI, Ss.ss_inv2_lt hE, ?_⟩
      · exact (Tl.tl_SC_facts hSC).2 hI
      · refine one_le_iff_ne_zero.2 fun e => ?_
        have hev : veblen (invVeblen₁ ξ) (invVeblen₂ ξ) = ξ := by
          rw [veblen_invVeblen₁_invVeblen₂, hE]
        rw [e, veblen_zero_apply] at hev
        have h2 : ω ^ invVeblen₂ ξ = ω ^ ξ := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 h2) (Ss.ss_inv2_lt hE).ne
      · rw [veblen_invVeblen₁_invVeblen₂, hE]
    · right; right
      have hSC : SC ξ := Tl.tl_SC_of hO1 hI
      have hne := Vp.vp_nf_ex hs hSC h1 hA
      obtain ⟨hlV, hlD, -, -, -⟩ := Vp.vpLev_spec hSC h1 hne
      obtain ⟨hH, hy⟩ := Vp.vp_nf hSC h1 hne
      exact ⟨hSC, hH, hy, hlV, (ul_vis hSC).1 hlD⟩
  · left
    have hΩE : ω ^ (Om s : Ordinal.{0}) = Om s := Low.opow_eq_self_of_SC (SC_Om (lt_of_lt_of_le zero_lt_one hs1).ne')
    refine ⟨hE, le_log_of_opow_le one_lt_omega0 (by rw [hΩE]; exact h1.le), Ss.ss_log_lt hξ0 hE⟩

end Googology.Trans.PoR.InaccPsi.R2.Vs
