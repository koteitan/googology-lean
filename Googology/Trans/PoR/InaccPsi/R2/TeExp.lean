import Googology.Trans.PoR.InaccPsi.R2.TeRoad
import Googology.Trans.PoR.InaccPsi.R2.GnIw

/-!
# Lemma EXACT for `ω^X` above any `ε`-number pseudo-base `V(ρ)` with Lemma EXACT for `V` and `ε_{V+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Gn.gn_GAtom_pi`, `Gn.gn_opowG_pi` prove `π(ω^X) = ω^{π X}` for `Γ_{ρ+1} ≤ X < ε_{Γ_{ρ+1}+1}`.  The proof uses only that
the pseudo-base `Γ_{ρ+1}` is an `ε`-number above `ρ` with Lemma EXACT, and that `ε_{Γ_{ρ+1}+1}` has Lemma EXACT and is
countable.  Here the pseudo-base is any function `V` with these properties:

* `te_pi_lt_eN` (`π` maps `Tᵖ[σ] ∩ ε_{V(ρ)+1}` below `ε_{V(σ)+1}`);
* `te_atom_pi` (**`π(ω^{V(ρ)+β}) = ω^{V(σ)+π β}`** for `β ∈ Tᵖ[σ]`, `V(ρ) + β < ε_{V(ρ)+1}`: it is `ϑᵖ(V(ρ) + β')`,
  [W07a] Lemma 4.2 through `vt_ps`, and `π(ϑᵖ(ξ)) = ϑ^σ(π ξ)`, [W07a] Def 5.1);
* `te_opow_pi` (**`π(ω^X) = ω^{π X}` for every `X ∈ Tᵖ[σ] ∩ [V(ρ), ε_{V(ρ)+1})`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) {V : Ordinal.{0} → Ordinal.{0}}
  (hVE : ∀ x, InE x → x < Om1 → InE (V x)) (hVgt : ∀ x, InE x → x < Om1 → x < V x)
  (hVN1 : ∀ x, InE x → x < Om1 → eN (V x) < Om1)
  (hVpi : V ρ ∈ TB ρ σ ∧ pi σ ρ (V ρ) = V σ)
  (hVNpi : eN (V ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (V ρ)) = eN (V σ))

include hB hVNpi in
/-- `π` maps `Tᵖ[σ] ∩ ε_{V(ρ)+1}` below `ε_{V(σ)+1}`. -/
theorem te_pi_lt_eN {β : Ordinal.{0}} (hβ : β ∈ TB ρ σ) (hβe : β < eN (V ρ)) : pi σ ρ β < eN (V σ) := by
  obtain ⟨e1, e2⟩ := hVNpi
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

include hB hVE hVgt hVN1 hVpi hVNpi in
/-- **Lemma EXACT for the atom `ω^{V(ρ)+β}`** (`β ∈ Tᵖ[σ]`, `V(ρ) + β < ε_{V(ρ)+1}`). -/
theorem te_atom_pi {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβe : V ρ + β < eN (V ρ)) :
    ω ^ (V ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (V ρ + β)) = ω ^ (V σ + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := hVpi
  have heE : InE (V ρ) := hVE ρ hB.2.1 hρ1
  have hseE : InE (V σ) := hVE σ hB.1 hσ1
  have hρG : ρ < V ρ := hVgt ρ hB.2.1 hρ1
  have hσG : σ < V σ := hVgt σ hB.1 hσ1
  have hN1 : eN (V ρ) < Om1 := hVN1 ρ hB.2.1 hρ1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ V ρ = V ρ := heE
    have h2 : ω ^ V σ = V σ := hseE
    rw [pi_lt hB hB.1.pos, add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
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
  have hξ1 : V ρ + β' < Om1 := lt_of_le_of_lt (add_le_add le_rfl (sub_le_self β 1)) (hβe.trans hN1)
  have hbρ : V ρ + 1 + β' < eN (V ρ) := by rw [add_assoc, hb]; exact hβe
  have hsum : V ρ + β ∈ TB ρ σ ∧ pi σ ρ (V ρ + β) = V σ + pi σ ρ β := by
    obtain ⟨s1, s2⟩ := pi_add hB heTB hβTB
    exact ⟨s1, by rw [s2, hpe]⟩
  have hlt : pi σ ρ (V ρ + β) < eN (V σ) := te_pi_lt_eN hB hVNpi hsum.1 hβe
  have hbσ : V σ + 1 + pi σ ρ β' < eN (V σ) := by
    rw [add_assoc, hπ1, ← hsum.2]; exact hlt
  have hξ1' : V σ + pi σ ρ β' < Om1 :=
    lt_of_le_of_lt (add_le_add le_rfl le_add_self) (by
      rw [hπ1, ← hsum.2]
      exact hlt.trans (hVN1 σ hB.1 hσ1))
  have hv := vt_ps hB.2.1 hρ1 heE hρG hbρ hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hv' := vt_ps hB.1 hσ1 hseE hσG hbσ hξ1'
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

include hB hVE hVgt hVN1 hVpi hVNpi in
/-- **`π(ω^X) = ω^{π X}`** for every `X ∈ Tᵖ[σ]` with `V(ρ) ≤ X < ε_{V(ρ)+1}`. -/
theorem te_opow_pi {X : Ordinal.{0}} (hX : X ∈ TB ρ σ) (hGX : V ρ ≤ X) (hXe : X < eN (V ρ)) :
    ω ^ X ∈ TB ρ σ ∧ pi σ ρ (ω ^ X) = ω ^ (pi σ ρ X) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨heTB, hpe⟩ := hVpi
  have hX1 : X < Om1 := hXe.trans (hVN1 ρ hB.2.1 hρ1)
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hX hGX hX1
  have e : V ρ + (X - V ρ) = X := Ordinal.add_sub_cancel_of_le hGX
  have hle : V σ ≤ pi σ ρ X := by
    rw [← hpe]; exact ((pi_bijOn hB).2.le_iff_le heTB hX).2 hGX
  obtain ⟨h1, h2⟩ := te_atom_pi hB hVE hVgt hVN1 ⟨heTB, hpe⟩ hVNpi hβTB (by rw [e]; exact hXe)
  rw [e] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, hpβ, hpe, Ordinal.add_sub_cancel_of_le hle]

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Te
