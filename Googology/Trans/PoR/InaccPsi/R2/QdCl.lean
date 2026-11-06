import Googology.Trans.PoR.InaccPsi.R2.QdBd

/-!
# QdCl: THE CODES OVER `Z` BELOW `B₃` — THE CODES `Uc.UcCl` AND THE VEBLEN ATOMS `Hᵛ_γ(y) ≥ B₂`

As `Uc.UcCl` (codes below `B₂`: the ordinals below `Z`, `Ω₁`, `+`, `φ`, the codes below `X` and the atoms `H_γ(y) ≥ X`
of the levels `γ < E₂` with code components), one more clause: the atoms `Hᵛ_γ(y) ≥ B₂` of the Veblen levels
`γ < Γ_{Ω₂+1}` whose leaves are codes, with a code index `y`.

* `QdCl`, `QdCl.mono`, `QdCl.small`, `QdCl.om`, `QdCl.zero`, `QdCl.one`, `QdCl.opow`;
* `qd_comps_supp`, `qd_supp` (**a code over a strongly critical `Z` is a code over some `Z' < Z`**).

No new axiom.  New definition: `QdCl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **The codes over `Z` below `B₃`**: the codes of `Uc.UcCl`, closed under `+`, `φ`, and the Veblen atoms
`Hᵛ_γ(y) ≥ B₂` with code leaves and a code index. -/
inductive QdCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | uc {x : Ordinal.{0}} : UcCl Z x → QdCl Z x
  | add {x y : Ordinal.{0}} : QdCl Z x → QdCl Z y → QdCl Z (x + y)
  | phi {x y : Ordinal.{0}} : QdCl Z x → QdCl Z y → QdCl Z (veblen x y)
  | hatom {γ y : Ordinal.{0}} : γ < qdG2 → (∀ d ∈ qdComps γ, QdCl Z d) → QdCl Z y → ucB ≤ qdH γ y →
      QdCl Z (qdH γ y)

variable {Z : Ordinal.{0}}

theorem QdCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : QdCl Z x) : QdCl Z' x := by
  induction hx with
  | uc h' => exact QdCl.uc (h'.mono h)
  | add _ _ ihx ihy => exact QdCl.add ihx ihy
  | phi _ _ ihx ihy => exact QdCl.phi ihx ihy
  | hatom hγ _ _ hB ihc ihy => exact QdCl.hatom hγ ihc ihy hB

theorem QdCl.small {x : Ordinal.{0}} (h : x < Z) : QdCl Z x := QdCl.uc (UcCl.small h)

theorem QdCl.om : QdCl Z Om1 := QdCl.uc UcCl.om

theorem QdCl.zero (hZ : 0 < Z) : QdCl Z 0 := QdCl.small hZ

theorem QdCl.one (hZ : 0 < Z) : QdCl Z 1 := QdCl.uc (UcCl.one hZ)

theorem QdCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : QdCl Z c) : QdCl Z (ω ^ c) := by
  have := QdCl.phi (QdCl.zero hZ) h; rwa [veblen_zero_apply] at this

/-- **The leaves of a level are codes over one `Z' < Z`** when each is a code over some `Z' < Z`. -/
theorem qd_comps_supp (hZ : SC Z) :
    ∀ γ, (∀ d ∈ qdComps γ, ∃ Z' < Z, QdCl Z' d) → ∃ Z' < Z, ∀ d ∈ qdComps γ, QdCl Z' d := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases hz : OmTwo < γ ∧ γ < qdG2
  · by_cases hE : ω ^ γ = γ
    · have e : qdComps γ = qdComps (invVeblen₁ γ) ∪ qdComps (invVeblen₂ γ) := by
        rw [qdComps, dif_pos hz, dif_pos hE]
      rw [e] at h ⊢
      obtain ⟨Z1, h1', g1⟩ := IH _ (qd_inv1_lt hz.1 hz.2) fun d hd => h d (Or.inl hd)
      obtain ⟨Z2, h2', g2⟩ := IH _ (Ss.ss_inv2_lt hE) fun d hd => h d (Or.inr hd)
      refine ⟨max Z1 Z2, max_lt h1' h2', fun d hd => ?_⟩
      rcases hd with hd | hd
      · exact (g1 d hd).mono (le_max_left _ _)
      · exact (g2 d hd).mono (le_max_right _ _)
    · have hγ0 : γ ≠ 0 := (qd_Om2_pos.trans hz.1).ne'
      have e : qdComps γ = qdComps (log ω γ) ∪ qdComps (γ % ω ^ log ω γ) := by
        rw [qdComps, dif_pos hz, dif_neg hE]
      rw [e] at h ⊢
      obtain ⟨Z1, h1', g1⟩ := IH _ (Ss.ss_log_lt hγ0 hE) fun d hd => h d (Or.inl hd)
      obtain ⟨Z2, h2', g2⟩ := IH _ (Rj.rj_mod_lt hγ0) fun d hd => h d (Or.inr hd)
      refine ⟨max Z1 Z2, max_lt h1' h2', fun d hd => ?_⟩
      rcases hd with hd | hd
      · exact (g1 d hd).mono (le_max_left _ _)
      · exact (g2 d hd).mono (le_max_right _ _)
  · by_cases h2 : γ < OmTwo
    · have e : qdComps γ = {γ} := by rw [qdComps, dif_neg hz, if_pos h2]
      rw [e] at h ⊢
      obtain ⟨Z', hZ', h'⟩ := h γ rfl
      exact ⟨Z', hZ', fun d hd => by rw [mem_singleton_iff.1 hd]; exact h'⟩
    · have e : qdComps γ = ∅ := by rw [qdComps, dif_neg hz, if_neg h2]
      rw [e]
      exact ⟨0, hZ.1, fun _ hd => absurd hd (Set.notMem_empty _)⟩

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem qd_supp (hZ : SC Z) {x : Ordinal.{0}} (hx : QdCl Z x) : ∃ Z' < Z, QdCl Z' x := by
  induction hx with
  | uc h =>
    obtain ⟨Z', hZ', h'⟩ := Qc.qc_supp hZ h
    exact ⟨Z', hZ', QdCl.uc h'⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', QdCl.add (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', QdCl.phi (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | @hatom γ y hγ _ _ hB ihc ihy =>
    obtain ⟨Z1, h1', g1⟩ := qd_comps_supp hZ γ ihc
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2',
      QdCl.hatom hγ (fun d hd => (g1 d hd).mono (le_max_left _ _)) (g2.mono (le_max_right _ _)) hB⟩

end Googology.Trans.PoR.InaccPsi.R2.Qd
