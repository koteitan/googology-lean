import Googology.Trans.PoR.InaccPsi.R2.VzV
import Googology.Trans.PoR.InaccPsi.R2.EvOZ

/-!
# The IMG package of `ζ_{x+1}`, and Theorem BLK^O at the block of `Λ_{ζ_{x+1}}`

The project's Lemma IMG for the value `ζ_{ρ+1} = evZ ρ`: every covering copy `f` of a set containing the witness
sets has `evZ (f ρ) ≤ f (evZ ρ)`.  Inside the block `evZ ρ ≤₁ evZ ρ·3` (`R₁⁺`, `vz_lh_evZ`), the copy keeps it; a
copy that is not a `υ`-point has its `R₁⁺` reach, so it is a fixed point of `ε` above `f ρ` (`vz_le1R_three`); a
copy that is a `υ`-point is above `evZ (f ρ)` (`evZ_le_ups`).

With it, Lemma TOP at `Λ_{ζ_{x+1}}` with the term `evZ`, Theorem BLK^O with `OrecZ` below `υ_{Λ_{ζ_{x+1}}+ω²}` (the
block of `ρ_{Λ_{ζ_{x+1}}}` included), and the exact reach there.

* `RstK.vzPkgZ` (**the IMG package of `ζ_{x+1}`**);
* `vz_topIn_LamZ`, `vz_specZ2`, `vz_blkZ2` (**BLK^O below `υ_{Λ_{ζ_{x+1}}+ω²}`**), `vz_coreZ2`, `vz_reach_LamZ`
  (**`lh(ρ_{Λ_{ζ_{x+1}}}) = δ + ζ_{ρ+1}`**), `vz_nuC_boundZ2` (**`υ_{Λ_{ζ_{x+1}}+ω²} ≤ ρ_L < ν_C`**).

The axioms of `R2.CitedVz` enter through `vz_vt_two_eq` and `vz_lh_evZ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem vz_evZ_lt_δ : evZ ρ < δ := vz_evZ_lt_ups h.ρE h.ρ1 h.ρδ h.next.2.1

/-- **The IMG package of `ζ_{x+1}`** (`evZ`): witness sets such that every covering copy `f` has
`evZ (f ρ) ≤ f (evZ ρ)` (inside the block `evZ ρ ≤₁ evZ ρ·3`). -/
theorem vzPkgZ : ImgPkg ρ δ evZ := by
  classical
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  set v := evZ ρ with hv
  have hρv : ρ < v := lt_evZ ρ
  have hvδ : v < δ := h.vz_evZ_lt_δ
  have hvE : InE v := evZ_E ρ
  have hv0 : 0 < v := hvE.pos
  have hvv : v + v < δ := hδI.add_lt hvδ hvδ
  have hvvv : v + v + v < δ := hδI.add_lt hvv hvδ
  have hsrcR : le1R v (v * 2 + v) := (vz_lh_evZ hρE h.ρ1).1
  have hsrc : le1 v (v + v + v) :=
    (h.lowδ _ _ hρv hvvv.le).2 (by rw [← mul_two_eq]; exact hsrcR)
  have w1 : WZ ρ δ {ρ} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
    simpa using this
  have w2 : WZ ρ δ (insert v {ρ}) ∅ := w1.insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w3 : WZ ρ δ (insert (v + v) (insert v {ρ})) ∅ :=
    w2.insW (hρv.le.trans le_self_add) hvv
      (Or.inr ⟨v, by simp, v, by simp, lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  have w4 : WZ ρ δ (insert (v + v + v) (insert (v + v) (insert v {ρ}))) ∅ :=
    w3.insW ((hρv.le.trans le_self_add).trans le_self_add) hvvv
      (Or.inr ⟨v + v, by simp, v, by simp, lt_add_of_pos_right _ hv0,
        lt_of_lt_of_le (lt_add_of_pos_right _ hv0) le_self_add, rfl⟩)
  refine ⟨(one_le_iff_pos.2 h.ρU.1).trans hρv.le, hvδ, _, _, w4, by simp [hv], fun A f hW _ C => ?_⟩
  have hvA : v ∈ A := hW (by simp)
  have hvvA : v + v ∈ A := hW (by simp)
  have hvvvA : v + v + v ∈ A := hW (by simp)
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hfvv : f v + f v = f (v + v) := C.add v hvA v hvA _ hvvA rfl
  have hfvvv : f (v + v) + f v = f (v + v + v) := C.add _ hvvA v hvA _ hvvvA rfl
  have himg : le1 (f v) (f v + f v + f v) := by
    have := C.cov1 v hvA _ hvvvA hsrc
    rwa [← hfvvv, ← hfvv] at this
  by_cases hU : UpsPt (f v)
  · exact evZ_le_ups hfρE hfρ1 hfρv hU
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    rw [← mul_two_eq] at hR
    exact vz_le1R_three hfρE hfρv hR

end RstK

/-! ## Theorem BLK^O at the block of `Λ_{ζ_{x+1}}` -/

/-- **The input of Lemma TOP at `Λ_{ζ_{x+1}}`** with the term `evZ` (`RstK.vzPkgZ`). -/
theorem vz_topIn_LamZ : TopInH OrecZ LamZ :=
  ⟨evZ, 0, OrecZ_LamZ, (ups_ri LamZ_ri).1, fun _ hμ hμl _ => OrecZ_lt_top hμ hμl, fun R => R.vzPkgZ⟩

/-- **`OrecZ` is a general offset specification up to `Λ_{ζ_{x+1}} + ω²`.** -/
theorem vz_specZ2 : OffSpecGen OrecZ (LamZ + ω * ω) :=
  specZ (dvd_add (ri_iff.1 LamZ_ri).2 (dvd_refl _)) (Om1_add_lt LamZ_lt_Om1 ww_lt_Om1)
    (fun l hl hlB => by
      rcases lt_trichotomy l LamZ with hlt | rfl | hgt
      · exact topIn_OrecZ hl (OrecZ_lt_top hl hlt)
      · exact vz_topIn_LamZ
      · exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 LamZ_ri).2 (ri_iff.1 hl).2 hgt)))

/-- **Theorem BLK^O with `OrecZ` below `υ_{Λ_{ζ_{x+1}}+ω²}`** in `R₂^C` (the block of `ρ_{Λ_{ζ_{x+1}}}`
included). -/
theorem vz_blkZ2 :
    (∀ c d, c < d → d < upsilon (LamZ + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamZ + ω * ω ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamZ + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecZ l)) ∧
    (∀ α < upsilon (LamZ + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen vz_specZ2

/-- **CORE-C up to `υ_{Λ_{ζ_{x+1}}+ω²}`.** -/
theorem vz_coreZ2 : Set.Iio (upsilon (LamZ + ω * ω)) ⊆ Core R2C := core_genGen vz_specZ2

/-- **The reach at `Λ_{ζ_{x+1}}`**: `lh(ρ) = δ + ζ_{ρ+1}` for `ρ = ρ_{Λ_{ζ_{x+1}}}`. -/
theorem vz_reach_LamZ : IsReach R2C (upsilon LamZ) (upsilon (LamZ + ω + 1) + evZ (upsilon LamZ)) := by
  have := (vz_blkZ2.2.1 LamZ LamZ_ri (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))).2.2
  rwa [OrecZ_LamZ] at this

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ζ_{x+1}} + ω² ≤ L < ξ` restart
indices, `υ_{Λ_{ζ_{x+1}}+ω²} ≤ ρ_L < ν_C < Ω₁`. -/
theorem vz_nuC_boundZ2 : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamZ + ω * ω ≤ L ∧ L < ξ ∧
    upsilon (LamZ + ω * ω) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec vz_specZ2 hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
