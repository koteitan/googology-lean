import Googology.Trans.PoR.InaccPsi.R2.SvB
import Googology.Trans.PoR.InaccPsi.R2.SsUnc

/-!
# The cited facts at the Veblen levels `(E₁, M)` as one hypothesis package, and the API at the levels `[E₁, M)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tᵗ = Tset τ`, `ϑᵗ = vt τ`, `E₁ = ε_{Ω₁+1} = Gg.ggE`, `Γ_{Ω₁+1} = Gg.ggGam`,
`Δ_μ = Ω₁·(Ω₁ + μ)` (the argument multiple of the level `μ`), `ssDatL μ = ssDat(Ω₁ + μ)` (its data).
`R2.CitedRj` / `R2.CitedRk` cite [W07a] Lemma 3.30 and the membership facts at the levels `μ < E₁`, `R2.CitedSs` at
the level `μ = E₁`.  For a level `μ ∈ (E₁, Γ_{Ω₁+1})` the code `Ω₁ + μ = μ` is a Veblen normal form over `{0, Ω₁}`,
and the same five facts are expected (with the data `ssDat`); they are **not** cited here.  This module states them as
one hypothesis package:

* `SvCit M` (**the five facts at every level `E₁ < μ < M`**: `mem` (data in `Tᵗ` ⇒ argument in `Tᵗ`), `dat` (the
  converse), `vt_lt` (Lemma 3.30 `⇐` against any lower argument `Ω₁·M' + η'`, `M' ≤ Ω₁ + μ`), `lt_of` (Lemma 3.30
  `⇒`), `level` (the data and `η` lie below `ϑᵗ(Δ_μ + η)`)), `svCit_E` (**`SvCit E₁` holds**: no level in `(E₁, E₁)`),
  `svCit_mono`;
* `svc_mem`, `svc_dat`, `svc_vt_lt`, `svc_lt_of`, `svc_level` (**the same facts at every level `E₁ ≤ μ < M`** under
  `SvCit M`: the level `E₁` from `R2.CitedSs`), `sv_arg_lt` (`Δ_μ + η < Γ_{Ω₁+1}` for `μ < Γ_{Ω₁+1}`).

No new axiom.  New definition: the hypothesis package `SvCit`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss

/-- **The cited facts at the levels `E₁ < μ < M`** ([W07a] Def 3.22, Lemma 3.30, Def 3.28 at the arguments `Δ_μ + η`;
not cited in this module): a hypothesis package. -/
structure SvCit (M : Ordinal.{0}) : Prop where
  /-- data in `Tᵗ` ⇒ argument in `Tᵗ` -/
  mem : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggE < μ → μ < M → ssDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → Om1 * (Om1 + μ) + η ∈ Tset τ
  /-- argument in `Tᵗ` ⇒ data in `Tᵗ` -/
  dat : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggE < μ → μ < M → η < Om1 →
    Om1 * (Om1 + μ) + η ∈ Tset τ → ssDatL μ ∈ Tset τ
  /-- Lemma 3.30, `⇐`, against a lower argument `Ω₁·M' + η'` -/
  vt_lt : ∀ {τ M' η' μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggE < μ → μ < M → M' ≤ Om1 + μ →
    ssDat M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → ssDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * (Om1 + μ) + η → ssDat M' < vt τ (Om1 * (Om1 + μ) + η) →
    η' < vt τ (Om1 * (Om1 + μ) + η) → vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)
  /-- Lemma 3.30, `⇒` -/
  lt_of : ∀ {τ ξ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggE < μ → μ < M → ξ ∈ Tset τ → ξ < OmTwo →
    ssDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 → ssDatL μ < vt τ ξ → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) → ξ < Om1 * (Om1 + μ) + η
  /-- the data and `η` lie below the value -/
  level : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggE < μ → μ < M → ssDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → ssDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

/-- **`SvCit E₁` holds** (no level in `(E₁, E₁)`). -/
theorem svCit_E : SvCit ggE where
  mem _ _ h3 h4 := absurd (h3.trans h4) (lt_irrefl _)
  dat _ _ h3 h4 := absurd (h3.trans h4) (lt_irrefl _)
  vt_lt _ _ h3 h4 := absurd (h3.trans h4) (lt_irrefl _)
  lt_of _ _ h3 h4 := absurd (h3.trans h4) (lt_irrefl _)
  level _ _ h3 h4 := absurd (h3.trans h4) (lt_irrefl _)

/-- `SvCit` is antitone in the bound. -/
theorem svCit_mono {M N : Ordinal.{0}} (h : SvCit N) (hMN : M ≤ N) : SvCit M where
  mem a b c d := h.mem a b c (d.trans_le hMN)
  dat a b c d := h.dat a b c (d.trans_le hMN)
  vt_lt a b c d := h.vt_lt a b c (d.trans_le hMN)
  lt_of a b c d := h.lt_of a b c (d.trans_le hMN)
  level a b c d := h.level a b c (d.trans_le hMN)

/-- `Δ_{E₁} = E₁`. -/
theorem sv_Delta_E : Om1 * (Om1 + ggE) = (ggE : Ordinal.{0}) := by rw [ss_Om1_add_E, ss_Om1_mul_E]

theorem sv_G_le_Om2 : (ggGam : Ordinal.{0}) ≤ OmTwo := by
  have h := ggGam_le_Om2; rwa [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h

/-- **`Δ_μ + η < Γ_{Ω₁+1}`** for `μ < Γ_{Ω₁+1}`, `η < Ω₁`. -/
theorem sv_arg_lt {μ η : Ordinal.{0}} (hμ : μ < ggGam) (hη : η < Om1) : Om1 * (Om1 + μ) + η < ggGam := by
  have h1 : (Om1 : Ordinal.{0}) < ggGam := ss_Om1_lt_Gam
  exact (Lq.lq_SC_indec ggGam_spec.1).add_lt
    (sv_Gam_inE.mul_lt h1 ((Lq.lq_SC_indec ggGam_spec.1).add_lt h1 hμ)) (hη.trans h1)

section API

variable {M : Ordinal.{0}} (hC : SvCit M)
include hC

/-- **membership** at every level `E₁ ≤ μ < M`. -/
theorem svc_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ := by
  rcases hEμ.lt_or_eq with h | rfl
  · exact hC.mem hτ hτ1 h hμM hμT hη hηΩ
  · rw [sv_Delta_E]; exact vzT_add hτ hτ1 (ssE_mem hτ hτ1) hη

/-- **the data of the argument** at every level `E₁ ≤ μ < M`. -/
theorem svc_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : ssDatL μ ∈ Tset τ := by
  rcases hEμ.lt_or_eq with h' | rfl
  · exact hC.dat hτ hτ1 h' hμM hηΩ h
  · rw [ssDatL_E]; exact mem_T_of_le hτ hτ1 (Lu.lu_one_lt_E hτ).le

/-- **Lemma 3.30 `⇐`** at every level `E₁ ≤ μ < M`. -/
theorem svc_vt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hM' : M' ≤ Om1 + μ) (hM'T : ssDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : ssDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases hEμ.lt_or_eq with h | rfl
  · exact hC.vt_lt hτ hτ1 h hμM hM' hM'T hη' hη'Ω hμT hη hηΩ harg hd' hη'v
  · rw [sv_Delta_E] at harg hd' hη'v ⊢
    rw [ss_Om1_add_E] at hM'
    have hpos : (0 : Ordinal.{0}) < vt τ (ggE + η) := lt_of_le_of_lt zero_le hη'v
    rcases hM'.lt_or_eq with hlt | rfl
    · rw [ssDat_eq_rj _ hlt] at hM'T hd'
      exact ssVt_lt hτ hτ1 hlt.le hM'T hη' hη'Ω hη hηΩ harg hd' hη'v
    · exact ssVt_lt hτ hτ1 le_rfl (by rw [Ss.ss_rjDat_E]; exact mem_T_of_le hτ hτ1 zero_le) hη' hη'Ω hη hηΩ
        harg (by rw [Ss.ss_rjDat_E]; exact hpos) hη'v

/-- **Lemma 3.30 `⇒`** at every level `E₁ ≤ μ < M`. -/
theorem svc_lt_of {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : ssDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η := by
  rcases hEμ.lt_or_eq with h' | rfl
  · exact hC.lt_of hτ hτ1 h' hμM hξ hξ2 hμT hη hηΩ hdξ hηξ h
  · rw [sv_Delta_E] at h ⊢
    exact ssLt_of_vt_lt hτ hτ1 hξ hξ2 hη hηΩ hηξ h

/-- **The data and `η` lie below `ϑᵗ(Δ_μ + η)`** at every level `E₁ ≤ μ < M`. -/
theorem svc_level {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ssDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases hEμ.lt_or_eq with h' | rfl
  · exact hC.level hτ hτ1 h' hμM hμT hη hηΩ
  · rw [sv_Delta_E, ssDatL_E]
    have hargT : ggE + η ∈ Tset τ := vzT_add hτ hτ1 (ssE_mem hτ hτ1) hη
    have hE := (vt_E_iff hτ hτ1 hargT (ss_arg_lt hηΩ)).2 (rj_Om1_lt_E.le.trans le_self_add)
    exact ⟨(Lu.lu_one_lt_E hτ).trans hE.1, ssLevel_lt hτ hτ1 hη hηΩ⟩

end API

end Googology.Trans.PoR.InaccPsi.R2.Sv
