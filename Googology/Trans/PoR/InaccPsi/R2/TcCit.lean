import Googology.Trans.PoR.InaccPsi.R2.TcLeast

/-!
# The [W07a] facts at the levels `[Γ_{Ω₁+1}, M)` as one hypothesis package, and the API at the levels `[E₁, M)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tᵗ = Tset τ`, `ϑᵗ = vt τ`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `Γ' = lgGam'` (the least
strongly critical ordinal above `Γ_{Ω₁+1}`), `Δ_μ = Ω₁·(Ω₁ + μ)`, `tcDatL μ = tcDat(Ω₁ + μ)` (`R2.TcDat`, `R2.TcFn`).
`R2.CitedSy` cites the five facts at the levels `E₁ < μ < Γ_{Ω₁+1}` (the package `Sv.SvCit Γ_{Ω₁+1}`, `Sy.syCit`).
At a level `μ ∈ [Γ_{Ω₁+1}, Γ')` the code `μ` is a Veblen normal form over `{0, Ω₁, Γ_{Ω₁+1}}` and the same five facts
hold with the data `tcDat`; this module states them as one package (cited in `R2.CitedTc`):

* `TcCit M` (**the five facts at every level `Γ_{Ω₁+1} ≤ μ < M`**: `mem`, `dat`, `vt_lt` (Lemma 3.30 `⇐` against any
  lower argument `Ω₁·M' + η'`, `M' ≤ Ω₁ + μ`), `lt_of` (Lemma 3.30 `⇒`), `level`), `tcCit_G` (**`TcCit Γ_{Ω₁+1}`
  holds**: no level in `[Γ_{Ω₁+1}, Γ_{Ω₁+1})`), `tcCit_mono`;
* `tcc_mem`, `tcc_dat`, `tcc_vt_lt`, `tcc_lt_of`, `tcc_level` (**the same facts at every level `E₁ ≤ μ < M`** under
  `TcCit M`, `M ≤ Γ'`: the levels below `Γ_{Ω₁+1}` from `Sy.syCit`), `tc_arg_lt` (`Δ_μ + η < Γ'` for `μ < Γ'`),
  `tc_G'_le_Om2`.

No new axiom.  New definition: the hypothesis package `TcCit`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss

/-- **The [W07a] facts at the levels `Γ_{Ω₁+1} ≤ μ < M`** (Def 3.22, Lemma 3.30, Def 3.28 at the arguments
`Δ_μ + η`): a hypothesis package. -/
structure TcCit (M : Ordinal.{0}) : Prop where
  /-- data in `Tᵗ` ⇒ argument in `Tᵗ` -/
  mem : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tcDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → Om1 * (Om1 + μ) + η ∈ Tset τ
  /-- argument in `Tᵗ` ⇒ data in `Tᵗ` -/
  dat : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → η < Om1 →
    Om1 * (Om1 + μ) + η ∈ Tset τ → tcDatL μ ∈ Tset τ
  /-- Lemma 3.30, `⇐`, against a lower argument `Ω₁·M' + η'` -/
  vt_lt : ∀ {τ M' η' μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → M' ≤ Om1 + μ →
    tcDat M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → tcDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * (Om1 + μ) + η → tcDat M' < vt τ (Om1 * (Om1 + μ) + η) →
    η' < vt τ (Om1 * (Om1 + μ) + η) → vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)
  /-- Lemma 3.30, `⇒` -/
  lt_of : ∀ {τ ξ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ξ ∈ Tset τ → ξ < OmTwo →
    tcDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 → tcDatL μ < vt τ ξ → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) → ξ < Om1 * (Om1 + μ) + η
  /-- the data and `η` lie below the value -/
  level : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tcDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → tcDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

/-- **`TcCit Γ_{Ω₁+1}` holds** (no level in `[Γ_{Ω₁+1}, Γ_{Ω₁+1})`). -/
theorem tcCit_G : TcCit ggGam where
  mem _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  dat _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  vt_lt _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  lt_of _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  level _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)

/-- `TcCit` is antitone in the bound. -/
theorem tcCit_mono {M N : Ordinal.{0}} (h : TcCit N) (hMN : M ≤ N) : TcCit M where
  mem a b c d := h.mem a b c (d.trans_le hMN)
  dat a b c d := h.dat a b c (d.trans_le hMN)
  vt_lt a b c d := h.vt_lt a b c (d.trans_le hMN)
  lt_of a b c d := h.lt_of a b c (d.trans_le hMN)
  level a b c d := h.level a b c (d.trans_le hMN)

theorem tc_G'_le_Om2 (S : InaccSeq.{0}) : (lgGam' : Ordinal.{0}) ≤ OmTwo := by
  have h := lgGam'_le_Om2 S; rwa [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h

/-- **`Δ_μ + η < Γ'`** for `μ < Γ'`, `η < Ω₁`. -/
theorem tc_arg_lt {μ η : Ordinal.{0}} (hμ : μ < lgGam') (hη : η < Om1) : Om1 * (Om1 + μ) + η < lgGam' := by
  have h1 : (Om1 : Ordinal.{0}) < lgGam' := tc_Om1_lt_G'
  exact tc_G'_indec.add_lt (tc_G'_inE.mul_lt h1 (tc_G'_indec.add_lt h1 hμ)) (hη.trans h1)

section API

variable {M : Ordinal.{0}} (hC : TcCit M)
include hC

/-- **membership** at every level `E₁ ≤ μ < M`. -/
theorem tcc_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ := by
  rcases lt_or_ge μ ggGam with h | h
  · rw [tcDatL_eq_ss h.le] at hμT; exact Sy.syc_mem hτ hτ1 hEμ h hμT hη hηΩ
  · exact hC.mem hτ hτ1 h hμM hμT hη hηΩ

/-- **the data of the argument** at every level `E₁ ≤ μ < M`. -/
theorem tcc_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : tcDatL μ ∈ Tset τ := by
  rcases lt_or_ge μ ggGam with h' | h'
  · rw [tcDatL_eq_ss h'.le]; exact Sy.syc_dat hτ hτ1 hEμ h' hηΩ h
  · exact hC.dat hτ hτ1 h' hμM hηΩ h

/-- **Lemma 3.30 `⇐`** at every level `E₁ ≤ μ < M`. -/
theorem tcc_vt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hM' : M' ≤ Om1 + μ) (hM'T : tcDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : tcDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases lt_or_ge μ ggGam with h | h
  · have hM'G : M' < ggGam :=
      hM'.trans_lt ((Lq.lq_SC_indec ggGam_spec.1).add_lt ss_Om1_lt_Gam h)
    rw [tcDatL_eq_ss h.le] at hμT
    rw [tcDat_eq_ss M' hM'G] at hM'T hd'
    exact Sy.syc_vt_lt hτ hτ1 hEμ h hM' hM'T hη' hη'Ω hμT hη hηΩ harg hd' hη'v
  · exact hC.vt_lt hτ hτ1 h hμM hM' hM'T hη' hη'Ω hμT hη hηΩ harg hd' hη'v

/-- **Lemma 3.30 `⇒`** at every level `E₁ ≤ μ < M`. -/
theorem tcc_lt_of {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : tcDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η := by
  rcases lt_or_ge μ ggGam with h' | h'
  · rw [tcDatL_eq_ss h'.le] at hμT hdξ
    exact Sy.syc_lt_of hτ hτ1 hEμ h' hξ hξ2 hμT hη hηΩ hdξ hηξ h
  · exact hC.lt_of hτ hτ1 h' hμM hξ hξ2 hμT hη hηΩ hdξ hηξ h

/-- **The data and `η` lie below `ϑᵗ(Δ_μ + η)`** at every level `E₁ ≤ μ < M`. -/
theorem tcc_level {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    tcDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases lt_or_ge μ ggGam with h' | h'
  · rw [tcDatL_eq_ss h'.le] at hμT ⊢
    exact Sy.syc_level hτ hτ1 hEμ h' hμT hη hηΩ
  · exact hC.level hτ hτ1 h' hμM hμT hη hηΩ

end API

end Googology.Trans.PoR.InaccPsi.R2.Tc
