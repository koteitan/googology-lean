import Googology.Trans.PoR.InaccPsi.R2.TiLeast
import Googology.Trans.PoR.InaccPsi.R2.CitedTf

/-!
# The [W07a] facts at the levels `[Γ_{Ω₁+1}, M)` as a package, discharged at `M = B_Γ` by `R2.CitedTf`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tᵗ = Tset τ`, `ϑᵗ = vt τ`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `B_Γ = Tf.tfBG` (the least
fixed point of `Γ` above `Ω₁`), `Δ_μ = Ω₁·(Ω₁ + μ)`, `tfDatL μ = tfDat(Ω₁ + μ)` (`R2.TfDat`, `R2.TfFn`).  `R2.CitedTf`
cites the five facts once at every level `Ω₁ ≤ M' < B_Γ` (here `M' = Ω₁ + μ`):

* `TiCit M` (**the five facts at every level `Γ_{Ω₁+1} ≤ μ < M`**: `mem`, `dat`, `vt_lt` (Lemma 3.30 `⇐` against any
  lower argument `Ω₁·M' + η'`, `M' ≤ Ω₁ + μ`), `lt_of` (Lemma 3.30 `⇒`), `level`; the shape of `Tc.TcCit` with the data
  `tfDat`), `tiCit_G`, `tiCit_mono`;
* `ti_lev_lt` (`Ω₁ ≤ Ω₁ + μ < B_Γ`), `ti_arg_lt` (`Δ_μ + η < B_Γ` for `μ < B_Γ`), `tiCit` (**`TiCit B_Γ` holds**, from
  `tfArg_mem`, `tfArg_dat`, `tfVt_lt`, `tfLt_of_vt_lt`, `tfLevel_lt`);
* `tic_mem`, `tic_dat`, `tic_vt_lt`, `tic_lt_of`, `tic_level` (**the same facts at every level `E₁ ≤ μ < M`** under
  `TiCit M`: the levels below `Γ_{Ω₁+1}` directly from `R2.CitedTf`).

No new axiom.  New definition: the package `TiCit`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss

/-- **The [W07a] facts at the levels `Γ_{Ω₁+1} ≤ μ < M`** (Def 3.22, Lemma 3.30, Def 3.28 at the arguments
`Δ_μ + η`): a hypothesis package. -/
structure TiCit (M : Ordinal.{0}) : Prop where
  /-- data in `Tᵗ` ⇒ argument in `Tᵗ` -/
  mem : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tfDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → Om1 * (Om1 + μ) + η ∈ Tset τ
  /-- argument in `Tᵗ` ⇒ data in `Tᵗ` -/
  dat : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → η < Om1 →
    Om1 * (Om1 + μ) + η ∈ Tset τ → tfDatL μ ∈ Tset τ
  /-- Lemma 3.30, `⇐`, against a lower argument `Ω₁·M' + η'` -/
  vt_lt : ∀ {τ M' η' μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → M' ≤ Om1 + μ →
    tfDat M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → tfDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * (Om1 + μ) + η → tfDat M' < vt τ (Om1 * (Om1 + μ) + η) →
    η' < vt τ (Om1 * (Om1 + μ) + η) → vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)
  /-- Lemma 3.30, `⇒` -/
  lt_of : ∀ {τ ξ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ξ ∈ Tset τ → ξ < OmTwo →
    tfDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 → tfDatL μ < vt τ ξ → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) → ξ < Om1 * (Om1 + μ) + η
  /-- the data and `η` lie below the value -/
  level : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tfDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → tfDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

/-- **`TiCit Γ_{Ω₁+1}` holds** (no level in `[Γ_{Ω₁+1}, Γ_{Ω₁+1})`). -/
theorem tiCit_G : TiCit ggGam where
  mem _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  dat _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  vt_lt _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  lt_of _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)
  level _ _ h3 h4 := absurd (h3.trans_lt h4) (lt_irrefl _)

/-- `TiCit` is antitone in the bound. -/
theorem tiCit_mono {M N : Ordinal.{0}} (h : TiCit N) (hMN : M ≤ N) : TiCit M where
  mem a b c d := h.mem a b c (d.trans_le hMN)
  dat a b c d := h.dat a b c (d.trans_le hMN)
  vt_lt a b c d := h.vt_lt a b c (d.trans_le hMN)
  lt_of a b c d := h.lt_of a b c (d.trans_le hMN)
  level a b c d := h.level a b c (d.trans_le hMN)

/-- `Ω₁ ≤ Ω₁ + μ < B_Γ` for `μ < B_Γ`. -/
theorem ti_lev_lt {μ : Ordinal.{0}} (hμ : μ < tfBG) : Om1 ≤ Om1 + μ ∧ Om1 + μ < tfBG :=
  ⟨le_self_add, tf_BG_indec.add_lt tfBG_gt hμ⟩

/-- **`Δ_μ + η < B_Γ`** for `μ < B_Γ`, `η < Ω₁`. -/
theorem ti_arg_lt {μ η : Ordinal.{0}} (hμ : μ < tfBG) (hη : η < Om1) : Om1 * (Om1 + μ) + η < tfBG := by
  have h1 : (Om1 : Ordinal.{0}) < tfBG := tfBG_gt
  exact tf_BG_indec.add_lt (tf_BG_inE.mul_lt h1 (tf_BG_indec.add_lt h1 hμ)) (hη.trans h1)

/-- **`TiCit B_Γ`**: the five facts at every level `Γ_{Ω₁+1} ≤ μ < B_Γ`, from `R2.CitedTf` (`M = Ω₁ + μ`). -/
theorem tiCit : TiCit tfBG where
  mem h1 h2 _ h4 h5 h6 h7 := tfArg_mem h1 h2 (ti_lev_lt h4).1 (ti_lev_lt h4).2 h5 h6 h7
  dat h1 h2 _ h4 h5 h6 := tfArg_dat h1 h2 (ti_lev_lt h4).1 (ti_lev_lt h4).2 h5 h6
  vt_lt h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    tfVt_lt h1 h2 (ti_lev_lt h4).1 (ti_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 :=
    tfLt_of_vt_lt h1 h2 (ti_lev_lt h4).1 (ti_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 _ h4 h5 h6 h7 := tfLevel_lt h1 h2 (ti_lev_lt h4).1 (ti_lev_lt h4).2 h5 h6 h7

section API

variable {M : Ordinal.{0}} (hC : TiCit M)
include hC

/-- **membership** at every level `E₁ ≤ μ < M`. -/
theorem tic_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : tfDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ := by
  rcases lt_or_ge μ ggGam with h | h
  · exact tfArg_mem hτ hτ1 (ti_lev_lt (h.trans tf_gg_lt_BG)).1 (ti_lev_lt (h.trans tf_gg_lt_BG)).2 hμT hη hηΩ
  · exact hC.mem hτ hτ1 h hμM hμT hη hηΩ

/-- **the data of the argument** at every level `E₁ ≤ μ < M`. -/
theorem tic_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : tfDatL μ ∈ Tset τ := by
  rcases lt_or_ge μ ggGam with h' | h'
  · exact tfArg_dat hτ hτ1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).2 hηΩ h
  · exact hC.dat hτ hτ1 h' hμM hηΩ h

/-- **Lemma 3.30 `⇐`** at every level `E₁ ≤ μ < M`. -/
theorem tic_vt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hM' : M' ≤ Om1 + μ) (hM'T : tfDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : tfDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : tfDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases lt_or_ge μ ggGam with h | h
  · exact tfVt_lt hτ hτ1 (ti_lev_lt (h.trans tf_gg_lt_BG)).1 (ti_lev_lt (h.trans tf_gg_lt_BG)).2 hM' hM'T hη' hη'Ω
      hμT hη hηΩ harg hd' hη'v
  · exact hC.vt_lt hτ hτ1 h hμM hM' hM'T hη' hη'Ω hμT hη hηΩ harg hd' hη'v

/-- **Lemma 3.30 `⇒`** at every level `E₁ ≤ μ < M`. -/
theorem tic_lt_of {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : tfDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : tfDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η := by
  rcases lt_or_ge μ ggGam with h' | h'
  · exact tfLt_of_vt_lt hτ hτ1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).2 hξ hξ2 hμT hη
      hηΩ hdξ hηξ h
  · exact hC.lt_of hτ hτ1 h' hμM hξ hξ2 hμT hη hηΩ hdξ hηξ h

/-- **The data and `η` lie below `ϑᵗ(Δ_μ + η)`** at every level `E₁ ≤ μ < M`. -/
theorem tic_level {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμM : μ < M)
    (hμT : tfDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    tfDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  rcases lt_or_ge μ ggGam with h' | h'
  · exact tfLevel_lt hτ hτ1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).1 (ti_lev_lt (h'.trans tf_gg_lt_BG)).2 hμT hη hηΩ
  · exact hC.level hτ hτ1 h' hμM hμT hη hηΩ

end API

end Googology.Trans.PoR.InaccPsi.R2.Ti
