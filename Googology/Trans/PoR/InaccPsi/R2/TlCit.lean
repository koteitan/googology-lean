import Googology.Trans.PoR.InaccPsi.R2.CitedTl
import Googology.Trans.PoR.InaccPsi.R2.TiPi

/-!
# The [W07a] facts at the levels `[Γ_{Ω₁+1}, M)` with the data `Tl.tlDat`, discharged at `M = X` by `R2.CitedTl`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ω₁ = Om1`, `Tᵗ = Tset τ`, `ϑᵗ = vt τ`, `Γ_{Ω₁+1} = Gg.ggGam`, `B_Γ = Tf.tfBG`, `X = Tl.tlX` (the least fixed point of
`β ↦ F_β(0)` above `Ω₁`, `F_β = Rh.rhF β`), `Δ_μ = Ω₁·(Ω₁ + μ)`, `tlDatL μ = tlDat(Ω₁ + μ)` (`R2.TlDat`).
`Ti.TiCit` / `Ti.TiCitPi` carry the data `Tf.tfDat`, which is the junk value `0` from `B_Γ` on; the packages below carry
`Tl.tlDat`, correct below `X`:

* `tlDatL`, `tlDatL_eq_tf` (`tlDatL μ = Tf.tfDatL μ` for `μ < B_Γ`), `tl_X_indec`, `tl_X_inE`, `tl_lev_lt`,
  `tl_arg_lt` (`Δ_μ + η < X` for `μ < X`);
* `TlCit M` (**the five facts at every level `Γ_{Ω₁+1} ≤ μ < M`**: the fields of `Ti.TiCit` with `tlDat`), `tlCit_mono`,
  `tlCit` (**`TlCit X` holds**, from `R2.CitedTl`), `tiCit_of_tl` (**`TlCit M` gives `Ti.TiCit (min M B_Γ)`**: the new
  package extends the old one);
* `TlCitPi M` (**[W07a] Def 5.1 on the codes `[Γ_{Ω₁+1}, M)`**: `atom` (every atom `F_β(y) < M` in normal form:
  `F_β(y) ∈ Tᵗ[σ] ↔ β, y ∈ Tᵗ[σ]`, `π(F_β(y)) = F_{πβ}(πy)`), `eps`, `opow`), `tlCitPi` (**`TlCitPi X` holds**),
  `tiCitPi_of_tl` (**`TlCitPi M` gives `Ti.TiCitPi M`** for `M ≤ B_Γ`: the atoms `Γ_ν` are the case `β = 0`).

No new axiom.  New definitions: `tlDatL`, the packages `TlCit`, `TlCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The data of the level `μ`**: `tlDat (Ω₁ + μ)`. -/
noncomputable def tlDatL (μ : Ordinal.{0}) : Ordinal.{0} := tlDat (Om1 + μ)

theorem tl_X_indec : Indec (tlX : Ordinal.{0}) := Lq.lq_SC_indec tlX_SC

theorem tl_X_inE : InE (tlX : Ordinal.{0}) := Low.opow_eq_self_of_SC tlX_SC

/-- `Ω₁ ≤ Ω₁ + μ < X` for `μ < X`. -/
theorem tl_lev_lt {μ : Ordinal.{0}} (hμ : μ < tlX) : Om1 ≤ Om1 + μ ∧ Om1 + μ < tlX :=
  ⟨le_self_add, tl_X_indec.add_lt tlX_gt hμ⟩

/-- **`Δ_μ + η < X`** for `μ < X`, `η < Ω₁`. -/
theorem tl_arg_lt {μ η : Ordinal.{0}} (hμ : μ < tlX) (hη : η < Om1) : Om1 * (Om1 + μ) + η < tlX :=
  tl_X_indec.add_lt (tl_X_inE.mul_lt tlX_gt (tl_X_indec.add_lt tlX_gt hμ)) (hη.trans tlX_gt)

/-- `tlDatL μ = Tf.tfDatL μ` for `μ < B_Γ`. -/
theorem tlDatL_eq_tf {μ : Ordinal.{0}} (hμ : μ < tfBG) : tlDatL μ = tfDatL μ := by
  unfold tlDatL tfDatL
  exact tlDat_eq_tf _ (tf_BG_indec.add_lt tfBG_gt hμ)

/-- **The [W07a] facts at the levels `Γ_{Ω₁+1} ≤ μ < M`** with the data `tlDat` (Def 3.22, Lemma 3.30, Def 3.28 at the
arguments `Δ_μ + η`): a hypothesis package, the fields of `Ti.TiCit`. -/
structure TlCit (M : Ordinal.{0}) : Prop where
  /-- data in `Tᵗ` ⇒ argument in `Tᵗ` -/
  mem : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tlDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → Om1 * (Om1 + μ) + η ∈ Tset τ
  /-- argument in `Tᵗ` ⇒ data in `Tᵗ` -/
  dat : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → η < Om1 →
    Om1 * (Om1 + μ) + η ∈ Tset τ → tlDatL μ ∈ Tset τ
  /-- Lemma 3.30, `⇐`, against a lower argument `Ω₁·M' + η'` -/
  vt_lt : ∀ {τ M' η' μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → M' ≤ Om1 + μ →
    tlDat M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → tlDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * (Om1 + μ) + η → tlDat M' < vt τ (Om1 * (Om1 + μ) + η) →
    η' < vt τ (Om1 * (Om1 + μ) + η) → vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)
  /-- Lemma 3.30, `⇒` -/
  lt_of : ∀ {τ ξ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ξ ∈ Tset τ → ξ < OmTwo →
    tlDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 → tlDatL μ < vt τ ξ → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) → ξ < Om1 * (Om1 + μ) + η
  /-- the data and `η` lie below the value -/
  level : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → tlDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → tlDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

/-- `TlCit` is antitone in the bound. -/
theorem tlCit_mono {M N : Ordinal.{0}} (h : TlCit N) (hMN : M ≤ N) : TlCit M where
  mem a b c d := h.mem a b c (d.trans_le hMN)
  dat a b c d := h.dat a b c (d.trans_le hMN)
  vt_lt a b c d := h.vt_lt a b c (d.trans_le hMN)
  lt_of a b c d := h.lt_of a b c (d.trans_le hMN)
  level a b c d := h.level a b c (d.trans_le hMN)

/-- **`TlCit X`**: the five facts at every level `Γ_{Ω₁+1} ≤ μ < X`, from `R2.CitedTl` (`M = Ω₁ + μ`). -/
theorem tlCit : TlCit tlX where
  mem h1 h2 _ h4 h5 h6 h7 := tlArg_mem h1 h2 (tl_lev_lt h4).1 (tl_lev_lt h4).2 h5 h6 h7
  dat h1 h2 _ h4 h5 h6 := tlArg_dat h1 h2 (tl_lev_lt h4).1 (tl_lev_lt h4).2 h5 h6
  vt_lt h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    tlVt_lt h1 h2 (tl_lev_lt h4).1 (tl_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 :=
    tlLt_of_vt_lt h1 h2 (tl_lev_lt h4).1 (tl_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 _ h4 h5 h6 h7 := tlLevel_lt h1 h2 (tl_lev_lt h4).1 (tl_lev_lt h4).2 h5 h6 h7

/-- **`TlCit M` gives `Ti.TiCit (min M B_Γ)`**: below `B_Γ` the data agree (`tlDat_eq_tf`). -/
theorem tiCit_of_tl {M : Ordinal.{0}} (h : TlCit M) : Ti.TiCit (min M tfBG) where
  mem h1 h2 h3 h4 h5 h6 h7 := by
    have hB := (lt_min_iff.1 h4).2
    exact h.mem h1 h2 h3 (lt_min_iff.1 h4).1 (by rwa [tlDatL_eq_tf hB]) h6 h7
  dat h1 h2 h3 h4 h5 h6 := by
    have hB := (lt_min_iff.1 h4).2
    rw [← tlDatL_eq_tf hB]; exact h.dat h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6
  vt_lt {τ M' η' μ η} h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 := by
    have hB := (lt_min_iff.1 h4).2
    have hM'B : M' < tfBG := h5.trans_lt (tf_BG_indec.add_lt tfBG_gt hB)
    rw [← tlDat_eq_tf M' hM'B] at h6 h13
    rw [← tlDatL_eq_tf hB] at h9
    exact h.vt_lt h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 := by
    have hB := (lt_min_iff.1 h4).2
    rw [← tlDatL_eq_tf hB] at h7 h10
    exact h.lt_of h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 h3 h4 h5 h6 h7 := by
    have hB := (lt_min_iff.1 h4).2
    rw [← tlDatL_eq_tf hB] at h5 ⊢
    exact h.level h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7

/-- **The base-change facts on the codes `[Γ_{Ω₁+1}, M)`** ([W07a] Def 5.1): a hypothesis package (every atom
`F_β(y)` in normal form below `M`, the `ε`-numbers `φ(a, c)` and the powers `ω^g`). -/
structure TlCitPi (M : Ordinal.{0}) : Prop where
  /-- an atom `F_β(y)`, `y < F_β(y)` -/
  atom : ∀ {σ τ β y : Ordinal.{0}}, Bases σ τ → Om1 < rhF β y → rhF β y < M → y < rhF β y →
    (rhF β y ∈ TB τ σ ↔ β ∈ TB τ σ ∧ y ∈ TB τ σ) ∧
      (β ∈ TB τ σ → y ∈ TB τ σ → pi σ τ (rhF β y) = rhF (pi σ τ β) (pi σ τ y))
  /-- an `ε`-number `φ(a, c)` in normal form -/
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → ggGam < veblen a c →
    veblen a c < M → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  /-- a power `ω^g`, `g ≥ E₁` not an `ε`-number -/
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → ggE ≤ g → ω ^ g ≠ g → ggGam < ω ^ g → ω ^ g < M →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- **`TlCitPi X`**, from `R2.CitedTl` (`tlAtom_TB`, `tlPhi_TB`, `tlOpow_TB`). -/
theorem tlCitPi : TlCitPi tlX where
  atom h h1 hX hy := tlAtom_TB h h1 hX hy
  eps h h1 h2 h3 h4 h5 := tlPhi_TB h h1 h2 h3 (Ss.ss_Om1_lt_Gam.trans h4) h5
  opow h h1 h2 _ h4 := tlOpow_TB h h1 h2 h4

/-- **`TlCitPi M` gives `Ti.TiCitPi M`** for `M ≤ B_Γ`: an atom `Γ_ν < M` is `F₀(ν)` with `ν < Γ_ν`
(`Tf.tf_idx_lt`). -/
theorem tiCitPi_of_tl {M : Ordinal.{0}} (h : TlCitPi M) (hM : M ≤ tfBG) : Ti.TiCitPi M where
  gam {σ τ ν} hB h1 hνM := by
    have hz1 : Om1 < gamma ν := tf_Om1_lt_gamma.2 h1
    have hν : ν < gamma ν := tf_idx_lt hz1 (hνM.trans_le hM)
    have hσ0 : (0 : Ordinal.{0}) < σ := zero_lt_one.trans (tf_one_lt hB.1)
    have h0 : (0 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt hB (hσ0.trans hB.2.2.1)).2 hσ0
    have hp0 : pi σ τ 0 = 0 := pi_lt hB hσ0
    obtain ⟨hA, hP⟩ := h.atom (β := 0) (y := ν) hB (by rw [rhF_zero]; exact hz1)
      (by rw [rhF_zero]; exact hνM) (by rw [rhF_zero]; exact hν)
    rw [rhF_zero] at hA hP
    refine ⟨⟨fun hg => (hA.1 hg).2, fun hν' => hA.2 ⟨h0, hν'⟩⟩, fun hν' => ?_⟩
    rw [hP h0 hν', hp0, rhF_zero]
  eps h1 h2 h3 h4 h5 h6 := h.eps h1 h2 h3 h4 h5 h6
  opow h1 h2 h3 h4 h5 := h.opow h1 h2 h3 h4 h5

end Googology.Trans.PoR.InaccPsi.R2.Tl
