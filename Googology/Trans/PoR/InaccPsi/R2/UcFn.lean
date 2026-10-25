import Googology.Trans.PoR.InaccPsi.R2.UcCl
import Googology.Trans.PoR.InaccPsi.R2.TlFn

/-!
# The levels `Φ_μ` on the data `ucDatL`, for every `μ < B₂`, and the [W07a] packages at `B₂`

`ucDatL μ = Uc.ucDat (Ω₁ + μ)` (**the data of the level `μ`**, `R2.UcCl`), `X = Tl.tlX`, `B₂ = Uc.ucB`,
`Φ_μ = Tl.tlP μ` below `X` (data `Tl.tlDatL`).  The same definition on `ucDatL` (the generic hierarchy `Uc.ucG`):

* `ucP μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > ucDatL μ` that are fixed points of
  every `ucP j`, `j < μ`, with `ucDatL j < v`), `ucP_normal`, `ucP_SC`, `ucDatL_lt_ucP`, `ucP_fix_lower`, `ucP_range`,
  `ucP_fix_mono`, `ucP_lt_iff`, `ucP_le_iff`, `ucP_le_self`, `ucDatL_lt_X`, `ucP_eq_tlP` (**`ucP μ = Tl.tlP μ` for every
  `μ < X`**: the new hierarchy extends the old one);
* `UcCit M` (**the five [W07a] Lemma 3.30 facts at every level `Γ_{Ω₁+1} ≤ μ < M`** with the data `ucDat`: the fields
  of `Tl.TlCit`), `ucCit_mono`, `ucCit` (**`UcCit B₂` holds**, from `R2.CitedUc`), `tlCit_of_uc` (**`UcCit M` gives
  `Tl.TlCit (min M X)`**);
* `UcCitPi M` (**[W07a] Def 5.1 on the codes `[Γ_{Ω₁+1}, M)`**: every atom below `M` (`F_λ(y)` below `X`, `H_λ(y)`
  from `X` on), the `ε`-numbers `φ(a, c)`, the powers `ω^g`), `ucCitPi` (**`UcCitPi B₂` holds**), `ucCitPi_H` (**an
  atom `H_γ(y) ∈ [X, M)` in normal form: `H_γ(y) ∈ Tᵗ[σ] ↔ comps(γ), y ⊆ Tᵗ[σ]`, `π(H_γ(y)) = H_{ucMap π γ}(π y)`**),
  `tlCitPi_of_uc` (**`UcCitPi M` gives `Tl.TlCitPi (min M X)`**).

No new axiom.  New definitions: `ucP`, the packages `UcCit`, `UcCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Gg

/-! ## The levels -/

/-- **The `μ`-th level** on the data `ucDatL`. -/
noncomputable def ucP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ucG ucDatL 0 μ

theorem ucP_normal (μ : Ordinal.{0}) : Order.IsNormal (ucP μ) := ucG_normal μ

theorem ucP_SC (μ o : Ordinal.{0}) : SC (ucP μ o) := ucG_SC μ o

theorem ucDatL_lt_ucP (μ o : Ordinal.{0}) : ucDatL μ < ucP μ o := ucG_d_lt μ o

theorem ucP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ucP μ a < ucP μ b ↔ a < b := ucG_lt_iff μ

theorem ucP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ucP μ a ≤ ucP μ b ↔ a ≤ b := ucG_le_iff μ

theorem ucP_le_self (μ o : Ordinal.{0}) : o ≤ ucP μ o := ucG_le_self μ o

theorem ucP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (ucP μ)) (hj : ucDatL j < v) :
    ucP j v = v := ucG_fix_lower h hv hj

theorem ucP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : ucDatL μ < v)
    (hfix : ∀ j < μ, ucDatL j < v → ucP j v = v) : ∃ e, ucP μ e = v :=
  ucG_range hSC hSC.1 hμ hfix

theorem ucP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : ucP μ x = x) (hj : ucDatL j < x) : ucP j x = x :=
  ucG_fix_mono h hx hj

theorem ucDatL_lt_X {μ : Ordinal.{0}} (hμ : μ < tlX) : ucDatL μ = tlDatL μ := by
  unfold ucDatL tlDatL
  exact ucDat_lt_X (tl_X_indec.add_lt tlX_gt hμ)

/-- **`ucP μ = Tl.tlP μ` for every `μ < X`.** -/
theorem ucP_eq_tlP : ∀ μ : Ordinal.{0}, μ < tlX → ucP μ = tlP μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  unfold ucP
  rw [ucG_eq, tlP_eq]
  congr 1
  ext v
  simp only [ucGC, tlC, mem_setOf_eq]
  rw [ucDatL_lt_X hμ]
  constructor
  · rintro ⟨h1, -, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    have := h3 j hj (by rw [ucDatL_lt_X (hj.trans hμ)]; exact hd)
    rw [← IH j hj (hj.trans hμ)]; exact this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h1.1, h2, fun j hj hd => ?_⟩
    have := h3 j hj (by rw [← ucDatL_lt_X (hj.trans hμ)]; exact hd)
    have e := IH j hj (hj.trans hμ)
    unfold ucP at e
    rw [e]; exact this

/-! ## The packages at `B₂` -/

theorem uc_lev_lt {μ : Ordinal.{0}} (hμ : μ < ucB) : Om1 ≤ Om1 + μ ∧ Om1 + μ < ucB :=
  ⟨le_self_add, uc_B_indec.add_lt ucB_gt hμ⟩

/-- **The [W07a] facts at the levels `Γ_{Ω₁+1} ≤ μ < M`** with the data `ucDat`: the fields of `Tl.TlCit`. -/
structure UcCit (M : Ordinal.{0}) : Prop where
  /-- data in `Tᵗ` ⇒ argument in `Tᵗ` -/
  mem : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ucDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → Om1 * (Om1 + μ) + η ∈ Tset τ
  /-- argument in `Tᵗ` ⇒ data in `Tᵗ` -/
  dat : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → η < Om1 →
    Om1 * (Om1 + μ) + η ∈ Tset τ → ucDatL μ ∈ Tset τ
  /-- Lemma 3.30, `⇐`, against a lower argument `Ω₁·M' + η'` -/
  vt_lt : ∀ {τ M' η' μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → M' ≤ Om1 + μ →
    ucDat M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → ucDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * (Om1 + μ) + η → ucDat M' < vt τ (Om1 * (Om1 + μ) + η) →
    η' < vt τ (Om1 * (Om1 + μ) + η) → vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)
  /-- Lemma 3.30, `⇒` -/
  lt_of : ∀ {τ ξ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ξ ∈ Tset τ → ξ < OmTwo →
    ucDatL μ ∈ Tset τ → η ∈ Tset τ → η < Om1 → ucDatL μ < vt τ ξ → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) → ξ < Om1 * (Om1 + μ) + η
  /-- the data and `η` lie below the value -/
  level : ∀ {τ μ η : Ordinal.{0}}, InE τ → τ < Om1 → ggGam ≤ μ → μ < M → ucDatL μ ∈ Tset τ → η ∈ Tset τ →
    η < Om1 → ucDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

theorem ucCit_mono {M N : Ordinal.{0}} (h : UcCit N) (hMN : M ≤ N) : UcCit M where
  mem a b c d := h.mem a b c (d.trans_le hMN)
  dat a b c d := h.dat a b c (d.trans_le hMN)
  vt_lt a b c d := h.vt_lt a b c (d.trans_le hMN)
  lt_of a b c d := h.lt_of a b c (d.trans_le hMN)
  level a b c d := h.level a b c (d.trans_le hMN)

/-- **`UcCit B₂`**: the five facts at every level `Γ_{Ω₁+1} ≤ μ < B₂`, from `R2.CitedUc` (`M = Ω₁ + μ`). -/
theorem ucCit : UcCit ucB where
  mem h1 h2 _ h4 h5 h6 h7 := ucArg_mem h1 h2 (uc_lev_lt h4).1 (uc_lev_lt h4).2 h5 h6 h7
  dat h1 h2 _ h4 h5 h6 := ucArg_dat h1 h2 (uc_lev_lt h4).1 (uc_lev_lt h4).2 h5 h6
  vt_lt h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    ucVt_lt h1 h2 (uc_lev_lt h4).1 (uc_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 _ h4 h5 h6 h7 h8 h9 h10 h11 h12 :=
    ucLt_of_vt_lt h1 h2 (uc_lev_lt h4).1 (uc_lev_lt h4).2 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 _ h4 h5 h6 h7 := ucLevel_lt h1 h2 (uc_lev_lt h4).1 (uc_lev_lt h4).2 h5 h6 h7

/-- **`UcCit M` gives `Tl.TlCit (min M X)`**: below `X` the data agree. -/
theorem tlCit_of_uc {M : Ordinal.{0}} (h : UcCit M) : TlCit (min M tlX) where
  mem h1 h2 h3 h4 h5 h6 h7 := by
    have hX := (lt_min_iff.1 h4).2
    exact h.mem h1 h2 h3 (lt_min_iff.1 h4).1 (by rwa [ucDatL_lt_X hX]) h6 h7
  dat h1 h2 h3 h4 h5 h6 := by
    have hX := (lt_min_iff.1 h4).2
    rw [← ucDatL_lt_X hX]; exact h.dat h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6
  vt_lt {τ M' η' μ η} h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 := by
    have hX := (lt_min_iff.1 h4).2
    have hM'X : M' < tlX := h5.trans_lt (tl_X_indec.add_lt tlX_gt hX)
    rw [← ucDat_lt_X hM'X] at h6 h13
    rw [← ucDatL_lt_X hX] at h9
    exact h.vt_lt h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 := by
    have hX := (lt_min_iff.1 h4).2
    rw [← ucDatL_lt_X hX] at h7 h10
    exact h.lt_of h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 h3 h4 h5 h6 h7 := by
    have hX := (lt_min_iff.1 h4).2
    rw [← ucDatL_lt_X hX] at h5 ⊢
    exact h.level h1 h2 h3 (lt_min_iff.1 h4).1 h5 h6 h7

/-- **The base-change facts on the codes `[Γ_{Ω₁+1}, M)`** ([W07a] Def 5.1): every atom below `M` (its parts, and the
atom rebuilt from their images), the `ε`-numbers `φ(a, c)`, the powers `ω^g`. -/
structure UcCitPi (M : Ordinal.{0}) : Prop where
  /-- an atom (strongly critical) `z ∈ (Ω₁, M)` -/
  atom : ∀ {σ τ z : Ordinal.{0}}, Bases σ τ → SC z → Om1 < z → z < M →
    (z ∈ TB τ σ ↔ ∀ x ∈ ucParts z, x ∈ TB τ σ) ∧
      ((∀ x ∈ ucParts z, x ∈ TB τ σ) → pi σ τ z = ucRebuild (pi σ τ) z)
  /-- an `ε`-number `φ(a, c)` in normal form -/
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → ggGam < veblen a c →
    veblen a c < M → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  /-- a power `ω^g`, `g ≥ E₁` not an `ε`-number -/
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → ggE ≤ g → ω ^ g ≠ g → ggGam < ω ^ g → ω ^ g < M →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- **`UcCitPi B₂`**, from `R2.CitedUc`. -/
theorem ucCitPi : UcCitPi ucB where
  atom h hSC h1 hB := ucAtom_TB h hSC h1 hB
  eps h h1 h2 h3 h4 h5 := ucPhi_TB h h1 h2 h3 (Ss.ss_Om1_lt_Gam.trans h4) h5
  opow h h1 h2 _ h4 := ucOpow_TB h h1 h2 h4

/-- **An atom `H_γ(y) ∈ [X, M)` in normal form**: `H_γ(y) ∈ Tᵗ[σ] ↔` every component of `γ` and `y` are, and then
`π(H_γ(y)) = H_{ucMap π γ}(π y)`. -/
theorem ucCitPi_H {M : Ordinal.{0}} (h : UcCitPi M) {σ τ γ y : Ordinal.{0}} (hB : Bases σ τ) (hγ : γ < ucE)
    (hy : y < ucH γ y) (hX : tlX ≤ ucH γ y) (hM : ucH γ y < M) :
    (ucH γ y ∈ TB τ σ ↔ (∀ x ∈ ucComps γ, x ∈ TB τ σ) ∧ y ∈ TB τ σ) ∧
      ((∀ x ∈ ucComps γ, x ∈ TB τ σ) → y ∈ TB τ σ → pi σ τ (ucH γ y) = ucH (ucMap (pi σ τ) γ) (pi σ τ y)) := by
  obtain ⟨hA, hP⟩ := h.atom hB (ucH_SC γ y) (ucH_gt γ y) hM
  rw [ucParts_H hγ hy hX] at hA hP
  rw [ucRebuild_H _ hγ hy hX] at hP
  have hiff : (∀ x ∈ ucComps γ ∪ {y}, x ∈ TB τ σ) ↔ (∀ x ∈ ucComps γ, x ∈ TB τ σ) ∧ y ∈ TB τ σ := by
    constructor
    · intro H; exact ⟨fun x hx => H x (Or.inl hx), H y (Or.inr rfl)⟩
    · rintro ⟨hc, hy'⟩ x hx
      rcases hx with hx | hx
      · exact hc x hx
      · rw [mem_singleton_iff] at hx; rw [hx]; exact hy'
  exact ⟨hA.trans hiff, fun hc hy' => hP (hiff.2 ⟨hc, hy'⟩)⟩

/-- **`UcCitPi M` gives `Tl.TlCitPi (min M X)`**: an atom `F_β(y) < X` has the parts `β, y`. -/
theorem tlCitPi_of_uc {M : Ordinal.{0}} (h : UcCitPi M) : TlCitPi (min M tlX) where
  atom {σ τ β y} hB h1 hM hy := by
    have hX := (lt_min_iff.1 hM).2
    obtain ⟨hA, hP⟩ := h.atom hB (rhF_SC β y) h1 (lt_min_iff.1 hM).1
    rw [ucParts_F hX hy] at hA hP
    rw [ucRebuild_F _ hX hy] at hP
    have hiff : (∀ x ∈ ({β, y} : Set Ordinal.{0}), x ∈ TB τ σ) ↔ β ∈ TB τ σ ∧ y ∈ TB τ σ := by
      constructor
      · intro H; exact ⟨H β (mem_insert _ _), H y (mem_insert_of_mem _ rfl)⟩
      · rintro ⟨hb, hy'⟩ x hx
        rcases hx with rfl | hx
        · exact hb
        · rw [mem_singleton_iff] at hx; rw [hx]; exact hy'
    exact ⟨hA.trans hiff, fun hb hy' => hP (hiff.2 ⟨hb, hy'⟩)⟩
  eps h1 h2 h3 h4 h5 h6 := h.eps h1 h2 h3 h4 h5 (lt_min_iff.1 h6).1
  opow h1 h2 h3 h4 h5 := h.opow h1 h2 h3 h4 (lt_min_iff.1 h5).1

end Googology.Trans.PoR.InaccPsi.R2.Uc
