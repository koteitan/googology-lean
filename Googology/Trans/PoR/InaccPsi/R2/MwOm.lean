import Googology.Trans.PoR.InaccPsi.R2.MwAlev
import Googology.Trans.PoR.InaccPsi.R2.LtP

/-!
# `SfLhTMove` at the level `ω`: the ε-numbers of `P_ω` up to `ϑ^{υ_ξ}(Ω₁·(ω+1))`

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `τ = υ_ξ` (strongly critical, countable), `ϑᵗ = vt τ`, `lhᵗ = lhT τ`, `φ_ω = veblen ω`,
`ind = mwIx ω τ` (`R2.MwAlev`), `P(τ) = ltP τ = ϑᵗ(Ω₁·(ω+1))` (`R2.LtP`), `V(τ) = φ_{ω+1}(τ + 1)`.  The cited values
used are the repo axioms `CitedVz.vzLhT_w` (`lhᵗ(ϑᵗ(Ω₁·ω)) = ϑᵗ(Ω₁·ω)·ω`), `CitedLt.ltLhT_w_lim`
(`lhᵗ(ϑᵗ(Ω₁·ω + η)) = ϑᵗ(Ω₁·ω + η)·ω + logend(η)` in the limit case), `CitedLt.ltLhT_w1`
(`lhᵗ(P(τ)) = P(τ)·ω + P(τ)`), with `CitedLz.lzVt_lt_ww`, `CitedLt.ltLt_vt_self_w`, `CitedLt.ltVt_lt_w1`.

* `mwV_least` (**`V(τ)` is the least fixed point of `φ_ω` above `τ`**), `mwOm_nfix` (no fixed point in `(τ, P(τ))`);
* `mwOmLev` (**THE LEVEL LEMMA at `ω`**): for `τ < β < P(τ)` with `ind(β) ∈ Tᵗ ∩ Ω₁`,
  `φ_ω(β) = ϑᵗ(Ω₁·ω + ind(β))` (as `Ph.phLev`, with `Lt.lt_w_min`, `Lt.lt_w_omega`);
* `mwLtP_fix`, `mwLtP_eq` (**`P(τ) = V(τ)`**: `P(τ)` is a fixed point of `φ_ω`);
* `mwFixW_zero` (the fixed case of [W07a] Def 4.11 below `P(τ)` is `η = 0` only), `mwLhT_om0`, `mwLhT_omlim`;
* `mwB_V` (**`B_n(V(τ)) = V(B_n τ)`**), `mwB_mul_omega` (`B_n(x·ω) = B_n x·ω` for an ε-number `x`);
* `mwLhT_w` (**`SfLhTMove` at every ε-number `x ∈ P_ω` with `υ_ξ < x ≤ P(υ_ξ)`**);
* `MwLhTopW S` (a hypothesis name): `SfLhTMove` at the ε-numbers `x ∈ P_ω` with `x > P(υ_ξ)`;
  `mwLhTop_of_W`: `MwLhTopW` gives `MwLhTop`; `mwRoad_w`: the road with `MwLhTopW` and `L(ω+1) ≤ ν_C → MwEQtop`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Lt

variable {S : InaccSeq.{0}}

theorem mw_omega_lt_SC {τ : Ordinal.{0}} (hτ : SC τ) : (ω : Ordinal.{0}) < τ := Lw.lw_omega_lt_SC hτ

theorem mw_omega1_lt_SC {τ : Ordinal.{0}} (hτ : SC τ) : (ω : Ordinal.{0}) + 1 < τ :=
  hτ.isPrincipal (mw_omega_lt_SC hτ) (one_lt_omega0.trans (mw_omega_lt_SC hτ))

/-- **`V(τ) = φ_{ω+1}(τ+1)` is the least fixed point of `φ_ω` above `τ`.** -/
theorem mwV_least {τ : Ordinal.{0}} (hτ : SC τ) :
    veblen ω (veblen (ω + 1) (τ + 1)) = veblen (ω + 1) (τ + 1) ∧ τ < veblen (ω + 1) (τ + 1) ∧
      ∀ u, veblen ω u = u → τ < u → veblen (ω + 1) (τ + 1) ≤ u := by
  refine ⟨veblen_veblen_of_lt (lt_add_one ω) _,
    (lt_add_one τ).trans_le (right_le_veblen _ _), fun u hu hτu => ?_⟩
  have hr : u ∈ Set.range (veblen (ω + 1)) := by
    refine (mem_range_veblen ((zero_le).trans_lt (lt_add_one ω)).ne').2 fun b hb => ?_
    exact veblen_eq_self_of_le (Order.lt_add_one_iff.1 hb) hu
  obtain ⟨j, rfl⟩ := hr
  have hτf : veblen (ω + 1) τ = τ := hτ.veblen_right (mw_omega1_lt_SC hτ)
  have hτj : τ < j := by
    rw [← hτf] at hτu; exact veblen_lt_veblen_iff_right.1 hτu
  exact veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt hτj)

theorem mwLtP_le_V {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) : ltP τ ≤ veblen (ω + 1) (τ + 1) :=
  ltP_le_fix (Gg.gg_SC_eps hτ) hτ1 (mwV_least hτ).1 (mwV_least hτ).2.1

/-- No fixed point of `φ_ω` in `(τ, P(τ))`. -/
theorem mwOm_nfix {τ y : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτy : τ < y) (hy : y < ltP τ) :
    veblen ω y ≠ y := fun h =>
  absurd ((mwV_least hτ).2.2 y h hτy) (not_le.2 (hy.trans_le (mwLtP_le_V hτ hτ1)))

theorem mwTh_w_lt {τ σ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (h : σ < η) : vt τ (Om1 * ω + σ) < vt τ (Om1 * ω + η) :=
  lzVt_lt_ww hτ hτ1 hσ hη hη1 h (h.trans (ltLt_vt_self_w hτ hτ1 hη hη1))

theorem mwTh_w_le {τ σ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (h : σ ≤ η) : vt τ (Om1 * ω + σ) ≤ vt τ (Om1 * ω + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (mwTh_w_lt hτ hτ1 hσ hη hη1 h).le
  · exact le_rfl

/-- `ϑᵗ(Ω₁·ω + η) < P(τ)` for `η < P(τ)`. -/
theorem mwTh_w_ltP {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hηP : η < ltP τ) : vt τ (Om1 * ω + η) < ltP τ := by
  rw [ltP_eq hτ hτ1] at hηP ⊢; exact ltVt_lt_w1 hτ hτ1 hη hη1 hηP

/-- **THE LEVEL LEMMA at `ω`**: `φ_ω(β) = ϑᵗ(Ω₁·ω + ind(β))` for `τ < β < P(τ)`. -/
theorem mwOmLev {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) :
    ∀ β, τ < β → β < ltP τ → mwIx ω τ β ∈ Tset τ → mwIx ω τ β < Om1 →
      veblen ω β = vt τ (Om1 * ω + mwIx ω τ β) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hτβ hβP hT h1
  have hβn : veblen ω β ≠ β := mwOm_nfix hτ hτ1 hτβ hβP
  have hβv : β < veblen ω β := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hβn)
  have hηP : mwIx ω τ β < ltP τ := (mwIx_le _ _ _).trans_lt hβP
  obtain ⟨-, hτv, -, -, -⟩ := lt_w_facts hτE hτ1 hT h1
  have hvP := mwTh_w_ltP hτE hτ1 hT h1 hηP
  apply le_antisymm
  · obtain ⟨β', hβ'⟩ := lt_w_omega hτE hτ1 hT h1
    have hτf : veblen ω τ = τ := hτ.veblen_right (mw_omega_lt_SC hτ)
    have hτβ' : τ < β' := by
      by_contra hle
      push Not at hle
      have h2 := (veblen_le_veblen_iff_right (o := ω)).2 hle
      rw [hτf, hβ'] at h2
      exact absurd hτv (not_lt.2 h2)
    have hβ'n : veblen ω β' ≠ β' := by
      intro hf
      have : vt τ (Om1 * ω + mwIx ω τ β) = β' := by rw [← hβ', hf]
      exact mwOm_nfix hτ hτ1 hτv hvP (by rw [this]; exact hf)
    rcases lt_or_ge β' β with hlt | hge
    · exfalso
      have hmem : β' ∈ mwC ω τ := mem_mwC.2 ⟨hτβ', hβ'n⟩
      have hlt' : mwIx ω τ β' < mwIx ω τ β := Cd.cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hτE hτ1 hT h1 hlt'.le
      have e := IH β' hlt hτβ' (hlt.trans hβP) hT' (hlt'.trans h1)
      have h3 := mwTh_w_lt hτE hτ1 hT' hT h1 hlt'
      rw [← e, hβ'] at h3
      exact lt_irrefl _ h3
    · rw [← hβ']; exact veblen_le_veblen_iff_right.2 hge
  · refine lt_w_min hτE hτ1 hT h1 ⟨β, rfl⟩ (hτβ.trans_le (right_le_veblen _ _))
      ((mwIx_le _ _ _).trans_lt hβv) fun σ hσ => ?_
    obtain ⟨β', hβ'C, hβ'β, hσe⟩ := Gg.ggOtp_onto (mwC ω τ) β σ hσ
    obtain ⟨hτβ', -⟩ := mem_mwC.1 hβ'C
    have hσe' : mwIx ω τ β' = σ := hσe
    have hT' : mwIx ω τ β' ∈ Tset τ := by rw [hσe']; exact vz_T_down hτE hτ1 hT h1 hσ.le
    rw [← hσe', ← IH β' hβ'β hτβ' (hβ'β.trans hβP) hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hβ'β

/-- **`P(τ)` is a fixed point of `φ_ω`.** -/
theorem mwLtP_fix {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) : veblen ω (ltP τ) = ltP τ := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hPE : InE (ltP τ) := vz_omega_E (ltP_omega hτE hτ1)
  have hτf : veblen ω τ = τ := hτ.veblen_right (mw_omega_lt_SC hτ)
  have hτP : τ < ltP τ := (ltC_facts hτE hτ1 0).2.2.1.trans_le (ltC_le_P τ 0)
  refine le_antisymm (((isNormal_veblen ω).le_iff_forall_le (ev_isSuccLimit_of_inE hPE)).2
    fun j hj => ?_) (right_le_veblen _ _)
  obtain ⟨K, hK⟩ := ltP_lt_iff.1 hj
  by_cases hjτ : j ≤ τ
  · calc veblen ω j ≤ veblen ω τ := veblen_le_veblen_iff_right.2 hjτ
      _ = τ := hτf
      _ ≤ ltP τ := hτP.le
  · obtain ⟨hcT, hc1, hτc, -⟩ := ltC_facts hτE hτ1 K
    have hcP : ltC τ K < ltP τ := ltC_lt_P hτE hτ1 K
    have hiT : mwIx ω τ (ltC τ K) ∈ Tset τ := vz_T_down hτE hτ1 hcT hc1 (mwIx_le _ _ _)
    have hi1 : mwIx ω τ (ltC τ K) < Om1 := (mwIx_le _ _ _).trans_lt hc1
    calc veblen ω j ≤ veblen ω (ltC τ K) := veblen_le_veblen_iff_right.2 hK.le
      _ = vt τ (Om1 * ω + mwIx ω τ (ltC τ K)) := mwOmLev hτ hτ1 _ hτc hcP hiT hi1
      _ ≤ vt τ (Om1 * ω + ltC τ K) := mwTh_w_le hτE hτ1 hiT hcT hc1 (mwIx_le _ _ _)
      _ = ltC τ (K + 1) := rfl
      _ ≤ ltP τ := ltC_le_P τ (K + 1)

/-- **`P(τ) = V(τ) = φ_{ω+1}(τ + 1)`.** -/
theorem mwLtP_eq {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) : ltP τ = veblen (ω + 1) (τ + 1) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hτP : τ < ltP τ := (ltC_facts hτE hτ1 0).2.2.1.trans_le (ltC_le_P τ 0)
  exact le_antisymm (mwLtP_le_V hτ hτ1) ((mwV_least hτ).2.2 _ (mwLtP_fix hτ hτ1) hτP)

/-- **Below `P(τ)` the fixed case of [W07a] Def 4.11 at the level `ω` is `η = 0` only.** -/
theorem mwFixW_zero {τ η : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hηP : η < ltP τ) (hfix : ∀ σ, σ < η → vt τ (Om1 * ω + σ) ≤ η) : η = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  by_contra h0
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := vz_T_down hτE hτ1 hη hη1 zero_le
  have hτη : τ < η :=
    (lt_w_facts hτE hτ1 h0T (lt_of_le_of_lt zero_le hη1)).2.1.trans_le (hfix 0 (pos_iff_ne_zero.2 h0))
  have hlim : IsSuccLimit η := by
    rcases zero_or_succ_or_isSuccLimit η with h | ⟨σ, hσ⟩ | h
    · exact absurd h h0
    · exfalso
      have hση : σ < η := hσ ▸ lt_succ σ
      have hσT := vz_T_down hτE hτ1 hη hη1 hση.le
      have hf := lt_w_facts hτE hτ1 hσT (hση.trans hη1)
      have heq : vt τ (Om1 * ω + σ) = η :=
        le_antisymm (hfix σ hση) (hσ ▸ Order.succ_le_of_lt (ltLt_vt_self_w hτE hτ1 hσT (hση.trans hη1)))
      have hvl : IsSuccLimit (vt τ (Om1 * ω + σ)) := ev_isSuccLimit_of_inE hf.2.2.2.1
      rw [heq, ← hσ] at hvl
      exact not_isSuccLimit_succ σ hvl
    · exact h
  have hall : ∀ β' < η, veblen ω β' ≤ η := by
    intro β' hβ'
    by_cases hτβ' : β' ≤ τ
    · calc veblen ω β' ≤ veblen ω τ := veblen_le_veblen_iff_right.2 hτβ'
        _ = τ := hτ.veblen_right (mw_omega_lt_SC hτ)
        _ ≤ η := hτη.le
    · push Not at hτβ'
      have hβ'P : β' < ltP τ := hβ'.trans hηP
      have hmem : β' ∈ mwC ω τ := mem_mwC.2 ⟨hτβ', mwOm_nfix hτ hτ1 hτβ' hβ'P⟩
      have hlt : mwIx ω τ β' < mwIx ω τ η := Cd.cdOtp_lt_of_mem hmem hβ'
      have hle : mwIx ω τ η ≤ η := mwIx_le _ _ _
      have hT' := vz_T_down hτE hτ1 hη hη1 (hlt.trans_le hle).le
      rw [mwOmLev hτ hτ1 β' hτβ' hβ'P hT' ((hlt.trans_le hle).trans hη1)]
      exact hfix _ (hlt.trans_le hle)
  have hv : veblen ω η ≤ η := ((isNormal_veblen _).le_iff_forall_le hlim).2 hall
  exact mwOm_nfix hτ hτ1 hτη hηP (le_antisymm hv (right_le_veblen _ _))

/-- **`lhᵗ(φ_ω(β)) = φ_ω(β)·ω`** when `ind(β) = 0`. -/
theorem mwLhT_om0 {τ β : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτβ : τ < β) (hβP : β < ltP τ)
    (h0 : mwIx ω τ β = 0) : lhT τ (veblen ω β) = veblen ω β * ω := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := vz_T_down hτE hτ1 (mem_T_of_le hτE hτ1 le_rfl) hτ1 zero_le
  rw [mwOmLev hτ hτ1 β hτβ hβP (h0 ▸ h0T) (h0 ▸ lt_of_le_of_lt zero_le hτ1), h0, add_zero]
  exact vzLhT_w hτE hτ1

/-- **`lhᵗ(φ_ω(β)) = φ_ω(β)·ω + logend(ind(β))`** when `ind(β) ≠ 0`. -/
theorem mwLhT_omlim {τ β : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτβ : τ < β) (hβP : β < ltP τ)
    (hT : mwIx ω τ β ∈ Tset τ) (h1 : mwIx ω τ β < Om1) (h0 : mwIx ω τ β ≠ 0) :
    lhT τ (veblen ω β) = veblen ω β * ω + lg (mwIx ω τ β) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hnf : ¬ ∀ σ, σ < mwIx ω τ β → vt τ (Om1 * ω + σ) ≤ mwIx ω τ β := fun h =>
    h0 (mwFixW_zero hτ hτ1 hT h1 ((mwIx_le _ _ _).trans_lt hβP) h)
  push Not at hnf
  rw [mwOmLev hτ hτ1 β hτβ hβP hT h1]
  exact ltLhT_w_lim hτE hτ1 hT h1 h0 (ltLt_vt_self_w hτE hτ1 hT h1) hnf

theorem mw_omega_L : (ω : Ordinal.{0}) < Nc.ncL S ω := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)

theorem mwB_omega (n : ℕ) : Bc.bcB S n (ω : Ordinal.{0}) = ω := Bc.bcB_fix (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))

/-- **`B_n(V(τ)) = V(B_n τ)`.** -/
theorem mwB_V {n : ℕ} {τ : Ordinal.{0}} (hτ : SC τ) (hVL : veblen (ω + 1) (τ + 1) < Nc.ncL S ω) :
    Bc.bcB S n (veblen (ω + 1) (τ + 1)) = veblen (ω + 1) (Bc.bcB S n τ + 1) := by
  have hτ1L : τ + 1 < Nc.ncL S ω := lt_of_le_of_lt (right_le_veblen _ _) hVL
  have hwL : (ω : Ordinal.{0}) + 1 < Nc.ncL S ω := (Lw.lw_L_SC S ω).isPrincipal mw_omega_L
    (one_lt_omega0.trans mw_omega_L)
  have h1 : (ω : Ordinal.{0}) + 1 < veblen (ω + 1) (τ + 1) :=
    (mw_omega1_lt_SC hτ).trans ((lt_add_one τ).trans_le (right_le_veblen _ _))
  have h2 : τ + 1 < veblen (ω + 1) (τ + 1) := by
    refine lt_of_le_of_ne (right_le_veblen _ _) fun e => mwFix_succ_not (a := ω) τ ?_
    have h3 : veblen ω (veblen (ω + 1) (τ + 1)) = veblen (ω + 1) (τ + 1) := veblen_veblen_of_lt (lt_add_one ω) _
    rw [← e] at h3
    exact h3
  obtain ⟨-, hB⟩ := mwB_phi (k := n) (mvD_of_lt hwL) (mvD_of_lt hτ1L) h1 h2
  rw [hB, mwB_succ (S := S) mw_omega_L, mwB_omega, mwB_succ ((lt_add_one τ).trans hτ1L)]

theorem mw_mul_omega_E {x : Ordinal.{0}} (hx : InE x) : x * ω = ω ^ (x + 1) := by
  rw [opow_add, opow_one]; unfold InE at hx; rw [hx]

/-- `B_n(x·ω) = B_n x·ω` for an ε-number `x` with `x·ω < L(ω)`. -/
theorem mwB_mul_omega {n : ℕ} {x : Ordinal.{0}} (hx : InE x) (hxL : x * ω < Nc.ncL S ω) :
    Bc.bcB S n (x * ω) = Bc.bcB S n x * ω := by
  have hx0 : x < Nc.ncL S ω := lt_of_le_of_lt (le_mul_left x omega0_pos) hxL
  have hBE : InE (Bc.bcB S n x) := by
    have h := Tp.tpOpowB (S := S) (n := n) (a := x) (by unfold InE at hx; rw [hx]; exact hx0)
    unfold InE at hx ⊢; rw [hx] at h; exact h.symm
  rw [mw_mul_omega_E hx, Tp.tpOpowB (by rw [← mw_mul_omega_E hx]; exact hxL), mwB_succ hx0,
    ← mw_mul_omega_E hBE]

/-- **`SfLhTMove` at every ε-number `x ∈ P_ω` with `υ_ξ < x ≤ P(υ_ξ)`.** -/
theorem mwLhT_w {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1)) (hall : ∀ m : ℕ, VzP (m + 1) x)
    (hxP : x ≤ ltP (upsilon ξ)) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hXSC : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := hτ1L.trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hτE : InE (upsilon ξ) := Gg.gg_SC_eps hτSC
  have hτ'E : InE (upsilon ξ') := Gg.gg_SC_eps hτ'SC
  have hxw : x * ω < Nc.ncL S ω := by
    rw [mw_mul_omega_E hE]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + 1)
      ((Lw.lw_L_SC S ω).isPrincipal hxL (one_lt_omega0.trans mw_omega_L))
    rwa [veblen_zero_apply] at this
  -- the bound `P(τ)` moves
  have hPV := mwLtP_eq hτSC hτ1
  have hPV' := mwLtP_eq hτ'SC hτ'1
  have hτfix : veblen ω (upsilon ξ) = upsilon ξ := hτSC.veblen_right (mw_omega_lt_SC hτSC)
  have hXfix : veblen ω (Bc.bcC S (n + 1)) = Bc.bcC S (n + 1) :=
    hXSC.veblen_right (mw_omega_lt_SC hXSC)
  have hτX : upsilon ξ < Bc.bcC S (n + 1) := hτx.trans hxX
  have hBlt : ∀ y, y < ltP (upsilon ξ) → Bc.bcB S n y < ltP (upsilon ξ') := by
    intro y hy
    have hyq : y < nfp (veblen ω) (upsilon ξ + 1) := by
      refine hy.trans_le ?_
      rw [hPV]
      exact (mwV_least hτSC).2.2 _ (nfp_fp (isNormal_veblen _) _) ((lt_add_one _).trans_le (le_nfp _ _))
    obtain ⟨j, hj⟩ := (lt_nfp_iff (f := veblen ω)).1 hyq
    have hjX := mwIterA_lt (a := ω) hXfix hτX j
    have hB := mwIterA_B (n := n) mw_omega_L (mwB_omega n) (mw_omega_lt_SC hτSC) hXfix hτX hLw j
    have h1 := (Bc.bcB_lt_iff (k := n) ((hj.trans hjX).trans hLw) (hjX.trans hLw)).2 hj
    rw [hB, hBξ] at h1
    refine h1.trans_le ((iterate_le_nfp _ _ j).trans ?_)
    rw [hPV']
    exact nfp_le_fp (isNormal_veblen _).strictMono.monotone
      (Order.add_one_le_of_lt (mwV_least hτ'SC).2.1) (mwV_least hτ'SC).1.le
  have hxR : x ∈ Set.range (veblen ω) := (mem_range_veblen omega0_ne_zero).2 fun b hb => by
    obtain ⟨m, rfl⟩ := lt_omega0.1 hb
    exact vzP_succ.1 (hall m)
  by_cases hxe : x = ltP (upsilon ξ)
  · -- `x = P(τ)`
    have hBx : Bc.bcB S n x = ltP (upsilon ξ') := by
      rw [hxe, hPV, mwB_V hτSC (by rw [← hPV, ← hxe]; exact hxL), hBξ, ← hPV']
    have hl : lhT (upsilon ξ) x = x * ω + x := by
      rw [hxe, ltP_eq hτE hτ1]; exact ltLhT_w1 hτE hτ1
    have hl' : lhT (upsilon ξ') (ltP (upsilon ξ')) = ltP (upsilon ξ') * ω + ltP (upsilon ξ') := by
      rw [ltP_eq hτ'E hτ'1]; exact ltLhT_w1 hτ'E hτ'1
    rw [hl, Bc.bcB_add hxw hxL, mwB_mul_omega hE hxw, hBx, hl']
  · -- `x < P(τ)`
    have hxlt : x < ltP (upsilon ξ) := lt_of_le_of_ne hxP hxe
    obtain ⟨β, hβx⟩ := hxR
    have hxn : veblen ω x ≠ x := mwOm_nfix hτSC hτ1 hτx hxlt
    have hβlt : β < x := by
      refine lt_of_le_of_ne (hβx ▸ right_le_veblen _ _) fun e => hxn ?_
      rw [← e] at hβx ⊢; rw [hβx]
    have hτβ : upsilon ξ < β := by
      by_contra hle
      push Not at hle
      have h2 := (veblen_le_veblen_iff_right (o := ω)).2 hle
      rw [hβx, hτfix] at h2
      exact absurd hτx (not_lt.2 h2)
    have hβP : β < ltP (upsilon ξ) := hβlt.trans hxlt
    have hβn : veblen ω β ≠ β := mwOm_nfix hτSC hτ1 hτβ hβP
    set η := mwIx ω (upsilon ξ) β with hη_def
    have hηβ : η ≤ β := mwIx_le _ _ _
    have hηT : η ∈ Tset (upsilon ξ) := hTm η ((hηβ.trans_lt hβlt).trans hx2)
    have hη1 : η < Om1 := ((hηβ.trans_lt hβlt).trans hx2).trans hu1
    have hβL : β < Nc.ncL S ω := hβlt.trans hxL
    have hηL : η < Nc.ncL S ω := hηβ.trans_lt hβL
    have hBx : Bc.bcB S n x = veblen ω (Bc.bcB S n β) := by
      rw [← hβx]
      exact (mwB_veblenA (k := n) mw_omega_L (mwB_omega n) (mvD_of_lt hβL)
        ((mw_omega_lt_SC hτSC).trans hτβ) hβn).2
    obtain ⟨hτβ', -, hind⟩ := mwIxA_move (n := n) mw_omega_L (mwB_omega n) hτfix (mw_omega_lt_SC hτSC)
      hBξ hτβ hβn hXfix (hβlt.trans hxX) hLw
    have hBβx : Bc.bcB S n β < Bc.bcB S n x := (Bc.bcB_lt_iff hβL hxL).2 hβlt
    have hBβP : Bc.bcB S n β < ltP (upsilon ξ') := hBβx.trans (hBlt x hxlt)
    have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
      rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
    have hBηβ : Bc.bcB S n η ≤ Bc.bcB S n β := Tp.tpB_le hβL hηβ
    have hBηT : mwIx ω (upsilon ξ') (Bc.bcB S n β) ∈ Tset (upsilon ξ') := by
      rw [hind]; exact hTm' _ ((hBηβ.trans_lt hBβx).trans hhi')
    have hBη1 : mwIx ω (upsilon ξ') (Bc.bcB S n β) < Om1 := by
      rw [hind]; exact ((hBηβ.trans_lt hBβx).trans hhi').trans hu1'
    by_cases h0 : η = 0
    · have hl := mwLhT_om0 hτSC hτ1 hτβ hβP h0
      have h0' : mwIx ω (upsilon ξ') (Bc.bcB S n β) = 0 := by rw [hind, ← hη_def, h0, Bc.bcB_zero]
      have hl' := mwLhT_om0 hτ'SC hτ'1 hτβ' hBβP h0'
      rw [hBx, hl', ← hβx, hl, hβx, mwB_mul_omega hE hxw, hBx]
    · have hl := mwLhT_omlim hτSC hτ1 hτβ hβP hηT hη1 h0
      have hB0 : Bc.bcB S n η ≠ 0 := by
        intro h
        have := (Bc.bcB_lt_iff (k := n) (Lw.lw_L_SC S ω).1 hηL).2 (pos_iff_ne_zero.2 h0)
        rw [Bc.bcB_zero, h] at this
        exact lt_irrefl _ this
      have h0' : mwIx ω (upsilon ξ') (Bc.bcB S n β) ≠ 0 := by rw [hind]; exact hB0
      have hl' := mwLhT_omlim hτ'SC hτ'1 hτβ' hBβP hBηT hBη1 h0'
      rw [hBx, hl', ← hβx, hl, hβx, Bc.bcB_add hxw ((lg_le h0).trans_lt hηL), mwB_mul_omega hE hxw, hBx,
        ← Tp.tpLgB h0 hηL, hind]

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω` (fixed points of every `φ_m`, `m < ω`) with `x > P(υ_ξ) =
ϑ^{υ_ξ}(Ω₁·(ω+1))`. -/
def MwLhTopW (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`MwLhTopW` gives `MwLhTop`.** -/
theorem mwLhTop_of_W (h : MwLhTopW S) : MwLhTop S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall
  by_cases hxP : x ≤ ltP (upsilon ξ)
  · exact mwLhT_w hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hxP
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall (not_le.1 hxP)

/-- **`MwLhTopW` gives `SfLhTMove`.** -/
theorem mwLhT_W (h : MwLhTopW S) : Sf.SfLhTMove S := mwLhT (mwLhTop_of_W h)

/-- **The road with `MwLhTopW` and `L(ω+1) ≤ ν_C → MwEQtop`.** -/
theorem mwRoad_w (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MwLhTopW S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MwEQtop S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mwRoad hU hO hL hV hN (mwLhTop_of_W hlh) htop

/-! ## The new hypotheses are restrictions of the old ones -/

/-- `SfEQlong` gives `MwEQtop`. -/
theorem mwEQtop_of_sf (h : Sf.SfEQlong S) : MwEQtop S :=
  fun n l l' hR h1 hr hl' hB hm _ => h n l l' hR h1 hr hl' hB hm

/-- `MvEQtop` gives `MwEQtop`. -/
theorem mwEQtop_of_mv (h : MvEQtop S) : MwEQtop S :=
  fun n l l' hR h1 hr hl' hB hm he => h n l l' hR h1 hr hl' hB hm (Gg.ggE_le_ggGam.trans he)

/-- `SfLhTMove` gives `MwLhTopW`. -/
theorem mwLhTopW_of_sf (h : Sf.SfLhTMove S) : MwLhTopW S :=
  fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 _ _ => h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1

/-- `MvLhTop` gives `MwLhTopW` (a point of `P_2` above `υ_ξ` is `≥ evZ(υ_ξ)`). -/
theorem mwLhTopW_of_mv (h : MvLhTop S) : MwLhTopW S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall _
  have hfix : Ordinal.epsilon x = x := by
    have := vzP_succ.1 (hall 1)
    simpa using this
  exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 (Or.inl (evZ_le hτx hfix))

end Googology.Trans.PoR.InaccPsi.R2.Mw
