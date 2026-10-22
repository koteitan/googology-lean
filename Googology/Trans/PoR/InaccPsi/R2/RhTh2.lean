import Googology.Trans.PoR.InaccPsi.R2.RhTh

/-!
# `ϑᵗ(Ω₁·(Ω₁+β) + η)` at every countable level `β ∈ Tᵗ`, also `β ≥ τ`

For a strongly critical base `τ < Ω₁` that is a fixed point of every `F_j`, `j < τ` (`F_j = Rh.rhF j`),
`Δ_β = Ω₁·(Ω₁·1 + β)`, from the cited facts of `R2.CitedLq` at `γ = 1`:

* `RhkREP2 τ β` (**every value `w ∈ Tᵗ ∩ (max(τ, β), Ω₁)` of `F_β` that is not a fixed point of `F_β` is
  `ϑᵗ(Δ_β + σ)`, `σ < w`**), proved with LE (`Rh.RhkLE`) by induction on all `β ∈ Tᵗ ∩ Ω₁` (`rhk_Q2`);
* `rhk_fixv2` (**`ϑᵗ(Δ_β + η)` is a fixed point of every `F_j`, `j < β`**, at every level);
* `rhk_enum0` (**`ϑᵗ(Δ_β + η) = F_β(c₀ + η)`** at a level `β ≥ τ`, `c₀` the least index with `F_β(c₀) > β`, when
  `c₀ + σ < F_β(c₀+σ)` for every `σ ≤ η`), `rhk_enum_fix2` (**`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** for a fixed point
  `p > τ` of `F_β`, at every level);
* `rhk_zeta_fix2`, `rhk_zeta_fix_add2` (**`ζᵗ = 0` at a fixed point `p > τ` of `F_β`, `ζᵗ = logend(p + δ)` above it**,
  at every level), `rhk_zeta0` (**`ζᵗ = logend(η)`** under the condition of `rhk_enum0`).

No new axiom beyond `R2.CitedLq` and the axioms of `R2.RbTh`.  New definition: the statement name `RhkREP2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd

/-- **REP2(β)**: every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `F_β` above `β` (strongly critical, a fixed point of every `F_j`,
`j < β`) that is not a fixed point of `F_β` is `ϑᵗ(Δ_β + σ)` with `σ ∈ Tᵗ`, `σ < w`. -/
def RhkREP2 (τ β : Ordinal.{0}) : Prop :=
  ∀ w, SC w → (∀ j < β, rhF j w = w) → τ < w → β < w → w ∈ Tset τ → w < Om1 → rhF β w ≠ w →
    ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * (Om1 * 1 + β) + σ) = w

/-- REP2 below `τ` gives REP. -/
theorem rhk_rep_of_rep2 {τ β : Ordinal.{0}} (hβτ : β < τ) (h : RhkREP2 τ β) : RhkREP τ β :=
  fun w hw hwF hτw hwT hw1 hnf => h w hw hwF hτw (hβτ.trans hτw) hwT hw1 hnf

/-- A fixed point `p` of `F_β`, `β ≥ 1`, lies above `β`. -/
theorem rhF_lt_fix {β p : Ordinal.{0}} (hβ0 : β ≠ 0) (hp : rhF β p = p) : β < p := by
  refine lt_of_le_of_ne ((rhF_left_le β p).trans_eq hp) fun e => hβ0 ?_
  have h1 : rhF β 0 ≤ rhF β p := (rhF_le β).2 zero_le
  have h2 : rhF β 0 = rhF β p := le_antisymm h1 (by rw [hp, ← e]; exact rhF_left_le β 0)
  rw [hp] at h2
  have h3 := (rhF_normal β).strictMono.injective (h2.trans hp.symm)
  rw [← h3] at e
  exact e

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **`ϑᵗ(Δ_β + η)` is a fixed point of every `F_j`, `j < β`**, given REP2 at the levels below `β`. -/
theorem rhk_fixv2_of {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hREP : ∀ j < β, RhkREP2 τ j)
    {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < β, rhF j (vt τ (Om1 * (Om1 * 1 + β) + η)) = vt τ (Om1 * (Om1 * 1 + β) + η) := by
  obtain ⟨-, -, hvT, hτv, hv1, -, hβv, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  have hvSC := rhk_SC hτ hτ1 hβT hβΩ hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk
  by_contra hnf
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    hREP j hjk _ hvSC (fun i hi => IHj i hi (hi.trans hjk)) hτv (hjk.trans hβv) hvT hv1 hnf
  have := rhk_lt_lower hτ hτ1 hβT hβΩ hjk hσT hσΩ hη hηΩ hσv
  rw [he] at this
  exact lt_irrefl _ this

/-- **`ϑᵗ(Δ_β + η) = F_β(c₀ + η)`** at a level `β ≥ τ`, for `c₀` with `F_β(c₀) > β ≥ F_β(c)`, `c < c₀`, when
`c₀ + σ < F_β(c₀+σ)` for every `σ ≤ η`. -/
theorem rhk_enum0_of {β c0 : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hτβ : τ ≤ β)
    (hLE : ∀ j < β, RhkLE τ j) (hREP : ∀ j < β, RhkREP2 τ j) (hc0 : β < rhF β c0)
    (hmin : ∀ c < c0, rhF β c ≤ β) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < rhF β (c0 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + η) = rhF β (c0 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 * 1 + β) + σ) = rhF β (c0 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hβs : β < rhF β (c0 + η) := hc0.trans_le ((rhF_le β).2 le_self_add)
  apply le_antisymm
  · refine rhk_min hτ hτ1 hβT hβΩ hLE hη hηΩ (rhF_SC β _) (fun j hj => rhF_fix_lower hj _)
      (hτβ.trans_lt hβs) (le_add_self.trans_lt (hcond η le_rfl)) hβs fun σ hσ => ?_
    rw [hIH σ hσ]; exact (rhF_lt β).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, -, -, -, hβv, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
    obtain ⟨e, he⟩ := rhF_range (rhk_SC hτ hτ1 hβT hβΩ hη hηΩ) (rhk_fixv2_of hτ hτ1 hβT hβΩ hREP hη hηΩ)
    rw [← he]
    refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
    rcases lt_or_ge e c0 with hec | hce
    · have := hmin e hec
      rw [he] at this
      exact absurd hβv (not_lt.2 this)
    · have hσe : c0 + (e - c0) = e := Ordinal.add_sub_cancel_of_le hce
      have hσ : e - c0 < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
      have h1 := rhk_lt hτ hτ1 hβT hβΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
      rw [hIH _ hσ, hσe, he] at h1
      exact lt_irrefl _ h1

/-- **`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** at every level `β ∈ Tᵗ ∩ Ω₁`, for a fixed point `p > τ` of `F_β` when
`p + 1 + σ < F_β(p+1+σ)` for every `σ ≤ δ`. -/
theorem rhk_enum_fix2_of {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hLE : ∀ j < β, RhkLE τ j)
    (hREP : ∀ j < β, RhkREP2 τ j) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ)) = rhF β (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLEk := rhk_le_of hτ hτ1 hβT hβΩ hLE
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ')) = rhF β (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < rhF β (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (rhF_lt β).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine rhk_min hτ hτ1 hβT hβΩ hLE hT h1 (rhF_SC β _) (fun j hj => rhF_fix_lower hj _) (hτp.trans hpg) ?_
      (((rhF_left_le β p).trans_eq hp).trans_lt hpg) fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (rhk_below_fix_of hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (rhF_lt β).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, -, hηv⟩ := rhk_facts hτ hτ1 hβT hβΩ hT h1
    obtain ⟨e, he⟩ := rhF_range (rhk_SC hτ hτ1 hβT hβΩ hT h1) (rhk_fixv2_of hτ hτ1 hβT hβΩ hREP hT h1)
    rw [← he]
    refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (rhF_lt β).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := rhk_lt hτ hτ1 hβT hβΩ hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

end Base

section Fix

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτF : ∀ j < τ, rhF j τ = τ)
include hτ hτ1 hτF

/-- **REP2(β)** at every level `β ∈ Tᵗ ∩ Ω₁` from LE and REP2 at the levels below `β`. -/
theorem rhk_rep2_of {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hLE : ∀ j < β, RhkLE τ j)
    (hREP : ∀ j < β, RhkREP2 τ j) : RhkREP2 τ β := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro w hw hwF hτw hβw hwT hw1 hnf
  obtain ⟨y, hy⟩ := rhF_range hw hwF
  have hyw : y < w := by
    refine lt_of_le_of_ne (hy ▸ rhF_le_self β y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpw, hmax⟩ := rh_base_below (rhF_normal β) hτw hnf
  have hnofix : ∀ z, p < z → z < w → z < rhF β z := by
    intro z hpz hzw
    by_contra h
    push Not at h
    have hz := le_antisymm h (rhF_le_self β z)
    have hτz : τ < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hτz hzw) (not_le.2 hpz)
  by_cases hcase : p = τ ∧ τ ≤ β
  · -- no fixed point of `F_β` in `(τ, w)` and `β ≥ τ`: the base `c₀`
    obtain ⟨hpτ, hτβ⟩ := hcase
    have hτ0 : τ ≠ 0 := hτ.1.ne'
    set c0 : Ordinal.{0} := if β < rhF β 0 then 0 else 1 with hc0def
    have hc0 : β < rhF β c0 := by
      by_cases h : β < rhF β 0
      · rw [hc0def, if_pos h]; exact h
      · rw [hc0def, if_neg h]
        exact (rhF_left_le β 0).trans_lt ((rhF_lt β).2 zero_lt_one)
    have hmin : ∀ c < c0, rhF β c ≤ β := by
      intro c hc
      by_cases h : β < rhF β 0
      · rw [hc0def, if_pos h] at hc; exact absurd hc (not_lt.2 zero_le)
      · rw [hc0def, if_neg h, Order.lt_one_iff] at hc
        rw [hc]; exact not_lt.1 h
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hβw (not_lt.2 this)
    set D := y - c0 with hDdef
    have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
    have hDw : D < w := (Ordinal.sub_le_self y c0).trans_lt hyw
    have hcond : ∀ σ, σ ≤ D → c0 + σ < rhF β (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (rhF_le_self β _) fun hz => ?_
      have hzβ : β ≤ c0 + σ := (rhF_left_le β _).trans_eq hz.symm
      rcases (hτβ.trans hzβ).lt_or_eq with hτz | hτz
      · have := hnofix _ (by rw [hpτ]; exact hτz) (hzy.trans_lt hyw)
        rw [← hz] at this
        exact lt_irrefl _ this
      · -- `c₀ + σ = τ = β`: then `F_β(0) = F_β(τ)`, so `τ = 0`
        have hβτ : β = τ := le_antisymm (hzβ.trans_eq hτz.symm) hτβ
        have h1 : rhF β τ = τ := by rw [hτz]; exact hz.symm
        have h2 : rhF β 0 ≤ τ := h1 ▸ (rhF_le β).2 zero_le
        have h3 : rhF β 0 = rhF β τ := by
          rw [h1]; exact le_antisymm h2 (hβτ ▸ rhF_left_le β 0)
        exact hτ0 ((rhF_normal β).strictMono.injective h3).symm
    have hT : D ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hDw.le
    have hτβ' : τ ≤ β := hτβ
    refine ⟨D, hT, hDw.trans hw1, hDw, ?_⟩
    rw [rhk_enum0_of hτ hτ1 hβT hβΩ hτβ' hLE hREP hc0 hmin D hT (hDw.trans hw1) hcond, hcD, hy]
  · have hpp : rhF β p = p := by
      rcases hbase with e | ⟨-, h⟩
      · have hβτ : β < τ := not_le.1 fun h' => hcase ⟨e, h'⟩
        rw [e]; exact hτF β hβτ
      · exact h
    have hpy : p < y := (rhF_lt β).1 (by rw [hpp, hy]; exact hpw)
    set D := y - p with hDdef
    have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
    have hD0 : D ≠ 0 := by
      rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
    set δ := D - 1 with hδdef
    have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
    have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
    have hδle : δ ≤ p + δ := le_add_self
    have hpδw : p + δ < w := by
      refine lt_of_le_of_lt ?_ hyw
      rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    rcases hbase with hpτ | ⟨hτp, -⟩
    · -- `p = τ`, `β < τ`
      have hβτ : β < τ := not_le.1 fun h' => hcase ⟨hpτ, h'⟩
      have hδw : δ < w := hδle.trans_lt hpδw
      have hT : δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hδw.le
      have hc : ∀ σ, σ ≤ δ → 1 + σ < rhF β (τ + 1 + σ) := by
        intro σ hσ
        have h := hcond σ hσ
        rw [hpτ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      refine ⟨δ, hT, hδw.trans hw1, hδw, ?_⟩
      rw [rhk_enum_of hτ hτ1 hτF hβτ hLE (fun j hj => rhk_rep_of_rep2 (hj.trans hβτ) (hREP j hj)) δ hT
        (hδw.trans hw1) hc, ← hpτ, hpδy, hy]
    · have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
      refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
      rw [rhk_enum_fix2_of hτ hτ1 hβT hβΩ hLE hREP hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

/-- **LE(β) and REP2(β) at every level `β ∈ Tᵗ ∩ Ω₁`.** -/
theorem rhk_Q2 (β : Ordinal.{0}) : β ∈ Tset τ → β < Om1 → RhkLE τ β ∧ RhkREP2 τ β := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβT hβΩ
  have hjT : ∀ j < β, j ∈ Tset τ := fun j hj => vz_T_down hτE hτ1 hβT hβΩ hj.le
  have hLE : ∀ j < β, RhkLE τ j := fun j hj => (IH j hj (hjT j hj) (hj.trans hβΩ)).1
  have hREP : ∀ j < β, RhkREP2 τ j := fun j hj => (IH j hj (hjT j hj) (hj.trans hβΩ)).2
  exact ⟨rhk_le_of hτ hτ1 hβT hβΩ hLE, rhk_rep2_of hτ hτ1 hτF hβT hβΩ hLE hREP⟩

/-- **`ϑᵗ(Δ_β + η)` is a fixed point of every `F_j`, `j < β`**, at every level `β ∈ Tᵗ ∩ Ω₁`. -/
theorem rhk_fixv2 {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) :
    ∀ j < β, rhF j (vt τ (Om1 * (Om1 * 1 + β) + η)) = vt τ (Om1 * (Om1 * 1 + β) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  exact rhk_fixv2_of hτ hτ1 hβT hβΩ (fun j hj =>
    (rhk_Q2 hτ hτ1 hτF j (vz_T_down hτE hτ1 hβT hβΩ hj.le) (hj.trans hβΩ)).2) hη hηΩ

/-- **`ϑᵗ(Δ_β + η) = F_β(c₀ + η)`** at a level `τ ≤ β ∈ Tᵗ ∩ Ω₁`. -/
theorem rhk_enum0 {β c0 : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hτβ : τ ≤ β)
    (hc0 : β < rhF β c0) (hmin : ∀ c < c0, rhF β c ≤ β) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < rhF β (c0 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + η) = rhF β (c0 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hQ := fun j (hj : j < β) =>
    rhk_Q2 hτ hτ1 hτF j (vz_T_down hτE hτ1 hβT hβΩ hj.le) (hj.trans hβΩ)
  exact rhk_enum0_of hτ hτ1 hβT hβΩ hτβ (fun j hj => (hQ j hj).1) (fun j hj => (hQ j hj).2) hc0 hmin

/-- **`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** at every level `β ∈ Tᵗ ∩ Ω₁`, for a fixed point `p > τ` of `F_β`. -/
theorem rhk_enum_fix2 {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {p : Ordinal.{0}}
    (hp : rhF β p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ)) = rhF β (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hQ := fun j (hj : j < β) =>
    rhk_Q2 hτ hτ1 hτF j (vz_T_down hτE hτ1 hβT hβΩ hj.le) (hj.trans hβΩ)
  exact rhk_enum_fix2_of hτ hτ1 hβT hβΩ (fun j hj => (hQ j hj).1) (fun j hj => (hQ j hj).2) hp hτp

/-- **`ζᵗ = 0` at a fixed point `p > τ` of `F_β`**, at every level `β ∈ Tᵗ ∩ Ω₁`. -/
theorem rhk_zeta_fix2 {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {p : Ordinal.{0}}
    (hp : rhF β p = p) (hτp : τ < p) (hpT : p ∈ Tset τ) (hp1 : p < Om1) :
    lqZeta τ (Om1 * (Om1 * 1 + β)) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE := (rhk_Q2 hτ hτ1 hτF β hβT hβΩ).1
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt (not_lt.2 (rhk_below_fix_of hLE hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rhk_enum_fix2`, at every level. -/
theorem rhk_zeta_fix_add2 {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {p δ : Ordinal.{0}}
    (hp : rhF β p = p) (hτp : τ < p) (hδ0 : δ ≠ 0) (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1)
    (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + β)) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ')) = rhF β (p + 1 + δ') := fun δ' hδ' =>
    rhk_enum_fix2 hτ hτ1 hτF hβT hβΩ hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
      (((add_le_add_iff_left p).2 hδ').trans_lt h1) fun σ hσ => hcond σ (hσ.trans hδ')
  unfold lqZeta
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit δ with h0 | ⟨δ0, rfl⟩ | hlim
  · exact absurd h0 hδ0
  · refine ⟨p + δ0, (add_lt_add_iff_left p).2 (Order.lt_succ δ0), ?_⟩
    rw [hen δ0 (Order.le_succ δ0), Order.succ_eq_add_one, ← add_assoc]
    have hle : p + δ0 + 1 ≤ p + 1 + δ0 + 1 := by
      refine add_le_add ?_ le_rfl
      rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    exact hle.trans_lt ((rhF_SC β _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < rhF β (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := ((rhF_normal β).lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : rhF β x ≤ p := by
        conv_rhs => rw [← hp]
        exact (rhF_le β).2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_β + η)` under the condition of `rhk_enum0` (a level `τ ≤ β`). -/
theorem rhk_zeta0 {β c0 : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hτβ : τ ≤ β)
    (hc0 : β < rhF β c0) (hmin : ∀ c < c0, rhF β c ≤ β) {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hcond : ∀ σ, σ ≤ η → c0 + σ < rhF β (c0 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + β)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 * 1 + β) + σ) = rhF β (c0 + σ) := fun σ hσ =>
    rhk_enum0 hτ hτ1 hτF hβT hβΩ hτβ hc0 hmin σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
      fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (rhF_SC β _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < rhF β (c0 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((rhF_normal β).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x c0 with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((rhF_lt β).2 hxc)
    · have hσe : c0 + (x - c0) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - c0 < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - c0, hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Rh
