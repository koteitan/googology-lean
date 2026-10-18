import Googology.Trans.PoR.InaccPsi.R2.LuSys

/-!
# The fixed-point levels of `ϑᵗ(Ω₁·β + η)` for every constant level `1 ≤ β < τ`, and the top `ϑᵗ(Ω₁·τ)`

`P_β` is the range of `φ_β = veblen β` (`LuP β`).  For a base `τ ∈ E ∩ Ω₁` and `η ∈ Tᵗ ∩ Ω₁`, from the cited facts of
`R2.CitedLu` ([W07a] Lemma 3.30 at `Ω₁·β + η` and at `Ω₁·τ`) only (the remark after [W07a] Convention 4.1: `η ↦
ϑᵗ(Δ + η)` "enumerates the ordinals of the interval `(τ, Ω₁)` of the same 'fixed point level' which is indicated by
`Δ`", here proved for every `Δ = Ω₁·β`, `β < τ`; `R2.VzL` did this for `β < ω`):

* `luP_E`, `luP_mono`, `luP_succ`; `luFixLevel` ([W07a] Lemma 4.4 `⇒` at `Δ = Ω₁·β`, from Lemma 3.30: a fixed point
  of `σ ↦ ϑᵗ(Ω₁·β + σ)` has an argument `≥ Ω₁·(β + 1)`);
* `lu_level` (by transfinite induction on `β`): **minimality** (every `u ∈ P_β` above `τ`, above `η` and above every
  `ϑᵗ(Ω₁·β + σ)`, `σ < η`, is `≥ ϑᵗ(Ω₁·β + η)`) and **`ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`**; `lu_th_min`, `lu_th_notP`;
* `lu_th_P` (**`ϑᵗ(Ω₁·β + η) ∈ P_β`**), `lu_veblen_le_th` (`φ_β(j) ≤ ϑᵗ(Ω₁·β + j)`);
* `lu_top_P` (**`ϑᵗ(Ω₁·τ) ∈ P_τ`**), `lu_top_least` (**`ϑᵗ(Ω₁·τ)` is the least element of `P_τ` above `τ`**).

No new axiom beyond `R2.CitedLu`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- `P_β`: the range of `φ_β`. -/
def LuP (β a : Ordinal.{0}) : Prop := a ∈ Set.range (veblen β)

theorem luP_veblen (β i : Ordinal.{0}) : LuP β (veblen β i) := ⟨i, rfl⟩

theorem luP_E {β : Ordinal.{0}} (hβ : 1 ≤ β) {a : Ordinal.{0}} (h : LuP β a) : InE a := by
  obtain ⟨j, rfl⟩ := h
  have := veblen_veblen_of_lt (o₁ := 0) (o₂ := β) (lt_of_lt_of_le zero_lt_one hβ) j
  rw [veblen_zero_apply] at this
  exact this

theorem luP_mono {β β' : Ordinal.{0}} (hβ : 1 ≤ β) (hββ : β ≤ β') {a : Ordinal.{0}} (h : LuP β' a) : LuP β a := by
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ).ne'
  have hβ0' : β' ≠ 0 := (lt_of_lt_of_le zero_lt_one (hβ.trans hββ)).ne'
  have h' := (mem_range_veblen hβ0').1 h
  exact (mem_range_veblen hβ0).2 (fun b hb => h' b (lt_of_lt_of_le hb hββ))

theorem luP_succ {β a : Ordinal.{0}} : LuP (β + 1) a ↔ veblen β a = a := by
  unfold LuP
  rw [veblen_add_one]
  exact mem_range_deriv (isNormal_veblen _)

section Base

variable {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **[W07a] Lemma 4.4 `⇒` at `Δ = Ω₁·β`**, from Lemma 3.30: a fixed point `η > 0` of `σ ↦ ϑᵗ(Ω₁·β + σ)` with
`ϑᵗ(ξ) = η` has `ξ ≥ Ω₁·(β + 1)`. -/
theorem luFixLevel {η ξ β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < τ) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hη0 : 0 < η) (hfix : ∀ σ, σ < η → vt τ (Om1 * β + σ) < η) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hv : vt τ ξ = η) : Om1 * (β + 1) ≤ ξ := by
  have hηE : InE η := by
    refine lu_inE_of_cof hη0 (fun c hc => ?_)
    have hcT : c ∈ Tset τ := vz_T_down hτ hτ1 hη hη1 hc.le
    obtain ⟨-, -, -, -, -, hE, -, hcv⟩ := lu_th_facts hτ hτ1 hβ1 hβ hcT (hc.trans hη1)
    exact ⟨_, hE, hcv, hfix c hc⟩
  have hτη : τ < η := by
    obtain ⟨-, -, -, h1, -, -, -, -⟩ := lu_th_facts hτ hτ1 hβ1 hβ (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
    exact h1.trans (hfix 0 hη0)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξ hξ2).1 ⟨by rw [hv]; exact hτη, by rw [hv]; exact hηE⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨hq1, hsT, hs1, hdec⟩ := lu_split hτ hτ1 hξ hξ2 hΩξ
  set q := ξ / Om1 with hq
  set s := ξ % Om1 with hs
  have hqβ : q ≤ β := by
    have h1 : Om1 * q < Om1 * (β + 1) := lt_of_le_of_lt (hdec ▸ le_self_add) hlt
    exact Order.lt_add_one_iff.1 ((mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1)
  have hqτ : q < τ := lt_of_le_of_lt hqβ hβ
  have hsη : s < η := by rw [← hv, ← hdec]; exact luLt_vt_self hτ hτ1 hq1 hqτ hsT hs1
  have h1 := hfix s hsη
  rcases hqβ.lt_or_eq with hqβ' | hqβ'
  · have h2 : vt τ (Om1 * q + s) < vt τ (Om1 * β + s) :=
      lu_lev_lt hτ hτ1 hqβ' hβ hsT hs1 hsT hs1 (luLt_vt_self hτ hτ1 hβ1 hβ hsT hs1)
    rw [hdec, hv] at h2
    exact lt_irrefl _ (h1.trans h2)
  · rw [← hqβ', hdec, hv] at h1
    exact lt_irrefl _ h1

/-- **The fixed-point levels** (`lu_level`): minimality at level `β`, and `ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`. -/
theorem lu_level : ∀ β, 1 ≤ β → β < τ →
    (∀ η u, η ∈ Tset τ → η < Om1 → LuP β u → τ < u → η < u →
      (∀ σ, σ < η → vt τ (Om1 * β + σ) < u) → vt τ (Om1 * β + η) ≤ u) ∧
    (∀ η, η ∈ Tset τ → η < Om1 → ¬ LuP (β + 1) (vt τ (Om1 * β + η))) := by
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ1 hβ
  -- minimality at `β`
  have Hmin : ∀ η u, η ∈ Tset τ → η < Om1 → LuP β u → τ < u → η < u →
      (∀ σ, σ < η → vt τ (Om1 * β + σ) < u) → vt τ (Om1 * β + η) ≤ u := by
    intro η u hηT hη1 hPu hτu hηu hprev
    by_contra hlt
    push Not at hlt
    obtain ⟨-, -, haT, -, ha1, -, -, -⟩ := lu_th_facts hτ hτ1 hβ1 hβ hηT hη1
    set a := vt τ (Om1 * β + η) with hadef
    have hu1 : u < Om1 := hlt.trans ha1
    have huT : u ∈ Tset τ := (hTm u hu1).2 (hlt.trans ((hTm a ha1).1 haT))
    have huE : InE u := luP_E hβ1 hPu
    obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
    have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
    have hξlt : ξ < Om1 * β + η :=
      luLt_of_vt_lt hτ hτ1 hξT hξ2 hβ hηT hη1 (by rw [hξu]; exact hηu) (by rw [hξu]; exact hlt)
    obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hτ hτ1 hξT hξ2 hΩξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqβ : q ≤ β := by
      have h1 : Om1 * q < Om1 * (β + 1) := by
        calc Om1 * q ≤ ξ := hdec ▸ le_self_add
          _ < Om1 * β + η := hξlt
          _ < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
          _ = Om1 * (β + 1) := by rw [mul_add_one]
      exact Order.lt_add_one_iff.1 ((mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1)
    have hu' : vt τ (Om1 * q + r) = u := by rw [hdec, hξu]
    rcases hqβ.lt_or_eq with hlt' | heq
    · exact (IH q hlt' hq1 (hlt'.trans hβ)).2 r hrT hr1
        (by rw [hu']; exact luP_mono (hq1.trans le_self_add) (add_one_le_of_lt hlt') hPu)
    · have hrη : r < η := by
        have : Om1 * β + r < Om1 * β + η := by
          calc Om1 * β + r = ξ := by rw [← heq, hdec]
            _ < Om1 * β + η := hξlt
        exact (add_lt_add_iff_left _).1 this
      have := hprev r hrη
      rw [← heq, hu'] at this
      exact lt_irrefl _ this
  refine ⟨Hmin, ?_⟩
  -- not a fixed point of `φ_β`
  have Hub : ∀ σ, σ ∈ Tset τ → σ < Om1 → vt τ (Om1 * β + σ) ≤ veblen β (τ + σ + 1) := by
    intro σ
    induction σ using WellFoundedLT.induction with
    | ind σ IHσ =>
    intro hσT hσ1
    have hσm : σ < m := (hTm σ hσ1).1 hσT
    refine Hmin σ _ hσT hσ1 (luP_veblen β _) ?_ ?_ (fun σ' hσ' => ?_)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one _)) (right_le_veblen _ _)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
    · have hσ'T : σ' ∈ Tset τ := (hTm σ' (hσ'.trans hσ1)).2 (hσ'.trans hσm)
      refine lt_of_le_of_lt (IHσ σ' hσ' hσ'T (hσ'.trans hσ1)) ?_
      refine (veblen_lt_veblen_iff_right).2 ?_
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left τ).2 ((add_one_le_of_lt hσ').trans_lt (lt_add_one σ))
  intro η hηT hη1 hP
  obtain ⟨hγT, hγ2, haT, hτa, ha1, haE, -, -⟩ := lu_th_facts hτ hτ1 hβ1 hβ hηT hη1
  set a := vt τ (Om1 * β + η) with hadef
  have hfixa : veblen β a = a := luP_succ.1 hP
  have ham : a < m := (hTm a ha1).1 haT
  have hfix : ∀ σ, σ < a → vt τ (Om1 * β + σ) < a := by
    intro σ hσ
    have hσ1 : σ < Om1 := hσ.trans ha1
    have hσT : σ ∈ Tset τ := (hTm σ hσ1).2 (hσ.trans ham)
    refine lt_of_le_of_lt (Hub σ hσT hσ1) ?_
    have hI := inE_indec haE
    have h1 : τ + σ + 1 < a := hI.add_lt (hI.add_lt hτa hσ) (lu_one_lt_E haE)
    have := (veblen_lt_veblen_iff_right (o := β)).2 h1
    rwa [hfixa] at this
  have := luFixLevel hτ hτ1 hβ1 hβ haT ha1 haE.pos hfix hγT hγ2 rfl
  have h2 : Om1 * β + η < Om1 * (β + 1) := by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hη1
  exact absurd this (not_le.2 h2)

/-- **Minimality at level `β`**. -/
theorem lu_th_min {η u β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < τ) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hPu : LuP β u) (hτu : τ < u) (hηu : η < u) (hprev : ∀ σ, σ < η → vt τ (Om1 * β + σ) < u) :
    vt τ (Om1 * β + η) ≤ u :=
  (lu_level hτ hτ1 β hβ1 hβ).1 η u hη hη1 hPu hτu hηu hprev

/-- **`ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`**. -/
theorem lu_th_notP {η β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < τ) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    ¬ LuP (β + 1) (vt τ (Om1 * β + η)) :=
  (lu_level hτ hτ1 β hβ1 hβ).2 η hη hη1

/-- **`ϑᵗ(Ω₁·β + η) ∈ P_β`** (`1 ≤ β < τ`): every `φ_{β'}(j)`, `β' < β`, `j < a`, is at most `ϑᵗ(Ω₁·β' + j) < a`. -/
theorem lu_th_P : ∀ β, 1 ≤ β → β < τ → ∀ η, η ∈ Tset τ → η < Om1 → LuP β (vt τ (Om1 * β + η)) := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ1 hβ η hηT hη1
  obtain ⟨-, -, haT, -, ha1, haE, -, -⟩ := lu_th_facts hτ hτ1 hβ1 hβ hηT hη1
  set a := vt τ (Om1 * β + η) with hadef
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ1).ne'
  refine (mem_range_veblen hβ0).2 (fun β' hβ' => ?_)
  rcases eq_or_ne β' 0 with rfl | hβ'0
  · rw [veblen_zero_apply]; exact haE
  have hβ'1 : 1 ≤ β' := one_le_iff_ne_zero.2 hβ'0
  have hβ'τ : β' < τ := hβ'.trans hβ
  -- `φ_{β'}(j) ≤ ϑᵗ(Ω₁·β' + j)`
  have hC : ∀ j, j ∈ Tset τ → j < Om1 → veblen β' j ≤ vt τ (Om1 * β' + j) := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j IHj =>
    intro hjT hj1
    refine vz_veblen_le_of_lt (IH β' hβ' hβ'1 hβ'τ j hjT hj1) (fun d hd => ?_)
    have hdT := vz_T_down hτ hτ1 hjT hj1 hd.le
    exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (lu_th_lt hτ hτ1 hβ'1 hβ'τ hdT hjT hj1 hd)
  refine le_antisymm ?_ (right_le_veblen _ a)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans ha1
  have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
  exact (hC j.1 hjT hj1).trans (lu_lev_lt hτ hτ1 hβ' hβ hjT hj1 hηT hη1 j.2).le

/-- `φ_β(j) ≤ ϑᵗ(Ω₁·β + j)` (`1 ≤ β < τ`, `j ∈ Tᵗ ∩ Ω₁`). -/
theorem lu_veblen_le_th {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < τ) :
    ∀ j, j ∈ Tset τ → j < Om1 → veblen β j ≤ vt τ (Om1 * β + j) := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjT hj1
  refine vz_veblen_le_of_lt (lu_th_P hτ hτ1 β hβ1 hβ j hjT hj1) (fun d hd => ?_)
  have hdT := vz_T_down hτ hτ1 hjT hj1 hd.le
  exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (lu_th_lt hτ hτ1 hβ1 hβ hdT hjT hj1 hd)

/-- **`ϑᵗ(Ω₁·τ) ∈ P_τ`**: every `φ_β(j)`, `β < τ`, `j < ϑᵗ(Ω₁·τ)`, is below it. -/
theorem lu_top_P : LuP τ (vt τ (Om1 * τ)) := by
  obtain ⟨-, -, haT, -, ha1, haE, -⟩ := lu_top_facts hτ hτ1
  set a := vt τ (Om1 * τ) with hadef
  refine (mem_range_veblen hτ.pos.ne').2 (fun β hβ => ?_)
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [veblen_zero_apply]; exact haE
  have hβ1 : 1 ≤ β := one_le_iff_ne_zero.2 hβ0
  refine le_antisymm ?_ (right_le_veblen _ a)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans ha1
  have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
  exact (lu_veblen_le_th hτ hτ1 hβ1 hβ j.1 hjT hj1).trans (lu_th_lt_top hτ hτ1 hβ hjT hj1 j.2).le

/-- **`ϑᵗ(Ω₁·τ)` is the least element of `P_τ` above `τ`.** -/
theorem lu_top_least {u : Ordinal.{0}} (hPu : LuP τ u) (hτu : τ < u) : vt τ (Om1 * τ) ≤ u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, -, haT, -, ha1, -, -⟩ := lu_top_facts hτ hτ1
  have hu1 : u < Om1 := hlt.trans ha1
  have huT : u ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
  have huE : InE u := luP_E (lu_one_lt_E hτ).le hPu
  obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hτ hτ1 hξT hξ2 hΩξ
  have hqτ : ξ / Om1 < τ := lu_rep_top hτ hτ1 hξT hξ2 (by rw [hξu]; exact hτu) (by rw [hξu]; exact hlt)
  have hnP := lu_th_notP hτ hτ1 hq1 hqτ hrT hr1
  rw [hdec, hξu] at hnP
  exact hnP (luP_mono (hq1.trans le_self_add) (add_one_le_of_lt hqτ) hPu)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Lu
