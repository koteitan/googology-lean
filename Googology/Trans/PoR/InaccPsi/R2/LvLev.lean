import Googology.Trans.PoR.InaccPsi.R2.LvSys
import Googology.Trans.PoR.InaccPsi.R2.LuLev

/-!
# The fixed-point levels of `ϑᵗ(Ω₁·β + η)` for every level `β ∈ Tᵗ`, `1 ≤ β < Ω₁`, and the top `ϑᵗ(Ω₁·(τ + τ))`

`P_β` is the range of `φ_β = veblen β` (`Lu.LuP β`).  For a base `τ ∈ E ∩ Ω₁` and `η ∈ Tᵗ ∩ Ω₁`, from the cited facts
of `R2.CitedLu` (constant levels `β < τ`) and `R2.CitedLv` (levels `τ ≤ β < Ω₁`) only, as `R2.LuLev` did for `β < τ`:

* `ul_facts`, `ul_lt`, `ul_eta_lt`, `ul_lev_lt`, `ul_lt_of_vt_lt` (the facts and the comparison at every level
  `β ∈ Tᵗ`, `1 ≤ β < Ω₁`, by cases `β < τ`, `β ≥ τ`);
* `lv_level` (by transfinite induction on `β`): **minimality** (every `u ∈ P_β` above `τ`, `β`, `η` and every
  `ϑᵗ(Ω₁·β + σ)`, `σ < η`, is `≥ ϑᵗ(Ω₁·β + η)`) and **`ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`**; `lv_th_min`, `lv_th_notP`;
* `lv_th_P` (**`ϑᵗ(Ω₁·β + η) ∈ P_β`**), `lv_veblen_le_th` (`φ_β(j) ≤ ϑᵗ(Ω₁·β + j)`);
* `lv_top_P` (**`ϑᵗ(Ω₁·(τ + τ)) ∈ P_{τ+τ}`**), `lv_top_least` (**`ϑᵗ(Ω₁·(τ + τ))` is the least element of
  `P_{τ+τ}` above `τ`**).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Lu

section Base

variable {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
include hτ hτ1

theorem lv_tt : τ + τ ∈ Tset τ ∧ τ + τ < Om1 :=
  ⟨vzT_add hτ hτ1 (mem_T_of_le hτ hτ1 le_rfl) (mem_T_of_le hτ hτ1 le_rfl), Om1_add_lt hτ1 hτ1⟩

/-- The facts on `ϑᵗ(Ω₁·β + η)` at every level `β ∈ Tᵗ`, `1 ≤ β < Ω₁`. -/
theorem ul_facts {β η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) :
    Om1 * β + η ∈ Tset τ ∧ Om1 * β + η < OmTwo ∧ vt τ (Om1 * β + η) ∈ Tset τ ∧
      τ < vt τ (Om1 * β + η) ∧ vt τ (Om1 * β + η) < Om1 ∧ InE (vt τ (Om1 * β + η)) ∧
      β < vt τ (Om1 * β + η) ∧ η < vt τ (Om1 * β + η) := by
  rcases lt_or_ge β τ with h | h
  · obtain ⟨a, b, c, d, e, f, -, g⟩ := lu_th_facts hτ hτ1 hβ1 h hη hη1
    exact ⟨a, b, c, d, e, f, h.trans d, g⟩
  · obtain ⟨a, b, c, d, e, f, -, g, i⟩ := Lv.gen_facts hτ hτ1 hβT h hβΩ hη hη1
    exact ⟨a, b, c, d, e, f, g, i⟩

/-- **The comparison at every level** `β' ≤ β`, `β ∈ Tᵗ`, `1 ≤ β < Ω₁`. -/
theorem ul_lt {β' η' β η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ'β : β' ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1)
    (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (harg : Om1 * β' + η' < Om1 * β + η) (h : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * β + η) := by
  rcases lt_or_ge β τ with hβτ | hτβ
  · exact luVt_lt hτ hτ1 (hβ'β.trans_lt hβτ) hη' hη'1 hβτ hη hη1 harg h
  · have hβ'T := vz_T_down hτ hτ1 hβT hβΩ hβ'β
    exact lvVt_lt_gen hτ hτ1 hβ'T (hβ'β.trans_lt hβΩ) hβT hτβ hβΩ hη' hη'1 hη hη1
      harg (hβ'β.trans_lt (ul_facts hτ hτ1 hβ1 hβT hβΩ hη hη1).2.2.2.2.2.2.1) h

theorem ul_eta_lt {β σ η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hσ : σ ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : σ < η) : vt τ (Om1 * β + σ) < vt τ (Om1 * β + η) :=
  ul_lt hτ hτ1 hβ1 le_rfl hβT hβΩ hσ (h.trans hη1) hη hη1 ((add_lt_add_iff_left _).2 h)
    (h.trans (ul_facts hτ hτ1 hβ1 hβT hβΩ hη hη1).2.2.2.2.2.2.2)

theorem ul_eta_le {β σ η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hσ : σ ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : σ ≤ η) : vt τ (Om1 * β + σ) ≤ vt τ (Om1 * β + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (ul_eta_lt hτ hτ1 hβ1 hβT hβΩ hσ hη hη1 h).le
  · exact le_rfl

/-- A lower level is below: `ϑᵗ(Ω₁·β' + η') < ϑᵗ(Ω₁·β + η)` for `β' < β` and `η' < ϑᵗ(Ω₁·β + η)`. -/
theorem ul_lev_lt {β' η' β η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ'β : β' < β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1)
    (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (h : η' < vt τ (Om1 * β + η)) : vt τ (Om1 * β' + η') < vt τ (Om1 * β + η) := by
  refine ul_lt hτ hτ1 hβ1 hβ'β.le hβT hβΩ hη' hη'1 hη hη1 ?_ h
  calc Om1 * β' + η' < Om1 * β' + Om1 := (add_lt_add_iff_left _).2 hη'1
    _ = Om1 * (β' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * β := mul_le_mul_right (add_one_le_of_lt hβ'β) Om1
    _ ≤ Om1 * β + η := le_self_add

/-- **Lemma 3.30 `⇒` at every level** `β ∈ Tᵗ ∩ Ω₁`. -/
theorem ul_lt_of_vt_lt {ξ β η : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ) (hβξ : β < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * β + η)) : ξ < Om1 * β + η := by
  rcases lt_or_ge β τ with hβτ | hτβ
  · exact luLt_of_vt_lt hτ hτ1 hξ hξ2 hβτ hη hη1 hηξ h
  · exact lvLt_of_vt_lt hτ hτ1 hξ hξ2 hβT hτβ hβΩ hη hη1 hηξ hβξ h

/-- Below the top: `ϑᵗ(Ω₁·β + η) < ϑᵗ(Ω₁·(τ + τ))` for `β < τ + τ` and `η < ϑᵗ(Ω₁·(τ + τ))`. -/
theorem lv_lt_top {β η : Ordinal.{0}} (hβ : β < τ + τ) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (h : η < lvTop τ) : vt τ (Om1 * β + η) < lvTop τ := by
  obtain ⟨hTT, hT1⟩ := lv_tt hτ hτ1
  have hβT := vz_T_down hτ hτ1 hTT hT1 hβ.le
  obtain ⟨-, -, -, hτt, -, htE⟩ := LvT.lvTop_facts hτ hτ1
  have hβt : β < lvTop τ := hβ.trans ((inE_indec htE).add_lt hτt hτt)
  have e : lvTop τ = vt τ (Om1 * (τ + τ) + 0) := by rw [add_zero]; rfl
  rw [e] at h hβt ⊢
  refine lvVt_lt_gen hτ hτ1 hβT (hβ.trans hT1) hTT le_self_add hT1 hη hη1
    (mem_T_of_le hτ hτ1 zero_le) (Ordinal.omega_pos 1) ?_ hβt h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * (τ + τ) := mul_le_mul_right (add_one_le_of_lt hβ) Om1

/-- **The fixed-point levels** (`lv_level`): minimality at level `β`, and `ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`. -/
theorem lv_level : ∀ β, 1 ≤ β → β ∈ Tset τ → β < Om1 →
    (∀ η u, η ∈ Tset τ → η < Om1 → LuP β u → τ < u → η < u → β < u →
      (∀ σ, σ < η → vt τ (Om1 * β + σ) < u) → vt τ (Om1 * β + η) ≤ u) ∧
    (∀ η, η ∈ Tset τ → η < Om1 → ¬ LuP (β + 1) (vt τ (Om1 * β + η))) := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ1 hβT hβΩ
  -- minimality at `β`
  have Hmin : ∀ η u, η ∈ Tset τ → η < Om1 → LuP β u → τ < u → η < u → β < u →
      (∀ σ, σ < η → vt τ (Om1 * β + σ) < u) → vt τ (Om1 * β + η) ≤ u := by
    intro η u hηT hη1 hPu hτu hηu hβu hprev
    by_contra hlt
    push Not at hlt
    obtain ⟨-, -, haT, -, ha1, -, -, -⟩ := ul_facts hτ hτ1 hβ1 hβT hβΩ hηT hη1
    have hu1 : u < Om1 := hlt.trans ha1
    have huT : u ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
    have huE : InE u := luP_E hβ1 hPu
    obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
    have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
    have hξlt : ξ < Om1 * β + η :=
      ul_lt_of_vt_lt hτ hτ1 hβT hβΩ hξT hξ2 hηT hη1 (by rw [hξu]; exact hηu) (by rw [hξu]; exact hβu)
        (by rw [hξu]; exact hlt)
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
    · exact (IH q hlt' hq1 (vz_T_down hτ hτ1 hβT hβΩ hlt'.le) (hlt'.trans hβΩ)).2 r hrT hr1
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
  have hβv : ∀ x, 0 < x → β < veblen β x := fun x hx =>
    (left_le_veblen β 0).trans_lt ((veblen_lt_veblen_iff_right).2 hx)
  have Hub : ∀ σ, σ ∈ Tset τ → σ < Om1 → vt τ (Om1 * β + σ) ≤ veblen β (τ + σ + 1) := by
    intro σ
    induction σ using WellFoundedLT.induction with
    | ind σ IHσ =>
    intro hσT hσ1
    refine Hmin σ _ hσT hσ1 (luP_veblen β _) ?_ ?_ (hβv _ (lt_of_le_of_lt zero_le (lt_add_one _)))
      (fun σ' hσ' => ?_)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one _)) (right_le_veblen _ _)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
    · have hσ'T : σ' ∈ Tset τ := vz_T_down hτ hτ1 hσT hσ1 hσ'.le
      refine lt_of_le_of_lt (IHσ σ' hσ' hσ'T (hσ'.trans hσ1)) ?_
      refine (veblen_lt_veblen_iff_right).2 ?_
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left τ).2 ((add_one_le_of_lt hσ').trans_lt (lt_add_one σ))
  intro η hηT hη1 hP
  obtain ⟨-, -, -, hτa, -, haE, -, hηa⟩ := ul_facts hτ hτ1 hβ1 hβT hβΩ hηT hη1
  set a := vt τ (Om1 * β + η) with hadef
  have hfixa : veblen β a = a := luP_succ.1 hP
  have hI := inE_indec haE
  have h1 : τ + η + 1 < a := hI.add_lt (hI.add_lt hτa hηa) (lu_one_lt_E haE)
  have h2 := (veblen_lt_veblen_iff_right (o := β)).2 h1
  rw [hfixa] at h2
  exact lt_irrefl _ ((Hub η hηT hη1).trans_lt h2)

/-- **Minimality at level `β`**. -/
theorem lv_th_min {η u β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1)
    (hPu : LuP β u) (hτu : τ < u) (hηu : η < u) (hβu : β < u)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * β + σ) < u) : vt τ (Om1 * β + η) ≤ u :=
  (lv_level hτ hτ1 β hβ1 hβT hβΩ).1 η u hη hη1 hPu hτu hηu hβu hprev

/-- **`ϑᵗ(Ω₁·β + η) ∉ P_{β+1}`**. -/
theorem lv_th_notP {η β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) :
    ¬ LuP (β + 1) (vt τ (Om1 * β + η)) :=
  (lv_level hτ hτ1 β hβ1 hβT hβΩ).2 η hη hη1

/-- **`ϑᵗ(Ω₁·β + η) ∈ P_β`** (`β ∈ Tᵗ`, `1 ≤ β < Ω₁`). -/
theorem lv_th_P : ∀ β, 1 ≤ β → β ∈ Tset τ → β < Om1 → ∀ η, η ∈ Tset τ → η < Om1 →
    LuP β (vt τ (Om1 * β + η)) := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ1 hβT hβΩ η hηT hη1
  obtain ⟨-, -, haT, -, ha1, haE, -, -⟩ := ul_facts hτ hτ1 hβ1 hβT hβΩ hηT hη1
  set a := vt τ (Om1 * β + η) with hadef
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ1).ne'
  refine (mem_range_veblen hβ0).2 (fun β' hβ' => ?_)
  rcases eq_or_ne β' 0 with rfl | hβ'0
  · rw [veblen_zero_apply]; exact haE
  have hβ'1 : 1 ≤ β' := one_le_iff_ne_zero.2 hβ'0
  have hβ'T : β' ∈ Tset τ := vz_T_down hτ hτ1 hβT hβΩ hβ'.le
  have hβ'Ω : β' < Om1 := hβ'.trans hβΩ
  have hC : ∀ j, j ∈ Tset τ → j < Om1 → veblen β' j ≤ vt τ (Om1 * β' + j) := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j IHj =>
    intro hjT hj1
    refine vz_veblen_le_of_lt (IH β' hβ' hβ'1 hβ'T hβ'Ω j hjT hj1) (fun d hd => ?_)
    have hdT := vz_T_down hτ hτ1 hjT hj1 hd.le
    exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (ul_eta_lt hτ hτ1 hβ'1 hβ'T hβ'Ω hdT hjT hj1 hd)
  refine le_antisymm ?_ (right_le_veblen _ a)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans ha1
  have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
  exact (hC j.1 hjT hj1).trans (ul_lev_lt hτ hτ1 hβ1 hβ' hβT hβΩ hjT hj1 hηT hη1 j.2).le

/-- `φ_β(j) ≤ ϑᵗ(Ω₁·β + j)` (`β ∈ Tᵗ`, `1 ≤ β < Ω₁`, `j ∈ Tᵗ ∩ Ω₁`). -/
theorem lv_veblen_le_th {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ) (hβΩ : β < Om1) :
    ∀ j, j ∈ Tset τ → j < Om1 → veblen β j ≤ vt τ (Om1 * β + j) := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjT hj1
  refine vz_veblen_le_of_lt (lv_th_P hτ hτ1 β hβ1 hβT hβΩ j hjT hj1) (fun d hd => ?_)
  have hdT := vz_T_down hτ hτ1 hjT hj1 hd.le
  exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (ul_eta_lt hτ hτ1 hβ1 hβT hβΩ hdT hjT hj1 hd)

/-- **`ϑᵗ(Ω₁·(τ + τ)) ∈ P_{τ+τ}`**. -/
theorem lv_top_P : LuP (τ + τ) (lvTop τ) := by
  obtain ⟨-, -, haT, hτa, ha1, haE⟩ := LvT.lvTop_facts hτ hτ1
  have hττ0 : τ + τ ≠ 0 := (lt_of_lt_of_le hτ.pos le_self_add).ne'
  refine (mem_range_veblen hττ0).2 (fun β hβ => ?_)
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [veblen_zero_apply]; exact haE
  have hβ1 : 1 ≤ β := one_le_iff_ne_zero.2 hβ0
  refine le_antisymm ?_ (right_le_veblen _ _)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans ha1
  have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
  obtain ⟨hTT, hT1⟩ := lv_tt hτ hτ1
  exact (lv_veblen_le_th hτ hτ1 hβ1 (vz_T_down hτ hτ1 hTT hT1 hβ.le) (hβ.trans hT1) j.1 hjT hj1).trans
    (lv_lt_top hτ hτ1 hβ hjT hj1 j.2).le

/-- **`ϑᵗ(Ω₁·(τ + τ))` is the least element of `P_{τ+τ}` above `τ`.** -/
theorem lv_top_least {u : Ordinal.{0}} (hPu : LuP (τ + τ) u) (hτu : τ < u) : lvTop τ ≤ u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, -, haT, -, ha1, -⟩ := LvT.lvTop_facts hτ hτ1
  have hu1 : u < Om1 := hlt.trans ha1
  have huT : u ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
  have huE : InE u := luP_E ((lu_one_lt_E hτ).le.trans le_self_add) hPu
  obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hτ hτ1 hξT hξ2 hΩξ
  have hqττ : ξ / Om1 < τ + τ :=
    lv_quot_top hτ hτ1 hξT hξ2 (by rw [hξu]; exact hτu) (by rw [hξu]; exact huE) (by rw [hξu]; exact hlt)
  obtain ⟨hTT, hT1⟩ := lv_tt hτ hτ1
  have hnP := lv_th_notP hτ hτ1 hq1 (vz_T_down hτ hτ1 hTT hT1 hqττ.le) (hqττ.trans hT1) hrT hr1
  rw [hdec, hξu] at hnP
  exact hnP (luP_mono (hq1.trans le_self_add) (add_one_le_of_lt hqττ) hPu)

end Base

end Googology.Trans.PoR.InaccPsi.R2
