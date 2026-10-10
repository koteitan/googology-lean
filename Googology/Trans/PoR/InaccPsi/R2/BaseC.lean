import Googology.Trans.PoR.InaccPsi.R2.ChainL

/-!
# One base change between two `υ`-points: indecomposables, closed images, `≤₁` of `R₁⁺`

For countable `υ`-points `σ < τ` (so `σ, τ ∈ E`), the base change `π = π_{σ,τ} : Tᵗ[σ] → Tᵟ`
([W07a] Def 5.1) and its inverse `up σ τ`:

* `lead_comp`, `exists_comp_absorb`: the leading Cantor normal form component of a decomposable
  `x ≠ 0` is a component `L < x` with `L + x ≠ x`;
* `down_indec`, `up_indec`: `π` and `π⁻¹` keep indecomposability (countable arguments);
* `closed_image_of_indec`: an arithmetic isomorphism of a closed set that keeps indecomposability
  has a closed image ([C09] Def 2.3);
* `down_le1R`, `up_le1R`: `π` and `π⁻¹` keep and reflect `≤₁` of `R₁⁺` on `Tᵗ[σ]` (all cases: below
  `σ`, the base `τ ↦ σ`, and Lemma ST above `τ`);
* `add_iff_indec`: on indecomposables the graph of `+` is `x + y = z ⇔ x < y ∧ y = z`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

theorem lead_comp {x : Ordinal.{0}} (hx : x ≠ 0) : ω ^ log ω x ∈ comps x := by
  unfold comps; rw [CNF.ne_zero hx]; simp

/-- A decomposable `x ≠ 0` has a component `L < x` (the leading one) with `L + x ≠ x`. -/
theorem exists_comp_absorb {x : Ordinal.{0}} (hx : x ≠ 0) (hI : ¬ Indec x) :
    ∃ L ∈ comps x, L < x ∧ L + x ≠ x := by
  refine ⟨_, lead_comp hx, lt_of_le_of_ne (opow_log_le_self ω hx) ?_, ?_⟩
  · intro e; exact hI (e ▸ indec_opow _)
  · intro e
    have h1 := add_eq_right_iff_mul_omega0_le.1 e
    have h2 := lt_opow_succ_log_self one_lt_omega0 x
    rw [opow_succ] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- On indecomposables: `x + y = z ⇔ x < y ∧ y = z`. -/
theorem add_iff_indec {x y z : Ordinal.{0}} (_hx : Indec x) (hy : Indec y) (hz : Indec z) :
    x + y = z ↔ x < y ∧ y = z := by
  constructor
  · intro e
    rcases lt_or_ge x y with hxy | hyx
    · exact ⟨hxy, (hy.add_eq hxy).symm.trans e⟩
    · exfalso
      have hxz : x < z := by
        rw [← e]; exact lt_add_of_pos_right x hy.pos
      have hyz : y < z := lt_of_le_of_lt hyx hxz
      exact absurd e (hz.add_lt hxz hyz).ne
  · rintro ⟨hxy, rfl⟩; exact hy.add_eq hxy

/-- A nonzero `υ`-point is indecomposable. -/
theorem indec_of_upsPt {u : Ordinal.{0}} (hu : UpsPt u) : Indec u := by
  have := indec_opow u; rwa [upsPt_inE hu] at this

/-- The image of a closed set under an arithmetic isomorphism that keeps indecomposability is
closed. -/
theorem closed_image_of_indec {S : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso S (h '' S) h) (hS : Closed S) (hI : ∀ s ∈ S, Indec s → Indec (h s)) :
    Closed (h '' S) := by
  rintro z ⟨s, hs, rfl⟩ hdz
  by_cases hsI : Indec s
  · exact absurd hdz (hI s hs hsI)
  · rcases hS s hs (not_not.1 hsI) with h0 | ⟨p, hp, q, hq, hp1, hq1, hpq⟩
    · subst h0; left; exact hh.map_zero hs
    · right
      exact ⟨h p, ⟨p, hp, rfl⟩, h q, ⟨q, hq, rfl⟩, hh.2.1 hp hs hp1, hh.2.1 hq hs hq1,
        (hh.2.2 p hp q hq s hs).1 hpq⟩

/-- `π_{σ,τ}` keeps indecomposability. -/
theorem down_indec {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hxT : x ∈ TB τ σ) (hx1 : x < Om1)
    (hI : Indec x) : Indec (pi σ τ x) := by
  obtain ⟨m, -, -, -, hT, -⟩ := T_next (Or.inr h.1) (h.2.2.1.trans h.2.2.2)
  have hyT : pi σ τ x ∈ Tset σ := (pi_bijOn h).1.mapsTo hxT
  have hy1 : pi σ τ x < Om1 := down_lt_Om1 h hxT hx1
  have hym : pi σ τ x < m := (hT _ hy1).1 hyT
  by_contra hyI
  have hσ0 : (0 : Ordinal.{0}) < σ := InE.pos h.1
  have hy0 : pi σ τ x ≠ 0 := by
    intro e; apply hI.ne_zero
    have h0T : (0 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ0.trans h.2.2.1)).2 hσ0
    exact (pi_bijOn h).1.injOn hxT h0T (by rw [e, pi_lt h hσ0])
  obtain ⟨L, -, hLy, hLne⟩ := exists_comp_absorb hy0 hyI
  have hLT : L ∈ Tset σ := (hT L (hLy.trans hy1)).2 (hLy.trans hym)
  obtain ⟨hL'T, hpL⟩ := up_spec h hLT
  have hL'x : up σ τ L < x := by
    by_contra hle
    have := ((pi_bijOn h).2.le_iff_le hxT hL'T).2 (not_lt.1 hle)
    rw [hpL] at this; exact absurd hLy (not_lt.2 this)
  obtain ⟨-, hpadd⟩ := pi_add h hL'T hxT
  rw [hI.add_eq hL'x, hpL] at hpadd
  exact hLne hpadd.symm

/-- `π_{σ,τ}⁻¹` keeps indecomposability. -/
theorem up_indec {σ τ y : Ordinal.{0}} (h : Bases σ τ) (hyT : y ∈ Tset σ) (hy1 : y < Om1)
    (hI : Indec y) : Indec (up σ τ y) := by
  obtain ⟨hxT, hpx⟩ := up_spec h hyT
  have hx1 : up σ τ y < Om1 := up_lt_Om1 h hyT hy1
  have hσ0 : (0 : Ordinal.{0}) < σ := InE.pos h.1
  by_contra hxI
  have hx0 : up σ τ y ≠ 0 := by
    intro e; apply hI.ne_zero; rw [← hpx, e, pi_lt h hσ0]
  by_cases hτx : τ ≤ up σ τ y
  · obtain ⟨L, hLc, hLx, hLne⟩ := exists_comp_absorb hx0 hxI
    have hLTB : L ∈ TB τ σ := by
      have hc := Par_comps h.2.1 h.2.2.2 hxT.1 hτx hx1 hLc
      by_cases hLτ : L < τ
      · exact (TB_inter_lt h hLτ).2 (hxT.2 (Finset.mem_coe.2 (hc.1 hLτ)))
      · obtain ⟨hLT, hLP⟩ := hc.2 (not_lt.1 hLτ)
        exact ⟨hLT, fun p hp => hxT.2 (Finset.mem_coe.2 (hLP (Finset.mem_coe.1 hp)))⟩
    obtain ⟨hsT, hps⟩ := pi_add h hLTB hxT
    have hpLx : pi σ τ L < y := by rw [← hpx]; exact (pi_bijOn h).2 hLTB hxT hLx
    rw [hpx, hI.add_eq hpLx] at hps
    exact hLne ((pi_bijOn h).1.injOn hsT hxT (by rw [hps, hpx]))
  · have hxσ : up σ τ y < σ := (TB_inter_lt h (not_le.1 hτx)).1 hxT
    rw [pi_lt h hxσ] at hpx
    exact hxI (by rw [hpx]; exact hI)

/-- `π_{σ,τ}` keeps and reflects `≤₁` of `R₁⁺` on `Tᵗ[σ]` (`σ < τ` countable `υ`-points). -/
theorem down_le1R {σ τ x y : Ordinal.{0}} (hσ : UpsPt σ) (hτ : UpsPt τ) (h : Bases σ τ)
    (hx : x ∈ TB τ σ) (hy : y ∈ TB τ σ) (hx1 : x < Om1) :
    le1R x y ↔ le1R (pi σ τ x) (pi σ τ y) := by
  have hlo : ∀ z ∈ TB τ σ, z < τ → z < σ ∧ pi σ τ z = z := fun z hz hzτ =>
    have h' := (TB_inter_lt h hzτ).1 hz; ⟨h', pi_lt h h'⟩
  rcases lt_or_ge x τ with hxτ | hxτ
  · obtain ⟨hxσ, hpx⟩ := hlo x hx hxτ
    rw [hpx]
    rcases lt_or_ge y τ with hyτ | hyτ
    · rw [(hlo y hy hyτ).2]
    · rw [le1R_lt_ups hσ hxσ (h.2.2.1.le.trans hyτ), le1R_lt_ups hσ hxσ (down_ge h hy hyτ)]
  · rcases eq_or_lt_of_le hxτ with e | hxτ'
    · have hpx : pi σ τ x = σ := by rw [← e]; exact (pi_base h).2
      rw [hpx]
      rcases lt_or_ge y τ with hyτ | hyτ
      · obtain ⟨hyσ, hpy⟩ := hlo y hy hyτ
        rw [hpy]
        exact ⟨fun h' => absurd (le1R_le h') (not_le.2 (e ▸ hyτ)),
          fun h' => absurd (le1R_le h') (not_le.2 hyσ)⟩
      · exact ⟨fun _ => hσ.2 _ (down_ge h hy hyτ), fun _ => e ▸ hτ.2 _ hyτ⟩
    · exact st_le1 h hx hxτ' hx1 hy

/-- `π_{σ,τ}⁻¹` keeps and reflects `≤₁` of `R₁⁺` on `Tᵟ ∩ Ω₁`. -/
theorem up_le1R {σ τ x y : Ordinal.{0}} (hσ : UpsPt σ) (hτ : UpsPt τ) (h : Bases σ τ)
    (hx : x ∈ Tset σ) (hy : y ∈ Tset σ) (hx1 : x < Om1) :
    le1R x y ↔ le1R (up σ τ x) (up σ τ y) := by
  obtain ⟨hxT, hpx⟩ := up_spec h hx
  obtain ⟨hyT, hpy⟩ := up_spec h hy
  have := down_le1R hσ hτ h hxT hyT (up_lt_Om1 h hx hx1)
  rw [hpx, hpy] at this
  exact this.symm

end Googology.Trans.PoR.InaccPsi.R2
