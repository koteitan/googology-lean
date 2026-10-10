import Googology.Trans.PoR.InaccPsi.R2.Arith
import Googology.Trans.PoR.InaccPsi.R2.CoreC

/-!
# Lemma MOVE and Theorem CP in `R₂^C`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

The project's Lemma MOVE and Theorem CP (the covering route to `o_k = ω` in `R₂^C`):

* `move` (**Lemma MOVE**): let `Z` be a finite closed set, `u ∈ Z` indecomposable, `α` indecomposable
  with `Z ∩ u < α < u`, `v* = max{v ∈ Z | u ≤₁ v}`.  The closed embedding `f⁺ = ext f` of `Z` that
  sends `u` to `α` and fixes every other indecomposable ([C09] Lemma 4.5) satisfies `f⁺ ≤ id`, and it
  is a covering of `Z` onto the closed set `f⁺[Z]` if (M1) `α ≤₁ v*` and (M2) no `v ∈ Z` has
  `u <₂ v`.  No axiom.
* `cp_star` (**Theorem CP\***): if `u` is indecomposable, not a `<₂`-left end, and `Z` is an
  isominimal set containing `u`, then `Pred₁(v*) ∩ u` is bounded in `u`.  Uses [C09] Thm 14.10.
* `cp` (**Theorem CP**): if `u` is indecomposable, lies in the core of `R₂^C`, and
  `{α < u | α ≤₁ lh(u)}` is cofinal in `u`, then `u` is a `<₂`-left end.  Uses [C09] Thm 14.10, 14.14.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The map of Lemma MOVE on indecomposables: `u ↦ α`, every other point fixed. -/
noncomputable def moveF (u α : Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} := if x = u then α else x

/-- The closed embedding of Lemma MOVE ([C09] Lemma 4.5). -/
noncomputable def moveMap (u α : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ext (moveF u α)

section Move

variable {Z : Finset Ordinal.{0}} {u α : Ordinal.{0}}

theorem moveF_strictMonoOn (hαu : α < u) (hX : ∀ x ∈ Z, x < u → x < α) :
    StrictMonoOn (moveF u α) (IndecIn ↑Z) := by
  intro x hx y hy hxy
  unfold moveF
  by_cases hxu : x = u <;> by_cases hyu : y = u
  · subst hxu; subst hyu; exact absurd hxy (lt_irrefl _)
  · rw [if_pos hxu, if_neg hyu]; subst hxu; exact hαu.trans hxy
  · rw [if_neg hxu, if_pos hyu]; subst hyu; exact hX x hx.1 hxy
  · rw [if_neg hxu, if_neg hyu]; exact hxy

theorem moveF_indec (hαI : Indec α) : ∀ a ∈ IndecIn (↑Z : Set Ordinal.{0}), Indec (moveF u α a) := by
  intro a ha
  unfold moveF
  split_ifs
  · exact hαI
  · exact ha.2

theorem moveMap_indec_ne {x : Ordinal.{0}} (hxI : Indec x) (hxu : x ≠ u) : moveMap u α x = x := by
  unfold moveMap; rw [ext_indec hxI]; simp [moveF, hxu]

theorem moveMap_u (huI : Indec u) : moveMap u α u = α := by
  unfold moveMap; rw [ext_indec huI]; simp [moveF]

/-- **Lemma MOVE.** -/
theorem move (hZ : Closed ↑Z) (hu : u ∈ Z) (huI : Indec u) (hαI : Indec α) (hαu : α < u)
    (hX : ∀ x ∈ Z, x < u → x < α) {vs : Ordinal.{0}} (hvs1 : le1 u vs)
    (hvsmax : ∀ v ∈ Z, le1 u v → v ≤ vs) (M1 : le1 α vs) (M2 : ∀ v ∈ Z, u < v → ¬ le2 u v) :
    Cov R2C R2C ↑Z (moveMap u α '' ↑Z) (moveMap u α) ∧ Closed (moveMap u α '' ↑Z) ∧
      moveMap u α u = α ∧ ∀ z ∈ Z, moveMap u α z ≤ z := by
  have hf := moveF_strictMonoOn (Z := Z) hαu hX
  have hfI := moveF_indec (Z := Z) (u := u) hαI
  have hiso : ArithIso ↑Z (moveMap u α '' ↑Z) (moveMap u α) := ext_arithIso hZ hf hfI
  have hcl : Closed (moveMap u α '' ↑Z) := ext_closed hZ hf hfI
  have hgu : moveMap u α u = α := moveMap_u huI
  have hle : ∀ z ∈ Z, moveMap u α z ≤ z := by
    intro z hz
    refine le_of_le_on_indec hZ hiso (Cov.id R2C ↑Z).1 (fun a _ hI => ?_) z hz
    by_cases hau : a = u
    · subst hau; rw [hgu]; exact hαu.le
    · rw [moveMap_indec_ne hI hau]; rfl
  have hlt : ∀ x ∈ Z, ∀ y ∈ Z, x < y → moveMap u α x < moveMap u α y :=
    fun x hx y hy hxy => (ext_lt_iff hZ hf hfI hx hy).2 hxy
  refine ⟨⟨hiso, ?_, ?_⟩, hcl, hgu, hle⟩
  · intro x hx y hy hxy
    change le1 x y at hxy
    change le1 (moveMap u α x) (moveMap u α y)
    rcases eq_or_lt_of_le (le1_le hxy) with rfl | hxy'
    · exact le1_refl _
    have hxI : Indec x := indec_of_lt1 hxy hxy'
    have hgxy := hlt x hx y hy hxy'
    have hgy := hle y hy
    by_cases hxu : x = u
    · subst hxu
      rw [hgu] at hgxy ⊢
      exact le1_of_le_of_le1 hgxy.le (hgy.trans (hvsmax y hy hxy)) M1
    · rw [moveMap_indec_ne hxI hxu] at hgxy ⊢
      exact le1_of_le_of_le1 hgxy.le hgy hxy
  · intro x hx y hy hxy
    change le2 x y at hxy
    change le2 (moveMap u α x) (moveMap u α y)
    rcases eq_or_lt_of_le (le2_le hxy) with rfl | hxy'
    · exact le2_refl _
    have hxI : Indec x := indec_of_lt1 (le2_le1 hxy) hxy'
    have hyI : Indec y := (indec_of_lt2_right hxy hxy').1
    have hxu : x ≠ u := by
      rintro rfl; exact M2 y hy hxy' hxy
    rw [moveMap_indec_ne hxI hxu]
    by_cases hyu : y = u
    · subst hyu
      rw [hgu]
      have hxα : x < α := hX x hx hxy'
      have hαu1 : le1 α y := le1_of_le_of_le1 hαu.le (le1_le hvs1) M1
      exact le2_of_le1 hxα.le hαu.le hxy hαu1
    · rw [moveMap_indec_ne hyI hyu]; exact hxy

end Move

/-- **Theorem CP\*.** Let `u` be indecomposable and not a `<₂`-left end, `Z` an isominimal set of
`R₂^C` with `u ∈ Z`, and `v* = max{v ∈ Z | u ≤₁ v}`.  Then `Pred₁(v*) ∩ u` is bounded in `u`. -/
theorem cp_star {u : Ordinal.{0}} (huI : Indec u) (hno2 : ∀ v, u < v → ¬ le2 u v)
    {Z : Finset Ordinal.{0}} (hZ : Isominimal R2C Z) (huZ : u ∈ Z) {vs : Ordinal.{0}}
    (hvs1 : le1 u vs) (hvsmax : ∀ v ∈ Z, le1 u v → v ≤ vs) :
    ∃ γ < u, ∀ α, γ < α → α < u → ¬ le1 α vs := by
  classical
  set γ := (Z.filter (· < u)).sup id with hγ
  have hγu : γ < u := by
    rw [hγ, Finset.sup_lt_iff huI.pos]
    intro b hb
    exact (Finset.mem_filter.1 hb).2
  have hXγ : ∀ x ∈ Z, x < u → x ≤ γ := fun x hx hxu =>
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hx, hxu⟩)
  refine ⟨γ, hγu, fun α hγα hαu h1 => ?_⟩
  have huvs : u ≤ vs := le1_le hvs1
  have hαI : Indec α := indec_of_lt1 h1 (lt_of_lt_of_le hαu huvs)
  obtain ⟨hcov, hcl, hgu, -⟩ := move hZ.1 huZ huI hαI hαu
    (fun x hx hxu => lt_of_le_of_lt (hXγ x hx hxu) hγα) hvs1 hvsmax h1
    (fun v _ huv => hno2 v huv)
  have hQ : (↑(Z.image (moveMap u α)) : Set Ordinal.{0}) = moveMap u α '' ↑Z := Finset.coe_image
  have hpw := isominimal_least hZ (Q := Z.image (moveMap u α)) (by rw [hQ]; exact hcl)
    ⟨moveMap u α, by rw [hQ]; exact hcov⟩
  have hb : Set.BijOn (moveMap u α) ↑Z ↑(Z.image (moveMap u α)) := by rw [hQ]; exact hcov.1.1
  have := pwLe_le hb hcov.1.2.1 hpw u huZ
  rw [hgu] at this
  exact absurd hαu (not_lt.2 this)

/-- **Theorem CP.** Let `u` be indecomposable and in the core of `R₂^C`, with reach `r = lh(u)`.  If
`{α < u | α ≤₁ r}` is cofinal in `u`, then `u` is a `<₂`-left end. -/
theorem cp {u r : Ordinal.{0}} (huI : Indec u) (hcore : u ∈ Core R2C) (hr : IsReach R2C u r)
    (hcof : ∀ γ < u, ∃ α, γ < α ∧ α < u ∧ le1 α r) : ∃ v, u < v ∧ le2 u v := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  obtain ⟨Z, hZ, huZ⟩ := hcore
  set S := Z.filter (le1 u ·) with hS
  have huS : u ∈ S := Finset.mem_filter.2 ⟨huZ, le1_refl u⟩
  set vs := S.max' ⟨u, huS⟩ with hvs
  have hvsS : vs ∈ S := S.max'_mem _
  have hvs1 : le1 u vs := (Finset.mem_filter.1 hvsS).2
  have hvsmax : ∀ v ∈ Z, le1 u v → v ≤ vs := fun v hv h => S.le_max' v (Finset.mem_filter.2 ⟨hv, h⟩)
  have hvsr : vs ≤ r := hr.2 vs hvs1
  obtain ⟨γ, hγu, hγ⟩ := cp_star huI (fun v huv h => hno v huv h) hZ huZ hvs1 hvsmax
  obtain ⟨α, hγα, hαu, hα⟩ := hcof γ hγu
  exact hγ α hγα hαu (le1_of_le_of_le1 (hαu.le.trans (le1_le hvs1)) hvsr hα)

/-- **Theorem CP** with the reach from the core ([C09] Thm 14.14). -/
theorem cp' {u : Ordinal.{0}} (huI : Indec u) (hcore : u ∈ Core R2C) :
    ∃ r, IsReach R2C u r ∧ ((∀ γ < u, ∃ α, γ < α ∧ α < u ∧ le1 α r) → ∃ v, u < v ∧ le2 u v) := by
  obtain ⟨r, hr⟩ := exists_reach_of_core hcore
  exact ⟨r, hr, cp huI hcore hr⟩

end Googology.Trans.PoR.InaccPsi.R2
