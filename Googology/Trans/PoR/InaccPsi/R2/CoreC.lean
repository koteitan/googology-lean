import Googology.Trans.PoR.InaccPsi.R2.Loc
import Googology.Trans.PoR.InaccPsi.R2.CitedC09

/-!
# The core of `R₂^C` after [C09] Theorems 14.10 and 14.14

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

From the two cited theorems of `R2.CitedC09`:

* `Iso.symm_exists`, `Iso.toCov`: an isomorphism has an inverse isomorphism; it is a covering.
* `pwLe_le`: if a strictly increasing bijection `h : B → Q` of finite sets has `B ≤pw Q`, then
  `b ≤ h(b)` for every `b ∈ B`.
* `isominimal_least`: an isominimal set of `R₂^C` is pointwise below every closed covering of it
  ([C09] Thm 14.10 (2), for `P*` = the set itself; this is the step "an isominimal set is its own
  least realization" of the paper proof of Theorem CP).
* `core_eq`, `core_downward`: the core is `Iio κ` for the least `κ ≤₁ ∞`, or `ORD`; in particular an
  initial segment ([C09] Thm 14.14).
* `exists_reach_of_core`: a point of the core has a reach `lh(x) = max{γ | x ≤₁ γ}`.
* `core_subset_of_agree_C`: LOC's corollary without its hypothesis on the core: if `R'` agrees with
  `R₂^C` below the least `κ ≤₁ ∞`, then `Core(R₂^C) ⊆ Core(R')`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

theorem Iso.toCov {R : Str} {A B : Set Ordinal.{0}} {g : Ordinal.{0} → Ordinal.{0}}
    (hg : Iso R A B g) : Cov R R A B g :=
  ⟨hg.1, fun x hx y hy h => (hg.2.1 x hx y hy).1 h, fun x hx y hy h => (hg.2.2 x hx y hy).1 h⟩

theorem Iso.symm_exists {R : Str} {A B : Set Ordinal.{0}} {g : Ordinal.{0} → Ordinal.{0}}
    (hg : Iso R A B g) : ∃ g', Iso R B A g' := by
  classical
  have hinv : Set.InvOn (Function.invFunOn g A) g A B := hg.1.1.invOn_invFunOn
  have hbij : Set.BijOn (Function.invFunOn g A) B A := hg.1.1.symm hinv.symm
  set g' := Function.invFunOn g A
  have hgg : ∀ y ∈ B, g (g' y) = y := fun y hy => hinv.2 hy
  refine ⟨g', ⟨hbij, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← hg.1.2.1.lt_iff_lt (hbij.mapsTo hx) (hbij.mapsTo hy), hgg x hx, hgg y hy]
    exact hxy
  · intro x hx y hy z hz
    rw [hg.1.2.2 _ (hbij.mapsTo hx) _ (hbij.mapsTo hy) _ (hbij.mapsTo hz), hgg x hx, hgg y hy,
      hgg z hz]
  · intro x hx y hy
    rw [hg.2.1 _ (hbij.mapsTo hx) _ (hbij.mapsTo hy), hgg x hx, hgg y hy]
  · intro x hx y hy
    rw [hg.2.2 _ (hbij.mapsTo hx) _ (hbij.mapsTo hy), hgg x hx, hgg y hy]

/-- For a strictly increasing bijection `h` of `B` onto `Q`, the `i`-th element of `Q` is `h` of the
`i`-th element of `B`. -/
theorem orderEmbOfFin_map {B Q : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hb : Set.BijOn h ↑B ↑Q) (hm : StrictMonoOn h ↑B) (hc : B.card = Q.card) (i : Fin B.card) :
    Q.orderEmbOfFin rfl (Fin.cast hc i) = h (B.orderEmbOfFin rfl i) := by
  set F : Fin Q.card → Ordinal.{0} := fun j => h (B.orderEmbOfFin rfl (Fin.cast hc.symm j))
  have hF : F = Q.orderEmbOfFin rfl := by
    refine Finset.orderEmbOfFin_unique rfl (fun j => hb.mapsTo (Finset.orderEmbOfFin_mem B rfl _))
      ?_
    intro j k hjk
    exact hm (Finset.orderEmbOfFin_mem B rfl _) (Finset.orderEmbOfFin_mem B rfl _)
      ((B.orderEmbOfFin rfl).strictMono (show Fin.cast hc.symm j < Fin.cast hc.symm k from hjk))
  have := congrFun hF (Fin.cast hc i)
  have hi : Fin.cast hc.symm (Fin.cast hc i) = i := Fin.ext rfl
  rw [← this]
  show h (B.orderEmbOfFin rfl (Fin.cast hc.symm (Fin.cast hc i))) = _
  rw [hi]

/-- If `B ≤pw Q` and `h` is a strictly increasing bijection of `B` onto `Q`, then `b ≤ h(b)`. -/
theorem pwLe_le {B Q : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hb : Set.BijOn h ↑B ↑Q) (hm : StrictMonoOn h ↑B) (hpw : PwLe B Q) : ∀ b ∈ B, b ≤ h b := by
  obtain ⟨hc, hle⟩ := hpw
  intro b hbB
  have hr : b ∈ Set.range (B.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hbB
  obtain ⟨i, rfl⟩ := hr
  have := hle i
  rwa [orderEmbOfFin_map hb hm hc i] at this

/-- An isominimal set of `R₂^C` is pointwise below every closed covering of it ([C09] Thm 14.10 (2)
and Def 2.6). -/
theorem isominimal_least {B : Finset Ordinal.{0}} (hB : Isominimal R2C B) {Q : Finset Ordinal.{0}}
    (hQ : Closed ↑Q) (hcov : ∃ h, Cov R2C R2C ↑B ↑Q h) : PwLe B Q := by
  obtain ⟨Ps, ⟨g, hg⟩, hmin, hPs⟩ := C09_thm14_10 hB.1
  obtain ⟨g', hg'⟩ := hg.symm_exists
  have hPsB : Ps = B := hB.2 Ps hPs.1 ⟨g, hg⟩ (hmin B hB.1 ⟨g', hg'.toCov⟩)
  subst hPsB
  exact hmin Q hQ hcov

theorem exists_isLeast_leInfC (h : ∃ κ, LeInfC κ) : ∃ κ, IsLeast {k | LeInfC k} κ :=
  ⟨sInf {k | LeInfC k}, csInf_mem h, fun _ hk => csInf_le' hk⟩

/-- [C09] Thm 14.14: the core of `R₂^C` is an initial segment. -/
theorem core_downward {x y : Ordinal.{0}} (hx : x ∈ Core R2C) (hyx : y ≤ x) : y ∈ Core R2C := by
  by_cases h : ∃ κ, LeInfC κ
  · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC h
    have hc := C09_thm14_14.1 κ hκ
    rw [hc] at hx ⊢
    exact lt_of_le_of_lt hyx hx
  · rw [C09_thm14_14.2 h]; trivial

/-- A point of the core of `R₂^C` has a reach ([C09] Thm 14.14 with `exists_reach`). -/
theorem exists_reach_of_core {x : Ordinal.{0}} (hx : x ∈ Core R2C) : ∃ r, IsReach R2C x r := by
  by_contra hno
  have hinf : LeInfC x := fun g hg => ltInf_iff.1 hno g hg
  obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC ⟨x, hinf⟩
  have hc := C09_thm14_14.1 κ hκ
  rw [hc] at hx
  exact absurd (hκ.2 hinf) (not_le.2 hx)

/-- **LOC's corollary for `R₂^C`, with no hypothesis on the core**: if `R'` agrees with `R₂^C` on all
pairs below the least `κ ≤₁ ∞`, then `Core(R₂^C) ⊆ Core(R')`. -/
theorem core_subset_of_agree_C {R' : Str} {κ : Ordinal.{0}} (hκ : IsLeast {k | LeInfC k} κ)
    (hA : ∀ x y, x < κ → y < κ → (R2C.le1 x y ↔ R'.le1 x y) ∧ (R2C.le2 x y ↔ R'.le2 x y)) :
    Core R2C ⊆ Core R' :=
  core_subset_of_agree (by rw [C09_thm14_14.1 κ hκ]) hA

end Googology.Trans.PoR.InaccPsi.R2
