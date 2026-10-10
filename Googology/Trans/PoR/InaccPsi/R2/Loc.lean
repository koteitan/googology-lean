import Googology.Trans.PoR.InaccPsi.R2.Basic

/-!
# Lemma LOC

The paper statement, Lemma LOC: "whether a finite set `P` is isominimal depends only on the
restriction of the structure to `[0, max P]` (every copy `Q ≤pw P` has `max Q ≤ max P`)", and
its corollary: if two interpretations agree below `κ` and the core of the first lies below `κ`,
then its core is contained in the core of the second.  For `R₂^C` the hypothesis
`Core(R₂^C) ⊆ κ_C` is [C09] Thm 14.14 (not used here; it is a hypothesis).  No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- `R` and `R'` agree on all pairs in `[0, m]`. -/
def AgreeLe (R R' : Str) (m : Ordinal.{0}) : Prop :=
  ∀ x y, x ≤ m → y ≤ m → (R.le1 x y ↔ R'.le1 x y) ∧ (R.le2 x y ↔ R'.le2 x y)

theorem AgreeLe.symm {R R' : Str} {m : Ordinal.{0}} (h : AgreeLe R R' m) : AgreeLe R' R m :=
  fun x y hx hy => ⟨(h x y hx hy).1.symm, (h x y hx hy).2.symm⟩

/-- Every element of `C ≤pw B` is at most some element of `B`. -/
theorem PwLe.le_some {C B : Finset Ordinal.{0}} (h : PwLe C B) : ∀ c ∈ C, ∃ b ∈ B, c ≤ b := by
  obtain ⟨hc, hle⟩ := h
  intro c hcC
  have hr : c ∈ Set.range (C.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hcC
  obtain ⟨i, rfl⟩ := hr
  exact ⟨_, Finset.orderEmbOfFin_mem B rfl _, hle i⟩

theorem Iso.congr {R R' : Str} {m : Ordinal.{0}} (hA : AgreeLe R R' m) {A B : Set Ordinal.{0}}
    (hAm : ∀ x ∈ A, x ≤ m) (hBm : ∀ x ∈ B, x ≤ m) {g : Ordinal.{0} → Ordinal.{0}}
    (hg : Iso R A B g) : Iso R' A B g := by
  refine ⟨hg.1, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · have h1 := hA x y (hAm x hx) (hAm y hy)
    have h2 := hA (g x) (g y) (hBm _ (hg.1.1.mapsTo hx)) (hBm _ (hg.1.1.mapsTo hy))
    rw [← h1.1, ← h2.1]; exact hg.2.1 x hx y hy
  · have h1 := hA x y (hAm x hx) (hAm y hy)
    have h2 := hA (g x) (g y) (hBm _ (hg.1.1.mapsTo hx)) (hBm _ (hg.1.1.mapsTo hy))
    rw [← h1.2, ← h2.2]; exact hg.2.2 x hx y hy

/-- **Lemma LOC**: if `R` and `R'` agree on `[0, m]` and `B ⊆ [0, m]`, then `B` is isominimal
for `R` iff it is for `R'`. -/
theorem isominimal_congr {R R' : Str} {B : Finset Ordinal.{0}} {m : Ordinal.{0}}
    (hm : ∀ x ∈ B, x ≤ m) (hA : AgreeLe R R' m) : Isominimal R B ↔ Isominimal R' B := by
  have key : ∀ {R R' : Str}, AgreeLe R R' m → Isominimal R B → Isominimal R' B := by
    intro R R' hA hB
    obtain ⟨hBc, hmin⟩ := hB
    refine ⟨hBc, fun C hC ⟨g, hg⟩ hpw => hmin C hC ⟨g, ?_⟩ hpw⟩
    have hCm : ∀ c ∈ (↑C : Set Ordinal.{0}), c ≤ m := fun c hc => by
      obtain ⟨b, hb, hcb⟩ := hpw.le_some c hc
      exact hcb.trans (hm b hb)
    exact hg.congr hA.symm (fun x hx => hm x hx) hCm
  exact ⟨key hA, key hA.symm⟩

/-- **Lemma LOC, corollary**: if `Core(R) ⊆ κ` and `R`, `R'` agree on all pairs below `κ`, then
`Core(R) ⊆ Core(R')`. -/
theorem core_subset_of_agree {R R' : Str} {κ : Ordinal.{0}} (hcore : Core R ⊆ Set.Iio κ)
    (hA : ∀ x y, x < κ → y < κ → (R.le1 x y ↔ R'.le1 x y) ∧ (R.le2 x y ↔ R'.le2 x y)) :
    Core R ⊆ Core R' := by
  rintro x ⟨B, hB, hxB⟩
  have hBk : ∀ b ∈ B, b < κ := fun b hb => hcore ⟨B, hB, hb⟩
  have hne : B.Nonempty := ⟨x, hxB⟩
  have hmk : B.max' hne < κ := hBk _ (B.max'_mem hne)
  refine ⟨B, (isominimal_congr (m := B.max' hne) (fun b hb => B.le_max' b hb) ?_).1 hB, hxB⟩
  intro u v hu hv
  exact hA u v (lt_of_le_of_lt hu hmk) (lt_of_le_of_lt hv hmk)

end Googology.Trans.PoR.InaccPsi.R2
