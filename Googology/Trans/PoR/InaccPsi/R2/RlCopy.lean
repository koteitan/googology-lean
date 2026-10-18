import Googology.Trans.PoR.InaccPsi.R2.CvCopy

/-!
# The copying principle with configuration-dependent domains

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`Cv.cvLe1_of_maps` asks for maps on the whole interval `[a, b)`; such maps do not exist once
`a + a < b` (`Rl.rlMaps_le`).  Here the maps are indexed by an arbitrary type `ι`, and the map `D_i`
is only defined (and only has to be increasing, additive, ...) on `[0, c_i) ∪ E_i` with `E_i ⊆ [a, b)`;
what is asked is that **every finite closed configuration** `X ∪ Y` (`X < a ≤ Y < b`) has an index
`i` with `X < c_i` and `Y ⊆ E_i`.  This is exactly what the proof of `Cv.cvLe1_of_maps` uses, from
[C09] Def 5.3–5.4 alone (`Cv.cvCov_inner`):

* `rlLe1_of_maps` (**the copying principle with domains**);
* `rlLe1_of_maps_seq`: the same with `ι = ℕ`, `c` monotone and cofinal in `a`, and every finite
  `Y ⊆ [a, b)` eventually in `E_k` (closedness not needed);
* `rlLe1_of_maps_full`: `E_i = [a, b)` gives back `Cv.cvLe1_of_maps` (so nothing is lost).

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rl

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cv

/-- The domain `[0, c) ∪ E` of a copy map. -/
def RlDom (c : Ordinal.{0}) (E : Set Ordinal.{0}) : Set Ordinal.{0} := {x | x < c ∨ x ∈ E}

/-- **The copying principle with configuration-dependent domains.** -/
theorem rlLe1_of_maps {ι : Type} {a b : Ordinal.{0}} {c : ι → Ordinal.{0}}
    {E : ι → Set Ordinal.{0}} {D : ι → Ordinal.{0} → Ordinal.{0}}
    (hab : a ≤ b) (hca : ∀ i, c i < a)
    (hE : ∀ i, ∀ y ∈ E i, a ≤ y ∧ y < b)
    (hex : ∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
      Closed ↑(X ∪ Y) → ∃ i, (∀ x ∈ X, x < c i) ∧ ∀ y ∈ Y, y ∈ E i)
    (hDm : ∀ i, StrictMonoOn (D i) (E i))
    (hDadd : ∀ i, ∀ x ∈ RlDom (c i) (E i), ∀ y ∈ RlDom (c i) (E i), ∀ z ∈ RlDom (c i) (E i),
      (x + y = z ↔ D i x + D i y = D i z))
    (hDdec : ∀ i, ∀ y ∈ E i, DecompR0 (D i y) → DecompR0 y)
    (hDfix : ∀ i, ∀ x < c i, D i x = x)
    (hDwin : ∀ i, ∀ y ∈ E i, c i ≤ D i y ∧ D i y < a)
    (hD1 : ∀ i, ∀ y ∈ E i, ∀ y' ∈ E i, y < y' → le1 y y' → le1 (D i y) (D i y'))
    (hD2 : ∀ i, ∀ y ∈ E i, ∀ y' ∈ E i, y < y' → le2 y y' → le2 (D i y) (D i y'))
    (hD2X : ∀ i, ∀ x < c i, ∀ y ∈ E i, le2 x y → le2 x (D i y)) :
    le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨k, hXk, hYk⟩ := hex X Y hX hY hXY
  have ha0 : 0 < a := lt_of_le_of_lt zero_le (hca k)
  have hW : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), u ∈ RlDom (c k) (E k) := by
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · exact Or.inl (hXk u hu)
    · exact Or.inr (hYk u hu)
  have hsm : StrictMonoOn (D k) (RlDom (c k) (E k)) := by
    intro u hu v hv huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hDfix k u hu, hDfix k v hv]; exact huv
    · rw [hDfix k u hu]; exact hu.trans_le (hDwin k v hv).1
    · exact absurd (huv.trans (hv.trans (hca k))) (not_lt.2 (hE k u hu).1)
    · exact hDm k hu hv huv
  have hfixX : ∀ x ∈ X, D k x = x := fun x hx => hDfix k x (hXk x hx)
  have himg := Qq.qqImage_fix (Y := Y) hfixX
  have hiso : ArithIso ↑(X ∪ Y) (D k '' ↑(X ∪ Y)) (D k) :=
    ⟨(hsm.injOn.mono hW).bijOn_image, hsm.mono hW,
      fun x hx y hy z hz => hDadd k x (hW x hx) y (hW y hy) z (hW z hz)⟩
  have hcl : Closed (D k '' ↑(X ∪ Y)) := by
    rintro z ⟨s, hs, rfl⟩ hdz
    have hsW := hW s hs
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hs) with hsX | hsY
    · have hsk := hXk s hsX
      rw [hDfix k s hsk] at hdz ⊢
      rcases hXY s hs hdz with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact Or.inl h0
      · exact Or.inr ⟨p, ⟨p, hp, hDfix k p (hps.trans hsk)⟩, q, ⟨q, hq, hDfix k q (hqs.trans hsk)⟩,
          hps, hqs, hpq⟩
    · have hdec := hDdec k s (hYk s hsY) hdz
      rcases hXY s hs hdec with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact absurd (h0 ▸ (hY s hsY).1) (not_le.2 ha0)
      · exact Or.inr ⟨D k p, ⟨p, hp, rfl⟩, D k q, ⟨q, hq, rfl⟩, hsm (hW p hp) hsW hps,
          hsm (hW q hq) hsW hqs, (hDadd k p (hW p hp) q (hW q hq) s hsW).1 hpq⟩
  have hYt : ∀ y ∈ Y.image (D k), y < a := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (hDwin k y (hYk y hy)).2
  have hXYt : ∀ x ∈ X, ∀ y ∈ Y.image (D k), x < y := by
    intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (hXk x hx).trans_le (hDwin k y (hYk y hy)).1
  refine ⟨Y.image (D k), hYt, hXYt, by rw [himg]; exact hcl, D k, ?_⟩
  rw [← himg] at hiso
  refine cvCov_inner hX (fun y hy => (hY y hy).1) hYt hXYt hiso ?_ ?_ ?_
  · intro y hy y' hy' h1
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · exact hD1 k y (hYk y hy) y' (hYk y' hy') hlt h1
    · exact le1_refl _
    · exact absurd (le1_le h1) (not_le.2 hgt)
  · intro y hy y' hy' h2
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · exact hD2 k y (hYk y hy) y' (hYk y' hy') hlt h2
    · exact le2_refl _
    · exact absurd (le2_le h2) (not_le.2 hgt)
  · intro x hx y hy h2
    exact hD2X k x (hXk x hx) y (hYk y hy) h2

/-- **Exhaustion from a monotone cofinal sequence** `c_k` and domains `E_k` that eventually contain
every finite `Y ⊆ [a, b)`. -/
theorem rlEx_seq {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {E : ℕ → Set Ordinal.{0}}
    (hcm : Monotone c) (hcof : ∀ γ < a, ∃ k, γ < c k)
    (hexF : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∃ K, ∀ k, K ≤ k → ∀ y ∈ Y, y ∈ E k) :
    ∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
      Closed ↑(X ∪ Y) → ∃ k, (∀ x ∈ X, x < c k) ∧ ∀ y ∈ Y, y ∈ E k := by
  intro X Y hX hY _
  obtain ⟨k1, hk1⟩ : ∃ k, ∀ x ∈ X, x < c k := by
    rcases X.eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨k, hk⟩ := hcof _ (hX _ (X.max'_mem hne))
      exact ⟨k, fun x hx => (X.le_max' x hx).trans_lt hk⟩
  obtain ⟨K, hK⟩ := hexF Y hY
  refine ⟨max k1 K, fun x hx => (hk1 x hx).trans_le (hcm (le_max_left _ _)), ?_⟩
  exact hK _ (le_max_right _ _)

/-- **The copying principle with eventual domains** (`ι = ℕ`). -/
theorem rlLe1_of_maps_seq {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {E : ℕ → Set Ordinal.{0}}
    {D : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hab : a ≤ b) (hca : ∀ k, c k < a) (hcm : Monotone c) (hcof : ∀ γ < a, ∃ k, γ < c k)
    (hE : ∀ k, ∀ y ∈ E k, a ≤ y ∧ y < b)
    (hexF : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∃ K, ∀ k, K ≤ k → ∀ y ∈ Y, y ∈ E k)
    (hDm : ∀ k, StrictMonoOn (D k) (E k))
    (hDadd : ∀ k, ∀ x ∈ RlDom (c k) (E k), ∀ y ∈ RlDom (c k) (E k), ∀ z ∈ RlDom (c k) (E k),
      (x + y = z ↔ D k x + D k y = D k z))
    (hDdec : ∀ k, ∀ y ∈ E k, DecompR0 (D k y) → DecompR0 y)
    (hDfix : ∀ k, ∀ x < c k, D k x = x)
    (hDwin : ∀ k, ∀ y ∈ E k, c k ≤ D k y ∧ D k y < a)
    (hD1 : ∀ k, ∀ y ∈ E k, ∀ y' ∈ E k, y < y' → le1 y y' → le1 (D k y) (D k y'))
    (hD2 : ∀ k, ∀ y ∈ E k, ∀ y' ∈ E k, y < y' → le2 y y' → le2 (D k y) (D k y'))
    (hD2X : ∀ k, ∀ x < c k, ∀ y ∈ E k, le2 x y → le2 x (D k y)) :
    le1 a b :=
  rlLe1_of_maps hab hca hE (rlEx_seq hcm hcof hexF) hDm hDadd hDdec hDfix hDwin hD1 hD2 hD2X

/-- **The full domains give back `Cv.cvLe1_of_maps`.** -/
theorem rlLe1_of_maps_full {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {D : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hab : a ≤ b) (hca : ∀ k, c k < a) (hcof : ∀ γ < a, ∃ k, γ < c k)
    (hDm : ∀ k, StrictMonoOn (D k) (Ico a b))
    (hDadd : ∀ k, ∀ x ∈ CvDom (c k) a b, ∀ y ∈ CvDom (c k) a b, ∀ z ∈ CvDom (c k) a b,
      (x + y = z ↔ D k x + D k y = D k z))
    (hDdec : ∀ k, ∀ y, a ≤ y → y < b → DecompR0 (D k y) → DecompR0 y)
    (hDfix : ∀ k, ∀ x < c k, D k x = x)
    (hDwin : ∀ k, ∀ y, a ≤ y → y < b → c k ≤ D k y ∧ D k y < a)
    (hD1 : ∀ k, ∀ y y', a ≤ y → y < y' → y' < b → le1 y y' → le1 (D k y) (D k y'))
    (hD2 : ∀ k, ∀ y y', a ≤ y → y < y' → y' < b → le2 y y' → le2 (D k y) (D k y'))
    (hD2X : ∀ k, ∀ x < c k, ∀ y, a ≤ y → y < b → le2 x y → le2 x (D k y)) :
    le1 a b := by
  refine rlLe1_of_maps (E := fun _ => Ico a b) hab hca (fun _ y hy => hy) ?_ hDm
    (fun k x hx y hy z hz => hDadd k x hx y hy z hz) (fun k y hy => hDdec k y hy.1 hy.2) hDfix
    (fun k y hy => hDwin k y hy.1 hy.2)
    (fun k y hy y' hy' h => hD1 k y y' hy.1 h hy'.2)
    (fun k y hy y' hy' h => hD2 k y y' hy.1 h hy'.2)
    (fun k x hx y hy => hD2X k x hx y hy.1 hy.2)
  intro X Y hX hY _
  obtain ⟨k, hk⟩ : ∃ k, ∀ x ∈ X, x < c k := by
    rcases X.eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨k, hk⟩ := hcof _ (hX _ (X.max'_mem hne))
      exact ⟨k, fun x hx => (X.le_max' x hx).trans_lt hk⟩
  exact ⟨k, hk, fun y hy => hY y hy⟩

end Googology.Trans.PoR.InaccPsi.R2.Rl
