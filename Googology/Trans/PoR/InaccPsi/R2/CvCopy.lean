import Googology.Trans.PoR.InaccPsi.R2.QqEmb

/-!
# The copying principle for `≤₁` in `R₂^C`: copies of the configurations above `a`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a ≤₁ b` in `R₂^C` is defined ([C09] Def 5.3, Def 5.4; `R2.Defs`) by coverings: every finite
`X ⊆ (−∞, a)` and `Y ⊆ [a, b)` with `X ∪ Y` closed has a finite `Ỹ ⊆ (−∞, a)`, `X < Ỹ`, `X ∪ Ỹ`
closed, and a covering of `X ∪ Y` onto `X ∪ Ỹ`.  This file proves, from the definition alone (no
cited theorem), that only the relations inside `Y` and the `≤₂`-pairs from `X` into `Y` have to be
copied:

* `cvCov_inner` (**the inner covering lemma**): an arithmetic isomorphism `h` of `X ∪ Y` onto
  `X ∪ Ỹ` (`X < a ≤ Y`, `X < Ỹ < a`) is a covering of `R₂^C` as soon as it keeps `≤₁` and `≤₂` on
  the pairs of `Y` and keeps the `≤₂`-pairs `(x, y)`, `x ∈ X`, `y ∈ Y`.  The pairs `(x, y)` of `≤₁`
  are kept by the interval property (`x ≤ h(y) ≤ y`, [C09] Lemma 5.5), `h` fixes `X`, and no pair
  goes from `Y` down to `X`.
* `cvLe1_of_maps` (**the copying principle with maps**): if `c_k < a` is cofinal in `a` and the maps
  `D_k` on `[0, c_k) ∪ [a, b)` fix `[0, c_k)`, send `[a, b)` strictly increasingly into `[c_k, a)`,
  keep and reflect the graph of `+` there, reflect decomposability on `[a, b)`, keep `≤₁`, `≤₂` on
  the pairs of `[a, b)`, and keep the `≤₂`-pairs from `[0, c_k)` into `[a, b)`, then `a ≤₁ b`.
  (The dual of the first clause of SHIFT, `Cx.cxShift_le1`, where the maps go up and must reflect
  the relations; here they go down and need only keep them.)

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cv

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- The domain `[0, c) ∪ [a, b)` of a copy map at stage `c`. -/
def CvDom (c a b : Ordinal.{0}) : Set Ordinal.{0} := {x | x < c ∨ (a ≤ x ∧ x < b)}

/-- **The inner covering lemma**: an arithmetic isomorphism of `X ∪ Y` onto `X ∪ Ỹ`, with
`X < a ≤ Y` and `X < Ỹ < a`, is a covering of `R₂^C` if it keeps `≤₁`, `≤₂` on the pairs of `Y` and
the `≤₂`-pairs from `X` into `Y`. -/
theorem cvCov_inner {a : Ordinal.{0}} {X Y Yt : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hX : ∀ x ∈ X, x < a) (hY : ∀ y ∈ Y, a ≤ y) (hYt : ∀ y ∈ Yt, y < a)
    (hXYt : ∀ x ∈ X, ∀ y ∈ Yt, x < y)
    (hiso : ArithIso ↑(X ∪ Y) ↑(X ∪ Yt) h)
    (h1 : ∀ y ∈ Y, ∀ y' ∈ Y, le1 y y' → le1 (h y) (h y'))
    (h2 : ∀ y ∈ Y, ∀ y' ∈ Y, le2 y y' → le2 (h y) (h y'))
    (h2X : ∀ x ∈ X, ∀ y ∈ Y, le2 x y → le2 x (h y)) :
    Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) h := by
  classical
  have hfix : ∀ x ∈ (↑X : Set Ordinal.{0}), h x = x := by
    refine fix_initial hiso.1 hiso.2.1 (by simp) (by simp) ?_ ?_
    · intro u hu hun s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
      · exact absurd hu hun
      · exact lt_of_lt_of_le (hX s hs) (hY u hu)
    · intro u hu hun s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
      · exact absurd hu hun
      · exact hXYt s hs u hu
  have hYmap : ∀ y ∈ Y, h y ∈ Yt := by
    intro y hy
    have hmem : h y ∈ (↑(X ∪ Yt) : Set Ordinal.{0}) := hiso.1.mapsTo (by simp [hy])
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hmem) with hm | hm
    · exfalso
      have h22 : h (h y) = h y := hfix _ hm
      have := hiso.1.injOn (by simp [hm]) (by simp [hy]) h22
      exact absurd (this ▸ hX _ hm) (not_lt.2 (hY y hy))
    · exact hm
  refine ⟨hiso, ?_, ?_⟩
  · intro u hu v hv huv
    change le1 u v at huv
    change le1 (h u) (h v)
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu <;>
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hv) with hv | hv
    · rw [hfix u hu, hfix v hv]; exact huv
    · rw [hfix u hu]
      have hyt := hYmap v hv
      exact le1_of_le_of_le1 (hXYt u hu _ hyt).le ((hYt _ hyt).le.trans (hY v hv)) huv
    · exact absurd ((le1_le huv).trans_lt (hX v hv)) (not_lt.2 (hY u hu))
    · exact h1 u hu v hv huv
  · intro u hu v hv huv
    change le2 u v at huv
    change le2 (h u) (h v)
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu <;>
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hv) with hv | hv
    · rw [hfix u hu, hfix v hv]; exact huv
    · rw [hfix u hu]; exact h2X u hu v hv huv
    · exact absurd ((le2_le huv).trans_lt (hX v hv)) (not_lt.2 (hY u hu))
    · exact h2 u hu v hv huv

/-- **The copying principle with maps**: maps `D_k` that fix `[0, c_k)` (`c_k < a` cofinal in `a`),
send `[a, b)` strictly increasingly into `[c_k, a)`, keep and reflect `+` on `[0, c_k) ∪ [a, b)`,
reflect decomposability on `[a, b)`, keep `≤₁` and `≤₂` on the pairs of `[a, b)`, and keep the
`≤₂`-pairs from `[0, c_k)` into `[a, b)`, give `a ≤₁ b`. -/
theorem cvLe1_of_maps {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {D : ℕ → Ordinal.{0} → Ordinal.{0}}
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
  classical
  have ha0 : 0 < a := lt_of_le_of_lt zero_le (hca 0)
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨k, hXk⟩ : ∃ k, ∀ x ∈ X, x < c k := by
    rcases X.eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨k, hk⟩ := hcof _ (hX _ (X.max'_mem hne))
      exact ⟨k, fun x hx => (X.le_max' x hx).trans_lt hk⟩
  have hW : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), u ∈ CvDom (c k) a b := by
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · exact Or.inl (hXk u hu)
    · exact Or.inr (hY u hu)
  have hsm : StrictMonoOn (D k) (CvDom (c k) a b) := by
    intro u hu v hv huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hDfix k u hu, hDfix k v hv]; exact huv
    · rw [hDfix k u hu]; exact hu.trans_le (hDwin k v hv.1 hv.2).1
    · exact absurd (huv.trans (hv.trans (hca k))) (not_lt.2 hu.1)
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
    · have hdec := hDdec k s (hY s hsY).1 (hY s hsY).2 hdz
      rcases hXY s hs hdec with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact absurd (h0 ▸ (hY s hsY).1) (not_le.2 ha0)
      · exact Or.inr ⟨D k p, ⟨p, hp, rfl⟩, D k q, ⟨q, hq, rfl⟩, hsm (hW p hp) hsW hps,
          hsm (hW q hq) hsW hqs, (hDadd k p (hW p hp) q (hW q hq) s hsW).1 hpq⟩
  have hYt : ∀ y ∈ Y.image (D k), y < a := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (hDwin k y (hY y hy).1 (hY y hy).2).2
  have hXYt : ∀ x ∈ X, ∀ y ∈ Y.image (D k), x < y := by
    intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (hXk x hx).trans_le (hDwin k y (hY y hy).1 (hY y hy).2).1
  refine ⟨Y.image (D k), hYt, hXYt, by rw [himg]; exact hcl, D k, ?_⟩
  rw [← himg] at hiso
  refine cvCov_inner hX (fun y hy => (hY y hy).1) hYt hXYt hiso ?_ ?_ ?_
  · intro y hy y' hy' h1
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · exact hD1 k y y' (hY y hy).1 hlt (hY y' hy').2 h1
    · exact le1_refl _
    · exact absurd (le1_le h1) (not_le.2 hgt)
  · intro y hy y' hy' h2
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · exact hD2 k y y' (hY y hy).1 hlt (hY y' hy').2 h2
    · exact le2_refl _
    · exact absurd (le2_le h2) (not_le.2 hgt)
  · intro x hx y hy h2
    exact hD2X k x (hXk x hx) y (hY y hy).1 (hY y hy).2 h2

end Googology.Trans.PoR.InaccPsi.R2.Cv
