import Googology.Trans.PoR.InaccPsi.R2.Arith

/-!
# Embeddings of an initial segment of `R₂^C`, and the coverings they give

Let `f` be an **embedding of `[0, d)` into `R₂^C`**: `f` is strictly increasing on `[0, d)`, keeps
and reflects the graph of `+` on `[0, d)`, and keeps and reflects `≤₁` and `≤₂` on `[0, d)`.

* `qqInv_cov`, `qqInv_closed`: if `h` is a right inverse of `f` on a set `A` (`h u < d`,
  `f (h u) = u` for `u ∈ A`), then `h` is a covering of `A` onto `h[A]` ([C09] Def 5.2), and `h[A]`
  is closed when `A` is ([C09] Def 2.3);
* `qqFwd_cov`, `qqFwd_closed`: `f` is a covering of every `A ⊆ [0, d)` onto `f[A]`, and `f[A]` is
  closed when `A` is and the range `f[[0, d)]` is closed;
* `qqFin_below`: a finite set below `a` lies below some member of a monotone sequence cofinal in `a`;
* `qqImage_fix`: the image of `X ∪ Y` under a map that fixes `X`.

No axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Qq

open Ordinal Googology.Trans.PoR.InaccPsi.R2

section Emb

variable {d : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
  (hm : StrictMonoOn f (Set.Iio d))
  (hadd : ∀ x < d, ∀ y < d, ∀ z < d, (x + y = z ↔ f x + f y = f z))
  (h1 : ∀ x < d, ∀ y < d, (le1 x y ↔ le1 (f x) (f y)))
  (h2 : ∀ x < d, ∀ y < d, (le2 x y ↔ le2 (f x) (f y)))

include hm hadd h1 h2 in
/-- A right inverse of the embedding `f` on `A` is a covering of `A` onto its image. -/
theorem qqInv_cov {A : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hA : ∀ u ∈ A, h u < d ∧ f (h u) = u) : Cov R2C R2C A (h '' A) h := by
  have hinj : Set.InjOn h A := by
    intro u hu v hv e
    rw [← (hA u hu).2, ← (hA v hv).2, e]
  have hmono : StrictMonoOn h A := by
    intro u hu v hv huv
    refine (hm.lt_iff_lt (Set.mem_Iio.2 (hA u hu).1) (Set.mem_Iio.2 (hA v hv).1)).1 ?_
    rw [(hA u hu).2, (hA v hv).2]
    exact huv
  refine ⟨⟨hinj.bijOn_image, hmono, fun x hx y hy z hz => ?_⟩, fun x hx y hy hr => ?_,
    fun x hx y hy hr => ?_⟩
  · have e := hadd (h x) (hA x hx).1 (h y) (hA y hy).1 (h z) (hA z hz).1
    rw [(hA x hx).2, (hA y hy).2, (hA z hz).2] at e
    exact e.symm
  · show le1 (h x) (h y)
    refine (h1 (h x) (hA x hx).1 (h y) (hA y hy).1).2 ?_
    rw [(hA x hx).2, (hA y hy).2]
    exact hr
  · show le2 (h x) (h y)
    refine (h2 (h x) (hA x hx).1 (h y) (hA y hy).1).2 ?_
    rw [(hA x hx).2, (hA y hy).2]
    exact hr

include hm hadd in
/-- The image of a closed set under a right inverse of the embedding `f` is closed. -/
theorem qqInv_closed {A : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hA : ∀ u ∈ A, h u < d ∧ f (h u) = u) (hAc : Closed A) : Closed (h '' A) := by
  rintro z ⟨s, hs, rfl⟩ hdz
  rcases hdz with h0 | ⟨p, q, hp, hq, hpq⟩
  · exact Or.inl h0
  have hsd := (hA s hs).1
  have hpd : p < d := hp.trans hsd
  have hqd : q < d := hq.trans hsd
  have e1 : f p + f q = s := by
    rw [← (hA s hs).2]; exact (hadd p hpd q hqd (h s) hsd).1 hpq
  have hfp : f p < s := by rw [← (hA s hs).2]; exact hm hpd hsd hp
  have hfq : f q < s := by rw [← (hA s hs).2]; exact hm hqd hsd hq
  rcases hAc s hs (Or.inr ⟨f p, f q, hfp, hfq, e1⟩) with hs0 | ⟨u, hu, v, hv, hus, hvs, huv⟩
  · rw [hs0] at hfp; exact absurd hfp (not_lt_zero)
  refine Or.inr ⟨h u, ⟨u, hu, rfl⟩, h v, ⟨v, hv, rfl⟩, ?_, ?_, ?_⟩
  · refine (hm.lt_iff_lt (Set.mem_Iio.2 (hA u hu).1) (Set.mem_Iio.2 hsd)).1 ?_
    rw [(hA u hu).2, (hA s hs).2]; exact hus
  · refine (hm.lt_iff_lt (Set.mem_Iio.2 (hA v hv).1) (Set.mem_Iio.2 hsd)).1 ?_
    rw [(hA v hv).2, (hA s hs).2]; exact hvs
  · refine (hadd (h u) (hA u hu).1 (h v) (hA v hv).1 (h s) hsd).2 ?_
    rw [(hA u hu).2, (hA v hv).2, (hA s hs).2]; exact huv

include hm hadd h1 h2 in
/-- The embedding `f` is a covering of every `A ⊆ [0, d)` onto `f[A]`. -/
theorem qqFwd_cov {A : Set Ordinal.{0}} (hA : A ⊆ Set.Iio d) : Cov R2C R2C A (f '' A) f := by
  refine ⟨⟨(hm.injOn.mono hA).bijOn_image, hm.mono hA, fun x hx y hy z hz =>
    hadd x (hA hx) y (hA hy) z (hA hz)⟩, fun x hx y hy hr => ?_, fun x hx y hy hr => ?_⟩
  · exact (h1 x (hA hx) y (hA hy)).1 hr
  · exact (h2 x (hA hx) y (hA hy)).1 hr

include hm hadd in
/-- If the range of the embedding `f` is closed, `f` maps closed subsets of `[0, d)` to closed
sets. -/
theorem qqFwd_closed (hcl : Closed (f '' Set.Iio d)) {A : Set Ordinal.{0}} (hA : A ⊆ Set.Iio d)
    (hAc : Closed A) : Closed (f '' A) := by
  have hiso : ArithIso (Set.Iio d) (f '' Set.Iio d) f :=
    ⟨hm.injOn.bijOn_image, hm, fun x hx y hy z hz => hadd x hx y hy z hz⟩
  exact closed_image hiso hcl hA hAc

end Emb

/-- A finite set below `a` lies below `c N` for some `N`, if `c` is monotone and cofinal in `a`. -/
theorem qqFin_below {a : Ordinal.{0}} {c : ℕ → Ordinal.{0}} (hmono : Monotone c)
    (hcof : ∀ γ < a, ∃ n, γ < c n) (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < a) :
    ∃ N, ∀ x ∈ X, x < c N := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert x X _ ih =>
    obtain ⟨N1, hN1⟩ := ih (fun z hz => hX z (Finset.mem_insert_of_mem hz))
    obtain ⟨N2, hN2⟩ := hcof x (hX x (Finset.mem_insert_self x X))
    refine ⟨max N1 N2, fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hN2.trans_le (hmono (le_max_right _ _))
    · exact (hN1 z hz).trans_le (hmono (le_max_left _ _))

/-- The image of `X ∪ Y` under a map that fixes `X`. -/
theorem qqImage_fix {X Y : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hfix : ∀ x ∈ X, h x = x) :
    (↑(X ∪ Y.image h) : Set Ordinal.{0}) = h '' ↑(X ∪ Y) := by
  classical
  rw [← Finset.coe_image, Finset.image_union]
  congr 2
  conv_lhs => rw [← Finset.image_id (s := X)]
  exact Finset.image_congr (fun x hx => (hfix x hx).symm)

end Googology.Trans.PoR.InaccPsi.R2.Qq
