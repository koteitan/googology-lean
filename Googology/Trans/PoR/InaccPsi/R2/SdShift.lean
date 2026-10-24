import Googology.Trans.PoR.InaccPsi.R2.RxTh
import Googology.Trans.PoR.InaccPsi.R2.RtLow

/-!
# `T` from the base changes `B_n` reflecting `≤₁` and `≤₂` (no keeping half, only from some `n` on)

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n` (the base change `L(n+1) ↦ L(ω)`, defined on `[0, L(n+2))`),
`T`: `L(ω) ≤₁ L(ω+1)`.  `Cx.cxShift_le1` proves `a ≤₁ b` from maps `B_n` that keep AND reflect `≤₁`, `≤₂`
on `[0, c(n+1))` for EVERY `n`.  Its covering is the inverse `B_n⁻¹` on `X ∪ Y`; an inverse is a covering
([C09] Def 5.2) as soon as `B_n` REFLECTS `≤₁` and `≤₂`.  So:

* `sdInv_cov` (**a right inverse of a strictly increasing map that keeps and reflects `+` and reflects
  `≤₁`, `≤₂` is a covering**);
* `sdShift_refl` (**`Cx.cxShift_le1` with only the reflecting halves, asked only for `n ≥ N₀`**);
* `SdRefl S n` (`B_n` reflects `≤₁` and `≤₂` on `[0, L(n+2))`), `sdT_of_refl` (**`T` from `SdRefl S n` for
  every `n ≥ N₀`**), `sdRefl_of_TC` (the old hypotheses (TC) and (EMB₂) give `SdRefl S n` for every `n`).

No new axiom.  New definition: `SdRefl` (a hypothesis name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **A right inverse of a reflecting map is a covering**: `f` strictly increasing on `[0, d)`, keeping
and reflecting `+` there, and reflecting `≤₁`, `≤₂` there; `h u < d`, `f (h u) = u` on `A`. -/
theorem sdInv_cov {d : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hm : StrictMonoOn f (Set.Iio d))
    (hadd : ∀ x < d, ∀ y < d, ∀ z < d, (x + y = z ↔ f x + f y = f z))
    (h1 : ∀ x < d, ∀ y < d, le1 (f x) (f y) → le1 x y)
    (h2 : ∀ x < d, ∀ y < d, le2 (f x) (f y) → le2 x y)
    {A : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
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
    refine h1 (h x) (hA x hx).1 (h y) (hA y hy).1 ?_
    rw [(hA x hx).2, (hA y hy).2]
    exact hr
  · show le2 (h x) (h y)
    refine h2 (h x) (hA x hx).1 (h y) (hA y hy).1 ?_
    rw [(hA x hx).2, (hA y hy).2]
    exact hr

/-- **The shift with reflecting maps only, from some `N₀` on**: `a ≤₁ b` from a monotone sequence `c`
cofinal in `a` and maps `B_n` (strictly increasing on `[0, c(n+1))`, keeping and reflecting `+`, fixing
`[0, c n)`, onto every finite `Y ⊆ [a, b)` for cofinally many `n`) that reflect `≤₁` and `≤₂` on
`[0, c(n+1))` for every `n ≥ N₀`. -/
theorem sdShift_refl {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {B : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hmono : Monotone c) (hca : ∀ n, c n < a) (hcof : ∀ γ < a, ∃ n, γ < c n) (hab : a ≤ b)
    (hBm : ∀ n, StrictMonoOn (B n) (Set.Iio (c (n + 1))))
    (hBadd : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), ∀ z < c (n + 1),
      (x + y = z ↔ B n x + B n y = B n z))
    (N0 : ℕ)
    (hR1 : ∀ n, N0 ≤ n → ∀ x < c (n + 1), ∀ y < c (n + 1), le1 (B n x) (B n y) → le1 x y)
    (hR2 : ∀ n, N0 ≤ n → ∀ x < c (n + 1), ∀ y < c (n + 1), le2 (B n x) (B n y) → le2 x y)
    (hfix : ∀ n, ∀ x < c n, B n x = x)
    (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∀ N, ∃ n, N ≤ n ∧
      ∀ y ∈ Y, ∃ y' < c (n + 1), B n y' = y) :
    le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨N, hN⟩ := Qq.qqFin_below hmono hcof X hX
  obtain ⟨n, hNn', hYn⟩ := honto Y hY (max N N0)
  have hNn : N ≤ n := (le_max_left _ _).trans hNn'
  have hN0 : N0 ≤ n := (le_max_right _ _).trans hNn'
  set d := c (n + 1) with hd
  have hcn : c n ≤ d := hmono (Nat.le_succ n)
  have hda : d < a := hca (n + 1)
  let g : Ordinal.{0} → Ordinal.{0} := fun y =>
    if hy : ∃ y' < d, B n y' = y then Classical.choose hy else 0
  have hg : ∀ y ∈ Y, g y < d ∧ B n (g y) = y := by
    intro y hy
    have hex : ∃ y' < d, B n y' = y := hYn y hy
    have hsp := Classical.choose_spec hex
    simp only [g, dif_pos hex]
    exact hsp
  let h : Ordinal.{0} → Ordinal.{0} := fun z => if z < a then z else g z
  have hXa : ∀ x ∈ X, x < c n := fun x hx => (hN x hx).trans_le (hmono hNn)
  have hhX : ∀ x ∈ X, h x = x := fun x hx => by simp only [h, if_pos (hX x hx)]
  have hhY : ∀ y ∈ Y, h y = g y := fun y hy => by
    simp only [h, if_neg (not_lt.2 (hY y hy).1)]
  have hA : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), h u < d ∧ B n (h u) = u := by
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · rw [hhX u hu]; exact ⟨(hXa u hu).trans_le hcn, hfix n u (hXa u hu)⟩
    · rw [hhY u hu]; exact hg u hu
  have hgc : ∀ y ∈ Y, c n ≤ g y := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have e := hfix n (g y) hlt
    rw [(hg y hy).2] at e
    exact absurd (e ▸ hlt.trans (hca n)) (not_lt.2 (hY y hy).1)
  have himg := Qq.qqImage_fix (Y := Y) hhX
  refine ⟨Y.image h, ?_, ?_, ?_, h, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    rw [hhY y hy]; exact (hg y hy).1.trans hda
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    rw [hhY y hy]; exact (hXa x hx).trans_le (hgc y hy)
  · rw [himg]; exact Qq.qqInv_closed (hBm n) (hBadd n) hA hXY
  · rw [himg]; exact sdInv_cov (hBm n) (hBadd n) (hR1 n hN0) (hR2 n hN0) hA

variable {S : InaccSeq.{0}}

/-- **`B_n` reflects `≤₁` and `≤₂` on `[0, L(n+2))`.** -/
def SdRefl (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ x < Bc.bcC S (n + 1), ∀ y < Bc.bcC S (n + 1),
    (le1 (Bc.bcB S n x) (Bc.bcB S n y) → le1 x y) ∧ (le2 (Bc.bcB S n x) (Bc.bcB S n y) → le2 x y)

/-- **`T` from the reflecting halves of `B_n`, for every `n ≥ N₀`.** -/
theorem sdT_of_refl (N0 : ℕ) (h : ∀ n, N0 ≤ n → SdRefl S n) : Cx.CxT S :=
  sdShift_refl (Bc.bcC_mono S) (Bc.bcC_lt S) (Bc.bcC_cof S) (Qq.qqL_lt_succ S).le
    (Bc.bcB_mono' S) (Bc.bcB_addIff' S) N0
    (fun n hn x hx y hy => (h n hn x hx y hy).1) (fun n hn x hx y hy => (h n hn x hx y hy).2)
    (Bc.bcB_fix' S) (Bc.bcOnto' S)

/-- **(TC) and (EMB₂) give `SdRefl S n` for every `n`** (the new hypothesis is weaker than the old). -/
theorem sdRefl_of_TC (hTC : CdTC S) (hB2 : CdEMB2 S) (n : ℕ) : SdRefl S n :=
  fun x hx y hy => ⟨(Bc.bcB1 S hTC n x hx y hy).2, (hB2 n x hx y hy).2⟩

end Googology.Trans.PoR.InaccPsi.R2.Sd
