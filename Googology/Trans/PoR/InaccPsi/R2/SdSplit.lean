import Googology.Trans.PoR.InaccPsi.R2.SdShift

/-!
# The reflection of `B_n` split into its parts: what is free, what is (CL), what is `CvNoPair`

`c_n = L(n+1) = Bc.bcC S n`, `B_n = Bc.bcB S n` (`B_n = id` below `c_n`, `B_n(c_n) = L(ω)`, `B_n` maps
`[c_n, c_{n+1})` into `[L(ω), L(ω+1))`).  For a pair `x, y < c_{n+1}` the reflection of `SdRefl S n` is

* free when both are below `c_n` (`B_n = id`), when `y < c_n ≤ x` or `x > y` (both sides false), and for
  `≤₁` when `x < c_n ≤ y` (`x ≤₁ B_n y` and `x ≤ y ≤ B_n y` give `x ≤₁ y`);
* at the base point `x = c_n`: `SdR1Base` (**from (CL) at `n`**: `L(n+1) ≤₁ L(n+2)`, `sdR1Base_of_CL`) and
  `SdR2Base` (**from the second clause of `CvNoPair L(ω) L(ω+1)`**, `sdR2Base_of_no2`);
* for `≤₂` across `c_n`: `SdR2Mix` (**from the first clause of `CvNoPair L(ω) L(ω+1)`**);
* away from the base point (`c_n < x < y < c_{n+1}`): `SdR1Away`, `SdR2Away` (**the reflecting halves of (TC)
  and (EMB₂) on the open interval**; `sdR1_of_TCAt`: the (TC) clause at `x` gives the `≤₁` half at `x`).

`sdRefl_of_parts`, `sdT_of_parts`, and `sdT_of_away` (**`T` from `CvNoPair L(ω) L(ω+1)` and, for every
`n ≥ N₀`, (CL) at `n`, `SdR1Away S n`, `SdR2Away S n`**); `sdR1Base_iff_CL` (**under `T`, the base-point
`≤₁` reflection at `n` is exactly (CL) at `n`**).

No new axiom.  New definitions (hypothesis names): `SdR1Base`, `SdR2Base`, `SdR2Mix`, `SdR1Away`, `SdR2Away`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The `≤₁`-reflection of `B_n` at its base point `L(n+1)`. -/
def SdR1Base (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ y, Bc.bcC S n ≤ y → y < Bc.bcC S (n + 1) → le1 (Nc.ncL S ω) (Bc.bcB S n y) → le1 (Bc.bcC S n) y

/-- The `≤₂`-reflection of `B_n` at its base point `L(n+1)`. -/
def SdR2Base (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ y, Bc.bcC S n ≤ y → y < Bc.bcC S (n + 1) → le2 (Nc.ncL S ω) (Bc.bcB S n y) → le2 (Bc.bcC S n) y

/-- The `≤₂`-reflection of `B_n` at the pairs across `L(n+1)`. -/
def SdR2Mix (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ x y, x < Bc.bcC S n → Bc.bcC S n ≤ y → y < Bc.bcC S (n + 1) → le2 x (Bc.bcB S n y) → le2 x y

/-- The `≤₁`-reflection of `B_n` away from its base point: `L(n+1) < x < y < L(n+2)`. -/
def SdR1Away (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ x y, Bc.bcC S n < x → x < y → y < Bc.bcC S (n + 1) →
    le1 (Bc.bcB S n x) (Bc.bcB S n y) → le1 x y

/-- The `≤₂`-reflection of `B_n` away from its base point: `L(n+1) < x < y < L(n+2)`. -/
def SdR2Away (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ x y, Bc.bcC S n < x → x < y → y < Bc.bcC S (n + 1) →
    le2 (Bc.bcB S n x) (Bc.bcB S n y) → le2 x y

/-- `L(n+2) < L(ω)`. -/
theorem sdC_lt_Lw (n : ℕ) : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)

/-- **The parts give the reflection of `B_n`.** -/
theorem sdRefl_of_parts {n : ℕ} (h1b : SdR1Base S n) (h2b : SdR2Base S n) (h2m : SdR2Mix S n)
    (h1a : SdR1Away S n) (h2a : SdR2Away S n) : SdRefl S n := by
  intro x hx y hy
  have hcw : Bc.bcC S (n + 1) < Nc.ncL S ω := sdC_lt_Lw n
  have hmono := Bc.bcB_mono' S n
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · rcases lt_or_ge y (Bc.bcC S n) with hyc | hyc
    · rw [Bc.bcB_fix' S n x (hxy.trans hyc), Bc.bcB_fix' S n y hyc]
      exact ⟨id, id⟩
    · rcases lt_or_ge x (Bc.bcC S n) with hxc | hxc
      · rw [Bc.bcB_fix' S n x hxc]
        refine ⟨fun h => le1_of_le_of_le1 hxy.le ?_ h, h2m x y hxc hyc hy⟩
        exact (hy.trans hcw).le.trans (Cx.cxB_window hyc hy).1
      · rcases eq_or_lt_of_le hxc with hxe | hxc'
        · subst hxe
          rw [Cx.cxB_base n]
          exact ⟨h1b y hyc hy, h2b y hyc hy⟩
        · exact ⟨h1a x y hxc' hxy hy, h2a x y hxc' hxy hy⟩
  · exact ⟨fun _ => le1_refl _, fun _ => le2_refl _⟩
  · have hB : Bc.bcB S n y < Bc.bcB S n x := hmono (Set.mem_Iio.2 hy) (Set.mem_Iio.2 hx) hyx
    exact ⟨fun h => absurd (le1_le h) (not_le.2 hB), fun h => absurd (le2_le h) (not_le.2 hB)⟩

/-- **(CL) at `n` gives the base-point `≤₁` reflection.** -/
theorem sdR1Base_of_CL {n : ℕ} (h : le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) : SdR1Base S n :=
  fun _ h1 h2 _ => le1_of_le_of_le1 h1 h2.le h

/-- **The second clause of `CvNoPair L(ω) L(ω+1)` gives the base-point `≤₂` reflection.** -/
theorem sdR2Base_of_no2 {n : ℕ}
    (h : ∀ y, Nc.ncL S ω < y → y < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) y) : SdR2Base S n := by
  intro y h1 h2 h3
  rcases eq_or_lt_of_le h1 with e | hlt
  · rw [← e]; exact le2_refl _
  · exfalso
    have hw : Nc.ncL S ω < Bc.bcB S n y := by
      rw [← Cx.cxB_base n]
      exact Bc.bcB_mono' S n (Set.mem_Iio.2 (Cx.cxC_lt n)) (Set.mem_Iio.2 h2) hlt
    exact h _ hw (Bc.bcB_bound' S n y h2) h3

/-- **The first clause of `CvNoPair L(ω) L(ω+1)` gives the `≤₂` reflection across `L(n+1)`.** -/
theorem sdR2Mix_of_cross {n : ℕ}
    (h : ∀ x y, x < Nc.ncL S ω → Nc.ncL S ω ≤ y → y < Nc.ncL S (ω + 1) → ¬ le2 x y) :
    SdR2Mix S n := by
  intro x y hx h1 h2 h3
  exfalso
  obtain ⟨w1, w2⟩ := Cx.cxB_window h1 h2
  exact h x _ (hx.trans ((Cx.cxC_lt n).trans (sdC_lt_Lw n))) w1 w2 h3

/-- **`CvNoPair L(ω) L(ω+1)`, (CL) at `n` and the reflection away from the base point give `SdRefl S n`.** -/
theorem sdRefl_of_noPair {n : ℕ} (hP : Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hCL : le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) (h1a : SdR1Away S n) (h2a : SdR2Away S n) :
    SdRefl S n :=
  sdRefl_of_parts (sdR1Base_of_CL hCL) (sdR2Base_of_no2 hP.2) (sdR2Mix_of_cross hP.1) h1a h2a

/-- **`T` from the five parts, for every `n ≥ N₀`.** -/
theorem sdT_of_parts (N0 : ℕ)
    (h : ∀ n, N0 ≤ n → SdR1Base S n ∧ SdR2Base S n ∧ SdR2Mix S n ∧ SdR1Away S n ∧ SdR2Away S n) :
    Cx.CxT S :=
  sdT_of_refl N0 fun n hn =>
    sdRefl_of_parts (h n hn).1 (h n hn).2.1 (h n hn).2.2.1 (h n hn).2.2.2.1 (h n hn).2.2.2.2

/-- **`T` from `CvNoPair L(ω) L(ω+1)` and, for every `n ≥ N₀`, (CL) at `n` and the reflection of `≤₁`, `≤₂`
away from the base point.** -/
theorem sdT_of_away (hP : Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1))) (N0 : ℕ)
    (h : ∀ n, N0 ≤ n → le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) ∧ SdR1Away S n ∧ SdR2Away S n) :
    Cx.CxT S :=
  sdT_of_refl N0 fun n hn => sdRefl_of_noPair hP (h n hn).1 (h n hn).2.1 (h n hn).2.2

/-- **The (TC) clause at `x` gives the `≤₁`-reflection of `B_n` at `x`.** -/
theorem sdR1_of_TCAt {n : ℕ} {x : Ordinal.{0}} (h : CdTCAt S n x) {y : Ordinal.{0}} (hxy : x ≤ y)
    (hy : y < Bc.bcC S (n + 1)) (hB : le1 (Bc.bcB S n x) (Bc.bcB S n y)) : le1 x y := by
  rcases h with ⟨r, hr, hR, hBR⟩ | hall
  · have hyr : y ≤ r := by
      by_contra hlt
      rw [not_le] at hlt
      have h' := Bc.bcB_mono' S n (Set.mem_Iio.2 hr) (Set.mem_Iio.2 hy) hlt
      exact absurd (hBR.2 _ hB) (not_le.2 h')
    exact le1_of_le_of_le1 hxy hyr hR.1
  · exact (hall y hxy hy).1

/-- **(TC) on the open interval `(L(n+1), L(n+2))` gives `SdR1Away S n`.** -/
theorem sdR1Away_of_TC {n : ℕ}
    (h : ∀ x, Bc.bcC S n < x → x < Bc.bcC S (n + 1) → CdTCAt S n x) : SdR1Away S n :=
  fun x _ hx hxy hy hB => sdR1_of_TCAt (h x hx (hxy.trans hy)) hxy.le hy hB

/-- **(EMB₂) gives `SdR2Away S n`.** -/
theorem sdR2Away_of_EMB2 (hB2 : CdEMB2 S) (n : ℕ) : SdR2Away S n :=
  fun x y _ hxy hy h => (hB2 n x (hxy.trans hy) y hy).2 h

/-- **Under `T`, the base-point `≤₁` reflection at `n` is exactly (CL) at `n`.** -/
theorem sdR1Base_iff_CL (hT : Cx.CxT S) (n : ℕ) :
    SdR1Base S n ↔ le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
  refine ⟨fun h => ?_, sdR1Base_of_CL⟩
  refine le1_limit (Cx.cxC_lim (n + 1)) (Cx.cxC_lt n) fun z h1 h2 => h z h1 h2 ?_
  obtain ⟨w1, w2⟩ := Cx.cxB_window h1 h2
  exact le1_of_le_of_le1 w1 w2.le hT

end Googology.Trans.PoR.InaccPsi.R2.Sd
