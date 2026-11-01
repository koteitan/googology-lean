import Googology.Trans.PoR.InaccPsi.R2.BlkGen

/-!
# Theorem BLK^O started at a restart `λ₀` (the relative block induction)

`R2.BlkGen` proves the block structure `Good O B` of `[0, υ_B)` by one induction from `0`.  Here the same
induction is started at a restart index `λ₀`: if the block structure is known at every block boundary up to
`λ₀ + ω²` and `O(λ₀) < δ_{λ₀}`, then the local conditions of a general offset specification on the restarts
`λ₀ < λ < B` give `Good O B`, Lemma RS and the exact reach `lh(ρ_λ) = δ_λ + O(λ)` for every restart
`λ₀ < λ < B`.  Nothing is asked at the restarts below `λ₀` except through `Good`.

* `YfSpec O λ₀ B`: the hypotheses (the base data `good`, `le0`; the local fields `le`, `one`, `top`, `succ`,
  `rs` of `OffSpecGen` on `(λ₀, B)` only);
* `yfGood_all`, `yfGood_B`, `yfRst`, `yfRs` (**Lemma RS_λ** on `(λ₀, B)`), `yfReach`, `yfSk`;
* `yfGood_congr`: `Good O λ` depends on `O` only through its values at the restart indices below `λ`;
* `yfBase_short` (**the base has a short reach**): the base data force `ρ_{λ₀} ≤₁ g ⇒ g ≤ δ_{λ₀} + O(λ₀)`,
  in particular `g < υ_{λ₀+ω+2}`; and `yfBase_noCross`: no point below `υ_{λ₀+ω²}` is `≤₁` a point
  `≥ υ_{λ₀+ω²}`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yf

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **The hypotheses of the relative block induction** from the restart index `λ₀` up to `B`. -/
structure YfSpec (O : Ordinal.{0} → Ordinal.{0}) (l0 B : Ordinal.{0}) : Prop where
  ri : IsRestartIdx l0
  mult : ω * ω ∣ B
  cnt : B < Om1
  lt : l0 < B
  good : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)
  le0 : O l0 < upsilon (l0 + ω + 1)
  le : ∀ l, IsRestartIdx l → l0 < l → l < B → O l < upsilon (l + ω + 1)
  one : ∀ l, IsRestartIdx l → l0 < l → l < B → 1 ≤ O l
  top : ∀ l, IsRestartIdx l → l0 < l → l < B → TopInH O l
  succ : ∀ l, IsRestartIdx l → l0 < l → l < B → cL l < 2 → O l = 1
  rs : ∀ l, IsRestartIdx l → l0 < l → l < B → 2 ≤ cL l → RsInGen O l

/-- **`Good O λ` depends on `O` only at the restart indices below `λ`.** -/
theorem yfGood_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ, IsRestartIdx μ → μ < l → O' μ = O μ) (G : Good O l) : Good O' l where
  below := G.below
  land := G.land
  caps := fun c d hcd hd h2 x hx g hg => by
    rcases G.caps c d hcd hd h2 x hx g hg with h1 | ⟨μ, hμ, hμl, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨μ, hμ, hμl, by rw [h μ hμ hμl]; exact h3⟩
  pairs := G.pairs
  sk := G.sk
  rst := fun μ hμ hμl => by rw [h μ hμ hμl]; exact G.rst μ hμ hμl

section Spec

variable {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (S : YfSpec O l0 B)
include S

/-- **The block structure at every boundary `ω²·η ≤ B`.** -/
theorem yfGood_all : ∀ η, ω * ω * η ≤ B → Good O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη
  by_cases hle : ω * ω * η ≤ l0 + ω * ω
  · exact S.good η hle
  have hle' : l0 + ω * ω < ω * ω * η := not_le.1 hle
  rcases zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
  · rw [mul_zero] at hle'; exact absurd hle' (not_lt.2 zero_le)
  · have IH' := IH η' (lt_succ η')
    rw [succ_eq_add_one, mul_add_one] at hη hle' ⊢
    have hgt : l0 < ω * ω * η' := by
      by_contra h
      exact absurd hle' (not_lt.2 (add_le_add (not_lt.1 h) le_rfl))
    have hl : IsRestartIdx (ω * ω * η') :=
      ri_iff.2 ⟨(lt_of_le_of_lt zero_le hgt).ne', dvd_mul_right _ _⟩
    have hlB : ω * ω * η' < B := lt_of_lt_of_le (lt_add_of_pos_right _ hww) hη
    exact good_stepH hl (S.top _ hl hgt hlB) (S.le _ hl hgt hlB) (IH' (le_self_add.trans hη))
      (lt_of_le_of_lt hη S.cnt)
  · exact good_limit hlim (fun η' hη' =>
      IH η' hη' (le_trans (mul_le_mul_right hη'.le _) hη))

theorem yfGood_B : Good O B := by
  obtain ⟨ξ, hξ⟩ := S.mult
  rw [hξ]; exact yfGood_all S ξ (hξ ▸ le_rfl)

theorem yfRst {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1))) :=
  (yfGood_B S).rst l hl hlB

/-- **Lemma RS_λ** at every restart index `λ₀ < λ < B`: `ρ_λ ≤₁ δ_λ + O(λ)`. -/
theorem yfRs : ∀ l, IsRestartIdx l → l0 < l → l < B →
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hl0l hlB
  obtain ⟨R, htop, -⟩ := yfRst S hl hlB
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · rw [S.succ l hl hl0l hlB h2]
    obtain ⟨l1, hl1', rfl⟩ := succ_ri hl h2
    rcases hl1' with rfl | hl1r
    · exfalso
      rw [zero_add] at hl0l
      exact absurd hl0l (not_lt.2 (ri_ge S.ri))
    · have hl1B : l1 < B := lt_of_le_of_lt le_self_add hlB
      obtain ⟨R0, htop0, C0⟩ := yfRst S hl1r hl1B
      have h01 : l0 ≤ l1 := by
        by_contra h
        have := next_mult (ri_iff.1 hl1r).2 (ri_iff.1 S.ri).2 (not_le.1 h)
        exact absurd hl0l (not_lt.2 this)
      have hle1 : O l1 < upsilon (l1 + ω + 1) := by
        rcases eq_or_lt_of_le h01 with e | h
        · rw [← e]; exact S.le0
        · exact S.le l1 hl1r h hl1B
      have hT3 := R0.T3off hle1 htop0
      have hTa : upsilon (l1 + ω) ≤ upsilon (l1 + ω + 1) + O l1 :=
        R0.next.1.le.trans le_self_add
      have hr : l1 + ω + ω * ω = l1 + ω * ω := by rw [add_assoc, w_add_ww]
      have RC := rst_of_chain C0 hT3 hTa hr R.δ1
      refine rs_gen RC ?_
      have := target_of_chain C0 hTa
      rwa [hr] at this
  · have hRs := S.rs l hl hl0l hlB h2
    have hlim : IsSuccLimit l := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
      rw [hq]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hq0)
    have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
      intro z hz
      obtain ⟨T, hzu, hRS, hcof⟩ := hRs z hz
      have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
          RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
          ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + T (upsilon μ) →
            le1 (upsilon μ) g := by
        intro κ' hκ'
        obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
        obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof (max ι l0) (max_lt hι hl0l)
        have hμB : μ < B := hμl.trans hlB
        obtain ⟨Rμ, -, -⟩ := yfRst S hμ hμB
        have hrsμ := IH μ hμl hμ ((le_max_right _ _).trans_lt hιμ) hμB
        refine ⟨μ, hκι.trans (upsilon_normal.strictMono ((le_max_left _ _).trans_lt hιμ)), ?_, Rμ,
          fun g hg1 hg2 => le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
        exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
          (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
      refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
        (add_le_add (add_le_add le_rfl hzu) le_rfl) ?_
      exact hRS R htg
    have hρδ := R.ρδ
    have hall : ∀ b', upsilon l ≤ b' → b' < upsilon (l + ω + 1) + O l → le1 (upsilon l) b' := by
      intro b' hb1 hb2
      rcases le_or_gt b' (upsilon (l + ω + 1)) with hbδ | hδb
      · exact R.le1ρδ b' hb1 hbδ
      · have he : upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) = b' :=
          Ordinal.add_sub_cancel_of_le hδb.le
        have hz : b' - upsilon (l + ω + 1) < O l := by
          rw [← he] at hb2; exact (add_lt_add_iff_left _).1 hb2
        have hb'le : b' ≤ upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) + 1 :=
          calc b' = upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) := he.symm
            _ ≤ _ := le_self_add
        exact le1_of_le_of_le1 hb1 hb'le (hstep _ hz)
    rcases zero_or_succ_or_isSuccLimit (O l) with h0 | ⟨z0, hz0⟩ | hlimo
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le zero_lt_one (S.one l hl hl0l hlB)))
    · rw [← hz0, succ_eq_add_one, ← add_assoc]
      exact hstep z0 (by rw [← hz0]; exact lt_succ z0)
    · exact le1_limit (isSuccLimit_add _ hlimo)
        (lt_of_lt_of_le hρδ le_self_add) (fun b' hb1 hb2 => hall b' hb1 hb2)

/-- **The exact reach** at every restart index `λ₀ < λ < B`: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem yfReach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl0l : l0 < l) (hlB : l < B) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l) :=
  ⟨yfRs S l hl hl0l hlB, fun g hg => not_lt.1 (fun h => (yfRst S hl hlB).2.1 g h hg)⟩

/-- Below `υ_B` the non-`υ`-points have the `≤₁` of `R₁⁺`. -/
theorem yfSk : ∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ := (yfGood_B S).sk

end Spec

/-- **The base has a short reach**: under the base data, every `≤₁`-successor of `ρ_{λ₀}` is at most
`δ_{λ₀} + O(λ₀) < υ_{λ₀+ω+2}`. -/
theorem yfBase_short {O : Ordinal.{0} → Ordinal.{0}} {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0)
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) (hO0 : O l0 < upsilon (l0 + ω + 1))
    {g : Ordinal.{0}} (hg : le1 (upsilon l0) g) :
    g ≤ upsilon (l0 + ω + 1) + O l0 ∧ g < upsilon (l0 + ω + 1 + 1) := by
  obtain ⟨q, hq⟩ := (ri_iff.1 hl0).2
  have hq' : l0 + ω * ω = ω * ω * (q + 1) := by rw [mul_add_one, ← hq]
  have G := hG (q + 1) hq'.symm.le
  rw [← hq'] at G
  have hll : l0 < l0 + ω * ω := lt_add_of_pos_right l0 (mul_pos omega0_pos omega0_pos)
  have h1 : g ≤ upsilon (l0 + ω + 1) + O l0 := not_lt.1 fun h => (G.rst l0 hl0 hll).2.1 g h hg
  refine ⟨h1, h1.trans_lt ?_⟩
  have hU : UpsPt (upsilon (l0 + ω + 1 + 1)) :=
    upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))
  have hp := (indec_iff.1 (indec_of_upsPt hU)).2
  have hδ : upsilon (l0 + ω + 1) < upsilon (l0 + ω + 1 + 1) := upsilon_normal.strictMono (lt_add_one _)
  exact hp hδ (hO0.trans hδ)

/-- **No crossing of the first block boundary after the base**: no point below `υ_{λ₀+ω²}` is `≤₁` a point
`≥ υ_{λ₀+ω²}`. -/
theorem yfBase_noCross {O : Ordinal.{0} → Ordinal.{0}} {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0)
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) :
    ∀ c < upsilon (l0 + ω * ω), ∀ g, upsilon (l0 + ω * ω) ≤ g → ¬ le1 c g := by
  obtain ⟨q, hq⟩ := (ri_iff.1 hl0).2
  have hq' : l0 + ω * ω = ω * ω * (q + 1) := by rw [mul_add_one, ← hq]
  have G := hG (q + 1) hq'.symm.le
  rw [← hq'] at G
  exact G.below

end Googology.Trans.PoR.InaccPsi.R2.Yf
