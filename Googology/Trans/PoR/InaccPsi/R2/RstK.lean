import Googology.Trans.PoR.InaccPsi.R2.RS

/-!
# Restart contexts without a cap below the restart, Lemma TOP with an offset

Stage 3 (`RstCtx`) asks for caps on all pairs between some `x₀ < ρ` and `ρ` (`RstCtx.capP`); this
holds when `ρ` is the restart after a chain of ordinary blocks (a successor restart index), but
fails when restarts are cofinal below `ρ` (for example `ρ = υ_{ω³}`): there `ρ_μ ≤₁ δ_μ + c(μ)`
passes the right end `δ_μ` of the pair `τ_μ <₂ δ_μ` above it.  This file drops that field.

* `RstK ρ τ δ`: the restart context without `capP`; `RstCtx.toK`.
* In a context `RstK`: the lemmas of stage 3 that do not use `capP` (`noSucc`, `le1ρ` (Lemma C″ (a)),
  `noPairGap`, `le1ρδ` (B″4), `lowδ`, `pair`, `pairs_at_top`, ...); `capδ` (no point of `(ρ, δ]` is
  `≤₁` a point `> δ`).
* `tv b k r`: the value at `r` of the offset term `k` (`b = false`, a constant) or `x + k`
  (`b = true`).
* `top_gen` (**Lemma TOP with an offset**, the project's Lemma TOP^O for these terms): if no pair
  above `x₀` below `ρ` has a point `x ≤` its left end that is `≤₁` its right end `+ e` whenever
  `e ≥ 1` and (`x` a `υ`-point) `e ≥ t(x)`, then `ρ` is not `≤₁` any `γ > δ + t(ρ)`.  The proof
  copies `{1, k} ∪ {ρ, τ, δ, ρ + k, δ + t(ρ)}` below `ρ` above `x₀` ([C09] Lemma 5.5 (1)); the copy
  keeps `+`, so the copy of `t(ρ)` is `t` at the copy of `ρ` (Lemmas EXACT / IMG of the project are
  equalities for these two kinds of terms).
* `T3off`: no point `≤ δ + o` is `≤₁` a point `> δ + o`, given TOP at `δ + o` (`1 ≤ o < δ`).

All in `R₂^C` ([C09] Def 5.3–5.4).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The value at `r` of an offset term: `tv false k r = k` (the constant `k`),
`tv true k r = r + k` (the term `x + k`). -/
def tv (b : Bool) (k r : Ordinal.{0}) : Ordinal.{0} := if b then r + k else k

theorem tv_false (k r : Ordinal.{0}) : tv false k r = k := by simp [tv]

theorem tv_true (k r : Ordinal.{0}) : tv true k r = r + k := by simp [tv]

/-- The value at `r` of the offset term `x·m + k` (`m` finite). -/
def tm (m : ℕ) (k r : Ordinal.{0}) : Ordinal.{0} := r * (m : Ordinal.{0}) + k

theorem tm_zero (k r : Ordinal.{0}) : tm 0 k r = k := by simp [tm]

theorem tm_one (k r : Ordinal.{0}) : tm 1 k r = r + k := by simp [tm]

/-- `tv` is `tm` with `m ∈ {0, 1}`. -/
theorem tv_eq_tm (b : Bool) (k r : Ordinal.{0}) : tv b k r = tm (if b then 1 else 0) k r := by
  cases b
  · simp [tv, tm]
  · simp [tv, tm]

/-- A finite closed set `A` together with finitely many points, each indecomposable or the sum of
two smaller points of the union, is closed. -/
theorem closed_union_of {A B : Finset Ordinal.{0}} (hA : Closed (↑A : Set Ordinal.{0}))
    (hB : ∀ y ∈ B, Indec y ∨ ∃ u ∈ A ∪ B, ∃ v ∈ A ∪ B, u < y ∧ v < y ∧ u + v = y) :
    Closed (↑(A ∪ B) : Set Ordinal.{0}) := by
  intro x hx hd
  rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hxA | hxB
  · exact (hA x (Finset.mem_coe.2 hxA) hd).mono
      (Finset.coe_subset.2 Finset.subset_union_left)
  · rcases hB x hxB with hI | ⟨u, hu, v, hv, h1, h2, h3⟩
    · exact absurd hd hI
    · exact Or.inr ⟨u, Finset.mem_coe.2 hu, v, Finset.mem_coe.2 hv, h1, h2, h3⟩

/-- A restart context without caps below the restart (`ρ` the restart, `τ <₂ δ` the pair of its
first block). -/
structure RstK (ρ τ δ : Ordinal.{0}) : Prop where
  ρU : UpsPt ρ
  ρτ : ρ < τ
  τU : UpsPt τ
  next : IsNext τ δ
  δ1 : δ < Om1
  below : ∀ c < ρ, ∀ g, ρ ≤ g → ¬ le1 c g
  land : ∀ c' < ρ, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < ρ ∧
    (∀ a b, σ < a → b < σ' → (le1 a b ↔ le1R a b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  left : ∀ l, IsSuccLimit l → ρ < upsilon l → upsilon l ≤ τ → upsilon l = τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ

/-- A stage-3 restart context is a restart context in the new sense. -/
theorem RstCtx.toK {ρ τ δ : Ordinal.{0}} (h : RstCtx ρ τ δ) : RstK ρ τ δ :=
  ⟨h.ρU, h.ρτ, h.τU, h.next, h.δ1, h.below, h.land, h.left, h.cof⟩

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem τ1 : τ < Om1 := h.next.1.trans h.δ1

theorem ρ1 : ρ < Om1 := h.ρτ.trans h.τ1

theorem τδ : τ < δ := h.next.1

/-- `ρ` has no `<₂`-successor. -/
theorem noSucc : ∀ b, ρ < b → ¬ le2 ρ b := by
  intro b hρb h2
  obtain ⟨y, -, hyρ, hy⟩ := le2_preds_cofinal h2 hρb 0 h.ρU.1
  exact h.below y hyρ ρ le_rfl hy

/-- No `<₂`-pair has its right end in `(ρ, τ]`. -/
theorem noPairUpto : ∀ c d, c < d → ρ < d → d ≤ τ → ¬ le2 c d := by
  intro c d hcd hρd hdτ h2
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ d hρd.le (le2_le1 h2)
  · exact h.noSucc d hcd h2
  · obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd (lt_of_le_of_lt (hcd.le.trans hdτ) h.τ1)
    have := h.left l hl hρc (hcd.le.trans hdτ)
    rw [this] at hcd
    exact absurd (lt_of_lt_of_le hcd hdτ) (lt_irrefl _)

/-- **Lemma C″ (a)** in `R₂^C`: `ρ ≤₁ γ` as long as no `<₂`-pair has its right end in `(ρ, γ)`. -/
theorem le1ρ : ∀ γ, ρ ≤ γ → γ < Om1 → (∀ c d, c < d → ρ < d → d < γ → ¬ le2 c d) →
    le1 ρ γ := by
  classical
  intro γ hργ hγ1 hno
  rcases eq_or_lt_of_le hργ with e | hργ'
  · rw [← e]; exact le1_refl _
  have hρ1 := h.ρ1
  have hρE := upsPt_inE h.ρU
  obtain ⟨s1, hs1n, hTρ⟩ := exists_next h.ρU hρ1
  refine le1_iff.2 ⟨hργ, fun X Y hX hY hXY => ?_⟩
  set Y2 := Y.filter (· < s1) with hY2
  set Y3 := Y.filter (fun y => ¬ y < s1) with hY3
  obtain ⟨X', hsub, hX'C, hX'b⟩ := exists_closed (insert 0 (insert ρ (X ∪ Y2)))
  have hX'lt : ∀ x ∈ X', x < s1 := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hX'b x hx
    refine lt_of_le_of_lt hxs ?_
    simp only [Finset.mem_insert, Finset.mem_union] at hs
    rcases hs with rfl | rfl | hs | hs
    · exact hs1n.2.1.1
    · exact hs1n.1
    · exact (hX s hs).trans hs1n.1
    · exact (Finset.mem_filter.1 hs).2
  have hXX' : ∀ x ∈ X, x ∈ X' := fun x hx => hsub (by simp [hx])
  have hY2X' : ∀ y ∈ Y2, y ∈ X' := fun y hy => hsub (by simp [hy])
  have h0X' : (0 : Ordinal.{0}) ∈ X' := hsub (by simp)
  have hρX' : ρ ∈ X' := hsub (by simp)
  have hY3 : ∀ y ∈ Y3, s1 ≤ y ∧ y < max γ s1 := by
    intro y hy
    obtain ⟨hy0, hys⟩ := Finset.mem_filter.1 hy
    exact ⟨not_lt.1 hys, lt_of_lt_of_le (hY y hy0).2 (le_max_left _ _)⟩
  have hD : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(X' ∪ Y3) := by
    intro w hw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (hXX' w hw)
    · by_cases hws : w < s1
      · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hws⟩))
      · exact Or.inr (Finset.mem_filter.2 ⟨hw, hws⟩)
  have hX'Y3 : Closed ↑(X' ∪ Y3) := by
    have he : (↑(X' ∪ Y3) : Set Ordinal.{0}) = ↑X' ∪ ↑(X ∪ Y) := by
      ext w
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro (hw | hw)
        · exact Or.inl hw
        · exact Or.inr (Or.inr (Finset.mem_filter.1 hw).1)
      · rintro (hw | hw | hw)
        · exact Or.inl hw
        · exact Or.inl (hXX' w hw)
        · by_cases hws : w < s1
          · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hws⟩))
          · exact Or.inr (Finset.mem_filter.2 ⟨hw, hws⟩)
    rw [he]; exact hX'C.union hXY
  obtain ⟨ψ, hψ, hψc, hψfix, hYψ, hψR⟩ :=
    ccf (hs1n.2.1.2 _ (le_max_right _ _)) X' Y3 hX'lt hY3 h0X' hX'Y3
  have hψD : ∀ w ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ψ w < s1 := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 (hD hw)) with h' | h'
    · rw [hψfix w h']; exact hX'lt w h'
    · exact (hYψ w h').2
  have hs11 : s1 < Om1 := next_lt_Om1 hs1n (Or.inr h.ρU) hρ1
  have hψX : ∀ x ∈ X, ψ x = x := fun x hx => hψfix x (hXX' x hx)
  have hρD' : ρ ∈ (↑(X' ∪ Y3) : Set Ordinal.{0}) := by simp [hρX']
  have hψρ : ψ ρ = ρ := hψfix ρ hρX'
  have hψY : ∀ y ∈ Y, ρ ≤ ψ y := by
    intro y hy
    rcases eq_or_lt_of_le (hY y hy).1 with e | hlt
    · rw [← e, hψρ]
    · have := hψ.2.1 hρD' (hD (by simp [hy])) hlt
      rw [hψρ] at this; exact this.le
  have hψYT : ∀ y ∈ Y, ψ y ∈ Tset ρ := fun y hy =>
    (hTρ _ ((hψD y (by simp [hy])).trans hs11)).2 (hψD y (by simp [hy]))
  set S := X ∪ Y.biUnion (fun y => Par ρ (ψ y)) with hSdef
  have hS : ∀ s ∈ S, s < ρ := by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · obtain ⟨y, hy, hsy⟩ := Finset.mem_biUnion.1 hs
      exact Par_sub hρE hρ1 (hψYT y hy) (Finset.mem_coe.2 hsy)
  have hsup : (insert 0 S).sup id < ρ := by
    rw [Finset.sup_lt_iff h.ρU.1]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact h.ρU.1
    · exact hS b hb
  obtain ⟨σ, σ', hσU, hc'σ, hσn, hσ'ρ, hlow, hσle1, hnop⟩ := h.land _ hsup
  have hSσ : ∀ s ∈ S, s < σ := fun s hs =>
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem hs)) hc'σ
  have hσρ : σ < ρ := hσn.1.trans hσ'ρ
  have hB : Bases σ ρ := ⟨upsPt_inE hσU, hρE, hσρ, hρ1⟩
  obtain ⟨mσ, hmσ, hTσ⟩ := exists_next hσU (hσρ.trans hρ1)
  have hmσ' : mσ = σ' := hmσ.unique hσn
  rw [hmσ'] at hTσ
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => hSσ x (Finset.mem_union_left _ hx)
  set W := ψ '' ↑(X ∪ Y) with hWdef
  have hWTB : W ⊆ TB ρ σ := by
    rintro _ ⟨w, hw, rfl⟩
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with hw | hw
    · rw [hψX w hw]; exact (TB_inter_lt hB (hX w hw)).2 (hXσ w hw)
    · exact ⟨hψYT w hw, fun p hp =>
        hSσ p (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_coe.1 hp⟩))⟩
  have hW1 : ∀ w ∈ W, w < Om1 := by
    rintro _ ⟨w, hw, rfl⟩; exact (hψD w hw).trans hs11
  have hψisoD : ArithIso ↑(X ∪ Y) W ψ :=
    ⟨(hψ.2.1.mono hD).injOn.bijOn_image, hψ.2.1.mono hD,
      fun x hx y hy z hz => hψ.2.2 x (hD hx) y (hD hy) z (hD hz)⟩
  have hWc : Closed W := closed_image hψ hψc hD hXY
  have hpiso : ArithIso W (pi σ ρ '' W) (pi σ ρ) :=
    ⟨(down_mono hB hWTB).injOn.bijOn_image, down_mono hB hWTB, down_add hB hWTB⟩
  set f := pi σ ρ ∘ ψ with hfdef
  have hfimg : f '' ↑(X ∪ Y) = pi σ ρ '' W := by rw [hfdef, Set.image_comp]
  have hfiso : ArithIso ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f := by
    rw [hfimg]; exact hψisoD.comp hpiso
  have hfcl : Closed (f '' ↑(X ∪ Y)) := by
    rw [hfimg]
    exact closed_image_of_indec hpiso hWc (fun s hs hI => down_indec hB (hWTB hs) (hW1 s hs) hI)
  have hfX : ∀ x ∈ X, f x = x := by
    intro x hx
    show pi σ ρ (ψ x) = x
    rw [hψX x hx, pi_lt hB (hXσ x hx)]
  have hψYW : ∀ y ∈ Y, ψ y ∈ W := fun y hy => ⟨y, by simp [hy], rfl⟩
  have hfY : ∀ y ∈ Y, σ ≤ f y ∧ f y < σ' := by
    intro y hy
    have hT := hWTB (hψYW y hy)
    refine ⟨down_ge hB hT (hψY y hy), (hTσ _ (down_lt_Om1 hB hT (hW1 _ (hψYW y hy)))).1
      ((pi_bijOn hB).1.mapsTo hT)⟩
  have hfρ : ρ ∈ Y → f ρ = σ := by
    intro _
    show pi σ ρ (ψ ρ) = σ
    rw [hψρ, (pi_base hB).2]
  have hXlt : ∀ c ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ∀ d ∈ X, c ≤ d → c ∈ X := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hc | hc
    · exact hc
    · exact absurd (lt_of_le_of_lt hcd (hX d hd)) (not_lt.2 (hY c hc).1)
  have hcov : Cov R2C R2C ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f := by
    refine ⟨hfiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (f c) (f d)
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfX c (hXlt c hc d hdX (le1_le hcd)), hfX d hdX]; exact hcd
      rcases lt_trichotomy c ρ with hcρ | e | hρc
      · exact absurd hcd (h.below c hcρ d (hY d hdY).1)
      · have hcY : c ∈ Y := by
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
          · exact absurd (e ▸ hX c hcX) (lt_irrefl _)
          · exact hcY
        rw [e] at hcY ⊢
        rw [hfρ hcY]
        exact hσle1 _ (hfY d hdY).1 (hfY d hdY).2
      · have hR := inc1 ((hY d hdY).2.trans hγ1) hcd
        have hcD := hD hc
        have hdD := hD hd
        have hR' := hψR c (Finset.mem_coe.1 hcD) d (Finset.mem_coe.1 hdD) hR
        have hψc : ρ < ψ c := by
          have := hψ.2.1 hρD' hcD hρc
          rwa [hψρ] at this
        have hcW : ψ c ∈ W := ⟨c, hc, rfl⟩
        have hdW : ψ d ∈ W := ⟨d, hd, rfl⟩
        have hR'' := (down_le1R hσU h.ρU hB (hWTB hcW) (hWTB hdW) (hW1 _ hcW)).1 hR'
        exact (hlow _ _ (down_gt hB (hWTB hcW) hψc) (hfY d hdY).2).2 hR''
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (f c) (f d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfX c (hXlt c hc d hdX hlt.le), hfX d hdX]; exact hcd
      rcases eq_or_lt_of_le (hY d hdY).1 with e | hρd
      · rw [← e] at hlt hcd
        exact absurd (le2_le1 hcd) (h.below c hlt ρ le_rfl)
      · exact absurd hcd (hno c d hlt hρd (hY d hdY).2)
  have himg : (↑(X ∪ Y.image f) : Set Ordinal.{0}) = f '' ↑(X ∪ Y) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfX w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hfX t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  refine ⟨Y.image f, ?_, ?_, ?_, f, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hfY t ht).2.trans hσ'ρ
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_lt_of_le (hXσ x hx) (hfY t ht).1
  · rw [himg]; exact hfcl
  · rw [himg]; exact hcov

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(ρ, B]` when no `<₂`-pair has its right end in `(ρ, B)`. -/
theorem lowB {B : Ordinal.{0}} (hB : B < Om1) (hno : ∀ c d, c < d → ρ < d → d < B → ¬ le2 c d) :
    ∀ a b, ρ < a → b ≤ B → (le1 a b ↔ le1R a b) := by
  intro a b ha hb
  refine le1_iff_le1R_blk' hB (fun c hc g hg hgB hcg => ?_) hno b hb a ha
  rcases eq_or_lt_of_le hc with e | hcρ
  · refine ⟨e, fun g' hg' hg'B => h.le1ρ g' hg'.le (lt_of_le_of_lt hg'B hB) ?_⟩
    exact fun c d hcd hρd hdg => hno c d hcd hρd (lt_of_lt_of_le hdg hg'B)
  · exact absurd hcg (h.below c hcρ g hg.le)

theorem lowτ : ∀ a b, ρ < a → b ≤ τ → (le1 a b ↔ le1R a b) :=
  h.lowB h.τ1 (fun c d hcd hρd hdτ => h.noPairUpto c d hcd hρd hdτ.le)

/-- No `<₂`-pair has its right end in `(ρ, δ)`. -/
theorem noPairGap : ∀ c d, c < d → ρ < d → d < δ → ¬ le2 c d := by
  intro c d hcd hρd hdδ h2
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ d hρd.le (le2_le1 h2)
  · exact h.noSucc d hcd h2
  have hc1 : c < Om1 := (hcd.trans hdδ).trans h.δ1
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hcd hc1
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd (lt_trans hcd hdδ) (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd hc1
  have := h.left l hl hρc hcτ
  rw [this] at h2 hcd
  exact not_le2_gap_of h.τU h.next h.δ1 (chains_of h.ρτ h.cof h.lowτ) d hcd hdδ h2

/-- **B″4**: `ρ ≤₁ γ` for every `γ ∈ [ρ, δ]`. -/
theorem le1ρδ : ∀ g, ρ ≤ g → g ≤ δ → le1 ρ g := fun g hg hgδ =>
  h.le1ρ g hg (lt_of_le_of_lt hgδ h.δ1)
    (fun c d hcd hρd hdg => h.noPairGap c d hcd hρd (lt_of_lt_of_le hdg hgδ))

/-- SK1 in the restart block: `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(ρ, δ]`. -/
theorem lowδ : ∀ a b, ρ < a → b ≤ δ → (le1 a b ↔ le1R a b) := h.lowB h.δ1 h.noPairGap

/-- The restart block as a pair context. -/
theorem toPair : PairCtx ρ τ δ := by
  refine ⟨h.τU, h.next, h.δ1, h.ρτ, h.cof, h.noPairGap, h.lowδ, ?_⟩
  intro c hc d hd hdδ hcd
  rcases eq_or_lt_of_le hc with e | hcρ
  · exact ⟨e, fun g hg hgδ => h.le1ρδ g hg.le hgδ⟩
  · exact absurd hcd (h.below c hcρ d hd.le)

/-- **The pair of the restart block**: `τ <₂ δ`. -/
theorem pair : le2 τ δ := h.toPair.pair

/-- `τ` is the only `<₂`-predecessor of `δ`. -/
theorem pairs_at_top {c : Ordinal.{0}} (hc : c < δ) (h2 : le2 c δ) : c = τ := by
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact absurd (le2_le1 h2) (h.below c hcρ δ (h.ρτ.trans h.τδ).le)
  · exact absurd h2 (h.noSucc δ hc)
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hc (hc.trans h.δ1)
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd hc (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hc (hc.trans h.δ1)
  exact h.left l hl hρc hcτ


/-- **The cap of the restart block**: no point of `(ρ, δ]` is `≤₁` a point `> δ`. -/
theorem capδ : ∀ c, ρ < c → c ≤ δ → ∀ g, δ < g → ¬ le1 c g := by
  classical
  intro c hρc hcδ g hδg hcg
  have hτI := indec_of_upsPt h.τU
  have hδI := indec_of_upsPt h.next.2.1
  rcases le_or_gt c τ with hcτ | hτc
  · have hmem : ∀ x ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}), x = τ ∨ x = δ := by
      intro x hx; simpa using hx
    obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hcg hρc ∅ {τ, δ} (by simp)
      (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨hcτ, h.τδ.trans hδg⟩
        · exact ⟨hcδ, hδg⟩)
      (closed_of_indec (by
        intro x hx
        rcases hmem x hx with rfl | rfl
        · exact hτI
        · exact hδI))
    have hτm : τ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hδm : δ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f δ) := hf.2.2 _ hτm _ hδm h.pair
    have hlt : f τ < f δ := hf.1.2.1 hτm hδm h.τδ
    have hfδ := hYt _ (hmap δ (by simp))
    exact h.noPairGap _ _ hlt hfδ.1 (lt_of_lt_of_le hfδ.2 (hcτ.trans h.τδ.le)) h2
  · obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hcg hτc {τ} {δ} (by simpa using hτc)
      (by simpa using ⟨hcδ, hδg⟩)
      (closed_of_indec (by
        intro x hx
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτI
        · exact hδI))
    have hτm : τ ∈ (↑({τ} ∪ {δ} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have hδm : δ ∈ (↑({τ} ∪ {δ} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f δ) := hf.2.2 _ hτm _ hδm h.pair
    have hfδ := hYt _ (hmap δ (by simp))
    rw [hfix τ (by simp)] at h2
    exact h.noPairGap _ _ hfδ.1 (h.ρτ.trans hfδ.1) (lt_of_lt_of_le hfδ.2 hcδ) h2

theorem ρδ : ρ < δ := h.ρτ.trans h.τδ

omit h in
/-- `ρ·j < δ` for an indecomposable `δ > ρ`. -/
theorem mul_nat_lt {ρ' δ' : Ordinal.{0}} (hI : Indec δ') (hρδ : ρ' < δ') (j : ℕ) :
    ρ' * (j : Ordinal.{0}) < δ' := by
  induction j with
  | zero => rw [Nat.cast_zero, mul_zero]; exact hI.pos
  | succ j ih => rw [Nat.cast_succ, mul_add_one]; exact hI.add_lt ih hρδ

theorem tm_lt_δ {m : ℕ} {k : Ordinal.{0}} (hk : k < ρ) : tm m k ρ < δ :=
  (indec_of_upsPt h.next.2.1).add_lt (mul_nat_lt (indec_of_upsPt h.next.2.1) h.ρδ m)
    (hk.trans h.ρδ)

/-- **Lemma TOP with an offset** in `R₂^C`.  Let `t = tm m k` (the term `x·m + k`, `k < ρ`; `k ≥ 1`
for a constant).  If for every pair `c <₂ d` with `x₀ < c < d < ρ`, every `x ∈ (x₀, c]` and every
`e ≥ 1` with `e ≥ t(x)` when `x` is a `υ`-point, `x` is not `≤₁ d + e`, then `ρ` is not `≤₁` any
`γ > δ + t(ρ)`.  The copy of `{1, k} ∪ {ρ, τ, δ, ρ·i, ρ·i + k (1 ≤ i ≤ m), δ + t(ρ)}` keeps `+`, so
the copy of `t(ρ)` is `t` at the copy of `ρ`. -/
theorem top_gen {m : ℕ} {k x0 : Ordinal.{0}} (hk : k < ρ) (hk1 : m = 0 → 1 ≤ k)
    (hx0 : x0 < ρ)
    (hcap : ∀ c d, x0 < c → c < d → d < ρ → le2 c d → ∀ x, x0 < x → x ≤ c → ∀ e, 1 ≤ e →
      (UpsPt x → tm m k x ≤ e) → ¬ le1 x (d + e)) :
    ∀ g, δ + tm m k ρ < g → ¬ le1 ρ g := by
  classical
  intro g hg hρg
  have hρδ : ρ < δ := h.ρδ
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hρI := indec_of_upsPt h.ρU
  have hτI := indec_of_upsPt h.τU
  have hδI := indec_of_upsPt h.next.2.1
  have hmul : ∀ j : ℕ, ρ * (j : Ordinal.{0}) < δ := mul_nat_lt hδI hρδ
  have hmulk : ∀ j : ℕ, ρ * (j : Ordinal.{0}) + k < δ := fun j =>
    hδI.add_lt (hmul j) (hk.trans hρδ)
  have hρle : ∀ i : ℕ, ρ ≤ ρ * ((i + 1 : ℕ) : Ordinal.{0}) := fun i =>
    le_mul_left ρ (by exact_mod_cast Nat.succ_pos i)
  have hcpos : 0 < tm m k ρ := by
    rcases m with _ | m
    · rw [tm_zero]; exact lt_of_lt_of_le zero_lt_one (hk1 rfl)
    · exact lt_of_lt_of_le hρI.pos ((hρle m).trans le_self_add)
  have hcδ : tm m k ρ < δ := hmulk m
  obtain ⟨X, hSX, hXC, hXb⟩ := exists_closed ({1, k} : Finset Ordinal.{0})
  have hXρ : ∀ x ∈ X, x < ρ := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hXb x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact lt_of_le_of_lt hxs h1ρ
    · exact lt_of_le_of_lt hxs hk
  have hkX : k ∈ X := hSX (by simp)
  set Pm : Finset Ordinal.{0} := (Finset.range m).image (fun i => ρ * ((i + 1 : ℕ) : Ordinal.{0}))
    with hPm
  set Pk : Finset Ordinal.{0} :=
    (Finset.range m).image (fun i => ρ * ((i + 1 : ℕ) : Ordinal.{0}) + k) with hPk
  set Y : Finset Ordinal.{0} := ({ρ, τ, δ, δ + tm m k ρ} ∪ Pm) ∪ Pk with hYdef
  have hρY : ρ ∈ Y := by simp [hYdef]
  have hτY : τ ∈ Y := by simp [hYdef]
  have hδY : δ ∈ Y := by simp [hYdef]
  have hδcY : δ + tm m k ρ ∈ Y := by simp [hYdef]
  have hPmY : ∀ i < m, ρ * ((i + 1 : ℕ) : Ordinal.{0}) ∈ Y := fun i hi => by
    simp only [hYdef, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hPkY : ∀ i < m, ρ * ((i + 1 : ℕ) : Ordinal.{0}) + k ∈ Y := fun i hi => by
    simp only [hYdef, Finset.mem_union]
    exact Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)
  have hcXY : tm m k ρ ∈ X ∪ Y := by
    rcases m with _ | m
    · rw [tm_zero]; exact Finset.mem_union_left _ hkX
    · exact Finset.mem_union_right _ (hPkY m (Nat.lt_succ_self m))
  have hδg : δ + tm m k ρ < g := hg
  have hδg' : δ < g := lt_of_le_of_lt le_self_add hδg
  have hYb : ∀ y ∈ Y, ρ ≤ y ∧ y < g := by
    intro y hy
    simp only [hYdef, hPm, hPk, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ((rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · exact ⟨le_rfl, hρδ.trans hδg'⟩
    · exact ⟨h.ρτ.le, h.τδ.trans hδg'⟩
    · exact ⟨hρδ.le, hδg'⟩
    · exact ⟨hρδ.le.trans le_self_add, hδg⟩
    · exact ⟨hρle i, (hmul _).trans hδg'⟩
    · exact ⟨(hρle i).trans le_self_add, (hmulk _).trans hδg'⟩
  have hPmdec : ∀ i < m, Indec (ρ * ((i + 1 : ℕ) : Ordinal.{0})) ∨
      ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, u < ρ * ((i + 1 : ℕ) : Ordinal.{0}) ∧
        v < ρ * ((i + 1 : ℕ) : Ordinal.{0}) ∧ u + v = ρ * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i hi
    rcases i with _ | i
    · left; simpa using hρI
    · right
      have he : ρ * ((i + 1 + 1 : ℕ) : Ordinal.{0}) = ρ * ((i + 1 : ℕ) : Ordinal.{0}) + ρ := by
        rw [Nat.cast_succ (i + 1), mul_add_one]
      refine ⟨ρ * ((i + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_right _ (hPmY i (by omega)), ρ,
        Finset.mem_union_right _ hρY, ?_, ?_, he.symm⟩
      · rw [he]; exact lt_add_of_pos_right _ hρI.pos
      · rw [he]; exact lt_of_le_of_lt (hρle i) (lt_add_of_pos_right _ hρI.pos)
  have hcl : Closed (↑(X ∪ Y) : Set Ordinal.{0}) := by
    refine closed_union_of hXC ?_
    intro y hy
    simp only [hYdef, hPm, hPk, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ((rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · exact Or.inl hρI
    · exact Or.inl hτI
    · exact Or.inl hδI
    · right
      exact ⟨δ, Finset.mem_union_right _ hδY, tm m k ρ, hcXY, lt_add_of_pos_right δ hcpos,
        lt_of_lt_of_le hcδ le_self_add, rfl⟩
    · exact hPmdec i hi
    · rcases eq_or_ne k 0 with e | hk0
      · rw [e, add_zero]; exact hPmdec i hi
      · right
        exact ⟨ρ * ((i + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_right _ (hPmY i hi), k,
          Finset.mem_union_left _ hkX, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hk0),
          lt_of_lt_of_le (lt_of_lt_of_le hk (hρle i)) le_self_add, rfl⟩
  obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hρg hx0 X Y hXρ hYb hcl
  have mY : ∀ y ∈ Y, y ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun y hy =>
    Finset.mem_coe.2 (Finset.mem_union_right _ hy)
  have mk : k ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := Finset.mem_coe.2 (Finset.mem_union_left _ hkX)
  have mc : tm m k ρ ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := Finset.mem_coe.2 hcXY
  have hfk : f k = k := hfix k hkX
  have hfadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, x + y = z → f x + f y = f z :=
    fun x hx y hy z hz e => (hf.1.2.2 x (Finset.mem_coe.2 hx) y (Finset.mem_coe.2 hy) z
      (Finset.mem_coe.2 hz)).1 e
  have hfPm : ∀ i < m, f (ρ * ((i + 1 : ℕ) : Ordinal.{0})) = f ρ * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have he : ρ * ((i + 1 + 1 : ℕ) : Ordinal.{0}) = ρ * ((i + 1 : ℕ) : Ordinal.{0}) + ρ := by
        rw [Nat.cast_succ (i + 1), mul_add_one]
      have := hfadd _ (Finset.mem_union_right _ (hPmY i (by omega))) ρ
        (Finset.mem_union_right _ hρY) _ (Finset.mem_union_right _ (hPmY (i + 1) hi)) he.symm
      rw [← this, ih (by omega), Nat.cast_succ (i + 1), mul_add_one]
  have hfc : f (tm m k ρ) = tm m k (f ρ) := by
    rcases m with _ | m
    · rw [tm_zero, tm_zero]; exact hfk
    · have := hfadd _ (Finset.mem_union_right _ (hPmY m (Nat.lt_succ_self m))) k
        (Finset.mem_union_left _ hkX) _ (Finset.mem_union_right _ (hPkY m (Nat.lt_succ_self m))) rfl
      rw [hfPm m (Nat.lt_succ_self m), hfk] at this
      exact this.symm
  have hfδc : f δ + f (tm m k ρ) = f (δ + tm m k ρ) :=
    hfadd δ (Finset.mem_union_right _ hδY) _ hcXY _ (Finset.mem_union_right _ hδcY) rfl
  have hρ' := hYt _ (hmap ρ hρY)
  have hτ' := hYt _ (hmap τ hτY)
  have hδ' := hYt _ (hmap δ hδY)
  have he1 : 1 ≤ tm m k (f ρ) := by
    rcases m with _ | m
    · rw [tm_zero]; exact hk1 rfl
    · have hfρ1 : 1 ≤ f ρ := one_le_iff_pos.2 (lt_of_le_of_lt zero_le hρ'.1)
      exact hfρ1.trans ((le_mul_left (f ρ) (by exact_mod_cast Nat.succ_pos m)).trans le_self_add)
  have h1 : le1 ρ (δ + tm m k ρ) := le1_of_le_of_le1 (hρδ.le.trans le_self_add) hδg.le hρg
  have h1' : le1 (f ρ) (f (δ + tm m k ρ)) := hf.2.1 _ (mY ρ hρY) _ (mY _ hδcY) h1
  rw [← hfδc, hfc] at h1'
  have h2 : le2 (f τ) (f δ) := hf.2.2 _ (mY τ hτY) _ (mY δ hδY) h.pair
  have hlt : f τ < f δ := hf.1.2.1 (mY τ hτY) (mY δ hδY) h.τδ
  have hρτ : f ρ ≤ f τ := (hf.1.2.1 (mY ρ hρY) (mY τ hτY) h.ρτ).le
  exact hcap (f τ) (f δ) hτ'.1 hlt hδ'.2 h2 (f ρ) hρ'.1 hρτ _ he1 (fun _ => le_rfl) h1'

/-- **The closedness after the restart block**: given Lemma TOP at `δ + o` (`1 ≤ o < δ`), no point
`≤ δ + o` is `≤₁` a point `> δ + o` (the points of `(δ, δ + o]` are decomposable). -/
theorem T3off {o : Ordinal.{0}} (hoδ : o < δ) (htop : ∀ g, δ + o < g → ¬ le1 ρ g) :
    ∀ c ≤ δ + o, ∀ g, δ + o < g → ¬ le1 c g := by
  intro c hc g hg hcg
  have hδg : δ < g := lt_of_le_of_lt le_self_add hg
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ g (h.ρδ.le.trans hδg.le) hcg
  · exact htop g hg hcg
  rcases le_or_gt c δ with hcδ | hδc
  · exact h.capδ c hρc hcδ g hδg hcg
  have hI := indec_of_lt1 hcg (lt_of_le_of_lt hc hg)
  have he : δ + (c - δ) = c := Ordinal.add_sub_cancel_of_le hδc.le
  have hξ0 : 0 < c - δ := by
    rcases eq_or_ne (c - δ) 0 with e | e
    · rw [e, add_zero] at he; exact absurd he (ne_of_lt hδc)
    · exact pos_iff_ne_zero.2 e
  have hξo : c - δ ≤ o := by
    rw [← he] at hc; exact (add_le_add_iff_left δ).1 hc
  apply hI
  refine Or.inr ⟨δ, c - δ, ?_, ?_, he⟩
  · rw [← he]; exact lt_add_of_pos_right δ hξ0
  · exact lt_of_le_of_lt hξo (lt_of_lt_of_le hoδ hδc.le)

end RstK

end Googology.Trans.PoR.InaccPsi.R2
