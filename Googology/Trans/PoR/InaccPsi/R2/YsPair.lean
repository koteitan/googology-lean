import Googology.Trans.PoR.InaccPsi.R2.YiWin

/-!
# Ys: SK1 and the pair of a block when points below the block cross into it

The repo's block lemmas (`R2.le1_iff_le1R_blk'`, `R2.PairCtx`) ask that a point `c ≤ T` which is `≤₁` a point
of the block `(T, β]` be `T` itself.  Inside a window `W_k = [L(k), L(k+1))` this fails at every restart
(`Yi.yiCross_win`: `L(k)` is `≤₁` every window point).  Here the field is weakened:

* `ysBlk` (**SK1 in a block, no crossing condition**): if no `<₂`-pair has its right end in `(T, B)`, then
  `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, B]`; a crossing `c ≤ T`, `c ≤₁ d` is copied by monotonicity
  (`c ≤ ψ(d) ≤ d`).  The repo's `le1_iff_le1R_blk'` has the same conclusion under an extra hypothesis.
* `YsPairCtx T τ β`: `R2.PairCtx` with `reachT` replaced by `reachW` (a point `c ≤ T` that is `≤₁` a point of
  `(T, β)` is `≤₁` every point of `(T, β]`); `R2.PairCtx.toYs`; clause 1, Lemma COMP-C, clause 2 and
  **the pair `τ <₂ β`** (`YsPairCtx.pair`) in this context.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **SK1 in a block with crossings allowed.**  If no `<₂`-pair has its right end in `(T, B)`, then for
`T < a`, `b ≤ B`: `a ≤₁ b` in `R₂^C` iff in `R₁⁺`.  No condition on the points `≤ T`. -/
theorem ysBlk {T B : Ordinal.{0}} (hB : B < Om1)
    (hno : ∀ c d, c < d → T < d → d < B → ¬ le2 c d) :
    ∀ b ≤ B, ∀ a, T < a → (le1 a b ↔ le1R a b) := by
  classical
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hbB a hTa
  refine ⟨fun h => inc1 (lt_of_le_of_lt hbB hB) h, fun hR => ?_⟩
  rcases eq_or_lt_of_le (le1R_le hR) with rfl | hab
  · exact le1_refl _
  refine le1_iff.2 ⟨hab.le, fun X Y hX hY hXY => ?_⟩
  obtain ⟨X2, hsub, hX2C, hX2b⟩ := exists_closed (insert 0 (insert T X))
  have hX2 : ∀ w ∈ X2, w < a := by
    intro w hw
    obtain ⟨s, hs, hws⟩ := hX2b w hw
    refine lt_of_le_of_lt hws ?_
    simp only [Finset.mem_insert] at hs
    rcases hs with rfl | rfl | hs
    · exact lt_of_le_of_lt zero_le hTa
    · exact hTa
    · exact hX s hs
  have hTX2 : T ∈ X2 := hsub (by simp)
  have h0X2 : (0 : Ordinal.{0}) ∈ X2 := hsub (by simp)
  have hXX2 : ∀ x ∈ X, x ∈ X2 := fun x hx => hsub (by simp [hx])
  have hX2Y : Closed ↑(X2 ∪ Y) := by
    have he : (↑(X2 ∪ Y) : Set Ordinal.{0}) = ↑X2 ∪ ↑(X ∪ Y) := by
      ext w
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (hXX2 w h)
        · exact Or.inr h
    rw [he]; exact hX2C.union hXY
  obtain ⟨ψ, hψ, hψc, hfix, hYψ, hψR⟩ := ccf hR X2 Y hX2 hY h0X2 hX2Y
  have hX2lt : ∀ c ∈ X2 ∪ Y, ∀ d ∈ X2, c < d → c ∈ X2 := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with h | h
    · exact h
    · exact absurd (lt_trans hcd (hX2 d hd)) (not_lt.2 (hY c h).1)
  have hTψ : ∀ c ∈ X2 ∪ Y, T < c → T < ψ c := by
    intro c hc hTc
    rcases Finset.mem_union.1 hc with h | h
    · rw [hfix c h]; exact hTc
    · exact (hYψ c h).1 T hTX2
  have hcov : Cov R2C R2C ↑(X2 ∪ Y) (ψ '' ↑(X2 ∪ Y)) ψ := by
    refine ⟨hψ, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (ψ c) (ψ d)
      rcases eq_or_lt_of_le (le1_le hcd) with rfl | hcd'
      · exact le1_refl _
      rcases Finset.mem_union.1 hd with hdX | hdY
      · rw [hfix c (hX2lt c hc d hdX hcd'), hfix d hdX]; exact hcd
      · have hTd : T < d := lt_of_lt_of_le hTa (hY d hdY).1
        have hdb : d < b := (hY d hdY).2
        rcases le_or_gt c T with hcT | hTc
        · have hcX2 : c ∈ X2 := by
            rcases Finset.mem_union.1 hc with h' | h'
            · exact h'
            · exact absurd (lt_of_le_of_lt hcT hTa) (not_lt.2 (hY c h').1)
          rw [hfix c hcX2]
          exact le1_of_le_of_le1 ((hYψ d hdY).1 c hcX2).le
            (((hYψ d hdY).2).trans_le (hY d hdY).1).le hcd
        have hRcd : le1R c d := inc1 (lt_of_lt_of_le (lt_of_lt_of_le hdb hbB) hB.le) hcd
        have hRψ := hψR c hc d hd hRcd
        have hψdb : ψ d < b := lt_trans (hYψ d hdY).2 hab
        exact (IH (ψ d) hψdb (hψdb.le.trans hbB) (ψ c) (hTψ c hc hTc)).2 hRψ
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (ψ c) (ψ d)
      rcases eq_or_lt_of_le (le2_le hcd) with rfl | hcd'
      · exact le2_refl _
      rcases Finset.mem_union.1 hd with hdX | hdY
      · rw [hfix c (hX2lt c hc d hdX hcd'), hfix d hdX]; exact hcd
      · exact absurd hcd (hno c d hcd' (lt_of_lt_of_le hTa (hY d hdY).1)
          (lt_of_lt_of_le (hY d hdY).2 hbB))
  have hsub' : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(X2 ∪ Y) := by
    intro w hw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (hXX2 w hw)
    · exact Or.inr hw
  have hfixX : ∀ w ∈ X, ψ w = w := fun w hw => hfix w (hXX2 w hw)
  have himg : ψ '' ↑(X ∪ Y) = ↑(X ∪ Y.image ψ) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ht | ht
      · left; rw [hfixX t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfixX w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
  refine ⟨Y.image ψ, ?_, ?_, ?_, ψ, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYψ t ht).2
  · intro w hw y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYψ t ht).1 w (hXX2 w hw)
  · rw [← himg]; exact closed_image hψ hψc hsub' hXY
  · rw [← himg]; exact hcov.restrict hsub'


/-- A pair context with crossings: `R2.PairCtx` with `reachT` replaced by `reachW`. -/
structure YsPairCtx (T τ β : Ordinal.{0}) : Prop where
  τU : UpsPt τ
  next : IsNext τ β
  β1 : β < Om1
  Tτ : T < τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ
  noPair : ∀ c d, c < d → T < d → d < β → ¬ le2 c d
  low : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b)
  reachW : ∀ c ≤ T, ∀ d, T < d → d < β → le1 c d → ∀ g, T < g → g ≤ β → le1 c g

namespace YsPairCtx

variable {T τ β : Ordinal.{0}} (h : YsPairCtx T τ β)
include h

theorem τ1 : τ < Om1 := h.next.1.trans h.β1

theorem τβ : τ < β := h.next.1

theorem T_iff : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < β) := by
  obtain ⟨m, hm, hT⟩ := exists_next h.τU h.τ1
  rw [← hm.unique h.next]; exact hT

/-- A base `σ` (a `υ`-point in `(T, τ)`) above a finite set `S ⊆ τ`. -/
theorem base_above (S : Finset Ordinal.{0}) (hS : ∀ s ∈ S, s < τ) :
    ∃ σ, UpsPt σ ∧ T < σ ∧ σ < τ ∧ (∀ s ∈ S, s < σ) := by
  classical
  have hsup : (insert T S).sup id < τ := by
    rw [Finset.sup_lt_iff (lt_of_le_of_lt zero_le h.Tτ)]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact h.Tτ
    · exact hS b hb
  obtain ⟨σ, hσU, hσ, hστ⟩ := h.cof _ hsup
  refine ⟨σ, hσU, lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_self T S)) hσ, hστ,
    fun s hs => lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem hs)) hσ⟩

/-- **Clause 1** of `τ ≤₂^∞ β` ([C09] Def 5.3) in a block context. -/
theorem clause1 (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < τ)
    (hY : ∀ y ∈ Y, τ ≤ y ∧ y < β) (hXY : Closed ↑(X ∪ Y)) :
    ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < τ) ∧ (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧
      Closed ↑(X ∪ Yt) ∧ ∃ f, Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) f ∧
        ∀ y ∈ Y, le1 y β → le1 (f y) τ := by
  classical
  have hτE := upsPt_inE h.τU
  have hτ1 := h.τ1
  have hYT : ∀ y ∈ Y, y ∈ Tset τ := fun y hy => (h.T_iff y ((hY y hy).2.trans h.β1)).2 (hY y hy).2
  obtain ⟨σ, hσU, hTσ, hστ, hSσ⟩ := h.base_above (X ∪ Y.biUnion (fun y => Par τ y)) (by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · obtain ⟨y, hy, hsy⟩ := Finset.mem_biUnion.1 hs
      exact Par_sub hτE hτ1 (hYT y hy) (Finset.mem_coe.2 hsy))
  have hB : Bases σ τ := ⟨upsPt_inE hσU, hτE, hστ, hτ1⟩
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => hSσ x (Finset.mem_union_left _ hx)
  obtain ⟨mσ, hmσ, hTσm⟩ := exists_next hσU (hστ.trans hτ1)
  have hmστ : mσ ≤ τ := hmσ.2.2 τ hστ h.τU
  have hA : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ TB τ σ := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with hw | hw
    · exact (TB_inter_lt hB (hX w hw)).2 (hXσ w hw)
    · exact ⟨hYT w hw, fun p hp =>
        hSσ p (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_coe.1 hp⟩))⟩
  have hA1 : ∀ w ∈ X ∪ Y, w < β := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact (hX w hw).trans h.τβ
    · exact (hY w hw).2
  let f := pi σ τ
  have hfix : ∀ x ∈ X, f x = x := fun x hx => pi_lt hB (hXσ x hx)
  have hiso : ArithIso ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f :=
    ⟨(down_mono hB hA).injOn.bijOn_image, down_mono hB hA, down_add hB hA⟩
  have hYf : ∀ y ∈ Y, σ ≤ f y ∧ f y < τ := by
    intro y hy
    have hyA : y ∈ TB τ σ := hA (Finset.mem_coe.2 (Finset.mem_union_right _ hy))
    have hy1 : y < Om1 := (hY y hy).2.trans h.β1
    exact ⟨down_ge hB hyA (hY y hy).1, lt_of_lt_of_le
      ((hTσm _ (down_lt_Om1 hB hyA hy1)).1 ((pi_bijOn hB).1.mapsTo hyA)) hmστ⟩
  have himg : (↑(X ∪ Y.image f) : Set Ordinal.{0}) = f '' ↑(X ∪ Y) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfix w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hfix t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  have hcl : Closed (f '' ↑(X ∪ Y)) :=
    closed_image_of_indec hiso hXY (fun s hs hI =>
      down_indec hB (hA hs) ((hA1 s (Finset.mem_coe.1 hs)).trans h.β1) hI)
  have hfβ : ∀ w ∈ X ∪ Y, f w < β := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [hfix w hw]; exact (hX w hw).trans h.τβ
    · exact (hYf w hw).2.trans h.τβ
  have hXlt : ∀ c ∈ X ∪ Y, ∀ d ∈ X, c ≤ d → c ∈ X := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc
    · exact hc
    · exact absurd (lt_of_lt_of_le (hX d hd) (hY c hc).1) (not_lt.2 hcd)
  have hTf : ∀ c ∈ X ∪ Y, T < c → T < f c := by
    intro c hc hTc
    rcases Finset.mem_union.1 hc with hc | hc
    · rw [hfix c hc]; exact hTc
    · exact lt_of_lt_of_le hTσ (hYf c hc).1
  have hcov : Cov R2C R2C ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f := by
    refine ⟨hiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (f c) (f d)
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfix c (hXlt c hc d hdX (le1_le hcd)), hfix d hdX]; exact hcd
      · have hTd : T < d := lt_of_lt_of_le h.Tτ (hY d hdY).1
        rcases le_or_gt c T with hcT | hTc
        · have hcX : c ∈ X := by
            rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
            · exact hcX
            · exact absurd (lt_of_le_of_lt hcT h.Tτ) (not_lt.2 (hY c hcY).1)
          rw [hfix c hcX]
          exact h.reachW c hcT d hTd (hY d hdY).2 hcd _ (hTf d (Finset.mem_coe.1 hd) hTd)
            (hfβ d (Finset.mem_coe.1 hd)).le
        have hR := inc1 ((hY d hdY).2.trans h.β1) hcd
        have hR' := (down_le1R hσU h.τU hB (hA hc) (hA hd)
          ((hA1 c (Finset.mem_coe.1 hc)).trans h.β1)).1 hR
        exact (h.low _ _ (hTf c hc hTc) (hfβ d hd).le).2 hR'
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (f c) (f d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfix c (hXlt c hc d hdX hlt.le), hfix d hdX]; exact hcd
      · exact absurd hcd (h.noPair c d hlt (lt_of_lt_of_le h.Tτ (hY d hdY).1) (hY d hdY).2)
  refine ⟨Y.image f, ?_, ?_, ?_, f, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYf t ht).2
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_lt_of_le (hXσ x hx) (hYf t ht).1
  · rw [himg]; exact hcl
  · rw [himg]; exact hcov
  · intro y hy hyβ
    have hR := inc1 h.β1 hyβ
    rcases eq_or_lt_of_le (hY y hy).1 with e | hlt
    · rw [← e]
      show le1 (pi σ τ τ) τ
      rw [(pi_base hB).2]
      exact (h.low _ _ hTσ h.τβ.le).2 (hσU.2 _ hστ.le)
    · exact absurd hR (not_le1R_gap h.next hlt (hY y hy).2 le_rfl)

/-- **Lemma COMP-C** in a block context (segment compression, a covering of `R₂^C`). -/
theorem comp (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < τ) {c' : Ordinal.{0}}
    (hc1 : τ ≤ c') (hc2 : c' < β) :
    ∃ c'' < τ, ∀ Y0 : Finset Ordinal.{0}, (∀ y ∈ Y0, c'' < y ∧ y < τ) →
      Closed ↑(X ∪ Y0) → ∃ Y : Finset Ordinal.{0}, (∀ y ∈ Y, c' < y ∧ y < β) ∧
        Closed ↑(X ∪ Y) ∧ ∃ g, Cov R2C R2C ↑(X ∪ Y0) ↑(X ∪ Y) g ∧ ∀ x ∈ X, g x = x := by
  classical
  have hτE := upsPt_inE h.τU
  have hτ1 := h.τ1
  have hcT : c' ∈ Tset τ := (h.T_iff c' (hc2.trans h.β1)).2 hc2
  obtain ⟨σ, hσU, hTσ, hστ, hSσ⟩ := h.base_above (X ∪ Par τ c') (by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · exact Par_sub hτE hτ1 hcT (Finset.mem_coe.2 hs))
  have hB : Bases σ τ := ⟨upsPt_inE hσU, hτE, hστ, hτ1⟩
  obtain ⟨σ', hnx, hT⟩ := exists_next hσU (hστ.trans hτ1)
  have hσ'τ : σ' ≤ τ := hnx.2.2 τ hστ h.τU
  have hσ'1 : σ' < Om1 := lt_of_le_of_lt hσ'τ hτ1
  have hσ'U : UpsPt σ' := hnx.2.1
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => hSσ x (Finset.mem_union_left _ hx)
  have hcTB : c' ∈ TB τ σ := ⟨hcT, fun p hp => hSσ p (Finset.mem_union_right _ (Finset.mem_coe.1 hp))⟩
  set ct := pi σ τ c' with hctdef
  have hctσ : σ ≤ ct := down_ge hB hcTB hc1
  have hct1 : ct < Om1 := down_lt_Om1 hB hcTB (hc2.trans h.β1)
  have hctT : ct ∈ Tset σ := (pi_bijOn hB).1.mapsTo hcTB
  have hctσ' : ct < σ' := (hT ct hct1).1 hctT
  refine ⟨ct, lt_of_lt_of_le hctσ' hσ'τ, fun Y0 hY0 hXY0 => ?_⟩
  set Y2 := Y0.filter (· < σ') with hY2
  set Y3 := Y0.filter (fun y => ¬ y < σ') with hY3
  obtain ⟨X', hsub, hX'C, hX'b⟩ := exists_closed (insert 0 (insert ct (X ∪ Y2)))
  have hX'lt : ∀ x ∈ X', x < σ' := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hX'b x hx
    refine lt_of_le_of_lt hxs ?_
    simp only [Finset.mem_insert, Finset.mem_union] at hs
    rcases hs with rfl | rfl | hs | hs
    · exact hσ'U.1
    · exact hctσ'
    · exact (hXσ s hs).trans hnx.1
    · exact (Finset.mem_filter.1 hs).2
  have hXX' : ∀ x ∈ X, x ∈ X' := fun x hx => hsub (by simp [hx])
  have hY2X' : ∀ y ∈ Y2, y ∈ X' := fun y hy => hsub (by simp [hy])
  have h0X' : (0 : Ordinal.{0}) ∈ X' := hsub (by simp)
  have hctX' : ct ∈ X' := hsub (by simp)
  have hY3 : ∀ y ∈ Y3, σ' ≤ y ∧ y < τ := by
    intro y hy
    obtain ⟨hy0, hyσ⟩ := Finset.mem_filter.1 hy
    exact ⟨not_lt.1 hyσ, (hY0 y hy0).2⟩
  have hD : (↑(X ∪ Y0) : Set Ordinal.{0}) ⊆ ↑(X' ∪ Y3) := by
    intro w hw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (hXX' w hw)
    · by_cases hwσ : w < σ'
      · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hwσ⟩))
      · exact Or.inr (Finset.mem_filter.2 ⟨hw, hwσ⟩)
  have hX'Y3 : Closed ↑(X' ∪ Y3) := by
    have he : (↑(X' ∪ Y3) : Set Ordinal.{0}) = ↑X' ∪ ↑(X ∪ Y0) := by
      ext w
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro (hw | hw)
        · exact Or.inl hw
        · exact Or.inr (Or.inr (Finset.mem_filter.1 hw).1)
      · rintro (hw | hw | hw)
        · exact Or.inl hw
        · exact Or.inl (hXX' w hw)
        · by_cases hwσ : w < σ'
          · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hwσ⟩))
          · exact Or.inr (Finset.mem_filter.2 ⟨hw, hwσ⟩)
    rw [he]; exact hX'C.union hXY0
  obtain ⟨ψ, hψ, hψc, hψfix, hYψ, hψR⟩ :=
    ccf (hσ'U.2 _ hσ'τ) X' Y3 hX'lt hY3 h0X' hX'Y3
  have hψD : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), ψ w < σ' := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 (hD hw)) with h' | h'
    · rw [hψfix w h']; exact hX'lt w h'
    · exact (hYψ w h').2
  have hψT : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), ψ w ∈ Tset σ ∧ ψ w < Om1 := fun w hw =>
    ⟨(hT _ ((hψD w hw).trans hσ'1)).2 (hψD w hw), (hψD w hw).trans hσ'1⟩
  have hψY0 : ∀ y ∈ Y0, ct < ψ y := by
    intro y hy
    by_cases hyσ : y < σ'
    · rw [hψfix y (hY2X' y (Finset.mem_filter.2 ⟨hy, hyσ⟩))]; exact (hY0 y hy).1
    · exact (hYψ y (Finset.mem_filter.2 ⟨hy, hyσ⟩)).1 ct hctX'
  set W := ψ '' ↑(X ∪ Y0) with hWdef
  have hWT : W ⊆ Tset σ := by rintro _ ⟨w, hw, rfl⟩; exact (hψT w hw).1
  have hψisoD : ArithIso ↑(X ∪ Y0) W ψ :=
    ⟨(hψ.2.1.mono hD).injOn.bijOn_image, hψ.2.1.mono hD,
      fun x hx y hy z hz => hψ.2.2 x (hD hx) y (hD hy) z (hD hz)⟩
  have hWc : Closed W := closed_image hψ hψc hD hXY0
  have hupiso : ArithIso W (up σ τ '' W) (up σ τ) :=
    ⟨(up_mono hB hWT).injOn.bijOn_image, up_mono hB hWT, up_add hB hWT⟩
  set g := up σ τ ∘ ψ with hgdef
  have hgimg : g '' ↑(X ∪ Y0) = up σ τ '' W := by rw [hgdef, Set.image_comp]
  have hgiso : ArithIso ↑(X ∪ Y0) (g '' ↑(X ∪ Y0)) g := by
    rw [hgimg]; exact hψisoD.comp hupiso
  have hgcl : Closed (g '' ↑(X ∪ Y0)) := by
    rw [hgimg]
    refine closed_image_of_indec hupiso hWc ?_
    rintro _ ⟨w, hw, rfl⟩ hI
    exact up_indec hB (hψT w hw).1 (hψT w hw).2 hI
  have hgfix : ∀ x ∈ X, g x = x := by
    intro x hx
    show up σ τ (ψ x) = x
    rw [hψfix x (hXX' x hx), up_lt hB (hXσ x hx)]
  have hgβ : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), g w < β := by
    intro w hw
    obtain ⟨hwT, hw1⟩ := hψT w hw
    have hu := (up_spec hB hwT).1
    exact (h.T_iff _ (up_lt_Om1 hB hwT hw1)).1 hu.1
  have hgY0 : ∀ y ∈ Y0, c' < g y := by
    intro y hy
    have hyD : y ∈ (↑(X ∪ Y0) : Set Ordinal.{0}) := by simp [hy]
    have := up_mono hB (S := {ct, ψ y}) (by
      intro w hw
      rcases hw with rfl | hw
      · exact hctT
      · rw [Set.mem_singleton_iff.1 hw]; exact (hψT y hyD).1) (by simp) (by simp) (hψY0 y hy)
    rwa [hctdef, up_pi hB hcTB] at this
  have hXlt : ∀ c ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), ∀ d ∈ X, c ≤ d → c ∈ X := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hc | hc
    · exact hc
    · exact absurd (lt_of_lt_of_le ((hXσ d hd).trans (lt_of_le_of_lt hctσ (hY0 c hc).1)) hcd)
        (lt_irrefl _)
  have hTg : ∀ c ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), T < c → T < g c := by
    intro c hc hTc
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hc | hc
    · rw [hgfix c hc]; exact hTc
    · exact lt_trans (lt_of_lt_of_le h.Tτ hc1) (hgY0 c hc)
  have hgcov : Cov R2C R2C ↑(X ∪ Y0) (g '' ↑(X ∪ Y0)) g := by
    refine ⟨hgiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (g c) (g d)
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hgfix c (hXlt c hc d hdX (le1_le hcd)), hgfix d hdX]; exact hcd
      · have hTd : T < d := lt_trans hTσ (lt_of_le_of_lt hctσ (hY0 d hdY).1)
        rcases le_or_gt c T with hcT | hTc
        · have hcX : c ∈ X := by
            rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
            · exact hcX
            · exact absurd (lt_of_le_of_lt hcT (lt_of_lt_of_le hTσ (hctσ.trans (hY0 c hcY).1.le)))
                (lt_irrefl _)
          rw [hgfix c hcX]
          exact h.reachW c hcT d hTd ((hY0 d hdY).2.trans h.τβ) hcd _ (hTg d hd hTd) (hgβ d hd).le
        have hR := inc1 ((hY0 d hdY).2.trans hτ1) hcd
        have hR' := hψR c (Finset.mem_coe.1 (hD hc)) d (Finset.mem_coe.1 (hD hd)) hR
        have hR'' := (up_le1R hσU h.τU hB (hψT c hc).1 (hψT d hd).1 (hψT c hc).2).1 hR'
        exact (h.low _ _ (hTg c hc hTc) (hgβ d hd).le).2 hR''
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (g c) (g d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hgfix c (hXlt c hc d hdX hlt.le), hgfix d hdX]; exact hcd
      · exact absurd hcd (h.noPair c d hlt
          (lt_trans hTσ (lt_of_le_of_lt hctσ (hY0 d hdY).1)) ((hY0 d hdY).2.trans h.τβ))
  have himg : (↑(X ∪ Y0.image g) : Set Ordinal.{0}) = g '' ↑(X ∪ Y0) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hgfix w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hgfix t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  refine ⟨Y0.image g, ?_, ?_, g, ?_, hgfix⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hgY0 t ht, hgβ t (by simp [ht])⟩
  · rw [himg]; exact hgcl
  · rw [himg]; exact hgcov

/-- **Clause 2** of `τ ≤₂^∞ β` in a block context. -/
theorem clause2 (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < τ) (Z : Finset Ordinal.{0}) (P : Str)
    (hC : CofCov R2C X Z P τ) : CofCov R2C X Z P β := by
  intro c' hc'
  rcases lt_or_ge c' τ with hlt | hge
  · obtain ⟨Y, hY, hcl, f, hcov⟩ := hC c' hlt
    exact ⟨Y, fun y hy => ⟨(hY y hy).1, (hY y hy).2.trans h.τβ⟩, hcl, f, hcov⟩
  · obtain ⟨c'', hc''τ, H⟩ := h.comp X hX hge hc'
    obtain ⟨Y0, hY0, hcl0, h0, hcov0⟩ := hC c'' hc''τ
    obtain ⟨Y, hY, hcl, g, hg, -⟩ := H Y0 hY0 hcl0
    exact ⟨Y, hY, hcl, g ∘ h0, hcov0.comp hg⟩

/-- **The pair of the block**: `τ <₂ β` in `R₂^C`. -/
theorem pair : le2 τ β :=
  le2_iff.2 ⟨h.τβ.le, fun X Y hX hY hXY => h.clause1 X Y hX hY hXY,
    fun X hX Z P _ hC => h.clause2 X hX Z P hC⟩

end YsPairCtx

/-- An old pair context is a pair context with crossings. -/
theorem _root_.Googology.Trans.PoR.InaccPsi.R2.PairCtx.toYs {T τ β : Ordinal.{0}} (h : PairCtx T τ β) :
    YsPairCtx T τ β :=
  ⟨h.τU, h.next, h.β1, h.Tτ, h.cof, h.noPair, h.low, fun c hc d hd hdβ hcd g hg hgβ => by
    obtain ⟨e, hr⟩ := h.reachT c hc d hd hdβ hcd
    rw [e]; exact hr g hg hgβ⟩

end Googology.Trans.PoR.InaccPsi.R2.Ys
