import Googology.Trans.PoR.InaccPsi.R2.Pair1

/-!
# Theorem B in `R₂^C`: the blocks below `υ_{ω·ω}`

A block context `BlkCtx T τ β`: `τ` a countable `υ`-point with `β = τ^∞` countable, `T < τ`, and
(T3) no `c ≤ T` is `≤₁` an ordinal `> T`; (LEFT) the only `υ_λ` (`λ` a limit) in `(T, τ]` is `τ`;
(COF) `υ`-points are cofinal below `τ`.  In such a context (all in `R₂^C`):

* `le1_iff_le1R_blk'` (**SK1 in a block**, general form): if no `<₂`-pair has its right end in
  `(T, B)` and a point `≤ T` that is `≤₁` a point of `(T, B]` is `T` itself with `T ≤₁` all of
  `(T, B]`, then `a ≤₁ b` in `R₂^C` iff `a ≤₁ b` in `R₁⁺`, for `T < a`, `b ≤ B` (copies by Theorem
  CC-F above `T`); `le1_iff_le1R_blk`: the case where no point `≤ T` is `≤₁` a point `> T`.
* `PairCtx T τ β` (a pair context: the facts above `T` that the pair needs) and
  `PairCtx.clause1`, `PairCtx.comp` (**Lemma COMP-C** above `T`: segment compression by Theorem CC-F
  and `π⁻¹`, a covering of `R₂^C`), `PairCtx.clause2`, `PairCtx.pair` (**`τ <₂ β`**).
* `BlkCtx.not_le2_gap`: `τ <₂ d` fails for `d ∈ (τ, β)` (Lemma L against clause 2 of [C09] Def 5.3);
  `BlkCtx.no_pair_gap`: no `<₂`-pair has its right end in `(T, β)`; `BlkCtx.toPair`, `BlkCtx.pair`,
  `BlkCtx.T3_next` ((T3) at `β`), `BlkCtx.pairs_at_top`.
* `ctxB j`: the context of block `j`: `T = top j` (`top 0 = 0`, `top (j+1) = υ_{ω·j+ω+1}`),
  `τ = υ_{ω·j+ω}`, `β = top (j+1)`.
* `thmB_C` (**Theorem B in `R₂^C`**): below `υ_{ω·ω}` the `<₂`-pairs are exactly
  `υ_{ω·(j+1)} <₂ υ_{ω·(j+1)+1}`; no point `≤ top j` is `≤₁` a point `> top j`; inside block `j`,
  `≤₁` of `R₂^C` is `≤₁` of `R₁⁺`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## SK1 in a block (general form) -/

/-- **SK1 in a block.** -/
theorem le1_iff_le1R_blk' {T B : Ordinal.{0}} (hB : B < Om1)
    (hT : ∀ c ≤ T, ∀ g, T < g → g ≤ B → le1 c g → c = T ∧ ∀ g', T < g' → g' ≤ B → le1 T g')
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
        · obtain ⟨e, hreach⟩ := hT c hcT d hTd ((hdb.le).trans hbB) hcd
          rw [e, hfix T hTX2]
          exact hreach _ ((hYψ d hdY).1 T hTX2)
            (((hYψ d hdY).2.trans hab).le.trans hbB)
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

/-- **SK1 in a block**, when no point `≤ T` is `≤₁` a point `> T`. -/
theorem le1_iff_le1R_blk {T B : Ordinal.{0}} (hB : B < Om1)
    (hT3 : ∀ c ≤ T, ∀ g, T < g → ¬ le1 c g)
    (hno : ∀ c d, c < d → T < d → d < B → ¬ le2 c d) :
    ∀ b ≤ B, ∀ a, T < a → (le1 a b ↔ le1R a b) :=
  le1_iff_le1R_blk' hB (fun c hc g hg _ h => absurd h (hT3 c hc g hg)) hno

/-! ## Pair contexts: the pair `τ <₂ β` above a lower end `T` -/

/-- A pair context: `τ` a countable `υ`-point with `β = τ^∞` countable, `T < τ`, `υ`-points cofinal
below `τ`; no `<₂`-pair has its right end in `(T, β)`; `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, β]`;
a point `c ≤ T` that is `≤₁` a point of `(T, β)` is `T`, and then `T` is `≤₁` every point of
`(T, β]`. -/
structure PairCtx (T τ β : Ordinal.{0}) : Prop where
  τU : UpsPt τ
  next : IsNext τ β
  β1 : β < Om1
  Tτ : T < τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ
  noPair : ∀ c d, c < d → T < d → d < β → ¬ le2 c d
  low : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b)
  reachT : ∀ c ≤ T, ∀ d, T < d → d < β → le1 c d → c = T ∧ ∀ g, T < g → g ≤ β → le1 T g

namespace PairCtx

variable {T τ β : Ordinal.{0}} (h : PairCtx T τ β)
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
        · obtain ⟨e, hreach⟩ := h.reachT c hcT d hTd (hY d hdY).2 hcd
          have hcX : c ∈ X := by
            rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
            · exact hcX
            · exact absurd (lt_of_le_of_lt hcT h.Tτ) (not_lt.2 (hY c hcY).1)
          rw [hfix c hcX, e]
          exact hreach _ (hTf d (Finset.mem_coe.1 hd) hTd) (hfβ d (Finset.mem_coe.1 hd)).le
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
        · obtain ⟨e, hreach⟩ := h.reachT c hcT d hTd ((hY0 d hdY).2.trans h.τβ) hcd
          have hcX : c ∈ X := by
            rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
            · exact hcX
            · exact absurd (lt_of_le_of_lt hcT (lt_of_lt_of_le hTσ (hctσ.trans (hY0 c hcY).1.le)))
                (lt_irrefl _)
          rw [hgfix c hcX, e]
          exact hreach _ (hTg d hd hTd) (hgβ d hd).le
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

end PairCtx

/-! ## Block contexts -/

/-- A block context. -/
structure BlkCtx (T τ β : Ordinal.{0}) : Prop where
  τU : UpsPt τ
  next : IsNext τ β
  β1 : β < Om1
  Tτ : T < τ
  T3 : ∀ c ≤ T, ∀ g, T < g → ¬ le1 c g
  left : ∀ l, IsSuccLimit l → T < upsilon l → upsilon l ≤ τ → upsilon l = τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ

namespace BlkCtx

variable {T τ β : Ordinal.{0}} (h : BlkCtx T τ β)
include h

theorem τ1 : τ < Om1 := h.next.1.trans h.β1

theorem τβ : τ < β := h.next.1

theorem T_iff : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < β) := by
  obtain ⟨m, hm, hT⟩ := exists_next h.τU h.τ1
  rw [← hm.unique h.next]; exact hT

/-- A `<₂`-left end in `(T, τ]` is `τ`. -/
theorem left_eq {c d : Ordinal.{0}} (h2 : le2 c d) (hcd : c < d) (hTc : T < c) (hcτ : c ≤ τ) :
    c = τ := by
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd (lt_of_le_of_lt hcτ h.τ1)
  exact h.left l hl hTc hcτ

/-- No `<₂`-pair has its right end in `(T, τ]`. -/
theorem no_pair_upto : ∀ c d, c < d → T < d → d ≤ τ → ¬ le2 c d := by
  intro c d hcd hTd hdτ h2
  rcases le_or_gt c T with hcT | hTc
  · exact h.T3 c hcT d hTd (le2_le1 h2)
  · have := h.left_eq h2 hcd hTc (hcd.le.trans hdτ)
    rw [this] at hcd
    exact absurd (lt_of_lt_of_le hcd hdτ) (lt_irrefl _)

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, τ]`. -/
theorem le1_lowτ : ∀ a b, T < a → b ≤ τ → (le1 a b ↔ le1R a b) := fun a b ha hb =>
  le1_iff_le1R_blk h.τ1 h.T3 (fun c d hcd hTd hdτ => h.no_pair_upto c d hcd hTd hdτ.le) b hb a ha

/-- `≤₁`-chains of `υ`-points of `R₂^C`, cofinal below `τ` (above `T`). -/
theorem chains : ∀ c' < τ, ∃ g : ℕ → Ordinal.{0}, StrictMono g ∧ (∀ i, Indec (g i)) ∧
    (∀ i, c' < g i ∧ g i < τ) ∧ ∀ i k, i ≤ k → le1 (g i) (g k) := by
  classical
  intro c' hc'
  let F : Ordinal.{0} → Ordinal.{0} := fun x => if hx : x < τ then Classical.choose (h.cof x hx) else 0
  have hF : ∀ x < τ, UpsPt (F x) ∧ x < F x ∧ F x < τ := fun x hx => by
    simp only [F, dif_pos hx]; exact Classical.choose_spec (h.cof x hx)
  let g : ℕ → Ordinal.{0} := fun i => Nat.rec (motive := fun _ => Ordinal.{0}) (F (max c' T))
    (fun _ y => F y) i
  have hm : max c' T < τ := max_lt hc' h.Tτ
  have hg : ∀ i, UpsPt (g i) ∧ max c' T < g i ∧ g i < τ := by
    intro i
    induction i with
    | zero => exact hF _ hm
    | succ i ih =>
      have := hF (g i) ih.2.2
      exact ⟨this.1, ih.2.1.trans this.2.1, this.2.2⟩
  have hgs : ∀ i, g i < g (i + 1) := fun i => (hF (g i) (hg i).2.2).2.1
  have hmono : StrictMono g := strictMono_nat_of_lt_succ hgs
  refine ⟨g, hmono, fun i => indec_of_upsPt (hg i).1,
    fun i => ⟨lt_of_le_of_lt (le_max_left _ _) (hg i).2.1, (hg i).2.2⟩, fun i k hik => ?_⟩
  refine (h.le1_lowτ (g i) (g k) (lt_of_le_of_lt (le_max_right _ _) (hg i).2.1)
    (hg k).2.2.le).2 ?_
  exact (hg i).1.2 _ (hmono.monotone hik)

/-- `τ <₂ d` fails for `d ∈ (τ, β)`. -/
theorem not_le2_gap : ∀ d, τ < d → d < β → ¬ le2 τ d := by
  classical
  intro d hτd hdβ h2
  have hd1 : d < Om1 := hdβ.trans h.β1
  set K := ht τ d + 2 with hK
  obtain ⟨f, hfM, hfI, -, -⟩ := h.chains 0 (lt_of_le_of_lt zero_le h.Tτ)
  have hZc : Closed (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    closed_of_indec (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact hfI i)
  have hcof : CofCov R2C ∅ ((Finset.range (K + 1)).image f) chainP τ := by
    intro c' hc'
    obtain ⟨g, hgM, hgI, hgb, hg1⟩ := h.chains c' hc'
    obtain ⟨hh, hcov, -⟩ := cov_chain R2C K hfM hgM hfI hgI (fun i j hij _ => hg1 i j hij)
      le2_refl
    refine ⟨(Finset.range (K + 1)).image g, ?_, ?_, hh, ?_⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hgb i
    · rw [Finset.empty_union]
      exact closed_of_indec (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hgI i)
    · rw [Finset.empty_union]; exact hcov
  obtain ⟨-, -, H2⟩ := le2_iff.1 h2
  have hcofd := H2 ∅ (by simp) _ chainP hZc hcof
  obtain ⟨Y, hY, -, hh, hcov⟩ := hcofd τ hτd
  have hmemZ : ∀ i ≤ K, f i ∈ (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    fun i hi => Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  have hzY : ∀ i ≤ K, τ < hh (f i) ∧ hh (f i) < d := by
    intro i hi
    have hm := hcov.1.1.mapsTo (hmemZ i hi)
    rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hm
    exact hY _ (Finset.mem_coe.1 hm)
  have hch : ∀ i < K, hh (f i) < hh (f (i + 1)) ∧ le1R (hh (f i)) (hh (f (i + 1))) := by
    intro i hi
    refine ⟨hcov.1.2.1 (hmemZ i hi.le) (hmemZ (i + 1) hi) (hfM (Nat.lt_succ_self i)), ?_⟩
    have h1 : le1 (hh (f i)) (hh (f (i + 1))) :=
      hcov.2.1 _ (hmemZ i hi.le) _ (hmemZ (i + 1) hi) (hfM.monotone (Nat.le_succ i))
    exact inc1 ((hzY (i + 1) hi).2.trans hd1) h1
  have hbound := chain_bound_gap (upsPt_inE h.τU) h.τ1 h.T_iff hdβ hd1 K
    (fun i => hh (f i)) (hzY 0 (Nat.zero_le K)).1 (hzY K le_rfl).2.le hch
  omega

/-- No `<₂`-pair has its right end in `(T, β)`. -/
theorem no_pair_gap : ∀ c d, c < d → T < d → d < β → ¬ le2 c d := by
  intro c d hcd hTd hdβ h2
  rcases le_or_gt c T with hcT | hTc
  · exact h.T3 c hcT d hTd (le2_le1 h2)
  have hc1 : c < Om1 := (hcd.trans hdβ).trans h.β1
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hcd hc1
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd (lt_trans hcd hdβ) (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  have := h.left_eq h2 hcd hTc hcτ
  subst this
  exact h.not_le2_gap d hcd hdβ h2

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, β]`. -/
theorem le1_lowβ : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b) := fun a b ha hb =>
  le1_iff_le1R_blk h.β1 h.T3 h.no_pair_gap b hb a ha

theorem le2_eq {c d : Ordinal.{0}} (h2 : le2 c d) (hTd : T < d) (hdβ : d < β) : c = d := by
  rcases eq_or_lt_of_le (le2_le h2) with e | hlt
  · exact e
  · exact absurd h2 (h.no_pair_gap c d hlt hTd hdβ)

/-- A block context is a pair context. -/
theorem toPair : PairCtx T τ β :=
  ⟨h.τU, h.next, h.β1, h.Tτ, h.cof, h.no_pair_gap, h.le1_lowβ,
    fun c hc d hd _ hcd => absurd hcd (h.T3 c hc d hd)⟩

/-- The pair of the block, from the pair context. -/
theorem pair : le2 τ β := h.toPair.pair

/-- (T3) at `β`: no `c ≤ β` is `≤₁` an ordinal `> β`. -/
theorem T3_next : ∀ c ≤ β, ∀ g, β < g → ¬ le1 c g := by
  classical
  intro c hcβ g hg hcg
  have hτI := indec_of_upsPt h.τU
  have hβI := indec_of_upsPt h.next.2.1
  rcases le_or_gt c T with hcT | hTc
  · exact h.T3 c hcT g (h.Tτ.trans (h.τβ.trans hg)) hcg
  rcases le_or_gt c τ with hcτ | hτc
  · have hmem : ∀ x ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}), x = τ ∨ x = β := by
      intro x hx; simpa using hx
    obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hcg hTc ∅ {τ, β} (by simp)
      (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨hcτ, h.τβ.trans hg⟩
        · exact ⟨hcβ, hg⟩)
      (closed_of_indec (by
        intro x hx
        rcases hmem x hx with rfl | rfl
        · exact hτI
        · exact hβI))
    have hτm : τ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hβm : β ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f β) := hf.2.2 _ hτm _ hβm h.pair
    have hlt : f τ < f β := hf.1.2.1 hτm hβm h.τβ
    have hfβ := hYt _ (hmap β (by simp))
    exact h.no_pair_gap _ _ hlt hfβ.1 (lt_of_lt_of_le hfβ.2 (hcτ.trans h.τβ.le)) h2
  · obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hcg hτc {τ} {β} (by simpa using hτc)
      (by simpa using ⟨hcβ, hg⟩)
      (closed_of_indec (by
        intro x hx
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτI
        · exact hβI))
    have hτm : τ ∈ (↑({τ} ∪ {β} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have hβm : β ∈ (↑({τ} ∪ {β} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f β) := hf.2.2 _ hτm _ hβm h.pair
    have hfβ := hYt _ (hmap β (by simp))
    rw [hfix τ (by simp)] at h2
    exact h.no_pair_gap _ _ hfβ.1 (h.Tτ.trans hfβ.1) (lt_of_lt_of_le hfβ.2 hcβ) h2

/-- `τ` is the only `<₂`-predecessor of `β`. -/
theorem pairs_at_top {c : Ordinal.{0}} (hc : c < β) (h2 : le2 c β) : c = τ := by
  rcases le_or_gt c T with hcT | hTc
  · exact absurd (le2_le1 h2) (h.T3 c hcT β (h.Tτ.trans h.τβ))
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hc (hc.trans h.β1)
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd hc (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  exact h.left_eq h2 hc hTc hcτ

end BlkCtx

/-! ## The blocks below `υ_{ω·ω}` -/

/-- `0 ≤₁ g` only for `g = 0`. -/
theorem not_le1_zero {g : Ordinal.{0}} (hg : 0 < g) : ¬ le1 0 g := by
  classical
  intro h
  obtain ⟨-, H⟩ := le1_iff.1 h
  obtain ⟨Yt, hYt, -, -, f, hf⟩ := H ∅ {0} (by simp) (by simpa using hg)
    (by simpa using closed_singleton_zero)
  have hm := hf.1.1.mapsTo (show (0 : Ordinal.{0}) ∈
    (↑((∅ : Finset Ordinal.{0}) ∪ {0} : Finset Ordinal.{0}) : Set Ordinal.{0}) by simp)
  rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hm
  exact absurd (hYt _ (Finset.mem_coe.1 hm)) (not_lt.2 zero_le)

/-- The top of block `j`: `top 0 = 0`, `top (j+1) = υ_{ω·j+ω+1}`. -/
noncomputable def top : ℕ → Ordinal.{0}
  | 0 => 0
  | j + 1 => upsilon (ω * (j : Ordinal.{0}) + ω + 1)

/-- The left end of the pair of block `j`: `υ_{ω·j+ω}`. -/
noncomputable def lp (j : ℕ) : Ordinal.{0} := upsilon (ω * (j : Ordinal.{0}) + ω)

theorem omega_mul_succ (j : ℕ) : ω * ((j + 1 : ℕ) : Ordinal.{0}) = ω * (j : Ordinal.{0}) + ω := by
  push_cast; rw [mul_add, mul_one]

/-- A limit `l` with `a < l ≤ a + ω` is `a + ω`. -/
theorem limit_eq_add_omega {a l : Ordinal.{0}} (hl : IsSuccLimit l) (hal : a < l)
    (hl2 : l ≤ a + ω) : l = a + ω := by
  rcases eq_or_lt_of_le hl2 with e | hlt
  · exact e
  exfalso
  have hsub := Ordinal.add_sub_cancel_of_le hal.le
  have hr : l - a < ω := by
    rw [← hsub] at hlt; exact (add_lt_add_iff_left a).1 hlt
  obtain ⟨n, hn⟩ := lt_omega0.1 hr
  rw [hn] at hsub
  rcases n with _ | m
  · simp at hsub; rw [hsub] at hal; exact lt_irrefl _ hal
  · have : l = succ (a + (m : Ordinal.{0})) := by
      rw [← hsub, succ_eq_add_one, Nat.cast_succ, add_assoc]
    exact not_isSuccLimit_succ _ (this ▸ hl)

/-- The `υ`-points of the first `ω·ω` indices are countable. -/
theorem ups_lt_Om1_blk : ∀ j n : ℕ, upsilon (ω * (j : Ordinal.{0}) + n) < Om1 := by
  intro j
  induction j with
  | zero =>
    intro n; simpa using upsilon_nat_lt_Om1 n
  | succ j ih =>
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, add_zero, omega_mul_succ]
      have hlub := upsilon_limit (isSuccLimit_add (ω * (j : Ordinal.{0})) isSuccLimit_omega0)
      have hs : (⨆ n : ℕ, upsilon (ω * (j : Ordinal.{0}) + n)) < Om1 :=
        Ordinal.iSup_lt_omega_one ih
      refine lt_of_le_of_lt (hlub.2 ?_) hs
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨d, hd, hid⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hi
      obtain ⟨n, rfl⟩ := lt_omega0.1 hd
      exact (upsilon_normal.strictMono hid).le.trans
        (le_ciSup (f := fun n : ℕ => upsilon (ω * (j : Ordinal.{0}) + n))
          ⟨Om1, by rintro _ ⟨k, rfl⟩; exact (ih k).le⟩ n)
    | succ n ihn =>
      have hn := upsilon_isNext (ω * ((j + 1 : ℕ) : Ordinal.{0}) + n)
      rw [succ_eq_add_one] at hn
      rw [Nat.cast_succ (n := n), ← add_assoc]
      refine next_lt_Om1 hn ?_ ihn
      rcases eq_or_ne (upsilon (ω * ((j + 1 : ℕ) : Ordinal.{0}) + n)) 0 with h0 | h0
      · left; exact h0
      · right; exact ⟨pos_iff_ne_zero.2 h0, ((upsilon_mem _).resolve_left h0).2⟩

theorem lp_index_pos (j : ℕ) : 0 < ω * (j : Ordinal.{0}) + ω :=
  lt_of_lt_of_le omega0_pos le_add_self

/-- The block context of block `j`. -/
theorem ctxB : ∀ j : ℕ, BlkCtx (top j) (lp j) (top (j + 1)) := by
  have base : ∀ j : ℕ, (∀ c ≤ top j, ∀ g, top j < g → ¬ le1 c g) →
      (top j < lp j) → (∀ l, IsSuccLimit l → top j < upsilon l → ω * (j : Ordinal.{0}) < l) →
      BlkCtx (top j) (lp j) (top (j + 1)) := by
    intro j hT3 hTτ hidx
    have hlim : IsSuccLimit (ω * (j : Ordinal.{0}) + ω) := isSuccLimit_add _ isSuccLimit_omega0
    have hnext : IsNext (lp j) (top (j + 1)) := by
      have := upsilon_isNext (ω * (j : Ordinal.{0}) + ω)
      rwa [succ_eq_add_one] at this
    refine ⟨upsPt_upsilon (lp_index_pos j), hnext, ?_, hTτ, hT3, ?_, ?_⟩
    · show upsilon (ω * (j : Ordinal.{0}) + ω + 1) < Om1
      have := ups_lt_Om1_blk (j + 1) 1
      rwa [omega_mul_succ, Nat.cast_one] at this
    · intro l hl hTl hlτ
      have h1 := hidx l hl hTl
      have h2 : l ≤ ω * (j : Ordinal.{0}) + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
      show upsilon l = upsilon (ω * (j : Ordinal.{0}) + ω)
      rw [limit_eq_add_omega hl h1 h2]
    · intro c' hc'
      obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
      refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
        hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
      exact upsilon_normal.strictMono (hlim.succ_lt hι)
  intro j
  induction j with
  | zero =>
    refine base 0 ?_ ?_ ?_
    · intro c hc g hg
      have : c = 0 := le_antisymm hc zero_le
      rw [this]; exact not_le1_zero hg
    · exact upsPt_upsilon (lp_index_pos 0) |>.1
    · intro l hl _
      simp only [Nat.cast_zero, mul_zero]
      exact pos_iff_ne_zero.2 hl.ne_bot
  | succ j ih =>
    refine base (j + 1) ih.T3_next ?_ ?_
    · show upsilon (ω * (j : Ordinal.{0}) + ω + 1) < upsilon (ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω)
      rw [omega_mul_succ]
      exact upsilon_normal.strictMono ((add_lt_add_iff_left _).2 one_lt_omega0)
    · intro l _ hTl
      have : ω * (j : Ordinal.{0}) + ω + 1 < l := upsilon_normal.strictMono.lt_iff_lt.1 hTl
      rw [omega_mul_succ]
      exact lt_of_le_of_lt le_self_add this

theorem top_mono : StrictMono top := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  exact lt_trans (ctxB j).Tτ (ctxB j).τβ

/-- Pairs with right end at most `top j`. -/
theorem pairs_upto : ∀ j : ℕ, ∀ c d, c < d → d ≤ top j → le2 c d →
    ∃ k < j, c = lp k ∧ d = top (k + 1) := by
  intro j
  induction j with
  | zero =>
    intro c d hcd hd _
    exact absurd (lt_of_lt_of_le hcd hd) (not_lt.2 zero_le)
  | succ j ih =>
    intro c d hcd hd h2
    rcases le_or_gt d (top j) with hdj | hdj
    · obtain ⟨k, hk, hck, hdk⟩ := ih c d hcd hdj h2
      exact ⟨k, Nat.lt_succ_of_lt hk, hck, hdk⟩
    rcases eq_or_lt_of_le hd with e | hlt
    · subst e
      exact ⟨j, Nat.lt_succ_self j, (ctxB j).pairs_at_top hcd h2, rfl⟩
    · exact absurd h2 ((ctxB j).no_pair_gap c d hcd hdj hlt)

/-- `υ_{ω·ω}` is the supremum of the block tops. -/
theorem exists_top_above {d : Ordinal.{0}} (hd : d < upsilon (ω * ω)) : ∃ j, d ≤ top j := by
  have hlim : IsSuccLimit (ω * ω) := isSuccLimit_mul_right omega0_pos isSuccLimit_omega0
  obtain ⟨_, ⟨ι, hι, rfl⟩, hdx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hd
  obtain ⟨c', hc', hιc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hι
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc'
  rcases n with _ | m
  · simp at hιc
  · refine ⟨m + 1, hdx.le.trans (upsilon_normal.strictMono.monotone ?_)⟩
    rw [omega_mul_succ] at hιc
    exact (hιc.trans (lt_add_one _)).le

/-- **Theorem B in `R₂^C`** (below `υ_{ω·ω}`; `lp j = υ_{ω·(j+1)}`, `top (j+1) = υ_{ω·(j+1)+1}`).
(1) `υ_{ω·(j+1)} <₂ υ_{ω·(j+1)+1}` for every `j`; (2) these are all the `<₂`-pairs with right end
below `υ_{ω·ω}`; (3) no `c ≤ top j` is `≤₁` an ordinal `> top j` (the blocks are closed); (4) inside
block `j`, `(top j, top (j+1)]`, `≤₁` of `R₂^C` is `≤₁` of `R₁⁺`. -/
theorem thmB_C :
    (∀ j : ℕ, le2 (lp j) (top (j + 1))) ∧
    (∀ c d, c < d → d < upsilon (ω * ω) → (le2 c d ↔ ∃ j : ℕ, c = lp j ∧ d = top (j + 1))) ∧
    (∀ j : ℕ, ∀ c ≤ top j, ∀ g, top j < g → ¬ le1 c g) ∧
    (∀ j : ℕ, ∀ a b, top j < a → b ≤ top (j + 1) → (le1 a b ↔ le1R a b)) := by
  refine ⟨fun j => (ctxB j).pair, fun c d hcd hd => ⟨fun h2 => ?_, ?_⟩, fun j => (ctxB j).T3,
    fun j => (ctxB j).le1_lowβ⟩
  · obtain ⟨j, hj⟩ := exists_top_above hd
    obtain ⟨k, -, hk⟩ := pairs_upto j c d hcd hj h2
    exact ⟨k, hk⟩
  · rintro ⟨j, rfl, rfl⟩; exact (ctxB j).pair

end Googology.Trans.PoR.InaccPsi.R2
