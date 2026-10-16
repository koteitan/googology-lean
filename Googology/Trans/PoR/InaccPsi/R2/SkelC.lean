import Googology.Trans.PoR.InaccPsi.R2.BlkX

/-!
# SKEL⁺ in `R₂^C` without reaches: the blocks below the first non-standard pair

A covering of `R₂^C` ([C09] Def 5.2–5.4) has to keep `≤₁` and `≤₂` only forward.  So a point `c`
below a block that is `≤₁` a point `d` of the block stays `≤₁` every copy of `d` that lies between
`c` and `d` (`le1_of_le_of_le1`); no reach of `c` has to be known.  Only one place moves points up
(the compression of clause 2 of `τ ≤₂ β`), and there one bound `σ₀ < τ` above the reaches that end
below `τ` suffices (`sigma0`: the least point with such a reach has the largest one).  With this the
proofs of stages 1–3 for a block become reach-free:

* `sk1F` (**SK1 in a block** without any hypothesis on the points below the block: `≤₁` of `R₂^C` is
  `≤₁` of `R₁⁺` on `(T, B]` when no `<₂`-pair has its right end in `(T, B)`);
* `reach_max` (the reach of a point below a bound is a maximum), `sigma0`;
* `PairCtxF` (a pair context without reach hypothesis), `PairCtxF.low`, `clause1`, `comp`,
  `clause2`, `pair` (**`τ <₂ β`**), `capF` (**the block cap**: no point of `(T, β]` is `≤₁` a point
  `> β`);
* `IsStd` (the standard pairs `(υ_{μ+ω·(j+1)}, υ_{μ+ω·(j+1)+1})`), `nuC` (`ν_C`, the least right end of
  a non-standard pair), `std_of_lt_nuC`, `le_nuC`, `blockF` (the block `j` of the region of `μ`
  below `ν_C` as a pair context), `pair_std` (**D3**), `block_le1` (**D1**), `land_C`, `le1ρF`
  (Lemma C″ (a) without the hypothesis "no `<₁`-predecessor"), `rst_C` (**D2**), `notRight_C`,
  `noSucc_C`, `classify` (every positive ordinal is a restart or a point of a block),
  `pred_restart_C` (the `<₁`-predecessors of a restart are restarts), `skelPlusC` (**SKEL⁺ in
  `R₂^C` on `[0, ν_C)`**);
* `PSReal`, `TnestC` (`T_C`, the least top of a pair with a pair nested inside), `capTC`
  (**Lemma CAP**), `nuC_le_TnestC` (`ν_C ≤ T_C`).

Everything is FRAG-free and uses no offset and no reach value.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## SK1 in a block, reach-free -/

/-- **SK1 in a block** (reach-free). -/
theorem sk1F {T B : Ordinal.{0}} (hB : B < Om1)
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
          exact le1_of_le_of_le1 (hcT.trans ((hYψ d hdY).1 T hTX2).le)
            ((hYψ d hdY).2.trans_le (hY d hdY).1).le hcd
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


/-- The reach of `c` below a bound `B ≥ c` is a maximum. -/
theorem reach_max {c B : Ordinal.{0}} (hcB : c ≤ B) :
    ∃ r, c ≤ r ∧ r ≤ B ∧ le1 c r ∧ ∀ g, g ≤ B → le1 c g → g ≤ r := by
  set G : Set Ordinal.{0} := {g | g ≤ B ∧ le1 c g} with hG
  have hne : G.Nonempty := ⟨c, hcB, le1_refl c⟩
  have hbdd : BddAbove G := ⟨B, fun g hg => hg.1⟩
  have hcr : c ≤ sSup G := le_csSup hbdd ⟨hcB, le1_refl c⟩
  have hrB : sSup G ≤ B := csSup_le hne (fun g hg => hg.1)
  have hle : ∀ g, g ≤ B → le1 c g → g ≤ sSup G := fun g hgB hg => le_csSup hbdd ⟨hgB, hg⟩
  have hbelow : ∀ b, c ≤ b → b < sSup G → le1 c b := by
    intro b hcb hbr
    obtain ⟨g, hg, hbg⟩ := (lt_csSup_iff hbdd hne).1 hbr
    exact le1_of_le_of_le1 hcb hbg.le hg.2
  refine ⟨sSup G, hcr, hrB, ?_, hle⟩
  by_cases hrG : sSup G ∈ G
  · exact hrG.2
  rcases eq_or_lt_of_le hcr with e | hcr'
  · rw [← e]; exact le1_refl c
  rcases zero_or_succ_or_isSuccLimit (sSup G) with h0 | ⟨x, hx⟩ | hlim
  · rw [h0] at hcr'; exact absurd hcr' (not_lt.2 zero_le)
  · exfalso
    have hxr : x < sSup G := by rw [← hx]; exact lt_succ x
    obtain ⟨g, hg, hxg⟩ := (lt_csSup_iff hbdd hne).1 hxr
    have hgr : g ≤ sSup G := le_csSup hbdd hg
    have : g = sSup G := le_antisymm hgr (by rw [← hx]; exact succ_le_of_lt hxg)
    exact hrG (this ▸ hg)
  · exact le1_limit hlim hcr' hbelow

/-- **The bound `σ₀`**: below a limit `τ > T` there is `σ₀ ∈ [T, τ)` such that every `c ≤ T` that is
`≤₁` a point of `(σ₀, τ)` is `≤₁ τ` (the least `c ≤ T` whose reach ends in `(T, τ)` has the largest
such reach, since a `≤₁`-predecessor has a larger reach). -/
theorem sigma0 {T τ : Ordinal.{0}} (hTτ : T < τ) :
    ∃ σ0, T ≤ σ0 ∧ σ0 < τ ∧ ∀ c ≤ T, ∀ d, σ0 < d → d < τ → le1 c d → le1 c τ := by
  by_cases hex : ∃ c, c ≤ T ∧ ∃ d, T < d ∧ d < τ ∧ le1 c d ∧ ¬ le1 c τ
  · set S : Set Ordinal.{0} := {c | c ≤ T ∧ ∃ d, T < d ∧ d < τ ∧ le1 c d ∧ ¬ le1 c τ} with hSdef
    have hS : S.Nonempty := hex
    have hc0 : sInf S ∈ S := csInf_mem hS
    obtain ⟨hc0T, d0, hTd0, hd0τ, hc0d0, hc0τ⟩ := hc0
    obtain ⟨r0, -, hrτ, hc0r, hmax⟩ := reach_max (c := sInf S) (B := τ) (hc0T.trans hTτ.le)
    have hrτ' : r0 < τ := lt_of_le_of_ne hrτ (fun e => hc0τ (e ▸ hc0r))
    have hd0r : d0 ≤ r0 := hmax d0 hd0τ.le hc0d0
    refine ⟨r0, hTd0.le.trans hd0r, hrτ', fun c hcT d hrd hdτ hcd => ?_⟩
    by_contra hcτ
    have hcS : c ∈ S := ⟨hcT, d, lt_of_le_of_lt (hTd0.le.trans hd0r) hrd, hdτ, hcd, hcτ⟩
    have hc0c : sInf S ≤ c := csInf_le (OrderBot.bddBelow S) hcS
    have h1 : le1 (sInf S) c := le1_of_le_of_le1 hc0c (hcT.trans (hTd0.le.trans hd0r)) hc0r
    have h2 : le1 (sInf S) d := le1_trans h1 hcd
    exact absurd (hmax d hdτ.le h2) (not_le.2 hrd)
  · push Not at hex
    exact ⟨T, le_rfl, hTτ, fun c hcT d hTd hdτ hcd => hex c hcT d hTd hdτ hcd⟩

/-! ## Reach-free pair contexts -/

/-- **A reach-free pair context**: `τ` a countable `υ`-point with `β = τ^∞` countable, `T < τ`,
`υ`-points cofinal below `τ`, and no `<₂`-pair has its right end in `(T, β)`.  Nothing is assumed
about the points `≤ T` that are `≤₁` points above `T`. -/
structure PairCtxF (T τ β : Ordinal.{0}) : Prop where
  τU : UpsPt τ
  next : IsNext τ β
  β1 : β < Om1
  Tτ : T < τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ
  noPair : ∀ c d, c < d → T < d → d < β → ¬ le2 c d

namespace PairCtxF

variable {T τ β : Ordinal.{0}} (h : PairCtxF T τ β)
include h

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, β]` (`sk1F`). -/
theorem low : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b) := fun a b ha hb =>
  sk1F h.β1 h.noPair b hb a ha

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
          -- the copy moves `d` down: `c ≤ f(d) ≤ d` and `c ≤₁ d` give `c ≤₁ f(d)`
          exact le1_of_le_of_le1 (hcT.trans (hTf d (Finset.mem_coe.1 hd) hTd).le)
            ((hYf d hdY).2.trans_le (hY d hdY).1).le hcd
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
    (hc1 : τ ≤ c') (hc2 : c' < β) {σ0 : Ordinal.{0}} (hσ0τ : σ0 < τ)
    (hσ0 : ∀ c ≤ T, ∀ d, σ0 < d → d < τ → le1 c d → le1 c τ) :
    ∃ c'' < τ, ∀ Y0 : Finset Ordinal.{0}, (∀ y ∈ Y0, c'' < y ∧ y < τ) →
      Closed ↑(X ∪ Y0) → ∃ Y : Finset Ordinal.{0}, (∀ y ∈ Y, c' < y ∧ y < β) ∧
        Closed ↑(X ∪ Y) ∧ ∃ g, Cov R2C R2C ↑(X ∪ Y0) ↑(X ∪ Y) g ∧ ∀ x ∈ X, g x = x := by
  classical
  have hτE := upsPt_inE h.τU
  have hτ1 := h.τ1
  have hcT : c' ∈ Tset τ := (h.T_iff c' (hc2.trans h.β1)).2 hc2
  obtain ⟨σ, hσU, hTσ, hστ, hSσ⟩ := h.base_above (insert σ0 (X ∪ Par τ c')) (by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hσ0τ
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · exact Par_sub hτE hτ1 hcT (Finset.mem_coe.2 hs))
  have hσ0σ : σ0 < σ := hSσ σ0 (Finset.mem_insert_self _ _)
  have hSσ : ∀ s ∈ X ∪ Par τ c', s < σ := fun s hs => hSσ s (Finset.mem_insert_of_mem hs)
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
          -- the copy moves `d` up: `d > σ₀`, so `c ≤₁ τ`, and `τ ≤₁ g(d)` inside the block
          have hcτ : le1 c τ := hσ0 c hcT d
            (lt_of_lt_of_le hσ0σ (hctσ.trans (hY0 d hdY).1.le)) (hY0 d hdY).2 hcd
          have hτg : le1 τ (g d) := (h.low τ (g d) h.Tτ (hgβ d hd).le).2
            (h.τU.2 _ (hc1.trans (hgY0 d hdY).le))
          exact le1_trans hcτ hτg
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
  obtain ⟨σ0, -, hσ0τ, hσ0⟩ := sigma0 h.Tτ
  intro c' hc'
  rcases lt_or_ge c' τ with hlt | hge
  · obtain ⟨Y, hY, hcl, f, hcov⟩ := hC c' hlt
    exact ⟨Y, fun y hy => ⟨(hY y hy).1, (hY y hy).2.trans h.τβ⟩, hcl, f, hcov⟩
  · obtain ⟨c'', hc''τ, H⟩ := h.comp X hX hge hc' hσ0τ hσ0
    obtain ⟨Y0, hY0, hcl0, h0, hcov0⟩ := hC c'' hc''τ
    obtain ⟨Y, hY, hcl, g, hg, -⟩ := H Y0 hY0 hcl0
    exact ⟨Y, hY, hcl, g ∘ h0, hcov0.comp hg⟩

/-- **The pair of the block**: `τ <₂ β` in `R₂^C`. -/
theorem pair : le2 τ β :=
  le2_iff.2 ⟨h.τβ.le, fun X Y hX hY hXY => h.clause1 X Y hX hY hXY,
    fun X hX Z P _ hC => h.clause2 X hX Z P hC⟩

/-- **The block cap** (reach-free): no point of `(T, β]` is `≤₁` a point `> β`. -/
theorem capF : ∀ c, T < c → c ≤ β → ∀ g, β < g → ¬ le1 c g := by
  classical
  intro c hTc hcβ g hg hcg
  have hτI := indec_of_upsPt h.τU
  have hβI := indec_of_upsPt h.next.2.1
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
    exact h.noPair _ _ hlt hfβ.1 (lt_of_lt_of_le hfβ.2 (hcτ.trans h.τβ.le)) h2
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
    exact h.noPair _ _ hfβ.1 (h.Tτ.trans hfβ.1) (lt_of_lt_of_le hfβ.2 hcβ) h2

end PairCtxF


/-! ## The standard pairs and the first non-standard right end `ν_C` -/

/-- `(c, d)` is a standard pair: `(υ_{μ+ω·(j+1)}, υ_{μ+ω·(j+1)+1})`, `μ = 0` or a restart index. -/
def IsStd (c d : Ordinal.{0}) : Prop :=
  ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
    d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)

/-- `ν_C`: the least right end of a `<₂`-pair of `R₂^C` that is not standard (`Ω₁` if there is
none); the project's `ν_new` for `R₂^C`. -/
noncomputable def nuC : Ordinal.{0} :=
  sInf (insert Om1 {d | ∃ c, c < d ∧ le2 c d ∧ ¬ IsStd c d})

theorem nuC_le_Om1 : nuC ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem std_of_lt_nuC {c d : Ordinal.{0}} (hd : d < nuC) (hcd : c < d) (h2 : le2 c d) :
    IsStd c d := by
  by_contra hns
  exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show d ∈ {d | ∃ c, c < d ∧ le2 c d ∧ ¬ IsStd c d} from ⟨c, hcd, h2, hns⟩))) (not_le.2 hd)

/-- A lower bound for `ν_C`: every pair with right end below `E ≤ Ω₁` is standard. -/
theorem le_nuC {E : Ordinal.{0}} (hE : E ≤ Om1)
    (h : ∀ c d, c < d → d < E → le2 c d → IsStd c d) : E ≤ nuC := by
  refine le_csInf ⟨Om1, Set.mem_insert _ _⟩ ?_
  rintro b (rfl | ⟨c, hcb, h2, hns⟩)
  · exact hE
  · by_contra hlt
    exact hns (h c b hcb (not_le.1 hlt) h2)

theorem tI_lim (μ : Ordinal.{0}) (j : ℕ) : IsSuccLimit (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) := by
  rw [omega_mul_succ, ← add_assoc]; exact isSuccLimit_add _ isSuccLimit_omega0

theorem tI_not_dvd {μ : Ordinal.{0}} (hμ : μ = 0 ∨ IsRestartIdx μ) (j : ℕ) :
    ¬ ω * ω ∣ μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
  intro hd
  have hpos : (0 : Ordinal.{0}) < ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
    mul_pos omega0_pos (by exact_mod_cast Nat.succ_pos j)
  have h1 := next_mult (mult_of hμ) hd (lt_add_of_pos_right μ hpos)
  have h2 : ω * ω ≤ ω * ((j + 1 : ℕ) : Ordinal.{0}) := (add_le_add_iff_left μ).1 h1
  have h3 : ω ≤ ((j + 1 : ℕ) : Ordinal.{0}) := (mul_le_mul_iff_right₀ omega0_pos).1 h2
  exact absurd h3 (not_le.2 (natCast_lt_omega0 _))

/-- A standard pair is `(υ_L, υ_{L+1})` with `L` a limit that is not a multiple of `ω²`. -/
theorem IsStd.parts {c d : Ordinal.{0}} (h : IsStd c d) :
    ∃ L, IsSuccLimit L ∧ ¬ ω * ω ∣ L ∧ c = upsilon L ∧ d = upsilon (L + 1) := by
  obtain ⟨μ, j, hμ, rfl, rfl⟩ := h
  exact ⟨_, tI_lim μ j, tI_not_dvd hμ j, rfl, rfl⟩

theorem ri_lim {l : Ordinal.{0}} (hl : IsRestartIdx l) : IsSuccLimit l := by
  obtain ⟨p, hp⟩ := (ri_iff.1 hl).2
  have hp0 : p ≠ 0 := by intro h0; rw [h0, mul_zero] at hp; exact hl.1 hp
  rw [hp]
  exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
    (pos_iff_ne_zero.2 hp0)

/-- The context of a block below `ν_C`, bottom `υ_ξ`. -/
theorem ctxF {μ ξ : Ordinal.{0}} (j : ℕ)
    (hξ1 : μ + ω * (j : Ordinal.{0}) ≤ ξ) (hξ2 : ξ < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}))
    (hξ3 : ∀ L, IsSuccLimit L → ¬ ω * ω ∣ L → ξ ≠ L)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) :
    PairCtxF (upsilon ξ) (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})))
      (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) := by
  have hLe : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
    rw [omega_mul_succ, add_assoc]
  have hlim : IsSuccLimit (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) := tI_lim μ j
  have hL0 : 0 < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := lt_of_le_of_lt zero_le hξ2
  refine ⟨upsPt_upsilon hL0, ?_, lt_of_lt_of_le hC nuC_le_Om1, upsilon_normal.strictMono hξ2, ?_, ?_⟩
  · have := upsilon_isNext (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})); rwa [succ_eq_add_one] at this
  · intro c' hc'
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
    refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
      hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
    exact upsilon_normal.strictMono (hlim.succ_lt hι)
  · intro c d hcd hTd hdβ h2
    obtain ⟨L', hL'lim, hL'nd, rfl, rfl⟩ := (std_of_lt_nuC (hdβ.trans hC) hcd h2).parts
    have h1 : ξ < L' + 1 := upsilon_normal.strictMono.lt_iff_lt.1 hTd
    have h2' : L' + 1 < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 :=
      upsilon_normal.strictMono.lt_iff_lt.1 hdβ
    have hL'L : L' < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
      Order.add_one_le_iff.1 (Order.lt_add_one_iff.1 h2')
    rcases eq_or_lt_of_le (Order.lt_add_one_iff.1 h1) with e | hlt
    · exact hξ3 L' hL'lim hL'nd e
    · have := limit_eq_add_omega hL'lim (lt_of_le_of_lt hξ1 hlt) (by rw [← hLe]; exact hL'L.le)
      rw [this, ← hLe] at hL'L
      exact lt_irrefl _ hL'L

/-- The bottom index of block `j` of the region of `μ` (`μ` for `j = 0`, `δ`-index before it
otherwise). -/
noncomputable def botI (μ : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => μ
  | j + 1 => μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1

/-- **The block `j` of the region of `μ` below `ν_C`** as a reach-free pair context. -/
theorem blockF {μ : Ordinal.{0}} (hμ : μ = 0 ∨ IsRestartIdx μ) (j : ℕ)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) :
    PairCtxF (upsilon (botI μ j)) (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})))
      (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) := by
  cases j with
  | zero =>
    refine ctxF 0 (by simp [botI]) ?_ (fun L _ hnd e => hnd (e ▸ mult_of hμ)) hC
    show μ < μ + ω * ((0 + 1 : ℕ) : Ordinal.{0})
    exact lt_add_of_pos_right μ (by simp [omega0_pos])
  | succ k =>
    refine ctxF (k + 1) (by simp only [botI]; exact le_self_add) ?_ ?_ hC
    · show μ + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1 < μ + ω * ((k + 1 + 1 : ℕ) : Ordinal.{0})
      rw [omega_mul_succ (k + 1), ← add_assoc]
      exact (add_lt_add_iff_left _).2 one_lt_omega0
    · intro L hL _ e
      have e' : μ + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1 = L := e
      rw [← e'] at hL
      exact not_isSuccLimit_add_one _ hL

/-- **D3 below `ν_C`**: every standard pair with right end below `ν_C` is a `<₂`-pair. -/
theorem pair_std {μ : Ordinal.{0}} (hμ : μ = 0 ∨ IsRestartIdx μ) (j : ℕ)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) :
    le2 (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})))
      (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) :=
  (blockF hμ j hC).pair

/-- **D1 below `ν_C`**: a point `a` of a block `(T, β]` (`β < ν_C`) is `≤₁ g` iff `g ≤ β` and
`a ≤₁ g` in `R₁⁺`. -/
theorem block_le1 {μ : Ordinal.{0}} (hμ : μ = 0 ∨ IsRestartIdx μ) (j : ℕ)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) {a : Ordinal.{0}}
    (ha1 : upsilon (botI μ j) < a) (ha2 : a ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) :
    ∀ g, le1 a g ↔ (g ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) ∧ le1R a g) := by
  have P := blockF hμ j hC
  intro g
  rcases le_or_gt g (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) with hg | hg
  · rw [P.low a g ha1 hg]; exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩
  · exact ⟨fun h => absurd h (P.capF a ha1 ha2 g hg), fun h => absurd h.1 (not_le.2 hg)⟩

/-! ## The restarts below `ν_C` (D2) -/

theorem add_omega_lt {l x : Ordinal.{0}} (hl : ω * ω ∣ l) (hx : x < l) : x + ω < l := by
  obtain ⟨q, rfl⟩ := hl
  have hww : ω * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  have hdm : ω * ω * (x / (ω * ω)) + x % (ω * ω) = x := div_add_mod x (ω * ω)
  have hm : x % (ω * ω) < ω * ω := mod_lt x hww
  have hq : x / (ω * ω) < q := (lt_mul_iff_div_lt hww).1 hx
  have hP : IsPrincipal (· + ·) (ω * ω) := by
    have : ω * ω = ω ^ (2 : Ordinal.{0}) := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
    rw [this]; exact isPrincipal_add_omega0_opow 2
  have hωww : ω < ω * ω := lt_mul_of_one_lt_right omega0_pos one_lt_omega0
  have h1 : x % (ω * ω) + ω < ω * ω := hP hm hωww
  calc x + ω = ω * ω * (x / (ω * ω)) + (x % (ω * ω) + ω) := by rw [← add_assoc, hdm]
    _ < ω * ω * (x / (ω * ω)) + ω * ω := (add_lt_add_iff_left _).2 h1
    _ = ω * ω * (x / (ω * ω) + 1) := (mul_add_one _ _).symm
    _ ≤ ω * ω * q := mul_le_mul_right (add_one_le_of_lt hq) _

/-- **The landing segments below a restart `ρ_λ ≤ ν_C`**: above every `c' < ρ_λ` a `υ`-point `σ`
with `σ' = σ^∞ < ρ_λ`, `≤₁ = ≤₁` of `R₁⁺` on `(σ, σ')`, `σ ≤₁` every point of `[σ, σ')` and no
`<₂`-pair with right end in `(σ, σ')`. -/
theorem land_C {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon l ≤ nuC) :
    ∀ c' < upsilon l, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l ∧
      (∀ a b, σ < a → b < σ' → (le1 a b ↔ le1R a b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
      (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d) := by
  have hlim : IsSuccLimit l := ri_lim hl
  intro c' hc'
  obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
  have hyl : ι + ω < l := add_omega_lt (ri_iff.1 hl).2 hι
  have hyωl : ι + ω + ω < l := add_omega_lt (ri_iff.1 hl).2 hyl
  have hz : ι + ω + 1 + 1 < l := by
    refine lt_of_lt_of_le ?_ hyωl.le
    rw [add_assoc (ι + ω)]
    exact (add_lt_add_iff_left _).2 (by
      have : (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) := by norm_num
      rw [this]; exact natCast_lt_omega0 2)
  have hsz : succ (ι + ω + 1 + 1) < l := hlim.succ_lt hz
  have hσn : IsNext (upsilon (ι + ω + 1 + 1)) (upsilon (succ (ι + ω + 1 + 1))) :=
    upsilon_isNext _
  have hσU : UpsPt (upsilon (ι + ω + 1 + 1)) := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))
  have hσ'l : upsilon (succ (ι + ω + 1 + 1)) < upsilon l := upsilon_normal.strictMono hsz
  have hσ'1 : upsilon (succ (ι + ω + 1 + 1)) < Om1 := lt_of_lt_of_le (hσ'l.trans_le hC) nuC_le_Om1
  have hno1 : ∀ c d, c < d → upsilon (ι + ω + 1) < d → d < upsilon (succ (ι + ω + 1 + 1)) →
      ¬ le2 c d := by
    intro c d hcd h1 h2 h2'
    obtain ⟨L', hL'lim, -, rfl, rfl⟩ := (std_of_lt_nuC ((h2.trans hσ'l).trans_le hC) hcd h2').parts
    have i1 : ι + ω + 1 < L' + 1 := upsilon_normal.strictMono.lt_iff_lt.1 h1
    have i2 : L' + 1 < succ (ι + ω + 1 + 1) := upsilon_normal.strictMono.lt_iff_lt.1 h2
    have j1 : ι + ω + 1 ≤ L' := Order.lt_add_one_iff.1 i1
    have j2 : L' ≤ ι + ω + 1 := by
      have : L' + 1 ≤ ι + ω + 1 + 1 := Order.lt_succ_iff.1 i2
      exact Order.lt_add_one_iff.1 (lt_of_lt_of_le (lt_add_one L') this)
    have e : L' = ι + ω + 1 := le_antisymm j2 j1
    rw [e] at hL'lim
    exact not_isSuccLimit_add_one _ hL'lim
  have hlt1 : upsilon (ι + ω + 1) < upsilon (ι + ω + 1 + 1) :=
    upsilon_normal.strictMono (lt_add_one _)
  refine ⟨upsilon (ι + ω + 1 + 1), upsilon (succ (ι + ω + 1 + 1)), hσU,
    hcx.trans (upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right ι omega0_pos)
      (le_self_add.trans le_self_add))), hσn, hσ'l, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact sk1F hσ'1 (fun c d hcd hd1 hd2 => hno1 c d hcd (hlt1.trans hd1) hd2) b hb.le a ha
  · intro b hσb hbσ'
    rcases eq_or_lt_of_le hσb with e | hlt
    · rw [← e]; exact le1_refl _
    · exact (sk1F hσ'1 hno1 b hbσ'.le _ hlt1).2 (hσU.2 b hσb)
  · intro c d hcd hd1 hd2
    exact hno1 c d hcd (hlt1.trans hd1) hd2

/-- **Lemma C″ (a), reach-free**: a restart `ρ` that is not a right end is `≤₁ γ` as long as no
`<₂`-pair has its right end in `(ρ, γ)`. -/
theorem le1ρF {ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρ1 : ρ < Om1)
    (hland : ∀ c' < ρ, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < ρ ∧
      (∀ a b, σ < a → b < σ' → (le1 a b ↔ le1R a b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
      (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d))
    (hnr : ∀ c < ρ, ¬ le2 c ρ) :
    ∀ γ, ρ ≤ γ → γ < Om1 → (∀ c d, c < d → ρ < d → d < γ → ¬ le2 c d) → le1 ρ γ := by
  classical
  intro γ hργ hγ1 hno
  rcases eq_or_lt_of_le hργ with e | hργ'
  · rw [← e]; exact le1_refl _
  have hρE := upsPt_inE hρU
  obtain ⟨s1, hs1n, hTρ⟩ := exists_next hρU hρ1
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
  have hs11 : s1 < Om1 := next_lt_Om1 hs1n (Or.inr hρU) hρ1
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
    rw [Finset.sup_lt_iff hρU.1]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hρU.1
    · exact hS b hb
  obtain ⟨σ, σ', hσU, hc'σ, hσn, hσ'ρ, hlow, hσle1, hnop⟩ := hland _ hsup
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
      · -- the copy moves `d` down below `ρ`: `c ≤ f(d) ≤ d` and `c ≤₁ d` give `c ≤₁ f(d)`
        have hcX : c ∈ X := by
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
          · exact hcX
          · exact absurd (hY c hcY).1 (not_le.2 hcρ)
        rw [hfX c hcX]
        exact le1_of_le_of_le1 ((hXσ c hcX).le.trans (hfY d hdY).1)
          (((hfY d hdY).2.trans hσ'ρ).le.trans (hY d hdY).1) hcd
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
        have hR'' := (down_le1R hσU hρU hB (hWTB hcW) (hWTB hdW) (hW1 _ hcW)).1 hR'
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
        exact absurd hcd (hnr c hlt)
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


/-- A restart below `ν_C` is not a right end. -/
theorem notRight_C {l : Ordinal.{0}} (hl : IsRestartIdx l) (hρC : upsilon l < nuC) :
    ∀ c < upsilon l, ¬ le2 c (upsilon l) := by
  intro c hc h2
  obtain ⟨L', -, -, -, e⟩ := (std_of_lt_nuC hρC hc h2).parts
  have he : l = L' + 1 := upsilon_normal.strictMono.injective e
  have := ri_lim hl
  rw [he] at this
  exact not_isSuccLimit_add_one _ this

/-- A restart has no `<₂`-successor below `ν_C`. -/
theorem noSucc_C {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    ∀ d, upsilon l < d → d < nuC → ¬ le2 (upsilon l) d := by
  intro d hd hdC h2
  obtain ⟨L', -, hL'nd, e, -⟩ := (std_of_lt_nuC hdC hd h2).parts
  have he : l = L' := upsilon_normal.strictMono.injective e
  exact hL'nd (he ▸ (ri_iff.1 hl).2)

/-- **D2 below `ν_C`**: a restart `ρ_λ` with `δ_λ < ν_C` is `≤₁` every point of `[ρ_λ, δ_λ]`. -/
theorem rst_C {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon (l + ω + 1) < nuC) :
    ∀ g, upsilon l ≤ g → g ≤ upsilon (l + ω + 1) → le1 (upsilon l) g := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρδ : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  have hρC : upsilon l < nuC := hρδ.trans hC
  intro g hg1 hg2
  refine le1ρF (upsPt_upsilon hl0) (lt_of_lt_of_le hρC nuC_le_Om1) (land_C hl hρC.le)
    (notRight_C hl hρC) g hg1 (lt_of_le_of_lt hg2 (lt_of_lt_of_le hC nuC_le_Om1)) ?_
  intro c d hcd hρd hdg h2
  obtain ⟨L', hL'lim, hL'nd, rfl, rfl⟩ :=
    (std_of_lt_nuC ((lt_of_lt_of_le hdg hg2).trans hC) hcd h2).parts
  have i1 : l < L' + 1 := upsilon_normal.strictMono.lt_iff_lt.1 hρd
  have i2 : L' + 1 < l + ω + 1 := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_lt_of_le hdg hg2)
  have hlL : l ≤ L' := Order.lt_add_one_iff.1 i1
  have hL'2 : L' < l + ω := Order.add_one_le_iff.1 (Order.lt_add_one_iff.1 i2)
  rcases eq_or_lt_of_le hlL with e | hlt
  · exact hL'nd (e ▸ (ri_iff.1 hl).2)
  · exact absurd (limit_eq_add_omega hL'lim hlt hL'2.le) (ne_of_lt hL'2)

/-! ## Lemma CAP: the least pair with a pair nested inside -/

/-- A realization of PS: a `<₂`-pair `x <₂ y` with a `<₂`-pair `x' <₂ y'` strictly inside. -/
def PSReal (x x' y' y : Ordinal.{0}) : Prop := x < x' ∧ x' < y' ∧ y' < y ∧ le2 x y ∧ le2 x' y'

/-- `T_C`: the least top of a realization of PS (`Ω₁` if there is none). -/
noncomputable def TnestC : Ordinal.{0} := sInf (insert Om1 {y | ∃ x x' y', PSReal x x' y' y})

theorem TnestC_le_Om1 : TnestC ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem TnestC_le {x x' y' y : Ordinal.{0}} (h : PSReal x x' y' y) : TnestC ≤ y :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨x, x', y', h⟩)

/-- **Lemma CAP** in `R₂^C`: if `T_C` is the top of a realization of PS, no `α ≤ T_C` is `≤₁` a point
`> T_C` ("a pair with a pair nested inside exists" is a `Σ₁` statement without parameters). -/
theorem capTC {x x' y' : Ordinal.{0}} (hR : PSReal x x' y' TnestC) :
    ∀ α ≤ TnestC, ∀ g, TnestC < g → ¬ le1 α g := by
  classical
  intro α hα g hg hαg
  obtain ⟨h1, h2, h3, hp, hp'⟩ := hR
  rcases eq_or_ne α 0 with rfl | hα0
  · exact not_le1_zero (lt_of_le_of_lt zero_le hg) hαg
  have hxy : x < TnestC := h1.trans (h2.trans h3)
  have hx1 : x < Om1 := lt_of_lt_of_le hxy TnestC_le_Om1
  have hx'1 : x' < Om1 := lt_of_lt_of_le (h2.trans h3) TnestC_le_Om1
  have hxI : Indec x := indec_of_upsPt (left hp hxy hx1)
  have hx'I : Indec x' := indec_of_upsPt (left hp' h2 hx'1)
  have hyI : Indec TnestC := (indec_of_lt2_right hp hxy).1
  have hy'I : Indec y' := (indec_of_lt2_right hp' h2).1
  set Rs : Finset Ordinal.{0} := {x, x', y', TnestC} with hRs
  have hRle : ∀ z ∈ Rs, z ≤ TnestC := by
    intro z hz
    simp only [hRs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hxy.le
    · exact (h2.trans h3).le
    · exact h3.le
    · exact le_rfl
  set X := Rs.filter (· < α) with hX
  set Y := Rs.filter (fun z => ¬ z < α) with hY
  have hXY : X ∪ Y = Rs := Finset.filter_union_filter_not_eq _ _
  have hcl : Closed (↑(X ∪ Y) : Set Ordinal.{0}) := by
    rw [hXY]
    refine closed_of_indec ?_
    intro z hz
    simp only [hRs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hxI
    · exact hx'I
    · exact hy'I
    · exact hyI
  obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hαg (pos_iff_ne_zero.2 hα0) X Y
    (fun z hz => (Finset.mem_filter.1 hz).2)
    (fun z hz => ⟨not_lt.1 (Finset.mem_filter.1 hz).2,
      lt_of_le_of_lt (hRle z (Finset.mem_filter.1 hz).1) hg⟩) hcl
  have hm : ∀ z ∈ Rs, z ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by
    intro z hz; rw [hXY]; exact hz
  have mx : x ∈ Rs := by simp [hRs]
  have mx' : x' ∈ Rs := by simp [hRs]
  have my' : y' ∈ Rs := by simp [hRs]
  have my : TnestC ∈ Rs := by simp [hRs]
  have hR' : PSReal (f x) (f x') (f y') (f TnestC) :=
    ⟨hf.1.2.1 (hm x mx) (hm x' mx') h1, hf.1.2.1 (hm x' mx') (hm y' my') h2,
      hf.1.2.1 (hm y' my') (hm _ my) h3, hf.2.2 _ (hm x mx) _ (hm _ my) hp,
      hf.2.2 _ (hm x' mx') _ (hm y' my') hp'⟩
  have hTY : TnestC ∈ Y := Finset.mem_filter.2 ⟨my, not_lt.2 hα⟩
  have hfT : f TnestC < α := (hYt _ (hmap TnestC hTY)).2
  exact absurd (TnestC_le hR') (not_le.2 (lt_of_lt_of_le hfT hα))

/-- The outer pair of a realization of PS is not standard, so `ν_C ≤` its top. -/
theorem nuC_le_of_PSReal {x x' y' y : Ordinal.{0}} (h : PSReal x x' y' y) : nuC ≤ y := by
  by_contra hlt
  have hlt : y < nuC := not_le.1 hlt
  obtain ⟨h1, h2, h3, hp, hp'⟩ := h
  obtain ⟨L, -, -, rfl, rfl⟩ := (std_of_lt_nuC hlt (h1.trans (h2.trans h3)) hp).parts
  have hn : IsNext (upsilon L) (upsilon (L + 1)) := by
    have := upsilon_isNext L; rwa [succ_eq_add_one] at this
  have hx'1 : x' < Om1 := lt_of_lt_of_le ((h2.trans h3).trans hlt) nuC_le_Om1
  exact absurd (hn.2.2 x' h1 (left hp' h2 hx'1)) (not_le.2 (h2.trans h3))

/-- **`ν_C ≤ T_C`**. -/
theorem nuC_le_TnestC : nuC ≤ TnestC := by
  rcases csInf_mem (s := insert Om1 {y | ∃ x x' y', PSReal x x' y' y}) ⟨Om1, Set.mem_insert _ _⟩
    with h | ⟨x, x', y', h⟩
  · show nuC ≤ sInf _; rw [h]; exact nuC_le_Om1
  · exact nuC_le_of_PSReal h

/-! ## Every point is a restart or lies in a block; the `<₁`-predecessors of a restart -/

theorem botI_ge (μ : Ordinal.{0}) : ∀ j : ℕ, μ + ω * (j : Ordinal.{0}) ≤ botI μ j
  | 0 => by simp [botI]
  | k + 1 => le_self_add

/-- **Every positive ordinal is a restart or a point of a block** (bottom excluded, top included). -/
theorem classify {c : Ordinal.{0}} (hc0 : 0 < c) :
    (∃ l, IsRestartIdx l ∧ c = upsilon l) ∨ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
      upsilon (botI μ j) < c ∧ c ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
  classical
  have hww : ω * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  -- the least index `ι₁` with `c < υ_{ι₁}` is a successor `ι + 1`
  set S : Set Ordinal.{0} := {ι | c < upsilon ι} with hSdef
  have hS : S.Nonempty := ⟨c + 1, lt_of_lt_of_le (lt_add_one c)
    (upsilon_normal.strictMono.id_le (c + 1))⟩
  have hmem : c < upsilon (sInf S) := csInf_mem hS
  have hmin : ∀ ι < sInf S, upsilon ι ≤ c := fun ι hι => not_lt.1 (fun h' =>
    absurd (csInf_le (OrderBot.bddBelow S) (show ι ∈ S from h')) (not_le.2 hι))
  obtain ⟨ι, hι1, hιc⟩ : ∃ ι, c < upsilon (ι + 1) ∧ upsilon ι ≤ c := by
    rcases zero_or_succ_or_isSuccLimit (sInf S) with h0 | ⟨x, hx⟩ | hlim
    · rw [h0, upsilon_zero] at hmem; exact absurd hmem (not_lt.2 zero_le)
    · refine ⟨x, ?_, hmin x (by rw [← hx]; exact lt_succ x)⟩
      rw [← succ_eq_add_one, hx]; exact hmem
    · exfalso
      obtain ⟨_, ⟨ι', hι', rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hmem
      exact absurd (hmin ι' hι') (not_le.2 hcx)
  -- the region `μ = ω²·⌊ι/ω²⌋`
  set μ := ω * ω * (ι / (ω * ω)) with hμdef
  have hdm : μ + ι % (ω * ω) = ι := div_add_mod ι (ω * ω)
  have hμι : μ ≤ ι := by rw [← hdm]; exact le_self_add
  have hιμ : ι < μ + ω * ω := by
    rw [← hdm]; exact (add_lt_add_iff_left μ).2 (mod_lt ι hww)
  have hμm : μ = 0 ∨ IsRestartIdx μ := by
    rcases eq_or_ne μ 0 with h | h
    · exact Or.inl h
    · exact Or.inr (ri_iff.2 ⟨h, dvd_mul_right _ _⟩)
  have hμc : upsilon μ ≤ c := (upsilon_normal.strictMono.monotone hμι).trans hιc
  have hcμ : c < upsilon (μ + ω * ω) :=
    lt_of_lt_of_le hι1 (upsilon_normal.strictMono.monotone (add_one_le_of_lt hιμ))
  rcases eq_or_lt_of_le hμc with e | hlt
  · left
    rcases hμm with h0 | hr
    · rw [h0, upsilon_zero] at e; exact absurd e.symm hc0.ne'
    · exact ⟨μ, hr, e.symm⟩
  · right
    rcases chainA_sup (a := μ) (T0 := upsilon μ) le_rfl hcμ with hle | hex
    · exact absurd hlt (not_lt.2 hle)
    set j := Nat.find hex with hj
    have hcj : c ≤ topA μ (upsilon μ) (j + 1) := Nat.find_spec hex
    have htop : topA μ (upsilon μ) (j + 1) = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
      show upsilon (μ + ω * (j : Ordinal.{0}) + ω + 1) = _
      rw [omega_mul_succ, ← add_assoc]
    refine ⟨μ, j, hμm, ?_, by rw [← htop]; exact hcj⟩
    rcases hj0 : j with _ | k
    · simpa [botI] using hlt
    · have hk : ¬ c ≤ topA μ (upsilon μ) (k + 1) := Nat.find_min hex (by omega)
      have : topA μ (upsilon μ) (k + 1) = upsilon (botI μ (k + 1)) := by
        show upsilon (μ + ω * (k : Ordinal.{0}) + ω + 1) = upsilon (μ + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1)
        rw [omega_mul_succ, ← add_assoc]
      rw [← this]; exact not_le.1 hk

/-- **The `<₁`-predecessors of a restart `ρ_λ ≤ ν_C` are restarts** (block points are capped by their
block tops, which lie below `ρ_λ`); conversely every restart `z < ρ_λ` with reach `≥ ρ_λ` is one
(interval property). -/
theorem pred_restart_C {l c : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon l ≤ nuC)
    (hc : c < upsilon l) (h : le1 c (upsilon l)) : ∃ μ, IsRestartIdx μ ∧ c = upsilon μ := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  rcases eq_or_ne c 0 with rfl | hc0
  · exact absurd h (not_le1_zero hρ0)
  rcases classify (pos_iff_ne_zero.2 hc0) with hr | ⟨μ, j, hμ, hb, hct⟩
  · exact hr
  exfalso
  have hβl : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon l := by
    by_contra hle
    have hle : upsilon l ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := not_lt.1 hle
    have i1 : botI μ j < l := upsilon_normal.strictMono.lt_iff_lt.1 (hb.trans hc)
    have i2 : l ≤ μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := upsilon_normal.strictMono.le_iff_le.1 hle
    have i3 : l ≤ μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
      rcases eq_or_lt_of_le i2 with e | hlt
      · have := ri_lim hl; rw [e] at this; exact absurd this (not_isSuccLimit_add_one _)
      · exact Order.lt_add_one_iff.1 hlt
    have hLe : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
      rw [omega_mul_succ, add_assoc]
    have e := limit_eq_add_omega (ri_lim hl) (lt_of_le_of_lt (botI_ge μ j) i1) (by rw [← hLe]; exact i3)
    rw [← hLe] at e
    exact tI_not_dvd hμ j (e ▸ (ri_iff.1 hl).2)
  have P := blockF hμ j (hβl.trans_le hC)
  exact P.capF c hb hct _ hβl h

/-- **SKEL⁺ in `R₂^C` on `[0, ν_C)`** (reach-free): (D0) every `<₂`-pair with right end below `ν_C`
is standard (the definition of `ν_C`); (D3) every standard pair with right end below `ν_C` is a
`<₂`-pair; (D1) every positive ordinal is a restart or a point `a` of a block `(T, β]`, and if
`β < ν_C` then `a ≤₁ g` iff `g ≤ β` and `a ≤₁ g` in `R₁⁺`; (D2) a restart `ρ_λ` with `δ_λ < ν_C` is
`≤₁` every point of `[ρ_λ, δ_λ]`; (PRED) the `<₁`-predecessors of a restart `ρ_λ ≤ ν_C` are restarts. -/
theorem skelPlusC :
    (∀ c d, c < d → d < nuC → le2 c d → IsStd c d) ∧
    (∀ μ (j : ℕ), (μ = 0 ∨ IsRestartIdx μ) →
      upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC →
      le2 (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})))
        (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ a, 0 < a → (∃ l, IsRestartIdx l ∧ a = upsilon l) ∨ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
      upsilon (botI μ j) < a ∧ a ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) ∧
      (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC → ∀ g, le1 a g ↔
        (g ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) ∧ le1R a g))) ∧
    (∀ l, IsRestartIdx l → upsilon (l + ω + 1) < nuC →
      ∀ g, upsilon l ≤ g → g ≤ upsilon (l + ω + 1) → le1 (upsilon l) g) ∧
    (∀ l, IsRestartIdx l → upsilon l ≤ nuC → ∀ c < upsilon l, le1 c (upsilon l) →
      ∃ μ, IsRestartIdx μ ∧ c = upsilon μ) := by
  refine ⟨fun c d hcd hd h2 => std_of_lt_nuC hd hcd h2, fun μ j hμ hC => pair_std hμ j hC,
    fun a ha => ?_, fun l hl hC => rst_C hl hC, fun l hl hC c hc h => pred_restart_C hl hC hc h⟩
  rcases classify ha with hr | ⟨μ, j, hμ, hb, ht⟩
  · exact Or.inl hr
  · exact Or.inr ⟨μ, j, hμ, hb, ht, fun hC => block_le1 hμ j hC hb ht⟩

end Googology.Trans.PoR.InaccPsi.R2
