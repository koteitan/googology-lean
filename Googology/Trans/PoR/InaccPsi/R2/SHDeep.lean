import Googology.Trans.PoR.InaccPsi.R2.LiftR

/-!
# Lemma DEEP, Corollary D, `T_ω`, and the predecessor clause of Theorem SH in `R₂^C`

A pair is `x <₂ y`; it is the outer pair of a `k`-nest if some `k`-nest `(a, b)` (`R2.NestDef`) has
`a 0 = x`, `b 0 = y`.  `T_ω = sup_k T_k` (`shTw`).

* `shDeep` (**Lemma DEEP**): if `x <₂ y` and `x ≤₁ g` for some `g > y` (the reach of `x` is beyond `y`),
  then `(x, y)` is the outer pair of a `k`-nest for every `k`.  By induction on `k`: `x ≤₁ y + 1`, a
  `k`-nest with outer pair `(x, y)` lies in `[x, y + 1)`, and NEST-UP (`nest_up`) gives a `(k+1)`-nest
  with the same outer pair.
* `shTw`, `shTk_lt_Tw` (`T_k < T_ω`), `shLt_Tw_iff`, `shTw_lt_Om1` (**`T_ω < Ω₁`**: a countable supremum
  of countable ordinals), `shTkA_lt_Tw` (`T_k(ξ) < T_ω` for `ξ < T_ω`).
* **Corollary D** (below `T_ω`): `shD_depth` (every pair has finite depth), `shD_reach` (the reach of the
  left end is the right end), `shD_noCross` (no `u ∈ (x, y]` is `≤₁` a point `> y`: two pairs are
  nested or disjoint, and no point is both a left end and a right end), `shD_oneRight` (each left end
  has one right end), `shD_oneLeft` (no `x' ∈ (x, y)` is `≤₁ y`; in particular each right end has one
  left end), `shD_inside` (a point strictly inside a pair has its reach below the right end).
* `shSH_pred` (**the predecessor clause of Theorem SH**): for `ξ < T_ω`, `T_k(ξ)` has exactly one
  `<₂`-predecessor among all points, not only among the points above `ξ`; `shSH_block` is the block
  shape of `sh_block` with this clause and with `T_k(ξ) < T_ω`.
* **LIM-CAP at `T_ω`**: `shTw_noCross` (no `a < T_ω ≤ b` with `a ≤₁ b`), `shTw_noPred1` (`T_ω` has no
  `<₁`-predecessor), `shTw_notLeft` (`T_ω` is no `<₂`-left end), so `T_ω` lies in no `<₂`-pair.

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## Lemma DEEP -/

/-- The empty nest. -/
theorem shNest_zero (a b : ℕ → Ordinal.{0}) : NestSeq 0 a b :=
  ⟨fun _ hi => absurd hi (by omega), fun _ hi => absurd hi (by omega)⟩

/-- **Lemma DEEP**: if `x <₂ y` and `x ≤₁ g` for some `g > y`, then `(x, y)` is the outer pair of a
`k`-nest for every `k`. -/
theorem shDeep {x y g : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y) (hyg : y < g) (h1 : le1 x g) :
    ∀ k : ℕ, ∃ a b, NestSeq (k + 1) a b ∧ a 0 = x ∧ b 0 = y := by
  have hx1 : le1 x (y + 1) :=
    le1_of_le_of_le1 (hxy.le.trans le_self_add) (Order.add_one_le_of_lt hyg) h1
  intro k
  induction k with
  | zero =>
    exact ⟨consS x (fun _ => 0), consS y (fun _ => 0),
      (shNest_zero _ _).cons (fun h => absurd h (lt_irrefl 0)) hxy h2, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨a, b, hN, ha, hb⟩ := ih
    exact nest_up hN hx1 (fun _ => ⟨ha.ge, by rw [hb]; exact Order.lt_add_one_iff.2 le_rfl⟩) h2 hxy

/-! ## `T_ω` -/

/-- `T_ω = sup_k T_k`. -/
noncomputable def shTw : Ordinal.{0} := ⨆ m : ℕ, Tk (m + 1)

theorem shTk_bdd : BddAbove (Set.range fun m : ℕ => Tk (m + 1)) :=
  ⟨Om1, by rintro _ ⟨m, rfl⟩; exact Tk_le_Om1 _⟩

theorem shTk_le_Tw (m : ℕ) : Tk (m + 1) ≤ shTw := le_ciSup shTk_bdd m

/-- **`T_k < T_ω`**. -/
theorem shTk_lt_Tw (m : ℕ) : Tk (m + 1) < shTw :=
  (Tk_lt_succ_all m).trans_le (shTk_le_Tw (m + 1))

theorem shLt_Tw_iff {ξ : Ordinal.{0}} : ξ < shTw ↔ ∃ m : ℕ, ξ < Tk (m + 1) :=
  lt_ciSup_iff shTk_bdd

theorem shTw_pos : 0 < shTw := lt_of_le_of_lt zero_le (shTk_lt_Tw 0)

/-- **`T_ω < Ω₁`**. -/
theorem shTw_lt_Om1 : shTw < Om1 :=
  Ordinal.iSup_lt_omega_one (fun m => Tk_lt_Om1_all (k := m + 1) (by omega))

/-- **`T_k(ξ) < T_ω` for `ξ < T_ω`**. -/
theorem shTkA_lt_Tw {ξ : Ordinal.{0}} (hξ : ξ < shTw) (m : ℕ) : TkA ξ (m + 1) < shTw := by
  obtain ⟨j, hj⟩ := shLt_Tw_iff.1 hξ
  have := TkA_le_Tk (j := j + 1) (by omega) hj m
  exact lt_of_le_of_lt this (shTk_lt_Tw (j + 1 + m))

/-- A point that is the top of a `k`-nest for every `k` is at least `T_ω`. -/
theorem shTw_le_of_deep {y : Ordinal.{0}} (h : ∀ k : ℕ, ∃ a b, NestSeq (k + 1) a b ∧ b 0 = y) :
    shTw ≤ y := by
  refine ciSup_le fun m => ?_
  obtain ⟨a, b, hN, hb⟩ := h m
  exact hb ▸ Tk_le hN

/-! ## Corollary D -/

section CorD

variable {x y : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y) (hyW : y < shTw)
include hxy h2 hyW

/-- Below `T_ω` the left end of a pair is `≤₁` no point above the right end. -/
theorem shD_noReach : ∀ g, y < g → ¬ le1 x g := by
  intro g hyg h1
  have hd := shDeep hxy h2 hyg h1
  exact absurd (shTw_le_of_deep fun k => by
    obtain ⟨a, b, hN, -, hb⟩ := hd k; exact ⟨a, b, hN, hb⟩) (not_le.2 hyW)

omit hxy h2 in
/-- **Every pair below `T_ω` has finite depth** (stated for any `x` and any `y < T_ω`). -/
theorem shD_depth : ∃ k : ℕ, ¬ ∃ a b, NestSeq (k + 1) a b ∧ a 0 = x ∧ b 0 = y := by
  obtain ⟨m, hm⟩ := shLt_Tw_iff.1 hyW
  refine ⟨m, ?_⟩
  rintro ⟨a, b, hN, -, hb⟩
  exact absurd (hb ▸ Tk_le hN) (not_le.2 hm)

/-- **The reach of the left end of a pair below `T_ω` is its right end.** -/
theorem shD_reach : IsReach R2C x y :=
  ⟨le2_le1 h2, fun g hg => not_lt.1 fun h => shD_noReach hxy h2 hyW g h hg⟩

/-- **No crossing**: no `u ∈ (x, y]` is `≤₁` a point above `y`.  So two pairs below `T_ω` are nested or
disjoint, and no point is both a left end and a right end. -/
theorem shD_noCross : ∀ u, x < u → u ≤ y → ∀ g, y < g → ¬ le1 u g := by
  intro u hxu huy g hyg h1
  have hxu1 : le1 x u := le1_of_le_of_le1 hxu.le huy (le2_le1 h2)
  exact shD_noReach hxy h2 hyW g hyg (le1_trans hxu1 h1)

/-- **Each left end has one right end.** -/
theorem shD_oneRight : ∀ y', y < y' → ¬ le2 x y' :=
  fun y' hyy' h2' => shD_noReach hxy h2 hyW y' hyy' (le2_le1 h2')

omit hxy in
/-- **No `x' ∈ (x, y)` is `≤₁ y`**; in particular each right end has one left end. -/
theorem shD_oneLeft : ∀ x', x < x' → x' < y → ¬ le1 x' y := by
  intro x' hxx' hx'y h1
  have h2' : le2 x x' := le2_of_le1 hxx'.le hx'y.le h2 h1
  exact shD_noReach hxx' h2' (hx'y.trans hyW) y hx'y (le2_le1 h2)

omit hxy in
/-- **A point strictly inside a pair has its reach below the right end.** -/
theorem shD_inside : ∀ z, x < z → z < y → ∀ g, le1 z g → g < y := by
  intro z hxz hzy g h1
  by_contra hg
  push Not at hg
  exact shD_oneLeft h2 hyW z hxz hzy (le1_of_le_of_le1 hzy.le hg h1)

end CorD

/-- **Each right end below `T_ω` has one left end.** -/
theorem shD_oneLeft2 {x x' y : Ordinal.{0}} (hxy : x < y) (hx'y : x' < y) (h2 : le2 x y)
    (h2' : le2 x' y) (hyW : y < shTw) : x = x' := by
  rcases lt_trichotomy x x' with h | h | h
  · exact absurd (le2_le1 h2') (shD_oneLeft h2 hyW x' h hx'y)
  · exact h
  · exact absurd (le2_le1 h2) (shD_oneLeft h2' hyW x h hxy)

/-! ## Theorem SH: the predecessor clause -/

/-- **`T_k(ξ)` has exactly one `<₂`-predecessor** (among all points), for `ξ < T_ω`: the outer left end
`x(ξ)` of the least `k`-nest above `ξ`. -/
theorem shSH_pred {ξ : Ordinal.{0}} (hξ : ξ < shTw) (m : ℕ) :
    ∃ x, ξ < x ∧ x < TkA ξ (m + 1) ∧ le2 x (TkA ξ (m + 1)) ∧
      ∀ c < TkA ξ (m + 1), le2 c (TkA ξ (m + 1)) → c = x := by
  obtain ⟨j, hj⟩ := shLt_Tw_iff.1 hξ
  obtain ⟨x, hξx, hxT, hx2, -⟩ := sh_block (j := j + 1) (by omega) hj m
  exact ⟨x, hξx, hxT, hx2, fun c hc h2 =>
    (shD_oneLeft2 hxT hc hx2 h2 (shTkA_lt_Tw hξ m)).symm⟩

/-- **The block of level `m + 1` above any `ξ < T_ω`** (Theorem SH, the block clauses): `sh_block` with
the predecessor clause for all points and `T(ξ) < T_ω`. -/
theorem shSH_block {ξ : Ordinal.{0}} (hξ : ξ < shTw) (m : ℕ) :
    ∃ x, ξ < x ∧ x < TkA ξ (m + 1) ∧ le2 x (TkA ξ (m + 1)) ∧ TkA ξ (m + 1) < shTw ∧
    Set.Iic (TkA ξ (m + 1)) ⊆ Core R2C ∧
    (∀ α, ξ < α → α ≤ TkA ξ (m + 1) → ∀ g, TkA ξ (m + 1) < g → ¬ le1 α g) ∧
    (∀ c < TkA ξ (m + 1), le2 c (TkA ξ (m + 1)) → c = x) ∧
    (∀ w, x < w → le2 x w → w = TkA ξ (m + 1)) ∧
    (∀ u, ξ < u → ((u ≤ TkA ξ (m + 1) ∧ le1 u (TkA ξ (m + 1))) ↔
      ((u < x ∧ le1 u x) ∨ u = x ∨ u = TkA ξ (m + 1)))) ∧
    (∀ u, ξ < u → u < x → le1 u x → ∀ w, u < w → ¬ le2 u w) ∧
    (∀ u, ξ < u → u ≤ TkA ξ (m + 1) → le1 u (TkA ξ (m + 1)) → IsReach R2C u (TkA ξ (m + 1))) ∧
    (∀ s < x, Set.Finite {u | ξ < u ∧ u < s ∧ le1 u x}) := by
  obtain ⟨j, hj⟩ := shLt_Tw_iff.1 hξ
  obtain ⟨x, hξx, hxT, hx2, -, -, hcore, hcap, -, hsucc, hU, hnoL, hreach, hoC⟩ :=
    sh_block (j := j + 1) (by omega) hj m
  have hTW := shTkA_lt_Tw hξ m
  exact ⟨x, hξx, hxT, hx2, hTW, hcore, hcap,
    fun c hc h2 => (shD_oneLeft2 hxT hc hx2 h2 hTW).symm, hsucc, hU, hnoL, hreach, hoC⟩

/-! ## LIM-CAP at `T_ω` -/

/-- **No `a < T_ω ≤ b` with `a ≤₁ b`.** -/
theorem shTw_noCross : ∀ a < shTw, ∀ b, shTw ≤ b → ¬ le1 a b := by
  intro a ha b hb h1
  obtain ⟨m, hm⟩ := shLt_Tw_iff.1 ha
  obtain ⟨a', b', hN, hT⟩ := Tk_attained (Tk_lt_Om1_all (k := m + 1) (by omega))
  exact cap_Tk (by omega) hN hT a hm.le b (lt_of_lt_of_le (shTk_lt_Tw m) hb) h1

/-- **`T_ω` has no `<₁`-predecessor.** -/
theorem shTw_noPred1 : ∀ a < shTw, ¬ le1 a shTw := fun a ha => shTw_noCross a ha _ le_rfl

/-- **`T_ω` is no `<₂`-left end** (its `≤₁`-predecessors would be cofinal below it). -/
theorem shTw_notLeft : ∀ w, shTw < w → ¬ le2 shTw w := by
  intro w hw h2
  obtain ⟨y, -, hy, hy1⟩ := pred1_cof h2 hw 0 shTw_pos
  exact shTw_noPred1 y hy hy1

end Googology.Trans.PoR.InaccPsi.R2
