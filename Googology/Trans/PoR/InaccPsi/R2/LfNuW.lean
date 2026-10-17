import Googology.Trans.PoR.InaccPsi.R2.SHTop

/-!
# NU-OMEGA in `R₂^C`: the reach of `T_ω`

`T_ω = sup_k T_k` (`shTw`, `R2.SHDeep`).  LIM-CAP (`shTw_noCross`, `shTw_noPred1`, `shTw_notLeft`) says that
`T_ω` lies in no pair and has no `<₁`-predecessor.  A **long pair** is `x <₂ y` with `x ≤₁ y'` for some
`y' > y` (equivalently `x ≤₁ y + 1`).  `Y_LL` (`lfYLL`) is the least `y'` with `x <₂ y < y'` and `x ≤₁ y'`
for some `x, y`.

* `lfLong_above` (**every long left end lies above `T_ω`**), `lfFan_above` (**every fan apex lies above
  `T_ω`**: a point with two `<₂`-successors);
* `lfTw_lh` (**`lh(T_ω) ≤ y + 1` for every long pair `(x, y)`**: if `T_ω ≤₁ g` then `g ≤ y + 1`), with
  `lfTw_reach` (`T_ω` then has a reach, and it is `≤ y + 1`);
* `lfTw_lh_YLL` (**`lh(T_ω) ≤ Y_LL`**, if a long pair exists).

Proof of `lfTw_lh`: `x > T_ω`; if `T_ω ≤₁ g` with `g > y + 1`, the closed set `{1} ∪ {x, y, y + 1}`
(with `{x, y, y + 1} ⊆ [T_ω, g)`) has a copy `{1} ∪ {x', y', y' + 1}` below `T_ω` ([C09] Def 5.3, as
`le1_cof`), and `x' <₂ y'`, `x' ≤₁ y' + 1` contradict Corollary D (`shD_noReach`).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **Every long left end lies above `T_ω`**: `x <₂ y < y'` and `x ≤₁ y'` give `T_ω < x`. -/
theorem lfLong_above {x y y' : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y) (hyy : y < y')
    (h1 : le1 x y') : shTw < x := by
  rcases lt_or_ge x shTw with hx | hx
  · rcases lt_or_ge y shTw with hy | hy
    · exact absurd h1 (shD_noReach hxy h2 hy y' hyy)
    · exact absurd (le2_le1 h2) (shTw_noCross x hx y hy)
  · rcases eq_or_lt_of_le hx with he | hlt
    · subst he
      exact absurd h2 (shTw_notLeft y hxy)
    · exact hlt

/-- **Every fan apex lies above `T_ω`**: `x <₂ y₁`, `x <₂ y₂`, `y₁ < y₂` give `T_ω < x`. -/
theorem lfFan_above {x y1 y2 : Ordinal.{0}} (hxy : x < y1) (h12 : y1 < y2) (h21 : le2 x y1)
    (h22 : le2 x y2) : shTw < x :=
  lfLong_above hxy h21 h12 (le2_le1 h22)

theorem lfOne_lt_Tw : (1 : Ordinal.{0}) < shTw := by
  obtain ⟨a, b, hN, hT⟩ := Tk_attained (Tk_lt_Om1_all (k := 1) le_rfl)
  have ha : 0 < a 0 := (hN.indec (hN.a_mem (by omega))).pos
  have h1 : (1 : Ordinal.{0}) ≤ a 0 := by simpa using Order.add_one_le_of_lt ha
  exact lt_of_le_of_lt h1 ((lv_xT hN).trans (by rw [hT]; exact shTk_lt_Tw 0))

/-- **`lh(T_ω) ≤ y + 1` for every long pair `(x, y)`**: if `x <₂ y` and `x ≤₁ y + 1`, then every `g` with
`T_ω ≤₁ g` is `≤ y + 1`. -/
theorem lfTw_lh {x y : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y) (h1 : le1 x (y + 1)) :
    ∀ g, le1 shTw g → g ≤ y + 1 := by
  classical
  intro g hg
  by_contra hgy
  push Not at hgy
  have hWx : shTw < x := lfLong_above hxy h2 (Order.lt_add_one_iff.2 le_rfl) h1
  have hxI : Indec x := indec_of_lt1 (le2_le1 h2) hxy
  have hyI : Indec y := (indec_of_lt2_right h2 hxy).1
  have h1I : Indec (1 : Ordinal.{0}) := by simpa using indec_opow 0
  have hy1 : y < y + 1 := Order.lt_add_one_iff.2 le_rfl
  have h1y : (1 : Ordinal.{0}) < y + 1 :=
    lt_of_le_of_lt (by simpa using Order.add_one_le_of_lt hyI.pos) hy1
  set X : Finset Ordinal.{0} := {1} with hXd
  set Y : Finset Ordinal.{0} := {x, y, y + 1} with hYd
  have hX : ∀ z ∈ X, z < shTw := by
    intro z hz
    rw [hXd, Finset.mem_singleton] at hz
    rw [hz]; exact lfOne_lt_Tw
  have hY : ∀ z ∈ Y, shTw ≤ z ∧ z < g := by
    intro z hz
    rw [hYd, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨hWx.le, (hxy.trans hy1).trans hgy⟩
    · exact ⟨(hWx.trans hxy).le, hy1.trans hgy⟩
    · exact ⟨(hWx.trans (hxy.trans hy1)).le, hgy⟩
  have hmem : ∀ z, z ∈ (↑(X ∪ Y) : Set Ordinal.{0}) ↔ z = 1 ∨ z = x ∨ z = y ∨ z = y + 1 := by
    intro z
    simp only [hXd, hYd, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcl : Closed ↑(X ∪ Y) := by
    intro z hz hd
    rcases (hmem z).1 hz with rfl | rfl | rfl | rfl
    · exact absurd hd h1I
    · exact absurd hd hxI
    · exact absurd hd hyI
    · exact Or.inr ⟨y, (hmem y).2 (Or.inr (Or.inr (Or.inl rfl))), 1, (hmem 1).2 (Or.inl rfl),
        hy1, h1y, rfl⟩
  obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hg shTw_pos X Y hX hY hcl
  have mx : x ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := (hmem x).2 (Or.inr (Or.inl rfl))
  have my : y ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := (hmem y).2 (Or.inr (Or.inr (Or.inl rfl)))
  have my1 : y + 1 ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := (hmem (y + 1)).2 (Or.inr (Or.inr (Or.inr rfl)))
  have m1 : (1 : Ordinal.{0}) ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := (hmem 1).2 (Or.inl rfl)
  have hf1 : f 1 = 1 := hfix 1 (by rw [hXd]; exact Finset.mem_singleton_self 1)
  have hfy1 : f y + 1 = f (y + 1) := by
    have := (hf.1.2.2 y my 1 m1 (y + 1) my1).1 rfl
    rwa [hf1] at this
  have hfxy : f x < f y := hf.1.2.1 mx my hxy
  have hf2 : le2 (f x) (f y) := hf.2.2 x mx y my h2
  have hf1' : le1 (f x) (f (y + 1)) := hf.2.1 x mx (y + 1) my1 h1
  have hfyW : f y < shTw := (hYt (f y) (hmap y (by rw [hYd]; simp))).2
  rw [← hfy1] at hf1'
  exact shD_noReach hfxy hf2 hfyW (f y + 1) (Order.lt_add_one_iff.2 le_rfl) hf1'

/-- **`T_ω` has a reach, and it is at most `y + 1`**, for every long pair `(x, y)`. -/
theorem lfTw_reach {x y : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y) (h1 : le1 x (y + 1)) :
    IsReach R2C shTw (reach shTw) ∧ reach shTw ≤ y + 1 := by
  have hlh := lfTw_lh hxy h2 h1
  have hWx : shTw < x := lfLong_above hxy h2 (Order.lt_add_one_iff.2 le_rfl) h1
  have hy1 : y + 1 < y + 1 + 1 := Order.lt_add_one_iff.2 le_rfl
  have hno : ¬ le1 shTw (y + 1 + 1) := fun h => absurd (hlh _ h) (not_le.2 hy1)
  have hr := reach_spec ((hWx.trans hxy).le.trans (le_self_add.trans le_self_add)) hno
  exact ⟨hr, hlh _ hr.1⟩

/-- `Y_LL`: the least `y'` with `x <₂ y < y'` and `x ≤₁ y'` for some `x, y`. -/
noncomputable def lfYLL : Ordinal.{0} :=
  sInf {y' | ∃ x y, x < y ∧ le2 x y ∧ y < y' ∧ le1 x y'}

/-- **`lh(T_ω) ≤ Y_LL`**: if a long pair exists, every `g` with `T_ω ≤₁ g` is `≤ Y_LL`. -/
theorem lfTw_lh_YLL (hex : ∃ x y y', x < y ∧ le2 x y ∧ y < y' ∧ le1 x y') :
    ∀ g, le1 shTw g → g ≤ lfYLL := by
  obtain ⟨x, y, y', hl⟩ := hex
  obtain ⟨x0, y0, hxy, h2, hyY, h1⟩ :=
    csInf_mem (s := {y' | ∃ x y, x < y ∧ le2 x y ∧ y < y' ∧ le1 x y'}) ⟨y', x, y, hl⟩
  intro g hg
  have h1' : le1 x0 (y0 + 1) :=
    le1_of_le_of_le1 (hxy.le.trans le_self_add) (Order.add_one_le_of_lt hyY) h1
  exact (lfTw_lh hxy h2 h1' g hg).trans (Order.add_one_le_of_lt hyY)

end Googology.Trans.PoR.InaccPsi.R2
