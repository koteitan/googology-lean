import Googology.Trans.PoR.InaccPsi.R2.Basic
import Googology.Trans.PoR.InaccPsi.R2.Cited

/-!
# `υ`-points, segments, restarts and reaches

* `UpsPt`, `UpsSet`, `upsilon`: the `υ`-points.  Wilken ([G20] Def 21.4) sets `υ₀ = 0`,
  `υ_{ξ+1} = T^{υ_ξ} ∩ Ω₁`, sups at limits; by [W07b] Cor 5.10 (`T_inter_Om1`) the nonzero
  `υ`-points are the `α` with `α <₁ ∞` in `R₁⁺`.  Here `upsilon` is defined as the enumeration
  of `{0} ∪ {α > 0 | α <₁ ∞}` (that this is Wilken's `υ`, i.e. that the class is closed, is the
  second half of [W07b] Cor 5.10 and is not used).
* `IsNext b m`: `m = b^∞`, the least `υ`-point above `b`; `seg(b) = [b, b^∞)`.
* `IsRestartIdx λ` (`λ` a nonzero multiple of `ω²`), `rho λ = υ_λ` (the restart `ρ_λ`),
  `reach x = lh(x)` in `R₂^C`, `rReach λ = r(λ) = lh(ρ_λ)` (the project's notation for restarts and reaches).

Proved (axioms only from `R2.Cited`):
* `upsPt_inE`: a nonzero `υ`-point is an `ε`-number;
* `le1R_lt_ups`: for a `υ`-point `κ`, `x < κ ≤ y`: `x ≤₁ y ⇔ x <₁ ∞` (in `R₁⁺`);
* `not_le1R_gap`: a point strictly inside `seg(b)` is not `≤₁` anything `≥ b^∞`;
* `exists_next`: `b^∞` exists for a countable `υ`-point `b` and `T^b ∩ Ω₁ = b^∞`;
* `reach_spec`: `reach x` is the reach in `R₂^C` whenever `x <₁ ∞` fails.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- `α` is a nonzero `υ`-point: `α > 0` and `α <₁ ∞` in `R₁⁺`. -/
def UpsPt (a : Ordinal.{0}) : Prop := 0 < a ∧ LtInf1 a

/-- `Im(υ) = {0} ∪ {α > 0 | α <₁ ∞}` ([W07b] Cor 5.10). -/
def UpsSet : Set Ordinal.{0} := {a | a = 0 ∨ UpsPt a}

/-- `υ_ι`: the enumeration of `Im(υ)`. -/
noncomputable def upsilon (ι : Ordinal.{0}) : Ordinal.{0} := enumOrd UpsSet ι

/-- `m = b^∞`: the least `υ`-point above `b`. -/
def IsNext (b m : Ordinal.{0}) : Prop := b < m ∧ UpsPt m ∧ ∀ u, b < u → UpsPt u → m ≤ u

/-- A restart index: a nonzero multiple of `ω²`. -/
def IsRestartIdx (l : Ordinal.{0}) : Prop := l ≠ 0 ∧ ω ^ 2 ∣ l

/-- The restart `ρ_λ = υ_λ`. -/
noncomputable def rho (l : Ordinal.{0}) : Ordinal.{0} := upsilon l

/-- The reach `lh(x) = max{γ | x ≤₁ γ}` in `R₂^C` (meaningful when `x <₁ ∞` fails,
`reach_spec`). -/
noncomputable def reach (x : Ordinal.{0}) : Ordinal.{0} := sSup {g | le1 x g}

/-- `r(λ) = lh(ρ_λ)` in `R₂^C`. -/
noncomputable def rReach (l : Ordinal.{0}) : Ordinal.{0} := reach (rho l)

theorem reach_spec {x g : Ordinal.{0}} (hxg : x ≤ g) (hg : ¬ le1 x g) :
    IsReach R2C x (reach x) := by
  obtain ⟨r, hr⟩ := exists_reach hxg hg
  have : reach x = r := (IsGreatest.csSup_eq ⟨hr.1, fun t ht => hr.2 t ht⟩)
  rw [this]; exact hr

theorem upsPt_inE {u : Ordinal.{0}} (hu : UpsPt u) : InE u :=
  (le1R_two_iff hu.1).1 (hu.2 _ (by
    rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]
    exact le_self_add))

/-- For a `υ`-point `κ` and `x < κ ≤ y`: `x ≤₁ y` iff `x <₁ ∞` (in `R₁⁺`). -/
theorem le1R_lt_ups {κ x y : Ordinal.{0}} (hκ : UpsPt κ) (hx : x < κ) (hy : κ ≤ y) :
    le1R x y ↔ LtInf1 x := by
  constructor
  · intro h g hxg
    have hxk : le1R x κ := le1R_of_le hx.le hy h
    by_cases hgk : g ≤ κ
    · exact le1R_of_le hxg hgk hxk
    · exact le1R_trans hxk (hκ.2 g (le_of_not_ge hgk))
  · intro h; exact h y (hx.le.trans hy)

/-- A point strictly inside `seg(b) = [b, b^∞)` is `≤₁` nothing `≥ b^∞`. -/
theorem not_le1R_gap {b m x y : Ordinal.{0}} (hn : IsNext b m) (hbx : b < x) (hxm : x < m)
    (hmy : m ≤ y) : ¬ le1R x y := by
  intro h
  have hx : LtInf1 x := (le1R_lt_ups hn.2.1 hxm hmy).1 h
  have := hn.2.2 x hbx ⟨lt_of_le_of_lt (by simp) hbx, hx⟩
  exact absurd this (not_le.2 hxm)

/-- No `υ`-point strictly inside `seg(b)`. -/
theorem not_upsPt_gap {b m x : Ordinal.{0}} (hn : IsNext b m) (hbx : b < x) (hxm : x < m) :
    ¬ UpsPt x := fun hx => absurd (hn.2.2 x hbx hx) (not_le.2 hxm)

/-- `b^∞` exists for a countable `υ`-point `b`, and `T^b ∩ Ω₁ = b^∞` ([W07b] Cor 5.10). -/
theorem exists_next {b : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) :
    ∃ m, IsNext b m ∧ ∀ a, a < Om1 → (a ∈ Tset b ↔ a < m) := by
  obtain ⟨m, hbm, hm, hmin, hT⟩ := T_inter_Om1 (upsPt_inE hb) hb1
  exact ⟨m, ⟨hbm, ⟨lt_of_le_of_lt (by simp) hbm, hm⟩, fun u hbu hu => hmin u hbu hu.2⟩, hT⟩

theorem IsNext.unique {b m m' : Ordinal.{0}} (h : IsNext b m) (h' : IsNext b m') : m = m' :=
  le_antisymm (h.2.2 m' h'.1 h'.2.1) (h'.2.2 m h.1 h.2.1)

end Googology.Trans.PoR.InaccPsi.R2
