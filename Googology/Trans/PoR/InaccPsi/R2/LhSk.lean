import Googology.Trans.PoR.InaccPsi.R2.LhPsi
import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# The general reach below `ν_C` in `R₂^C`: every point that is not a `υ`-point

All `≤₁` without index are those of `R₂^C` ([C09] Def 5.3–5.4); `le1R` is `≤₁` of `R₁⁺`.  `ν_C` is the least
right end of a non-standard `<₂`-pair (`nuC`); it is a restart (`nuC_restart`).  By SKEL⁺ (D1, `block_le1`), a
point of a block `(T, β]` with `β < ν_C` has `α ≤₁ g ⇔ g ≤ β ∧ α ≤₁ g in R₁⁺`.  Here:

* `lhSk_top` (**the block of a point below `ν_C` ends below `ν_C`**): the block top `υ_{μ+ω(j+1)+1}` of a point
  `α < ν_C` is `< ν_C` (`ν_C` is a restart, and no multiple of `ω²` lies in `(μ + ω·j, μ + ω·(j+1)]`);
* `lhSk_le1` (**`≤₁` of `R₂^C` is `≤₁` of `R₁⁺` at every non-`υ`-point below `ν_C`**): for `α < ν_C` not a
  `υ`-point, `α ≤₁ g ⇔ α ≤₁ g in R₁⁺` for every `g` (the cap `g ≤ β` of D1 is automatic: an `R₁⁺`-reach never
  passes the next `υ`-point, `lhGap_lt`);
* `lhSk_reach`: so the `R₂^C`-reach and the `R₁⁺`-reach agree there; `lhSk_all`: **the exact `R₂^C`-reach of
  every non-`υ`-point `α < ν_C`**, the four cases of `lhR1_all`;
* `lhSk_Pv`, `lhSk_L` (InaccPsi form): for `α` in a gap `(P(η), P(η+1))` (`η` good) or `(L(ξ), P(Ω_ω + P'·ξ + 1))`
  (`ξ < L(ξ)`) with `α < ν_C`, the `R₂^C`-reach of `α` is the value of `lhGap_Pv` / `lhGap_L`;
* `lhSk_below_L` (target (3) away from the `υ`-points, under the explicit hypothesis `L(ω+1) ≤ ν_C`): on
  `[0, L(ω+1))`, `≤₁` of `R₂^C` at a non-`υ`-point is `≤₁` of `R₁⁺`.

At a `υ`-point none of this applies: there `R₁⁺` gives `≤₁` to every larger ordinal (`lhPv_inf`), while
`R₂^C`'s `≤₁` is bounded by the cap of the point (SK2, `R2.Frag2`).

No new axiom, no new definition.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

/-- **The block of a point below `ν_C` ends below `ν_C`.** -/
theorem lhSk_top {μ : Ordinal.{0}} {j : ℕ} (hμ : μ = 0 ∨ IsRestartIdx μ) {a : Ordinal.{0}}
    (ha1 : upsilon (botI μ j) < a) (haC : a < nuC) :
    upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
  obtain ⟨l, hl, hlC⟩ := nuC_restart
  by_contra hge
  have hge' : upsilon l ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
    rw [← hlC]; exact not_lt.1 hge
  rw [hlC] at haC
  have i1 : botI μ j < l := upsilon_normal.strictMono.lt_iff_lt.1 (ha1.trans haC)
  have i2 : l ≤ μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := upsilon_normal.strictMono.le_iff_le.1 hge'
  have hlim := ri_lim hl
  have i3 : l ≤ μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
    rcases eq_or_lt_of_le i2 with e | e
    · exfalso; rw [e] at hlim; exact not_isSuccLimit_add_one _ hlim
    · exact Order.lt_add_one_iff.1 e
  have hLe : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
    rw [omega_mul_succ, add_assoc]
  have he := limit_eq_add_omega hlim (lt_of_le_of_lt (botI_ge μ j) i1) (by rw [← hLe]; exact i3)
  rw [← hLe] at he
  exact tI_not_dvd hμ j (he ▸ (ri_iff.1 hl).2)

/-- **`≤₁` of `R₂^C` is `≤₁` of `R₁⁺` at every point below `ν_C` that is not a `υ`-point.** -/
theorem lhSk_le1 {a : Ordinal.{0}} (haC : a < nuC) (hU : ¬ UpsPt a) :
    ∀ g, le1 a g ↔ le1R a g := by
  by_cases hI : Indec a
  · rcases classify hI.pos with ⟨l, hl, rfl⟩ | ⟨μ, j, hμ, hb, hct⟩
    · exact absurd (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) hU
    · have hβ := lhSk_top hμ hb haC
      have hbl := block_le1 hμ j hβ hb hct
      intro g
      rw [hbl g]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨ξ, h1, h2⟩ := lhBracket a
      have hg := lhGap_lt hU h1 h2 h
      have hβU : UpsPt (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) :=
        upsPt_upsilon (lt_of_lt_of_le zero_lt_one le_add_self)
      have haβ : a < upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) :=
        lt_of_le_of_ne hct fun e => hU (e ▸ hβU)
      have hn := upsilon_isNext ξ
      rw [succ_eq_add_one] at hn
      exact (hg.trans_le (hn.2.2 _ (lt_of_le_of_lt h1 haβ) hβU)).le
  · exact sk_decomp hI

/-- The `R₂^C`-reach and the `R₁⁺`-reach agree at every non-`υ`-point below `ν_C`. -/
theorem lhSk_reach {a r : Ordinal.{0}} (haC : a < nuC) (hU : ¬ UpsPt a) :
    IsReach R2C a r ↔ IsLh1 a r := by
  have h := lhSk_le1 haC hU
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(h r).1 h1, fun g hg => h2 g ((h g).2 hg)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h r).2 h1, fun g hg => h2 g ((h g).1 hg)⟩

/-- **The exact `R₂^C`-reach of every non-`υ`-point below `ν_C`.** -/
theorem lhSk_all {a : Ordinal.{0}} (haC : a < nuC) (hU : ¬ UpsPt a) :
    ∃ ξ r, upsilon ξ ≤ a ∧ a < upsilon (ξ + 1) ∧ IsReach R2C a r ∧ a ≤ r ∧ r < upsilon (ξ + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (a = 1 ∧ r = 1) ∨
       (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (if ξ = 0 then 1 else upsilon ξ) a ∧ a * 2 ≤ r)) := by
  obtain ⟨ξ, h1, h2⟩ := lhBracket a
  obtain ⟨r, hr, hr'⟩ := lhR1_at (lt_of_lt_of_le haC nuC_le_Om1) hU h1 h2
  exact ⟨ξ, r, h1, h2, (lhSk_reach haC hU).2 hr, hr'⟩

/-- **InaccPsi form**: the `R₂^C`-reach of every point `α < ν_C` of a gap `(P(η), P(η+1))`, `η` good. -/
theorem lhSk_Pv (S : InaccSeq.{0}) {η a : Ordinal.{0}} (hg : Bt.Good S η)
    (h1 : Nm.Pv S η < a) (h2 : a < Nm.Pv S (η + 1)) (haC : a < nuC) :
    ∃ r, IsReach R2C a r ∧ a ≤ r ∧ r < Nm.Pv S (η + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (Nm.Pv S η) a ∧ a * 2 ≤ r)) := by
  obtain ⟨hU, r, hr, hr'⟩ := lhGap_Pv S hg h1 h2
  exact ⟨r, (lhSk_reach haC hU).2 hr, hr'⟩

/-- **InaccPsi form at a named gap**: the `R₂^C`-reach of every `α < ν_C` in `(L(ξ), P(Ω_ω + P'·ξ + 1))`
(`ξ < L(ξ)`), with `τ = L(ξ)`. -/
theorem lhSk_L (S : InaccSeq.{0}) {ξ a : Ordinal.{0}} (hξ : ξ < ncL S ξ) (h1 : ncL S ξ < a)
    (h2 : a < Nm.Pv S (Om ω + ncPp S * ξ + 1)) (haC : a < nuC) :
    ∃ r, IsReach R2C a r ∧ a ≤ r ∧ r < Nm.Pv S (Om ω + ncPp S * ξ + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (ncL S ξ) a ∧ a * 2 ≤ r)) := by
  obtain ⟨hU, r, hr, hr'⟩ := lhGap_L S hξ h1 h2
  exact ⟨r, (lhSk_reach haC hU).2 hr, hr'⟩

/-- **Target (3) away from the `υ`-points**, under the explicit hypothesis `L(ω+1) ≤ ν_C`: below `L(ω+1)`,
`≤₁` of `R₂^C` at a non-`υ`-point is `≤₁` of `R₁⁺`, and its `R₂^C`-reach is its `R₁⁺`-reach. -/
theorem lhSk_below_L (S : InaccSeq.{0}) (hlow : ncL S (ω + 1) ≤ nuC) {a : Ordinal.{0}}
    (ha : a < ncL S (ω + 1)) (hU : ¬ UpsPt a) :
    (∀ g, le1 a g ↔ le1R a g) ∧ ∀ r, IsReach R2C a r ↔ IsLh1 a r :=
  ⟨lhSk_le1 (lt_of_lt_of_le ha hlow) hU, fun _ => lhSk_reach (lt_of_lt_of_le ha hlow) hU⟩

end Googology.Trans.PoR.InaccPsi.R2.Lh
