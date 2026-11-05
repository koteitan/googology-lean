import Googology.Trans.PoR.InaccPsi.R2.ZnWin

/-!
# Zn: the window input at the non-fixed restarts is the chain reach datum

At a non-fixed restart `λ = λ₀ + z` (`z < ρ_{λ₀}`, `Cp.cpDecomp`) every point of `(λ₀, λ)` is no `υ`-fixed point
(`zn_nonfix_between`), and below `ν_C` the bound is the offset, `O(μ) = c(μ)` (`Zn.zn_O_nonfix`).  With the
separation `R2.cL_sep` (restarts just below `λ` have a smaller offset) the short input `Yx.YxShortIn` of the window
(`Zc.ZcInR`) holds with `m = 0`, `k = c(λ)`, except for its chain reach datum:

* `zn_nonfix_between`: `λ₀ < μ < λ₀ + z`, `z < ρ_{λ₀}` ⇒ `μ < υ_μ`;
* `ZnSepReach a λ` (**the separated chain reach datum**): some `x₀ ∈ [a, ρ_λ)` above which every restart below
  `λ` is non-fixed with a smaller offset, and `Ys.YsReachIn λ c(λ) x₀`;
* `znSep_exists` (**the separation exists**): for every `a < ρ_λ` such an `x₀` exists (so `ZnSepReach` asks only
  the chain reach datum `Ys.YsReachIn λ c(λ) x₀` at one such `x₀`);
* `znShortIn_of_sep` (**the short input at a non-fixed restart below `ν_C`** from `ZnSepReach`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **No fixed point between `λ₀` and `λ₀ + z`** for `0 < λ₀`, `z < ρ_{λ₀}`. -/
theorem zn_nonfix_between {l0 z μ : Ordinal.{0}} (hl00 : 0 < l0) (hz : z < upsilon l0) (h1 : l0 < μ)
    (h2 : μ < l0 + z) : μ < upsilon μ := by
  have hm := upsilon_normal.strictMono
  obtain ⟨z', rfl⟩ := exists_add_of_le h1.le
  have hz' : z' < z := (add_lt_add_iff_left l0).1 h2
  by_contra hne
  have he : upsilon (l0 + z') = l0 + z' := le_antisymm (not_lt.1 hne) hm.le_apply
  have hpos : 0 < l0 + z' := lt_of_le_of_lt zero_le h1
  have hI : Indec (l0 + z') := by
    have := indec_of_upsPt (upsPt_upsilon hpos); rwa [he] at this
  have hρμ : upsilon l0 < l0 + z' := by rw [← he]; exact hm h1
  rcases eq_or_lt_of_le (hm.le_apply (x := l0)) with hl0 | hl0
  · -- `l0` fixed: `z' < l0 < μ`, so `μ = l0 + z' < μ`
    have hz'l : z' < l0 + z' := (hz'.trans (hl0 ▸ hz)).trans h1
    exact absurd (hI.add_lt h1 hz'l) (lt_irrefl _)
  · -- `l0 < ρ_{l0}`: `l0 + z' < ρ_{l0} < l0 + z'`
    have hl0I : Indec (upsilon l0) := indec_of_upsPt (upsPt_upsilon hl00)
    exact absurd (hl0I.add_lt hl0 (hz'.trans hz)) (not_lt.2 hρμ.le)

/-- **The separated chain reach datum** at `λ` above `a`. -/
def ZnSepReach (a l : Ordinal.{0}) : Prop :=
  ∃ x0, a ≤ x0 ∧ x0 < upsilon l ∧
    (∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → ω * ω < μ ∧ μ < upsilon μ ∧ cL μ < cL l) ∧
    Ys.YsReachIn l (cL l) x0

/-- **The separation exists** at a non-fixed restart `λ > ω²` for every `a < ρ_λ`. -/
theorem znSep_exists {a l : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (ha : a < upsilon l) :
    ∃ x0, a ≤ x0 ∧ x0 < upsilon l ∧
      ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → ω * ω < μ ∧ μ < upsilon μ ∧ cL μ < cL l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨l0, z, hl0, hz0, hzρ, -, hlz⟩ := Cp.cpDecomp hl hww hfix
  obtain ⟨ν, hνl, hν⟩ := cL_sep hl
  have hl0l : l0 < l := by rw [hlz]; exact lt_add_of_pos_right l0 hz0
  refine ⟨max (max a (upsilon l0)) (max (upsilon ν) (upsilon (ω * ω))),
    (le_max_left _ _).trans (le_max_left _ _),
    max_lt (max_lt ha (hm hl0l)) (max_lt (hm hνl) (hm hww)), fun μ hμ hμl hx => ?_⟩
  have hl0μ : l0 < μ := hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_left _ _)).trans_lt hx)
  have hνμ : ν < μ := hm.lt_iff_lt.1 (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx)
  have hwμ : ω * ω < μ := hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hx)
  refine ⟨hwμ, zn_nonfix_between (pos_iff_ne_zero.2 hl0.1) hzρ hl0μ (hlz ▸ hμl), hν μ hμ hνμ hμl⟩

/-- **The short input at a non-fixed restart below `ν_C`** (`m = 0`, `k = c(λ)`) from the separated chain reach
datum. -/
theorem znShortIn_of_sep {a l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (h : ZnSepReach a l) : Yx.YxShortIn a (Ys.ysO S) l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨x0, hax, hxl, hsep, hR⟩ := h
  have hO := zn_O_nonfix hl hww hfix hν hn
  have htm : ∀ r : Ordinal.{0}, tm 0 (cL l) r = cL l := fun r => by simp [tm]
  refine ⟨0, cL l, x0, by rw [hO, htm], zn_cL_lt_nonfix hl hfix, fun _ => one_le_cL hl, hax, hxl,
    fun μ hμ hμl hx => ?_, ?_, by rw [hO]; exact hR⟩
  · obtain ⟨hwwμ, hfμ, hcμ⟩ := hsep μ hμ hμl hx
    rw [htm, zn_O_nonfix hμ hwwμ hfμ ((hm hμl).trans hν) ((hm hμl).trans hn)]
    exact hcμ
  · rw [hO]; exact (zn_cL_lt_nonfix hl hfix).trans
      (hm (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add))

end Googology.Trans.PoR.InaccPsi.R2.Zn
