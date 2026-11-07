import Googology.Trans.PoR.InaccPsi.R2.ZcRsAll

/-!
# Zc: the inputs at a supply restart (a restart with a long reach `υ_{λ+ω²} ≤ r(λ)`)

* `zcRsTerm_long_false` (**NO-GO for the term input at a long restart**): if `υ_{λ+ω²} ≤ δ_λ + O(λ)` then
  `ZcRsTerm O λ` is false (the value `z = δ_λ < O(λ)` is above every `t(ρ_λ)`, `t` an offset term with constants
  below `ρ_λ`: `t(ρ_λ) < δ_λ`, `R2.OT.ev_lt`).  So at a supply restart the RS input `ZcRsIn (ysO S) λ` is LOWER
  itself (`zcRsIn_long_lower`): Lemma RS by terms gives nothing there.
* `zcGiven_of_up` (**the given input from UPPER and the short `≤₁`**): UPPER at `λ` and `ρ_λ ≤₁ υ_{λ+ω²}` give
  `Yx.YxGivenIn (ysO S) λ` (no LOWER, no long reach: `Yx.yxGiven_of_supply` without them);
* `zcGiven_of_sup`: the same with `ρ_λ ≤₁ υ_{λ+ω²}` from the supply `Ra.RaSupAt S ρ_λ`, LOWER below `ρ_λ` and
  `ρ_λ < ν_C` (`Zc.zcBase_le1`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.OT

variable {S : InaccSeq.{0}}

/-- **NO-GO: no term input at a restart whose bound reaches `υ_{λ+ω²}`.** -/
theorem zcRsTerm_long_false {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlong : upsilon (l + ω * ω) ≤ upsilon (l + ω + 1) + O l) : ¬ ZcRsTerm O l := by
  intro hT
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρδ : upsilon l < upsilon (l + ω + 1) :=
    hm (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  have hδE : InE (upsilon (l + ω + 1)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have hδW : upsilon (l + ω + 1) < upsilon (l + ω * ω) := hm (by simpa using idx_lt l 0 1)
  have hWI := indec_of_upsPt (upsPt_upsilon (show 0 < l + ω * ω from lt_of_lt_of_le hl0 le_self_add))
  have hδO : upsilon (l + ω + 1) < O l := by
    by_contra h
    push Not at h
    have := lt_of_le_of_lt (add_le_add le_rfl h) (hWI.add_lt hδW hδW)
    exact absurd hlong (not_le.2 this)
  obtain ⟨t, ht, hz, -⟩ := hT _ hδO
  exact absurd (ev_lt hδE hρδ t (CB_mono ht hρδ.le)) (not_lt.2 hz)

/-- **At a supply restart the RS input is LOWER.** -/
theorem zcRsIn_long_lower {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlong : upsilon (l + ω * ω) ≤ cdR S l) (h : ZcRsIn (Ys.ysO S) l) : CdLower S l := by
  have hlong' : upsilon (l + ω * ω) ≤ upsilon (l + ω + 1) + Ys.ysO S l := by rw [Ys.ysO_eq]; exact hlong
  rcases h with h1 | ⟨-, h1⟩ | ⟨-, -, h1⟩
  · unfold CdLower; rw [← Ys.ysO_eq]; exact h1
  · exfalso
    have hm := upsilon_normal.strictMono
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hδW : upsilon (l + ω + 1) < upsilon (l + ω * ω) := hm (by simpa using idx_lt l 0 1)
    have hWI := indec_of_upsPt (upsPt_upsilon (show 0 < l + ω * ω from lt_of_lt_of_le hl0 le_self_add))
    rw [h1] at hlong'
    have h1W : (1 : Ordinal.{0}) < upsilon (l + ω * ω) :=
      lt_of_lt_of_le one_lt_omega0 (ups_omega_lt (lt_of_lt_of_le hl0 le_self_add)).le
    exact absurd hlong' (not_le.2 (hWI.add_lt hδW h1W))
  · exact absurd h1 (zcRsTerm_long_false hl hlong')

/-- **The given input from UPPER and `ρ_λ ≤₁ υ_{λ+ω²}`** (chain start `δ_λ`). -/
theorem zcGiven_of_up {l : Ordinal.{0}} (hl : IsRestartIdx l) (hU : CdUpper S l)
    (hE : le1 (upsilon l) (upsilon (l + ω * ω))) : Yx.YxGivenIn (Ys.ysO S) l := by
  refine ⟨0, lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le
    (pos_iff_ne_zero.2 hl.1) (le_self_add.trans le_self_add))), zero_le, ?_⟩
  intro g hg h
  rw [Ys.ysO_eq] at hg
  exact hU (le1_of_le_of_le1 ((cdRho_lt_R S l).le.trans le_self_add) (Order.add_one_le_of_lt hg) h)

/-- **The given input from UPPER, the supply below `ρ_λ`, LOWER below `ρ_λ` and `ρ_λ < ν_C`.** -/
theorem zcGiven_of_sup {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hU : CdUpper S l) (hsup : Ra.RaSupAt S (upsilon l))
    (hL : ∀ μ, CdRange S μ → upsilon μ < upsilon l → CdLower S μ) : Yx.YxGivenIn (Ys.ysO S) l :=
  zcGiven_of_up hl hU (zcBase_le1 hl hl1 hν hsup hL)

end Googology.Trans.PoR.InaccPsi.R2.Zc
