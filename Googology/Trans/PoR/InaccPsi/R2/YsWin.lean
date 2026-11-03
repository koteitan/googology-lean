import Googology.Trans.PoR.InaccPsi.R2.YsRS
import Googology.Trans.PoR.InaccPsi.R2.WjSplit

/-!
# Ys: the window step from the relative block induction

For a window `W = (υ_{l₀}, υ_{l₁})` between two restarts (`W_k = (L(k), L(k+1))`, `W_ω = (L(ω), L(ω+1))`) the
relative block induction `Ys.YsSpec O l₀ l₁` with the bounds `δ_μ + O(μ) = r(μ)` gives

* `ysWin_upper` / `ysTop_upper`: **UPPER at every range restart of `W_k` / `W_ω`**;
* `ysWin_lower_succ`: **LOWER** at the successor restarts `μ = μ₁ + ω²` (`μ₁ ≥ l₀`) of the window with
  `O(μ) = 1`, `r(μ) = δ_μ + 1` (Lemma RS with crossings);
* `ysGiven_of_supply`: the input of a supply restart (`Ys.YsGivenIn`) from UPPER, LOWER, the long reach
  `υ_{μ+ω²} ≤ r(μ)` and the pair datum `Ys.YsNostrIn` (the datum `reach` follows from LOWER);
* `ysIdx_win`: a restart of the window has its index in `(l₀, l₁)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

variable {S : InaccSeq.{0}}

/-- A restart index whose point lies strictly between `υ_{l₀}` and `υ_{l₁}` lies strictly between `l₀`
and `l₁`. -/
theorem ysIdx_win {l0 l1 μ : Ordinal.{0}} (h0 : upsilon l0 < upsilon μ) (h1 : upsilon μ < upsilon l1) :
    l0 < μ ∧ μ < l1 :=
  ⟨upsilon_normal.strictMono.lt_iff_lt.1 h0, upsilon_normal.strictMono.lt_iff_lt.1 h1⟩

/-- **UPPER in a window between two restarts** from the relative block induction. -/
theorem ysUpper_between {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 : Ordinal.{0}} (Sp : YsSpec O l0 l1)
    (hO : ∀ μ, IsRestartIdx μ → upsilon l0 < upsilon μ → upsilon μ < upsilon l1 →
      upsilon (μ + ω + 1) + O μ = Cd.cdR S μ) :
    ∀ μ, IsRestartIdx μ → upsilon l0 < upsilon μ → upsilon μ < upsilon l1 → Cd.CdUpper S μ := by
  intro μ hμ h0 h1
  obtain ⟨i0, i1⟩ := ysIdx_win h0 h1
  exact ysUpper_all Sp hμ i0.le i1 (hO μ hμ h0 h1)

/-- **UPPER at every range restart of the window `W_k`** from the relative block induction on
`[ι(L(k)), ι(L(k+1)))` with `δ_μ + O(μ) = r(μ)`. -/
theorem ysWin_upper (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 : Ordinal.{0}}
    (e0 : Nc.ncL S (k : Ordinal.{0}) = upsilon l0) (e1 : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) = upsilon l1)
    (Sp : YsSpec O l0 l1)
    (hO : ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → upsilon (μ + ω + 1) + O μ = Cd.cdR S μ) :
    ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → Cd.CdUpper S μ := by
  intro μ hr hw
  have h0 : upsilon l0 < upsilon μ := e0 ▸ hw.1
  have h1 : upsilon μ < upsilon l1 := e1 ▸ hw.2
  obtain ⟨i0, i1⟩ := ysIdx_win h0 h1
  exact ysUpper_all Sp hr.1 i0.le i1 (hO μ hr hw)

/-- **UPPER at every range restart of the top window `W_ω`** from the relative block induction on
`[ι(L(ω)), ι(L(ω+1)))`. -/
theorem ysTop_upper {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 : Ordinal.{0}}
    (e0 : Nc.ncL S ω = upsilon l0) (e1 : Nc.ncL S (ω + 1) = upsilon l1) (Sp : YsSpec O l0 l1)
    (hO : ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → upsilon (μ + ω + 1) + O μ = Cd.cdR S μ) :
    ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → Cd.CdUpper S μ := by
  intro μ hr hw
  have h0 : upsilon l0 < upsilon μ := e0 ▸ hw.1
  have h1 : upsilon μ < upsilon l1 := e1 ▸ hw.2
  obtain ⟨i0, i1⟩ := ysIdx_win h0 h1
  exact ysUpper_all Sp hr.1 i0.le i1 (hO μ hr hw)

/-- **LOWER at a successor restart of a window** (`μ = μ₁ + ω²`, `l₀ ≤ μ₁`, `O(μ) = 1`, `r(μ) = δ_μ + 1`). -/
theorem ysWin_lower_succ {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 μ1 : Ordinal.{0}} (Sp : YsSpec O l0 l1)
    (hμ1 : IsRestartIdx μ1) (h0 : l0 ≤ μ1) (h1 : μ1 + ω * ω < l1)
    (hR : Cd.cdR S (μ1 + ω * ω) = upsilon (μ1 + ω * ω + ω + 1) + 1) : Cd.CdLower S (μ1 + ω * ω) := by
  unfold Cd.CdLower
  rw [hR]
  exact ysRs_succ Sp hμ1 h0 h1

/-- **The input of a supply restart** from UPPER, LOWER, the long reach and the pair datum (with the bound
`O(μ) = r(μ) − δ_μ`). -/
theorem ysGiven_of_supply {O : Ordinal.{0} → Ordinal.{0}} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (hOμ : O μ = Cd.cdR S μ - upsilon (μ + ω + 1)) (hU : Cd.CdUpper S μ) (hL : Cd.CdLower S μ)
    (hlong : upsilon (μ + ω * ω) ≤ Cd.cdR S μ) (hN : YsNostrIn μ 0 (upsilon μ)) : YsGivenIn O μ := by
  have hδ : upsilon (μ + ω + 1) ≤ Cd.cdR S μ :=
    (upsilon_normal.strictMono.monotone (by simpa using (idx_lt μ 0 1).le)).trans hlong
  have hle : le1 (upsilon μ) (upsilon (μ + ω * ω)) :=
    le1_of_le_of_le1 (upsilon_normal.strictMono.monotone le_self_add) hlong hL
  refine ⟨0, lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le
    (pos_iff_ne_zero.2 hμ.1) (le_self_add.trans le_self_add))), zero_le, ?_, ?_, ?_⟩
  · rw [hOμ]; exact (ysTopR_iff hδ).2 hU
  · exact ysReach_long hle
  · exact hN

end Googology.Trans.PoR.InaccPsi.R2.Ys
