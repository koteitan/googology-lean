import Googology.Trans.PoR.InaccPsi.R2.CxLow
import Googology.Trans.PoR.InaccPsi.R2.CxEmb

/-!
# The hypotheses of the reduced road on the top window and above `υ_{Λ_B⁺}`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `Λ_B⁺ = Rz.rzLam` (the frontier of
BLK^O of `R2.RzSpec`: below `υ_{Λ_B⁺}` the `<₂`-pairs are the standard ones and no point below a
restart `ρ_λ`, `λ < Λ_B⁺`, is `≤₁` a point `≥ ρ_λ`, `Rz.rzBlk`).

* `cxStd_straddle`: no standard pair `(c, d)` has `c < ρ_λ ≤ d` for a restart index `λ`;
* `CxStdMoveTop S` (`CxStdMove` for `x ≥ L(n+1)` only) and `cxStdMove_of_top`;
* `CxStdPairTop S` (`CxStdPair` for `d ≥ υ_{Λ_B⁺}` only) and `cxStdPair_of_top` (by `Rz.rzBlk`);
* `CxUpsRestTop S` (`CxUpsRest` only at the points above every `ρ_λ`, `λ < Λ_B⁺`) and
  `cxUpsRest_of_top`: a point below some `ρ_λ` (`λ < Λ_B⁺`) has its reach below the least such
  `ρ_λ`, which is at most `L(n+1)`;
* `CxTCtopOff S` (TCrest on `(L(n+1), L(n+2))` at the points that are not restarts of the range) and
  `cxTCtop_of`: with CapV below `L(ω)`, the restarts of the range there have `r(λ) < L(n+2)`
  (`cxR_lt_of_below`), so `CxTCtop` holds.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **No standard pair straddles a restart.** -/
theorem cxStd_straddle {c d lam : Ordinal.{0}} (hs : IsStd c d) (hl : IsRestartIdx lam)
    (h1 : c < upsilon lam) (h2 : upsilon lam ≤ d) : False := by
  obtain ⟨L, -, -, rfl, rfl⟩ := hs.parts
  have hL : L < lam := upsilon_normal.strictMono.lt_iff_lt.1 h1
  have hL1 : L + 1 < lam := by
    rw [← Order.succ_eq_add_one]; exact (ri_lim hl).succ_lt hL
  exact absurd (upsilon_normal.strictMono hL1) (not_lt.2 h2)

/-- **`CxStdMove` above `L(n+1)`**: for `L(n+1) ≤ x < y < L(n+2)`, `IsStd x y ↔ IsStd (B_n x) (B_n y)`. -/
def CxStdMoveTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x y, Bc.bcC S n ≤ x → x < y → y < Bc.bcC S (n + 1) →
    (IsStd x y ↔ IsStd (Bc.bcB S n x) (Bc.bcB S n y))

/-- **`CxStdMove` from its part above `L(n+1)`** (below, `B_n = id`; no standard pair straddles
`L(n+1)`, nor `L(n+1)`'s image `L(ω)`). -/
theorem cxStdMove_of_top (h : CxStdMoveTop S) : CxStdMove S := by
  intro n x y hxy hy
  obtain ⟨lam, hlam, hL⟩ := Pp.ppL_succ_restart (S := S) n
  have hLc : Bc.bcC S n = upsilon lam := hL
  rcases lt_or_ge y (Bc.bcC S n) with hyc | hyc
  · rw [Bc.bcB_fix' S n x (hxy.trans hyc), Bc.bcB_fix' S n y hyc]
  rcases lt_or_ge x (Bc.bcC S n) with hxc | hxc
  · have hBx : Bc.bcB S n x = x := Bc.bcB_fix' S n x hxc
    have hBy : Bc.bcC S n ≤ Bc.bcB S n y :=
      (le_of_lt (Bc.bcC_lt S n)).trans (cxB_window hyc hy).1
    refine ⟨fun hs => (cxStd_straddle hs hlam (hLc ▸ hxc) (hLc ▸ hyc)).elim, fun hs => ?_⟩
    rw [hBx] at hs
    exact (cxStd_straddle hs hlam (hLc ▸ hxc) (hLc ▸ hBy)).elim
  · exact h n x y hxc hxy hy

/-- **`CxStdPair` above `υ_{Λ_B⁺}`.** -/
def CxStdPairTop (S : InaccSeq.{0}) : Prop :=
  ∀ c d, c < d → upsilon Rz.rzLam ≤ d → d < Nc.ncL S (ω + 1) → IsStd c d → le2 c d

/-- **`CxStdPair` from its part above `υ_{Λ_B⁺}`** (below it, `Rz.rzBlk`). -/
theorem cxStdPair_of_top (h : CxStdPairTop S) : CxStdPair S := by
  intro c d hcd hdL hs
  rcases lt_or_ge d (upsilon Rz.rzLam) with hd | hd
  · obtain ⟨μ, j, hμ, hc, hd'⟩ := hs
    refine (Rz.rzBlk.1 c d hcd hd).2 ⟨μ, j, hμ, ?_, hc, hd'⟩
    have : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < Rz.rzLam := by
      rw [hd'] at hd; exact upsilon_normal.strictMono.lt_iff_lt.1 hd
    exact lt_of_le_of_lt (le_self_add.trans le_self_add) this
  · exact h c d hcd hd hdL hs

/-- **`CxUpsRest` above every `ρ_λ`, `λ < Λ_B⁺`.** -/
def CxUpsRestTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S n, UpsPt x → (∀ l, IsRestartIdx l → x ≠ upsilon l) →
    (∀ l, IsRestartIdx l → l < Rz.rzLam → upsilon l ≤ x) →
    (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ le1 x (Nc.ncL S (ω + 1))

/-- **A point below a restart `ρ_λ`, `λ < Λ_B⁺`, and below `L(n+1)` has its reach below `L(n+1)`.** -/
theorem cxGap_rz {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S n)
    (h : ∃ l, IsRestartIdx l ∧ l < Rz.rzLam ∧ x < upsilon l) :
    ∃ r < Bc.bcC S n, IsReach R2C x r := by
  set A := {l | IsRestartIdx l ∧ x < upsilon l} with hA
  obtain ⟨l1, hl1, hl1R, hxl1⟩ := h
  have hne : A.Nonempty := ⟨l1, hl1, hxl1⟩
  have hmem : sInf A ∈ A := csInf_mem hne
  have hle1 : sInf A ≤ l1 := csInf_le (OrderBot.bddBelow _) ⟨hl1, hxl1⟩
  obtain ⟨lam, hlam, hL⟩ := Pp.ppL_succ_restart (S := S) n
  have hLc : Bc.bcC S n = upsilon lam := hL
  have hle2 : sInf A ≤ lam := csInf_le (OrderBot.bddBelow _) ⟨hlam, hLc ▸ hx⟩
  have hno : ∀ g, upsilon (sInf A) ≤ g → ¬ le1 x g :=
    (Rz.rzBlk.2.1 (sInf A) hmem.1 (lt_of_le_of_lt hle1 hl1R)).1 x hmem.2
  obtain ⟨r, hr⟩ := exists_reach hmem.2.le (hno _ le_rfl)
  have hrl : r < upsilon (sInf A) := not_le.1 fun h' => hno r h' hr.1
  refine ⟨r, lt_of_lt_of_le hrl ?_, hr⟩
  rw [hLc]; exact upsilon_normal.strictMono.monotone hle2

/-- **`CxUpsRest` from its part above every `ρ_λ`, `λ < Λ_B⁺`.** -/
theorem cxUpsRest_of_top (h : CxUpsRestTop S) : CxUpsRest S := by
  intro n x hx hU hnr
  by_cases hb : ∃ l, IsRestartIdx l ∧ l < Rz.rzLam ∧ x < upsilon l
  · exact Or.inl (cxGap_rz hx hb)
  · push Not at hb
    exact h n x hx hU hnr hb

/-- **TCrest on `(L(n+1), L(n+2))` at the points that are not restarts of the range.** -/
def CxTCtopOff (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n < x → x < Bc.bcC S (n + 1) → (∀ l, CdRange S l → x ≠ upsilon l) →
    CdTCAt S n x

/-- **`CxTCtop` from CapV below `L(ω)` and `CxTCtopOff`.** -/
theorem cxTCtop_of (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (h : CxTCtopOff S) : CxTCtop S := by
  intro n x h1 h2
  by_cases hr : ∃ l, CdRange S l ∧ x = upsilon l
  · obtain ⟨l, hl, rfl⟩ := hr
    have hω : upsilon l < Nc.ncL S ω := h2.trans (Bc.bcC_lt S (n + 1))
    exact Or.inl ⟨l, hl, rfl, cxR_lt_of_below hl (hV l hl hω) (n + 1) h2⟩
  · push Not at hr
    exact Or.inr (h n x h1 h2 hr)

end Googology.Trans.PoR.InaccPsi.R2.Cx
