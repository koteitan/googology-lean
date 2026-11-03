import Googology.Trans.PoR.InaccPsi.R2.YsInd
import Googology.Trans.PoR.InaccPsi.R2.YiWin

/-!
# Ys: non-vacuity and refute-first results for the relative block induction

* `ysSpec_old` (**non-vacuity**): the relative specification `Ys.YsSpec` holds for the repo's offsets `c*`
  from `l₀ = ω²` up to `Ξ_ω + ω²` (base restart with TOP given, the others with the short input); so
  `Ys.ysGood_all` has satisfiable hypotheses, and there it reproves `TOP` at every restart.
* `ysShortX_ref` (**REFUTE FIRST**, windows): under LOWER and TOP in `W_n`, cofinally in `W_n` there are range
  restarts `μ` such that at the next restart `μ + ω²` the short input with a crossing bound `x₀ < ρ_μ` is
  impossible: the crossing bound must lie above the supply restarts (`x₀ = L(n)` is refuted there).
* `ysReach_supply`: at those supply restarts the chain datum `reach` of the long input holds (from LOWER).
* `ysReach_base`: at a base `ρ_{l₀} ≤₁ ρ_{l₁}` (`l₀ < l₁` restarts), e.g. `L(n) ≤₁ L(n+1)`, the chain datum
  `reach` holds with `x₀ = ρ_{l₀}` for every chain start.
* `ysTopR_iff`: with `O(μ) = r(μ) − δ_μ` and `δ_μ ≤ r(μ)`, Lemma TOP at `δ_μ + O(μ)` is exactly UPPER.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

/-- The chain start `δ_l + o` (`o < δ_l`) is below every chain top. -/
theorem ysT0_le_top {l o : Ordinal.{0}} (ho : o < upsilon (l + ω + 1)) (j : ℕ) :
    upsilon (l + ω + 1) + o ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    show upsilon (l + ω + 1) + o ≤ upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1)
    have hU : UpsPt (upsilon (l + ω + ω)) := upsPt_upsilon (lt_of_lt_of_le omega0_pos le_add_self)
    have hδ : upsilon (l + ω + 1) < upsilon (l + ω + ω) :=
      upsilon_normal.strictMono ((add_lt_add_iff_left _).2 one_lt_omega0)
    have h1 : upsilon (l + ω + 1) + o < upsilon (l + ω + ω) :=
      (indec_of_upsPt hU).add_lt hδ (ho.trans hδ)
    refine h1.le.trans (upsilon_normal.strictMono.monotone ?_)
    rw [add_assoc (l + ω) (ω * (j : Ordinal.{0})) ω]
    exact (add_le_add le_rfl le_add_self).trans le_self_add

/-- The chain data of a restart `l` in an old block structure (`Good`), for a crossing bound `x₀ < ρ_l`, or
`x₀ = ρ_l` when Lemma TOP holds at the chain start. -/
theorem ysChain_of_good {O : Ordinal.{0} → Ordinal.{0}} {l o x0 : Ordinal.{0}} (G : Good O l)
    (ho : o < upsilon (l + ω + 1)) (hx : x0 ≤ upsilon l)
    (htop : ∀ g, upsilon (l + ω + 1) + o < g → x0 = upsilon l → ¬ le1 (upsilon l) g) :
    YsChainIn l o x0 := by
  have key : ∀ j : ℕ, ∀ c, c ≤ x0 → ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d → le1 c d →
      False := by
    intro j c hcx d hjd hcd
    have hTd : upsilon (l + ω + 1) + o < d := lt_of_le_of_lt (ysT0_le_top ho j) hjd
    have hld : upsilon l ≤ d :=
      ((upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)).trans le_self_add).trans
        hTd.le
    rcases lt_or_eq_of_le (hcx.trans hx) with hlt | e
    · exact G.below c hlt d hld hcd
    · have hxe : x0 = upsilon l := le_antisymm hx (e ▸ hcx)
      exact htop d hTd hxe (e ▸ hcd)
  exact ⟨fun j c hcx _ d hjd _ hcd => (key j c hcx d hjd hcd).elim,
    fun j c hcx _ d hjd _ h2 => key j c hcx d hjd (le2_le1 h2)⟩

/-- The old block structure at a restart index below `B`, from an offset specification. -/
theorem ysGood_at {O : Ordinal.{0} → Ordinal.{0}} {B l : Ordinal.{0}} (Sp : OffSpec O B)
    (hl : IsRestartIdx l) (hlB : l ≤ B) : Good O l := by
  obtain ⟨η, rfl⟩ := (ri_iff.1 hl).2
  exact good_all Sp η hlB

/-- **Non-vacuity of the relative block induction**: the repo's offsets `c*` satisfy `Ys.YsSpec` from
`l₀ = ω²` up to `Ξ_ω + ω²`. -/
theorem ysSpec_old : YsSpec off (ω * ω) (XiW + ω * ω) := by
  have Sp := specXi
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hri : IsRestartIdx (ω * ω) := ri_iff.2 ⟨hww.ne', dvd_refl _⟩
  have hB : ∀ l, IsRestartIdx l → l < XiW + ω * ω → l + ω * ω ≤ XiW + ω * ω := fun l hl h =>
    next_mult (ri_iff.1 hl).2 Sp.mult h
  have hδ1 : ∀ l, IsRestartIdx l → l < XiW + ω * ω → upsilon (l + ω + 1) < Om1 := fun l hl h =>
    ups_lt_Om1 _ (lt_of_lt_of_le (by simpa using idx_lt l 0 1) ((hB l hl h).trans Sp.cnt.le))
  have hR : ∀ l, IsRestartIdx l → l < XiW + ω * ω →
      RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) := fun l hl h =>
    rstK_of_good hl (ysGood_at Sp hl h.le) (hδ1 l hl h)
  refine ⟨hri, Sp.mult, Sp.cnt, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (ri_ge XiW_ri) (lt_add_of_pos_right _ hww)
  · have G1 := good_first off
    rw [zero_add] at G1
    exact G1.land hww
  · intro l hl _ hlB
    exact (hR l hl hlB).toYs.nostr
  · intro l hl h0 hlB
    have G := ysGood_at Sp hl hlB.le
    have hll : l < l + ω * ω := lt_add_of_pos_right l hww
    have G' := ysGood_at Sp (ri_iff.2 ⟨(lt_of_lt_of_le hww (h0.trans le_self_add)).ne',
      dvd_add (ri_iff.1 hl).2 (dvd_refl _)⟩) (hB l hl hlB)
    have htop := (G'.rst l hl hll).2.1
    have hO := Sp.le l hl hlB
    rcases eq_or_lt_of_le h0 with e | hlt
    · right
      refine ⟨off l, hO, le_rfl, htop, ysChain_of_good G hO le_rfl fun g hg _ => htop g hg⟩
    · left
      obtain ⟨m, k, x0, hoff, hk, hk1, hx0, hreal⟩ := Sp.top l hl hlB
      have hal : upsilon (ω * ω) < upsilon l := upsilon_normal.strictMono hlt
      refine ⟨m, k, max x0 (upsilon (ω * ω)), hoff, hk, hk1, le_max_right _ _, max_lt hx0 hal,
        fun μ hμ hμl hx => hreal μ hμ hμl ((le_max_left _ _).trans_lt hx), hO, ?_⟩
      exact ysChain_of_good G hO (max_lt hx0 hal).le
        fun _ _ hxe => absurd hxe (ne_of_lt (max_lt hx0 hal))

/-- **The relative block induction reproves Lemma TOP below `Ξ_ω`** (every restart `ω² ≤ μ < Ξ_ω + ω²`). -/
theorem ysTop_old {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h0 : ω * ω ≤ μ) (hμB : μ < XiW + ω * ω) :
    ∀ g, upsilon (μ + ω + 1) + off μ < g → ¬ le1 (upsilon μ) g :=
  (ysTop_all ysSpec_old hμ h0 hμB).2

variable {S : InaccSeq.{0}}

/-- **REFUTE FIRST (windows): the crossing bound must lie above the supply restarts.**  Under LOWER at the
range restarts of `W_n` and Lemma TOP at `δ_μ + O(μ)` there, cofinally in `W_n` there are range restarts
`μ` such that at the next restart `μ + ω²` NO short input with a crossing bound `x₀ < ρ_μ` exists (for every
term `x·m + k`, `k < υ_{μ+ω²}`, some restart above `x₀` realizes it). -/
theorem ysShortX_ref (n : ℕ) (O : Ordinal.{0} → Ordinal.{0})
    (hL : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) → Cd.CdLower S μ)
    (hT : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) →
      ∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g) :
    ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧
      Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      ∀ (m : ℕ) (k x0 : Ordinal.{0}), x0 < upsilon μ → k < upsilon (μ + ω * ω) →
        ¬ ∀ ν, IsRestartIdx ν → ν < μ + ω * ω → x0 < upsilon ν → O ν < tm m k (upsilon ν) := by
  intro γ hγ
  obtain ⟨μ, hr, h1, h2, h3, hle, -, -⟩ := Yi.yiWinShort_ref (S := S) n hL γ hγ
  refine ⟨μ, hr, h1, h2, h3, fun m k x0 hx hk hreal => ?_⟩
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hl : IsRestartIdx (μ + ω * ω) :=
    ri_iff.2 ⟨(lt_of_lt_of_le hww le_add_self).ne', dvd_add (ri_iff.1 hr.1).2 (dvd_refl _)⟩
  have hcr := ysNoCross_short hl hk hreal μ hr.1 (lt_add_of_pos_right μ hww) hx
  exact hT μ hr h2 h3 _ hcr hle

/-- **The chain datum `reach` at the supply restarts of a window** (under LOWER there): the long input's
first datum holds at cofinally many range restarts of `W_n`. -/
theorem ysReach_supply (n : ℕ)
    (hL : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) → Cd.CdLower S μ) :
    ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧
      Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      upsilon (μ + ω * ω) ≤ Cd.cdR S μ ∧ YsReachIn μ 0 (upsilon μ) := by
  intro γ hγ
  obtain ⟨μ, hr, h1, h2, h3, h4⟩ := Yi.yiLong_win (S := S) n γ hγ
  have hle : le1 (upsilon μ) (upsilon (μ + ω * ω)) :=
    le1_of_le_of_le1 (upsilon_normal.strictMono.monotone le_self_add) h4 (hL μ hr h2 h3)
  exact ⟨μ, hr, h1, h2, h3, h4, ysReach_long hle⟩

/-- **The chain datum `reach` at a base** `ρ_{l₀} ≤₁ ρ_{l₁}` (`l₀ < l₁` restart indices), for every chain
start `o < δ_{l₀}`: e.g. `L(n) ≤₁ L(n+1)` at the restart of `L(n)`. -/
theorem ysReach_base {l0 l1 o : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hl1 : IsRestartIdx l1)
    (h01 : l0 < l1) (hle : le1 (upsilon l0) (upsilon l1)) :
    YsReachIn l0 o (upsilon l0) := by
  have hE : upsilon (l0 + ω * ω) ≤ upsilon l1 :=
    upsilon_normal.strictMono.monotone (next_mult (ri_iff.1 hl0).2 (ri_iff.1 hl1).2 h01)
  exact ysReach_of_le1 (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)) hle
    (fun j => (ysTop_lt l0 o j).trans hE)

/-- **TOP at `δ_μ + (r(μ) − δ_μ)` is exactly UPPER** when `δ_μ ≤ r(μ)`. -/
theorem ysTopR_iff {μ : Ordinal.{0}} (hδ : upsilon (μ + ω + 1) ≤ Cd.cdR S μ) :
    (∀ g, upsilon (μ + ω + 1) + (Cd.cdR S μ - upsilon (μ + ω + 1)) < g → ¬ le1 (upsilon μ) g) ↔
      Cd.CdUpper S μ := by
  rw [Ordinal.add_sub_cancel_of_le hδ]
  constructor
  · intro h h1; exact h _ (lt_add_one _) h1
  · intro hU g hg h1
    exact hU (le1_of_le_of_le1 ((Cd.cdRho_lt_R S μ).le.trans le_self_add) (add_one_le_of_lt hg) h1)

end Googology.Trans.PoR.InaccPsi.R2.Ys
