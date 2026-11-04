import Googology.Trans.PoR.InaccPsi.R2.YxInd

/-!
# Yx: non-vacuity of the window induction (its hypotheses from the target)

The hypotheses of `Yx.yxWins` / `Yx.yxTopAll` follow from ENUM-REACH and CapV at the range restarts (the natural
target of the windows) together with the chain reach data `Ys.YsReachIn l 0 ρ_l` (a point `≤ ρ_l` that is `≤₁` a
point inside a chain block after `δ_l` is `≤₁` its top), plus `Yx.YxLwNo2` from `L(ω+1) ≤ ν_C`:

* `yxWin_range`: every restart strictly inside `(L(ξ), L(ξ+1))`, `ξ ≤ ω`, is a range restart;
* `yxIn_of_upper`: the base datum and, at every restart of `(l₀, B)`, UPPER and the chain reach datum give
  `Yx.YxIn S l₀ B` (the given input with chain start `0`, Lemma TOP from UPPER);
* `yxRs_of_lower`: LOWER gives the RS input (its first case);
* `yxWins_of_target`: all hypotheses of `Yx.yxWins` from UPPER, LOWER, CapV below `L(ω)` and the reach data.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Every restart strictly between `L(ξ)` and `L(ξ+1)` (`ξ ≤ ω`) is a range restart.** -/
theorem yxWin_range {ξ l : Ordinal.{0}} (hξ : ξ ≤ ω) (hl : IsRestartIdx l) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) : CdRange S l := by
  have hB0 : cdB0 ≤ l := by
    by_contra hB
    push Not at hB
    have h3 : upsilon l < upsilon cdB0 := upsilon_normal.strictMono hB
    have h4 : upsilon cdB0 < Nc.ncL S ξ := (Fp.fpB0_lt_M (S := S)).trans_le (Pp.ppL_mono zero_le)
    exact absurd (h3.trans h4) (not_lt.2 h1.le)
  have hX : upsilon l < Nc.ncL S (ω + 1) := h2.trans_le (Pp.ppL_mono (add_le_add_left hξ 1))
  exact ⟨hl, hB0, hX, Te.teCode_mid hl.1 h1 h2⟩

/-- **The window input from UPPER and the chain reach data** (given input with chain start `0`). -/
theorem yxIn_of_upper {l0 B : Ordinal.{0}} (hbase : Ys.YsReachIn l0 0 (upsilon l0))
    (h : ∀ l, IsRestartIdx l → l0 < l → l < B → CdUpper S l ∧ Ys.YsReachIn l 0 (upsilon l)) :
    YxIn S l0 B := by
  refine ⟨hbase, fun l hl h0 h1 => Or.inr ⟨0, ?_, zero_le, ?_, (h l hl h0 h1).2⟩⟩
  · exact lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le
      (pos_iff_ne_zero.2 hl.1) (le_self_add.trans le_self_add)))
  · exact (Ys.ysTopR_iff (S := S) (cdR_ge S l)).2 (h l hl h0 h1).1

/-- **LOWER gives the RS input** (its first case, `ρ_λ ≤₁ δ_λ + (r − δ) = r(λ)`). -/
theorem yxRs_of_lower {l : Ordinal.{0}} (hL : CdLower S l) :
    le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
      (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l) :=
  Or.inl (by rw [Ys.ysO_eq]; exact hL)

/-- **Non-vacuity of `Yx.yxWins`**: its hypotheses follow from UPPER, LOWER and CapV at the range restarts below
`L(ω)` and the chain reach data at `ι(L(k))` and at the restarts of the windows. -/
theorem yxWins_of_target
    (hU : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdUpper S μ)
    (hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ)
    (hV : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → upsilon l < Nc.ncL S ω → Ys.YsReachIn l 0 (upsilon l)) :
    (∀ k : ℕ, YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) ∧
    (∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ) ∧
    (∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ) ∧
    (∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l)) := by
  have hL0ω : Nc.ncL S 0 < Nc.ncL S ω :=
    (Pp.ppL_mono (S := S) zero_le).trans_lt (Pp.ppL_lt_omega (S := S) 0)
  have hwin : ∀ (k : ℕ) (l : Ordinal.{0}), IsRestartIdx l →
      Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      CdRange S l ∧ upsilon l < Nc.ncL S ω := by
    intro k l hl h0 h1
    have a0 : Nc.ncL S (k : Ordinal.{0}) < upsilon l := by
      rw [← yxUps_base (S := S)]; exact upsilon_normal.strictMono h0
    have a1 : upsilon l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [← yxUps_base (S := S)]; exact upsilon_normal.strictMono h1
    refine ⟨yxWin_range (ξ := (k : Ordinal.{0})) (natCast_lt_omega0 k).le hl a0 (by exact_mod_cast a1),
      a1.trans (Pp.ppL_lt_omega (S := S) k)⟩
  refine ⟨fun k => yxIn_of_upper ?_ fun l hl h0 h1 => ⟨hU l (hwin k l hl h0 h1).1 (hwin k l hl h0 h1).2,
      hR l hl (hwin k l hl h0 h1).2⟩, fun μ hr h => ⟨hU μ hr (h.trans hL0ω), hV μ hr (h.trans hL0ω)⟩,
    fun k μ hr hw => hV μ hr (hw.2.trans (Pp.ppL_lt_omega (S := S) k)),
    fun k l hl h0 h1 => yxRs_of_lower (hL l (hwin k l hl h0 h1).1 (hwin k l hl h0 h1).2)⟩
  refine hR _ (yxBase_ri k) ?_
  rw [yxUps_base]
  rcases k with _ | n
  · exact hL0ω
  · exact (Pp.ppL_mono (S := S) le_rfl).trans_lt (Pp.ppL_lt_omega (S := S) n)

end Googology.Trans.PoR.InaccPsi.R2.Yx
