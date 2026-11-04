import Googology.Trans.PoR.InaccPsi.R2.YxTop

/-!
# Yx: the windows `W_k`, `W_ω` with the pair-free specification

The window instances of `Yx.yxSpec_caps` / `Yx.yxSpec_capsTop`, with the base `l₀ = ι(Ω_ω + P'·ξ)`
(`ρ_{l₀} = L(ξ)`, code `≥ P'`, so not a range restart: `yxL_notRange`, `yxLw_notRange`):

* `yxWin_spec` (**W_k**): a pair-free `Yx.YxSpec` on `[ι(L(k)), ι(L(k+1)))` with `O = r − δ` above the base,
  CAP-0, the caps at the range restarts below `L(k)` and CapV on `W_k` give `L(k+1) ≤ ν_C` and `Ys.YsSpec`;
* `yxWin_UL`: with the RS input also UPPER ∧ LOWER at every range restart of `W_k` (`Ys.ysWin_UL`);
* `yxTop_spec`, `yxTop_UL` (**W_ω**): the same with the caps below `L(ω)` and the pair hypothesis
  `Yx.YxLwNo2 S` (`L(ω+1) ≤ ν_C` follows);
* `yxSpec_old` (**non-vacuity**): the repo's offsets satisfy `YxSpec off (ω²) (Ξ_ω + ω²)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `ρ_{ι(Ω_ω + P'·ξ)} = L(ξ)`. -/
theorem yxUps_base (ξ : Ordinal.{0}) :
    upsilon (Bt.iota S (Om ω + Nc.ncPp S * ξ)) = Nc.ncL S ξ := (Pp.ppL_eq_ups (S := S) ξ).symm

/-- **`ι(L(k))` is not a range restart** (its code is `P'`). -/
theorem yxL_notRange (k : ℕ) : ¬ CdRange S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) := by
  intro hr
  have hc := hr.2.2.2
  rcases k with _ | n
  · rw [(cdCode_L0 (by simpa using yxUps_base (S := S) 0)).2] at hc
    exact lt_irrefl _ hc
  · rw [cdCode_L n (yxUps_base (S := S) _)] at hc
    exact lt_irrefl _ hc

/-- **`ι(L(ω))` is not a range restart** (its code is `P' + 1`). -/
theorem yxLw_notRange : ¬ CdRange S (Bt.iota S (Om ω + Nc.ncPp S * ω)) := by
  intro hr
  have hc := hr.2.2.2
  rw [cdCode_Lω (yxUps_base (S := S) ω)] at hc
  exact absurd hc (not_lt.2 le_self_add)

/-- **W_k: the pair fields from the caps.** -/
theorem yxWin_spec (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YxSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (h0 : CdCAP0 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ)
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ) :
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  have e0 := yxUps_base (S := S) (k : Ordinal.{0})
  have e1 := yxUps_base (S := S) ((k + 1 : ℕ) : Ordinal.{0})
  have hX : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (S := S) k).le
  have := yxSpec_caps Sp (e1 ▸ hX) h0 (fun μ hr h => hb μ hr (e0 ▸ h)) (yxL_notRange k) hO
    (fun μ hr h1 h2 => hV μ hr ⟨e0 ▸ h1, e1 ▸ h2⟩)
  exact ⟨e1 ▸ this.1, this.2⟩

/-- **W_k: UPPER ∧ LOWER** from the pair-free specification, the caps below `L(k)`, CapV and the RS input. -/
theorem yxWin_UL (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YxSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (h0 : CdCAP0 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ)
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ Ys.YsRsIn O l)) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ :=
  Ys.ysWin_UL k hO (yxWin_spec k Sp h0 hb hO hV).2 hin

/-- **W_ω: the pair fields from the caps and the pair hypothesis at `L(ω)`.** -/
theorem yxTop_spec {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YxSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (h0 : CdCAP0 S) (hLw : YxLwNo2 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ)
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  have e0 := yxUps_base (S := S) ω
  have e1 := yxUps_base (S := S) (ω + 1)
  have := yxSpec_capsTop Sp (e1 ▸ le_rfl) h0 hLw (fun μ hr h => hb μ hr (e0 ▸ h)) yxLw_notRange hO
    (fun μ hr h1 h2 => hV μ hr ⟨e0 ▸ h1, e1 ▸ h2⟩)
  exact ⟨e1 ▸ this.1, this.2⟩

/-- **W_ω: UPPER ∧ LOWER** from the pair-free specification. -/
theorem yxTop_UL {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YxSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (h0 : CdCAP0 S) (hLw : YxLwNo2 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ)
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ Ys.YsRsIn O l)) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ :=
  Ys.ysTop_UL hO (yxTop_spec Sp h0 hLw hb hO hV).2 hin

/-- **Non-vacuity**: the pair-free specification holds for the repo's offsets below `Ξ_ω`. -/
theorem yxSpec_old : YxSpec off (ω * ω) (XiW + ω * ω) := Ys.ysSpec_old.toYx

end Googology.Trans.PoR.InaccPsi.R2.Yx
