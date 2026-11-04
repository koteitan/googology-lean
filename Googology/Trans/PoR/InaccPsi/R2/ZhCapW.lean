import Googology.Trans.PoR.InaccPsi.R2.ZhCap

/-!
# Zh: the windows with CapV asked only at the restarts with a long last exponent

The least-counterexample argument of `Yx.yxSpec_capsG` reads CapV only at the Range restarts `μ` with
`ρ_μ < ν_C`; there `Zh.zhCapV_short` proves CapV when the last exponent `e = e(η_μ)` has `2 ≤ e < ρ_μ`.  So the
CapV input of the window induction is needed only at the other restarts (`ρ_μ ≤ e`, or `e ≤ 1`):

* `ZhShortExp S μ`: `ω² ≤ ω^e` and `e < ρ_μ`;
* `zhSpec_capsV`, `zhSpec_capsTopV`: `Yx.yxSpec_caps`, `Yx.yxSpec_capsTop` with CapV asked below `ν_C` only;
* `zhWin_fullV`, `zhTop_fullV`: `Yx.yxWin_full`, `Yx.yxTop_full` with CapV asked below `ν_C` only;
* `zhWins5`, `zhTopAll5` (**the windows with the CapV input at the long exponents only**; the RS input is asked
  given `L(k+1) ≤ ν_C`, which the induction knows at that point);
* `zhWinCapV_all`, `zhTopCapV_all`: CapV at every range restart of `W_k` (`W_ω`) from the long-exponent input
  and `L(k+1) ≤ ν_C` (`L(ω+1) ≤ ν_C`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A short last exponent**: `2 ≤ e(η_μ) < ρ_μ` (as `ω² ≤ ω^e`). -/
def ZhShortExp (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ω ^ 2 ≤ ω ^ cdExp (cdEta S μ) ∧ cdExp (cdEta S μ) < upsilon μ

/-- CapV from the long-exponent input, below `ν_C`. -/
theorem zhCapV_of {μ η1 : Ordinal.{0}} (hr : CdRange S μ) (hν : upsilon μ < nuC)
    (hn : upsilon μ < Nm.Pv S η1) (hlong : ¬ ZhShortExp S μ → CdCapV S μ) : CdCapV S μ := by
  by_cases h : ZhShortExp S μ
  · exact zhCapV_short hr.1 hν hn h.1 h.2
  · exact hlong h

/-- **`Yx.yxSpec_caps` with CapV asked below `ν_C` only.** -/
theorem zhSpec_capsV {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Yx.YxSpec O l0 B)
    (hX : upsilon B ≤ Nc.ncL S ω) (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : ¬ CdRange S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → upsilon μ < nuC →
      CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B := by
  have hLω : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  have hρ0 : upsilon l0 < nuC := by
    refine Yx.yxNu_gt ((upsilon_normal.strictMono Sp.lt).le.trans hX) h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (((upsilon_normal.strictMono Sp.lt).le.trans hX).trans_lt hLω), hc⟩ hlX
  suffices hν : upsilon B ≤ nuC from ⟨hν, Sp.toYs hν⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have i0 : l0 < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hρ0)
  have i1 : ξ < B := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlt)
  have Sp' : Ys.YsSpec O l0 ξ := (Sp.restr hξ i0 i1.le).toYs he.symm.le
  have hνX : nuC ≤ Nc.ncL S ω := hlt.le.trans hX
  refine absurd (Yx.yxNu_gt hνX h0 ?_) (lt_irrefl _)
  intro μ hμ hB hlev hlX hc
  have hr : CdRange S μ := ⟨hμ, hB, hlX.trans (hνX.trans_lt hLω), hc⟩
  rcases lt_trichotomy (upsilon μ) (upsilon l0) with h | h | h
  · exact hb μ hr h
  · exact absurd (upsilon_normal.strictMono.injective h ▸ hr) hl0
  · have j0 : l0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 h
    have j1 : μ < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlX)
    have hU : CdUpper S μ := Ys.ysUpper_all Sp' hμ j0.le j1 (by rw [hO μ j0]; exact Ys.ysO_eq S μ)
    exact cdCapAt_of_upper hU (hV μ hr h (hlX.trans hlt) hlX)

/-- **`Yx.yxSpec_capsTop` with CapV asked below `ν_C` only.** -/
theorem zhSpec_capsTopV {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Yx.YxSpec O l0 B)
    (hX : upsilon B ≤ Nc.ncL S (ω + 1)) (h0 : CdCAP0 S) (hLw : Yx.YxLwNo2 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : ¬ CdRange S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → upsilon μ < nuC →
      CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B := by
  have hρB : upsilon l0 < upsilon B := upsilon_normal.strictMono Sp.lt
  have hρ0 : upsilon l0 < nuC := by
    refine Yx.yxNu_gtTop (hρB.trans_le hX) h0 ?_ hLw
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (hρB.trans_le hX), hc⟩ hlX
  suffices hν : upsilon B ≤ nuC from ⟨hν, Sp.toYs hν⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have i0 : l0 < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hρ0)
  have i1 : ξ < B := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlt)
  have Sp' : Ys.YsSpec O l0 ξ := (Sp.restr hξ i0 i1.le).toYs he.symm.le
  have hνX : nuC < Nc.ncL S (ω + 1) := hlt.trans_le hX
  refine absurd (Yx.yxNu_gtTop hνX h0 ?_ hLw) (lt_irrefl _)
  intro μ hμ hB hlev hlX hc
  have hr : CdRange S μ := ⟨hμ, hB, hlX.trans hνX, hc⟩
  rcases lt_trichotomy (upsilon μ) (upsilon l0) with h | h | h
  · exact hb μ hr h
  · exact absurd (upsilon_normal.strictMono.injective h ▸ hr) hl0
  · have j0 : l0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 h
    have j1 : μ < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlX)
    have hU : CdUpper S μ := Ys.ysUpper_all Sp' hμ j0.le j1 (by rw [hO μ j0]; exact Ys.ysO_eq S μ)
    exact cdCapAt_of_upper hU (hV μ hr h (hlX.trans hlt) hlX)

/-- **`W_k` with the fixed bound** (`Yx.yxWin_full`) with CapV asked below `ν_C` only. -/
theorem zhWin_fullV (k : ℕ)
    (hin : Yx.YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (h0 : CdCAP0 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → CdCapV S μ) :
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  have hlt := Yx.yxIdx_lt (S := S) (Yx.yxL_lt_succ (S := S) k)
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt (Pp.ppL_mono (S := S) (le_of_lt (by exact_mod_cast (natCast_lt_omega0 k)))) h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (((Pp.ppL_mono (S := S) (le_of_lt
      (natCast_lt_omega0 k))).trans_lt (Qq.qqL_lt_succ S))), hc⟩ hlX
  have Sp := Yx.yxSpec_ofIn (Yx.yxBase_ri k) (Yx.yxBase_ri (k + 1)) hlt (Yx.yxIdx_cnt _)
    (land_C (Yx.yxBase_ri k) hρ.le) hin hρ.le
  have e0 := Yx.yxUps_base (S := S) (k : Ordinal.{0})
  have e1 := Yx.yxUps_base (S := S) ((k + 1 : ℕ) : Ordinal.{0})
  have hX : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (S := S) k).le
  have := zhSpec_capsV Sp (e1 ▸ hX) h0 (fun μ hr h => hb μ hr (e0 ▸ h)) (Yx.yxL_notRange k)
    (fun μ h => Yx.yxO_above h) (fun μ hr h1 h2 h3 => hV μ hr ⟨e0 ▸ h1, e1 ▸ h2⟩ h3)
  exact ⟨e1 ▸ this.1, this.2⟩

/-- **`W_ω` with the fixed bound** (`Yx.yxTop_full`) with CapV asked below `ν_C` only. -/
theorem zhTop_fullV
    (hin : Yx.YxIn S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (h0 : CdCAP0 S) (hLw : Yx.YxLwNo2 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ < nuC → CdCapV S μ) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  have hlt := Yx.yxIdx_lt (S := S) (Qq.qqL_lt_succ S)
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have Sp := Yx.yxSpec_ofIn Yx.yxBaseW_ri Yx.yxBaseW1_ri hlt (Yx.yxIdx_cnt _)
    (land_C Yx.yxBaseW_ri hρ.le) hin hρ.le
  have e0 := Yx.yxUps_base (S := S) ω
  have e1 := Yx.yxUps_base (S := S) (ω + 1)
  have := zhSpec_capsTopV Sp (e1 ▸ le_rfl) h0 hLw (fun μ hr h => hb μ hr (e0 ▸ h)) Yx.yxLw_notRange
    (fun μ h => Yx.yxO_above h) (fun μ hr h1 h2 h3 => hV μ hr ⟨e0 ▸ h1, e1 ▸ h2⟩ h3)
  exact ⟨e1 ▸ this.1, this.2⟩

/-- **CapV at every range restart of `W_k`** from the long-exponent input and `L(k+1) ≤ ν_C`. -/
theorem zhWinCapV_all (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hVL : ∀ μ, CdRange S μ → Wj.WjWin S k μ → ¬ ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ := by
  intro μ hr hw
  have hlt : upsilon μ < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := hw.2
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact hlt
  exact zhCapV_of hr (hlt.trans_le hν) hn (hVL μ hr hw)

/-- **CapV at every range restart of `W_ω`** from the long-exponent input and `L(ω+1) ≤ ν_C`. -/
theorem zhTopCapV_all (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVL : ∀ μ, CdRange S μ → Wj.WjTop S μ → ¬ ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ := by
  intro μ hr hw
  have hlt : upsilon μ < Nc.ncL S (ω + 1) := hw.2
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S]; exact hlt
  exact zhCapV_of hr (hlt.trans_le hν) hn (hVL μ hr hw)

/-- **ALL WINDOWS `W_k`**: the RS input `ZcRsIn ∨ ZhSupInB`, CapV only at the long exponents. -/
theorem zhWins5
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVL : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  have hb := Yx.yxCaps_below k hlow' fun j hj μ hr hw =>
    ⟨((IH j hj).2.2 μ hr hw).1, zhWinCapV_all j (IH j hj).1 (hVL j) μ hr hw⟩
  have hL := Zc.zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  have hVk : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → CdCapV S μ := by
    intro μ hr hw hμν
    have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact zhCapV_of hr hμν hn (hVL k μ hr hw)
  obtain ⟨hν, Sp⟩ := zhWin_fullV k ⟨Zc.zcBaseIn k h0 hb hL, hin k⟩ h0 hb hVk
  have hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hL μ hr (by rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono hμ)
    · exact absurd hr (Yx.yxL_notRange k)
  have hνB : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC := by
    rw [Yx.yxUps_base]; exact hν
  have hnB : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤
      Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
    rw [Yx.yxUps_base, Lw.lw_L_eq S]
  refine ⟨hν, Sp, zhWin_UL k (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    zhIn_congr h1 (zhIn_of_B hl hνB hnB h2 (hrs k l hl h1 h2 hνB))⟩

/-- **THE TOP WINDOW `W_ω`**: the RS input `ZcRsIn ∨ ZhSupInB`, CapV only at the long exponents. -/
theorem zhTopAll5
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVL : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVLT : ∀ μ, CdRange S μ → Wj.WjTop S μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := zhWins5 hin hlow hVL hrs
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Yx.yxCaps_below (n + 1) hlow' (fun j _ μ hr hw =>
      ⟨((W j).2.2 μ hr hw).1, zhWinCapV_all j (W j).1 (hVL j) μ hr hw⟩) μ hr hn
  have hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Zc.zcLower_below (n + 1) (fun μ hr h => (hlow μ hr h).2.1)
      (fun j _ μ hr hw => ((W j).2.2 μ hr hw).2) μ hr hn
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have hbase : Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * ω)) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω))) :=
    Zc.zcBase_reach Yx.yxBaseW_ri (Zc.zcL_cnt _) hρ Zc.zcSupW
      (fun μ hr h => hL μ hr (by rw [Yx.yxUps_base] at h; exact h))
  have hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ < nuC → CdCapV S μ := by
    intro μ hr hw hμν
    have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact zhCapV_of hr hμν hn (hVLT μ hr hw)
  obtain ⟨hν, Sp⟩ := zhTop_fullV ⟨hbase, hinT⟩ h0 hLw hb hVT
  have hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * ω) → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hL μ hr (by rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono hμ)
    · exact absurd hr Yx.yxLw_notRange
  have hνB : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC := by
    rw [Yx.yxUps_base]; exact hν
  have hnB : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤
      Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [Yx.yxUps_base, Lw.lw_L_eq S]
  exact ⟨hν, Sp, zhTop_UL (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    zhIn_congr h1 (zhIn_of_B hl hνB hnB h2 (hrsT l hl h1 h2 hνB))⟩

end Googology.Trans.PoR.InaccPsi.R2.Zh
