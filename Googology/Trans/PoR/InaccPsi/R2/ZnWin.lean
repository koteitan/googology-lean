import Googology.Trans.PoR.InaccPsi.R2.ZnFix

/-!
# Zn: the windows with the value input, the RS input and CapV asked only where the reading is long

The window theorems `Zh.zhWins6`, `Zh.zhTopAll6` ask at the `υ`-fixed window restarts the RS input
`ZcRsIn ∨ ZhSupInB` and CapV (no short exponent).  Here:

* the RS input may also be the value input `Zn.ZnRsVal` (Lemma RS with a value, `Zn.znRs_all`), and is asked
  given `υ_{B_k} ≤ ν_C`;
* CapV is asked below `ν_C` only;
* at the fixed restarts with `Θ_λ(m_λ) ≤ ρ_λ` the RS input is a theorem (`Zn.znRsIn_fixShort`), at the fixed
  restarts with `Θ_λ(m_λ) < δ_λ·ω` CapV is a theorem (`Zn.znCapV_fixThW`).

* `znVal_congr`, `znIn_congr`, `znIn_of_B`: the inputs in the bound `Yx.yxO`, the supply form;
* `znWin_UL`, `znTop_UL`: UPPER ∧ LOWER on `W_k`, `W_ω` with the input `ZcRsIn ∨ ZhSupIn ∨ ZnRsVal`;
* `znWinCapV_all`, `znTopCapV_all`: CapV on `W_k`, `W_ω` from the long-exponent input below `ν_C`;
* `znWins5`, `znTopAll5`: the windows with these inputs;
* `znWins`, `znTopAll` (**THE WINDOWS WITH THE INPUTS ASKED ONLY AT THE FIXED RESTARTS WITH A LONG READING**:
  RS input where `ρ_λ < Θ_λ(m_λ)`, CapV where `δ_λ·ω ≤ Θ_λ(m_λ)`);
* `znWins_of_zh`, `znTopAll_of_zh` (**non-vacuity**: the inputs of `Zh.zhWins6`, `Zh.zhTopAll6` give these).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The value input in the bound `yxO`. -/
theorem znVal_congr {l0 l : Ordinal.{0}} (hl : l0 < l) (h : ZnRsVal (Ys.ysO S) l) :
    ZnRsVal (Yx.yxO S l0) l := by
  intro z hz
  rw [Yx.yxO_above hl] at hz
  obtain ⟨v, h1, h2, h3⟩ := h z hz
  refine ⟨v, h1, h2, fun ν hν => ?_⟩
  obtain ⟨μ, hμ, hνμ, hμl, hle⟩ := h3 (max ν l0) (max_lt hν hl)
  refine ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, ?_⟩
  rw [Yx.yxO_above ((le_max_right _ _).trans_lt hνμ)]
  exact hle

/-- The input in the bound `yxO`. -/
theorem znIn_congr {l0 l B : Ordinal.{0}} (hl : l0 < l)
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupIn S l B ∨ ZnRsVal (Ys.ysO S) l) :
    Zc.ZcRsIn (Yx.yxO S l0) l ∨ Zh.ZhSupIn S l B ∨ ZnRsVal (Yx.yxO S l0) l := by
  rcases h with h | h | h
  · exact Or.inl (Zc.zcRsIn_congr (fun μ h => Yx.yxO_above h) hl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (znVal_congr hl h))

/-- The supply form of the input. -/
theorem znIn_of_B {l B η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon B ≤ nuC)
    (hn : upsilon B ≤ Nm.Pv S η1) (hlB : l < B)
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ ZnRsVal (Ys.ysO S) l) :
    Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupIn S l B ∨ ZnRsVal (Ys.ysO S) l := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Zh.zhSupIn_of_B hl hν hn hlB h))
  · exact Or.inr (Or.inr h)

/-- **UPPER ∧ LOWER at every Range restart of `W_k`** with the input `ZcRsIn ∨ ZhSupIn ∨ ZnRsVal`. -/
theorem znWin_UL (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      Zc.ZcRsIn O l ∨ Zh.ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal O l) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysWin_upper k (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact znRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hO hL0 hin μ hr.1 i0 i1

/-- **UPPER ∧ LOWER at every Range restart of `W_ω`** with the input `ZcRsIn ∨ ZhSupIn ∨ ZnRsVal`. -/
theorem znTop_UL {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * ω) → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      Zc.ZcRsIn O l ∨ Zh.ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∨ ZnRsVal O l) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysTop_upper (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact znRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hO hL0 hin μ hr.1 i0 i1

/-- **CapV at every range restart of `W_k`** from the long-exponent input below `ν_C`. -/
theorem znWinCapV_all (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hVL : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ := by
  intro μ hr hw
  have hlt : upsilon μ < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := hw.2
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact hlt
  exact Zh.zhCapV_of hr (hlt.trans_le hν) hn (hVL μ hr hw (hlt.trans_le hν))

/-- **CapV at every range restart of `W_ω`** from the long-exponent input below `ν_C`. -/
theorem znTopCapV_all (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVL : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ := by
  intro μ hr hw
  have hlt : upsilon μ < Nc.ncL S (ω + 1) := hw.2
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S]; exact hlt
  exact Zh.zhCapV_of hr (hlt.trans_le hν) hn (hVL μ hr hw (hlt.trans_le hν))

/-- **ALL WINDOWS `W_k`**: the RS input `ZcRsIn ∨ ZhSupInB ∨ ZnRsVal`, CapV only at the long exponents
below `ν_C`. -/
theorem znWins5
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVL : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
      CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal (Ys.ysO S) l) :
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
    ⟨((IH j hj).2.2 μ hr hw).1, znWinCapV_all j (IH j hj).1 (hVL j) μ hr hw⟩
  have hL := Zc.zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  have hVk : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → CdCapV S μ := by
    intro μ hr hw hμν
    have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact Zh.zhCapV_of hr hμν hn (hVL k μ hr hw hμν)
  obtain ⟨hν, Sp⟩ := Zh.zhWin_fullV k ⟨Zc.zcBaseIn k h0 hb hL, hin k⟩ h0 hb hVk
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
  refine ⟨hν, Sp, znWin_UL k (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    znIn_congr h1 (znIn_of_B hl hνB hnB h2 (hrs k l hl h1 h2 hνB))⟩

/-- **THE TOP WINDOW `W_ω`**: the RS input `ZcRsIn ∨ ZhSupInB ∨ ZnRsVal`, CapV only at the long exponents
below `ν_C`. -/
theorem znTopAll5
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVL : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
      CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal (Ys.ysO S) l)
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVLT : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∨
        ZnRsVal (Ys.ysO S) l)
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := znWins5 hin hlow hVL hrs
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Yx.yxCaps_below (n + 1) hlow' (fun j _ μ hr hw =>
      ⟨((W j).2.2 μ hr hw).1, znWinCapV_all j (W j).1 (hVL j) μ hr hw⟩) μ hr hn
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
    exact Zh.zhCapV_of hr hμν hn (hVLT μ hr hw hμν)
  obtain ⟨hν, Sp⟩ := Zh.zhTop_fullV ⟨hbase, hinT⟩ h0 hLw hb hVT
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
  exact ⟨hν, Sp, znTop_UL (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    znIn_congr h1 (znIn_of_B hl hνB hnB h2 (hrsT l hl h1 h2 hνB))⟩

/-- A `υ`-fixed restart with a name has no short exponent (`e(η_λ) ≥ λ`, `Fx.fxExp_fix`). -/
theorem zn_notShort_fix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hn : upsilon l < Nm.Pv S η1) : ¬ Zh.ZhShortExp S l := by
  intro h
  have he := Fx.fxExp_fix hl hfix hn
  exact absurd h.2 (not_lt.2 (by rw [hfix]; exact he))

/-- **ALL WINDOWS `W_k`** with the RS input asked only at the fixed restarts with `ρ_λ < Θ_λ(m_λ)` (it may be
the value input) and CapV only at the fixed restarts with `δ_λ·ω ≤ Θ_λ(m_λ)` below `ν_C`. -/
theorem znWins
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVF : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal (Ys.ysO S) l) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))) (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hm := upsilon_normal.strictMono
  refine znWins5 hin hlow (fun k μ hr hw hμν hns => ?_) (fun k l hl h1 h2 hνB => ?_)
  · have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases lt_or_ge (cdTheta S μ (cdCode S μ)) (cdDelta μ * ω) with hθ | hθ
      · exact znCapV_fixThW hr.1 he.symm hμν hn hθ
      · exact hVF k μ hr hw he.symm hμν hθ
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := Zh.zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
      exact hns (Zh.zh_short_of_nonfix hr.1 hww hfix hn)
  · have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
    have hlν : upsilon l < nuC := (hm h2).trans_le hνB
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases le_or_gt (cdTheta S l (cdCode S l)) (upsilon l) with hθ | hθ
      · exact Or.inl (znRsIn_fixShort hl he.symm hlν hn hθ)
      · exact hrsF k l hl h1 h2 he.symm hνB hθ
    · have hww := Zh.zh_ww_lt (Yx.yxBase_ri k) h1
      exact Or.inl (Zh.zhRsIn_nonfix hl hww hfix hlν hn)

/-- **THE TOP WINDOW `W_ω`** with the inputs asked only at the fixed restarts with a long reading. -/
theorem znTopAll
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVF : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal (Ys.ysO S) l)
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVFT : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ)
    (hrsFT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∨
        ZnRsVal (Ys.ysO S) l)
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have hm := upsilon_normal.strictMono
  refine znTopAll5 hin hlow (fun k μ hr hw hμν hns => ?_) (fun k l hl h1 h2 hνB => ?_) hinT
    (fun μ hr hw hμν hns => ?_) (fun l hl h1 h2 hνB => ?_) hLw
  · have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases lt_or_ge (cdTheta S μ (cdCode S μ)) (cdDelta μ * ω) with hθ | hθ
      · exact znCapV_fixThW hr.1 he.symm hμν hn hθ
      · exact hVF k μ hr hw he.symm hμν hθ
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := Zh.zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
      exact hns (Zh.zh_short_of_nonfix hr.1 hww hfix hn)
  · have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
    have hlν : upsilon l < nuC := (hm h2).trans_le hνB
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases le_or_gt (cdTheta S l (cdCode S l)) (upsilon l) with hθ | hθ
      · exact Or.inl (znRsIn_fixShort hl he.symm hlν hn hθ)
      · exact hrsF k l hl h1 h2 he.symm hνB hθ
    · have hww := Zh.zh_ww_lt (Yx.yxBase_ri k) h1
      exact Or.inl (Zh.zhRsIn_nonfix hl hww hfix hlν hn)
  · have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases lt_or_ge (cdTheta S μ (cdCode S μ)) (cdDelta μ * ω) with hθ | hθ
      · exact znCapV_fixThW hr.1 he.symm hμν hn hθ
      · exact hVFT μ hr hw he.symm hμν hθ
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := Zh.zh_ww_lt Yx.yxBaseW_ri (hm.lt_iff_lt.1 h0)
      exact hns (Zh.zh_short_of_nonfix hr.1 hww hfix hn)
  · have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
      rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
    have hlν : upsilon l < nuC := (hm h2).trans_le hνB
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · rcases le_or_gt (cdTheta S l (cdCode S l)) (upsilon l) with hθ | hθ
      · exact Or.inl (znRsIn_fixShort hl he.symm hlν hn hθ)
      · exact hrsFT l hl h1 h2 he.symm hνB hθ
    · have hww := Zh.zh_ww_lt Yx.yxBaseW_ri h1
      exact Or.inl (Zh.zhRsIn_nonfix hl hww hfix hlν hn)

/-- **Non-vacuity**: the fixed-restart inputs of `Zh.zhWins6` give those of `znWins` (CapV: a fixed restart
has no short exponent; RS: `ZcRsIn ∨ ZhSupInB` is a case of the new input). -/
theorem znInputs_of_zh
    (hVF : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    (∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ) ∧
    (∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨
        ZnRsVal (Ys.ysO S) l) := by
  refine ⟨fun k μ hr hw hfix _ _ => hVF k μ hr hw hfix ?_, fun k l hl h1 h2 hfix _ _ => ?_⟩
  · have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact zn_notShort_fix hr.1 hfix hn
  · rcases hrsF k l hl h1 h2 hfix with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **At a fixed restart with `υ_{λ+1} < Θ_λ(m_λ)` the RS input `ZcRsIn` is LOWER**: the successor branch
needs `c(λ) < 2` (`c(λ) = λ`), the term branch is refuted by the `ε`-number `υ_{λ+1} ∈ (ρ_λ, O(λ))`
(`Zn.znRsTerm_false`), and the value branch by `Zn.znRsVal_false`. -/
theorem znRsIn_big_lower {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hbig : upsilon (succ l) < cdTheta S l (cdCode S l))
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ ZnRsVal (Ys.ysO S) l) : CdLower S l := by
  have hO : upsilon (succ l) < Ys.ysO S l := hbig.trans_le (zn_theta_le_O l)
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρs : upsilon l < upsilon (succ l) := upsilon_normal.strictMono (Order.lt_succ l)
  have hE : InE (upsilon (succ l)) := upsPt_inE (upsPt_upsilon (hl0.trans (Order.lt_succ l)))
  rcases h with (h | ⟨h2, -⟩ | ⟨-, -, ht⟩) | h
  · unfold CdLower; rw [← Ys.ysO_eq S l]; exact h
  · obtain ⟨-, -, hww⟩ := Cp.cp_fix_facts hl hfix
    rw [zn_cL_fix hl hfix] at h2
    have : (2 : Ordinal.{0}) < l := zn_two_lt_omega.trans_le ((le_mul_left _ omega0_pos).trans hww.le)
    exact absurd h2 (not_lt.2 this.le)
  · exact absurd ht (znRsTerm_false hE hρs hO)
  · exact absurd h (znRsVal_false hO)

/-- **The RS input at the fixed restarts of `(l₀, B)` from two parts**: the code continuity `Zn.ZnThCont`
where `ρ_λ < Θ_λ(m_λ) ≤ υ_{λ+1}`, and LOWER or the supply where `υ_{λ+1} < Θ_λ(m_λ)`. -/
theorem znRsF_of_parts {l0 B : Ordinal.{0}}
    (hP1 : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → upsilon B ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) → cdTheta S l (cdCode S l) ≤ upsilon (succ l) → ZnThCont S l)
    (hP2 : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → upsilon B ≤ nuC →
      upsilon (succ l) < cdTheta S l (cdCode S l) → CdLower S l ∨ Zh.ZhSupInB S l B) :
    ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → upsilon B ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ ZnRsVal (Ys.ysO S) l := by
  intro l hl h1 h2 hfix hνB hθ
  have hlν : upsilon l < nuC := (upsilon_normal.strictMono h2).trans_le hνB
  rcases le_or_gt (cdTheta S l (cdCode S l)) (upsilon (succ l)) with hs | hb
  · have hθw : cdTheta S l (cdCode S l) < cdDelta l * ω :=
      hs.trans_lt ((zn_succ_le_delta l).trans_lt (by
        have h0 : 0 < cdDelta l := pos_iff_ne_zero.2 (indec_iff.1 (Wd.wdDelta_indec hl)).1
        have := (mul_lt_mul_iff_right₀ h0).2 one_lt_omega0
        rwa [mul_one] at this))
    exact Or.inr (Or.inr (znVal_of_cont hl hlν hθw (hP1 l hl h1 h2 hfix hνB hθ hs)))
  · rcases hP2 l hl h1 h2 hfix hνB hb with h | h
    · exact Or.inl (Zc.zcRsIn_of_lower h)
    · exact Or.inr (Or.inl h)

/-- The long-exponent CapV input of `W_k` below `ν_C` from its part at the fixed restarts with
`δ_λ·ω ≤ Θ_λ(m_λ)`. -/
theorem znVL_of_fixW (k : ℕ)
    (hVF : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  intro μ hr hw hμν hns
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact hw.2
  rcases eq_or_lt_of_le hm.le_apply with he | hfix
  · rcases lt_or_ge (cdTheta S μ (cdCode S μ)) (cdDelta μ * ω) with hθ | hθ
    · exact znCapV_fixThW hr.1 he.symm hμν hn hθ
    · exact hVF μ hr hw he.symm hμν hθ
  · exfalso
    have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
      rw [Yx.yxUps_base]; exact hw.1
    have hww := Zh.zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
    exact hns (Zh.zh_short_of_nonfix hr.1 hww hfix hn)

/-- The long-exponent CapV input of `W_ω` below `ν_C` from its part at the fixed restarts with
`δ_λ·ω ≤ Θ_λ(m_λ)`. -/
theorem znVLT_of_fixW
    (hVF : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ = μ → upsilon μ < nuC →
      cdDelta μ * ω ≤ cdTheta S μ (cdCode S μ) → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  intro μ hr hw hμν hns
  have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S]; exact hw.2
  rcases eq_or_lt_of_le hm.le_apply with he | hfix
  · rcases lt_or_ge (cdTheta S μ (cdCode S μ)) (cdDelta μ * ω) with hθ | hθ
    · exact znCapV_fixThW hr.1 he.symm hμν hn hθ
    · exact hVF μ hr hw he.symm hμν hθ
  · exfalso
    have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ := by
      rw [Yx.yxUps_base]; exact hw.1
    have hww := Zh.zh_ww_lt Yx.yxBaseW_ri (hm.lt_iff_lt.1 h0)
    exact hns (Zh.zh_short_of_nonfix hr.1 hww hfix hn)

/-- **The RS input at the fixed restarts of `(l₀, B)` from the code statement at the isolated ones and the two
parts at the others** (`¬ Cp.CpIso λ`: `λ` is a limit of fixed restarts). -/
theorem znRsF_of_parts2 {l0 B : Ordinal.{0}} (hI : ZnIsoCode S l0 B)
    (hP1 : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → ¬ Cp.CpIso l → upsilon B ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) → cdTheta S l (cdCode S l) ≤ upsilon (succ l) → ZnThCont S l)
    (hP2 : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → ¬ Cp.CpIso l → upsilon B ≤ nuC →
      upsilon (succ l) < cdTheta S l (cdCode S l) → CdLower S l ∨ Zh.ZhSupInB S l B) :
    ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → upsilon B ≤ nuC →
      upsilon l < cdTheta S l (cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ ZnRsVal (Ys.ysO S) l := by
  refine znRsF_of_parts (fun l hl h1 h2 hfix hνB hθ hs => ?_) (fun l hl h1 h2 hfix hνB hθ => ?_)
  · by_cases hiso : Cp.CpIso l
    · exact absurd (hI l hl h1 h2 hfix hiso) (not_le.2 hθ)
    · exact hP1 l hl h1 h2 hfix hiso hνB hθ hs
  · by_cases hiso : Cp.CpIso l
    · have hρs : upsilon l < upsilon (succ l) := upsilon_normal.strictMono (Order.lt_succ l)
      exact absurd (hI l hl h1 h2 hfix hiso) (not_le.2 (hρs.trans hθ))
    · exact hP2 l hl h1 h2 hfix hiso hνB hθ

end Googology.Trans.PoR.InaccPsi.R2.Zn
