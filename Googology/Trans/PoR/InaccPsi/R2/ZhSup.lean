import Googology.Trans.PoR.InaccPsi.R2.ZhRs

/-!
# Zh: the carry is a theorem below `ρ_μ`; the RS input at supply restarts is the supply alone

The inner restarts of `[λ, λ+β)` and `[μ, μ+β)` with `β ≤ ρ_μ < ρ_λ` have the names `η_λ + γ`, `η_μ + γ` and
the same code `-1 + e(γ)` (`Cp.cpCode_add`), which is below `ρ_μ`.  So `Zh.zhCarry_of_codes` gives the carry
with no hypothesis:

* `zhCarry_auto` (**the carry below `ρ_μ`**): `λ`, `μ` restarts, `ρ_μ < ρ_λ < P(η₁)`, `β ≤ ρ_μ`,
  `υ_{λ+β} ≤ ν_C` ⇒ `ZhCarry S λ μ β`;
* `ZhSupB S λ β` (**the supply at `ρ_λ` for one target**): Range restarts `μ` cofinal below `ρ_λ` with
  `μ + β ≤ λ`, `β ≤ ρ_μ`, `υ_{μ+β} ≤ r(μ)`; `ZhSupInB S λ B`: some `β` with `λ + β ≤ B`, `r(λ) ≤ υ_{λ+β}` and
  `ZhSupB S λ β`;
* `zhSupIn_of_B`: `ZhSupInB` gives `Zh.ZhSupIn` (`υ_B ≤ ν_C`, `υ_B ≤ P(η₁)`);
* `zhSupB_of_ra`: the supply `Ra.RaSupAt S ρ_λ` gives `ZhSupB S λ β` for every `β < ρ_λ` for which the
  restarts `μ` close below `λ` have `μ + β ≤ λ`;
* `zhWins4`, `zhTopAll4` (**the windows with the RS input `ZcRsIn ∨ ZhSupInB`**);
* `zhIn4_of_lower` (non-vacuity: LOWER gives the input).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The carry below `ρ_μ`** (the inner codes agree, `Cp.cpCode_add`). -/
theorem zhCarry_auto {l μ β η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hμ : IsRestartIdx μ)
    (hn : upsilon l < Nm.Pv S η1) (hνβ : upsilon (l + β) ≤ nuC) (hβμ : β ≤ upsilon μ)
    (hμl : upsilon μ < upsilon l) : ZhCarry S l μ β := by
  refine zhCarry_of_codes hl hνβ fun γ hγ0 hγd hγβ => ?_
  have hγμ : γ < upsilon μ := hγβ.trans_le hβμ
  have hγl : γ < upsilon l := hγμ.trans hμl
  have e1 := Cp.cpCode_add (S := S) hl.1 hn hγl hγ0.ne'
  have e2 := Cp.cpCode_add (S := S) hμ.1 (hμl.trans hn) hγμ hγ0.ne'
  have hle : cdOff (cdExp γ) ≤ γ := (cdOff_le _).trans (Cp.cpExp_le hγ0.ne')
  rw [e1, e2]
  exact ⟨hle.trans_lt hγl, hle.trans hγμ.le, le_rfl⟩

/-- **The supply at `ρ_λ` for the target `υ_{λ+β}`.** -/
def ZhSupB (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
    β ≤ upsilon μ ∧ upsilon (μ + β) ≤ cdR S μ

/-- **The supply input at a restart of a window with top index `B`.** -/
def ZhSupInB (S : InaccSeq.{0}) (l B : Ordinal.{0}) : Prop :=
  ∃ β, l + β ≤ B ∧ cdR S l ≤ upsilon (l + β) ∧ ZhSupB S l β

/-- **The supply input gives the carry input.** -/
theorem zhSupIn_of_B {l B η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon B ≤ nuC)
    (hn : upsilon B ≤ Nm.Pv S η1) (hlB : l < B) (h : ZhSupInB S l B) : ZhSupIn S l B := by
  obtain ⟨β, hlβ, hr, hc⟩ := h
  have hm := upsilon_normal.strictMono
  refine ⟨β, hlβ, hr, fun x hx => ?_⟩
  obtain ⟨μ, h1, h2, h3, h4, h5, h6⟩ := hc x hx
  exact ⟨μ, h1, h2, h3, h4, h6, zhCarry_auto hl h1.1 ((hm hlB).trans_le hn)
    ((hm.monotone hlβ).trans hν) h5 h3⟩

/-- **The supply from `Ra.RaSupAt`** for a target `β < ρ_λ` that fits above the restarts close below `λ`. -/
theorem zhSupB_of_ra {l β x0 : Ordinal.{0}} (hsup : Ra.RaSupAt S (upsilon l)) (hβ : β < upsilon l)
    (hx0 : x0 < upsilon l) (hfit : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ + β ≤ l) :
    ZhSupB S l β := by
  intro x hx
  obtain ⟨μ, hR, h1, h2, -, h4⟩ := hsup (max (max x x0) β) (max_lt (max_lt hx hx0) hβ)
  have hm := upsilon_normal.strictMono
  refine ⟨μ, hR, (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt h1), h2,
    hfit μ hR.1 ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt h1)) h2,
    ((le_max_right _ _).trans_lt h1).le, (hm.monotone (add_le_add le_rfl (le_max_right _ _))).trans h4⟩

/-- The input of the new windows: `ZcRsIn ∨ ZhSupInB` gives `ZcRsIn ∨ ZhSupIn` below `ν_C`. -/
theorem zhIn_of_B {l B η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon B ≤ nuC)
    (hn : upsilon B ≤ Nm.Pv S η1) (hlB : l < B) (h : Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l B) :
    Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l B := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (zhSupIn_of_B hl hν hn hlB h)

/-- **ALL WINDOWS `W_k`** with the RS input `ZcRsIn ∨ ZhSupInB` (the supply alone at supply restarts). -/
theorem zhWins4
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
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
    ⟨((IH j hj).2.2 μ hr hw).1, hV j μ hr hw⟩
  have hL := Zc.zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  obtain ⟨hν, Sp⟩ := Yx.yxWin_full k ⟨Zc.zcBaseIn k h0 hb hL, hin k⟩ h0 hb (hV k)
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
    zhIn_congr h1 (zhIn_of_B hl hνB hnB h2 (hrs k l hl h1 h2))⟩

/-- **THE TOP WINDOW `W_ω`** with the RS input `ZcRsIn ∨ ZhSupInB`. -/
theorem zhTopAll4
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := zhWins4 hin hlow hV hrs
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Yx.yxCaps_below (n + 1) hlow' (fun j _ μ hr hw => ⟨((W j).2.2 μ hr hw).1, hV j μ hr hw⟩) μ hr hn
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
  obtain ⟨hν, Sp⟩ := Yx.yxTop_full ⟨hbase, hinT⟩ h0 hLw hb hVT
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
    zhIn_congr h1 (zhIn_of_B hl hνB hnB h2 (hrsT l hl h1 h2))⟩

/-- **Non-vacuity**: LOWER at a restart gives the new input. -/
theorem zhIn4_of_lower {l B : Ordinal.{0}} (hL : CdLower S l) :
    Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l B := Or.inl (Zc.zcRsIn_of_lower hL)

end Googology.Trans.PoR.InaccPsi.R2.Zh
