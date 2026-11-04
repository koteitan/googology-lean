import Googology.Trans.PoR.InaccPsi.R2.ZcReal
import Googology.Trans.PoR.InaccPsi.R2.YxVac
import Googology.Trans.PoR.InaccPsi.R2.RcT

/-!
# Zc: the windows by one induction with the base reach datum PROVED inside the induction

`Yx.yxWins` takes the window input `Yx.YxIn S l₀ l₁` on every window `W_k`; its first part is the base reach
datum `Ys.YsReachIn l₀ 0 L(k)` (a point `c ≤ L(k)` that is `≤₁` a point inside a chain block after `δ_{l₀}` is
`≤₁` its top).  Here it is proved at the step `k` of the induction from what the earlier steps give:

* LOWER at every Range restart below `L(k)` (below `L(0)` from the hypothesis, in `W_j`, `j < k`, from the
  induction; the points `L(j)` are no Range restarts);
* `L(k) < ν_C` from the caps (`Yx.yxNu_gt`);
* the supply `Ra.RaSupAt S L(k)` (`Rx.rxSupAt`, unconditional; at `L(ω)` from the `L(n+1)`, `Rc.rcSupAt_Lw_of`);

by the realizer maps of the shift (`Zc.zcReal_shift`, `Zc.zcLe1_of_real`): `L(k) ≤₁ υ_{l₀+ω²}`, which gives the
reach datum (`Ys.ysReach_long`).  So the window input that is left is the part at the restarts strictly inside
the window, `ZcInR S l₀ l₁`.

* `zcLower_below`, `zcRho_lt`: LOWER below `L(k)`, `L(k) < ν_C` from the earlier windows and the caps;
* `zcWins` (**all windows**): `ZcInR` on every `W_k`, UPPER ∧ LOWER ∧ CapV at the Range restarts below `L(0)`,
  CapV and the RS input on every `W_k` ⇒ for every `k`: `L(k+1) ≤ ν_C`, `Ys.YsSpec` on `W_k`, UPPER ∧ LOWER on
  `W_k`;
* `zcTopAll` (**the top window**): the same with `ZcInR`, CapV, the RS input on `W_ω` and `Yx.YxLwNo2 S`;
* `zcWins_of_target` (**non-vacuity**): the hypotheses of `zcWins` follow from UPPER, LOWER, CapV at the Range
  restarts below `L(ω)` and the chain reach data of the restarts inside the windows.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The window input at the restarts strictly inside the window** (the part of `Yx.YxIn` that is left). -/
def ZcInR (S : InaccSeq.{0}) (l0 B : Ordinal.{0}) : Prop :=
  ∀ l, IsRestartIdx l → l0 < l → l < B →
    Yx.YxShortIn (upsilon l0) (Ys.ysO S) l ∨ Yx.YxGivenIn (Ys.ysO S) l

/-- The points `L(ξ)` are countable. -/
theorem zcL_cnt (ξ : Ordinal.{0}) : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ξ)) < Om1 :=
  (Yx.yxUps_base (S := S) ξ).trans_lt (by rw [Lw.lw_L_eq, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _)

/-- **LOWER below `L(k)`** from LOWER below `L(0)` and in the windows `W_j`, `j < k`. -/
theorem zcLower_below (k : ℕ)
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdLower S μ)
    (hwin : ∀ j : ℕ, j < k → ∀ μ, CdRange S μ → Wj.WjWin S j μ → CdLower S μ) :
    ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdLower S μ := by
  intro μ hr hk
  rcases lt_or_ge (upsilon μ) (Nc.ncL S 0) with h | h
  · exact hlow μ hr h
  obtain ⟨j, hj, h1, h2⟩ := Yx.yxWinOf k h hk
  rcases h1.lt_or_eq with h1 | h1
  · exact hwin j hj μ hr ⟨h1, h2⟩
  · have e : μ = Bt.iota S (Om ω + Nc.ncPp S * (j : Ordinal.{0})) :=
      upsilon_normal.strictMono.injective (h1.symm.trans (Yx.yxUps_base (S := S) _).symm)
    exact absurd (e ▸ hr) (Yx.yxL_notRange j)

/-- **`L(k) < ν_C`** from CAP-0 and the caps below `L(k)`. -/
theorem zcRho_lt (k : ℕ) (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ) :
    upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < nuC := by
  rw [Yx.yxUps_base]
  refine Yx.yxNu_gt (Pp.ppL_mono (S := S) (le_of_lt (by exact_mod_cast (natCast_lt_omega0 k)))) h0 ?_
  intro μ hμ hB hlev hlX hc
  exact hb μ ⟨hμ, hB, hlX.trans (((Pp.ppL_mono (S := S) (le_of_lt
    (natCast_lt_omega0 k))).trans_lt (Qq.qqL_lt_succ S))), hc⟩ hlX

/-- The supply at `L(k)` (unconditional). -/
theorem zcSup (k : ℕ) : Ra.RaSupAt S (upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))) := by
  rw [Yx.yxUps_base]
  rcases k with _ | n
  · simpa using (Rx.rxSupAt (S := S)).1
  · exact (Rx.rxSupAt (S := S)).2 n

/-- The supply at `L(ω)` (unconditional). -/
theorem zcSupW : Ra.RaSupAt S (upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω))) := by
  rw [Yx.yxUps_base]
  exact Rc.rcSupAt_Lw_of (Rx.rxSupAt (S := S)).2

/-- **The base reach datum of `W_k`** from LOWER below `L(k)` and the caps below `L(k)`. -/
theorem zcBaseIn (k : ℕ) (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ)
    (hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdLower S μ) :
    Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))) :=
  zcBase_reach (Yx.yxBase_ri k) (zcL_cnt _) (zcRho_lt k h0 hb) (zcSup k)
    (fun μ hr h => hL μ hr (by rw [Yx.yxUps_base] at h; exact h))

/-- **ALL WINDOWS `W_k` BY ONE INDUCTION ON `k`, with the base reach datum proved.** -/
theorem zcWins
    (hin : ∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l)) :
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
  have hL := zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  obtain ⟨hν, Sp⟩ := Yx.yxWin_full k ⟨zcBaseIn k h0 hb hL, hin k⟩ h0 hb (hV k)
  refine ⟨hν, Sp, Ys.ysWin_UL k (fun μ h => Yx.yxO_above h) Sp fun l hl h1 h2 =>
    Yx.yxRsIn_congr (fun μ h => Yx.yxO_above h) h1 (hrs k l hl h1 h2)⟩

/-- **THE TOP WINDOW `W_ω` after all windows, with the base reach datum proved.** -/
theorem zcTopAll
    (hin : ∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l))
    (hinT : ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l))
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := zcWins hin hlow hV hrs
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
    exact zcLower_below (n + 1) (fun μ hr h => (hlow μ hr h).2.1)
      (fun j _ μ hr hw => ((W j).2.2 μ hr hw).2) μ hr hn
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have hbase : Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * ω)) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω))) :=
    zcBase_reach Yx.yxBaseW_ri (zcL_cnt _) hρ zcSupW
      (fun μ hr h => hL μ hr (by rw [Yx.yxUps_base] at h; exact h))
  obtain ⟨hν, Sp⟩ := Yx.yxTop_full ⟨hbase, hinT⟩ h0 hLw hb hVT
  exact ⟨hν, Sp, Ys.ysTop_UL (fun μ h => Yx.yxO_above h) Sp fun l hl h1 h2 =>
    Yx.yxRsIn_congr (fun μ h => Yx.yxO_above h) h1 (hrsT l hl h1 h2)⟩

/-- **NON-VACUITY of `zcWins`**: its hypotheses follow from UPPER, LOWER, CapV at the Range restarts below
`L(ω)` and the chain reach data `Ys.YsReachIn l 0 ρ_l` at the restarts below `L(ω)`. -/
theorem zcWins_of_target
    (hU : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdUpper S μ)
    (hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ)
    (hV : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → upsilon l < Nc.ncL S ω → Ys.YsReachIn l 0 (upsilon l)) :
    (∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) ∧
    (∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ) := by
  have hL0ω : Nc.ncL S 0 < Nc.ncL S ω :=
    (Pp.ppL_mono (S := S) zero_le).trans_lt (Pp.ppL_lt_omega (S := S) 0)
  obtain ⟨hin, -, -, -⟩ := Yx.yxWins_of_target hU hL hV hR
  exact ⟨fun k => (hin k).2, fun μ hr h =>
    ⟨hU μ hr (h.trans hL0ω), hL μ hr (h.trans hL0ω), hV μ hr (h.trans hL0ω)⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Zc
