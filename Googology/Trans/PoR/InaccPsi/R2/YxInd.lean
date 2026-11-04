import Googology.Trans.PoR.InaccPsi.R2.YxWin

/-!
# Yx: the windows by one induction (the base bound, the landing blocks, the window inputs)

The bound `O` of the relative block induction is fixed: `yxO S l₀ = ν_C` at the base `l₀` (Lemma TOP at
`ρ_{l₀} ≤ ν_C` with this bound is `nuC_cap`) and `ysO S = r − δ` above it.  What remains of a window
specification is

* `YxIn S l₀ B`: the reach datum of the base chain (`Ys.YsReachIn l₀ 0 ρ_{l₀}`) and at every restart of
  `(l₀, B)` a pair-free input (`Yx.YxShortIn` or `Yx.YxGivenIn`) with the bound `ysO S`;
* the landing blocks below `ρ_{l₀}` (`YxLand`) are NOT an input: they hold below every restart point `≤ ν_C`
  (`R2.land_C`), and `ρ_{l₀} < ν_C` comes from the caps (`Yx.yxNu_gt`); they also come from the window below
  (`yxLand_next`, `yxLand_top`).

Main statements:

* `yxBase_ri`, `yxBase_lt`, `yxBase_cnt`: the bases `ι(Ω_ω + P'·ξ)` are restart indices, increasing, countable;
* `yxSpec_ofIn`: `YxLand`, `YxIn`, `ρ_{l₀} ≤ ν_C` ⇒ `Yx.YxSpec (yxO S l₀) l₀ B`;
* `yxWin_full` (**W_k**): `YxIn` on `W_k`, CAP-0, the caps below `L(k)`, CapV on `W_k`
  ⇒ `L(k+1) ≤ ν_C` and `Ys.YsSpec (yxO S l₀) l₀ l₁` (with `yxO = ysO` above `l₀`);
* `yxTop_full` (**W_ω**): the same on `W_ω` with `Yx.YxLwNo2 S`;
* `yxCaps_of_UV`: the caps below `X` from UPPER and CapV below `X`;
* `yxWins` (**all windows by induction on `k`**): `YxIn` on every `W_k`,
  UPPER ∧ CapV at the range restarts below `L(0)`, CapV and the RS input on every `W_k`
  ⇒ for every `k`: `L(k+1) ≤ ν_C`, `Ys.YsSpec` on `W_k`, UPPER ∧ LOWER on `W_k`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The landing blocks below `υ_{l₀}` (the field `land0`). -/
def YxLand (l0 : Ordinal.{0}) : Prop :=
  ∀ c' < upsilon l0, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l0 ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)

/-- **The window input**: the base reach datum and the pair-free inputs above the base (bound `ysO`). -/
def YxIn (S : InaccSeq.{0}) (l0 B : Ordinal.{0}) : Prop :=
  Ys.YsReachIn l0 0 (upsilon l0) ∧
    ∀ l, IsRestartIdx l → l0 < l → l < B → YxShortIn (upsilon l0) (Ys.ysO S) l ∨ YxGivenIn (Ys.ysO S) l

/-- The bound: `ν_C` at the base, `r − δ` above it. -/
noncomputable def yxO (S : InaccSeq.{0}) (l0 : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  fun μ => if μ = l0 then nuC else Ys.ysO S μ

theorem yxO_above {l0 μ : Ordinal.{0}} (h : l0 < μ) : yxO S l0 μ = Ys.ysO S μ := by
  unfold yxO; rw [if_neg h.ne']

/-- The base indices `ι(Ω_ω + P'·k)` are restart indices. -/
theorem yxBase_ri (k : ℕ) : IsRestartIdx (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) := by
  rcases k with _ | n
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    have e' : upsilon l = upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((0 : ℕ) : Ordinal.{0}))) := by
      rw [← e, yxUps_base]; rfl
    rw [← upsilon_normal.strictMono.injective e']; exact hl
  · exact Pp.ppIota_succ_restart n

theorem yxBaseW_ri : IsRestartIdx (Bt.iota S (Om ω + Nc.ncPp S * ω)) := Pp.ppIota_omega_restart

theorem yxBaseW1_ri : IsRestartIdx (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
  (Lw.lw_restart_L_omega_succ S).1

theorem yxL_lt_succ (k : ℕ) :
    Nc.ncL S (k : Ordinal.{0}) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  rcases k with _ | n
  · simpa using Rl.rlM_lt_L1 (S := S)
  · exact Pp.ppL_lt_succ n

theorem yxIdx_lt {ξ ξ' : Ordinal.{0}} (h : Nc.ncL S ξ < Nc.ncL S ξ') :
    Bt.iota S (Om ω + Nc.ncPp S * ξ) < Bt.iota S (Om ω + Nc.ncPp S * ξ') := by
  rw [← yxUps_base (S := S) ξ, ← yxUps_base (S := S) ξ'] at h
  exact upsilon_normal.strictMono.lt_iff_lt.1 h

theorem yxIdx_cnt (ξ : Ordinal.{0}) : Bt.iota S (Om ω + Nc.ncPp S * ξ) < Om1 :=
  (upsilon_normal.strictMono.le_apply).trans_lt
    ((yxUps_base (S := S) ξ).trans_lt (by rw [Lw.lw_L_eq, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _))

/-- **The pair-free specification from the window input** (`ρ_{l₀} ≤ ν_C`). -/
theorem yxSpec_ofIn {l0 B : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hB : IsRestartIdx B) (hlt : l0 < B)
    (hcnt : B < Om1) (hland : YxLand l0) (hin : YxIn S l0 B) (hν : upsilon l0 ≤ nuC) :
    YxSpec (yxO S l0) l0 B := by
  refine ⟨hl0, (ri_iff.1 hB).2, hcnt, hlt, hland, fun l hl h0 h1 => ?_⟩
  rcases h0.lt_or_eq with h0 | rfl
  · rcases hin.2 l hl h0 h1 with ⟨m, k, x0, a1, a2, a3, a4, a5, a6, a7, a8⟩ | ⟨o, b1, b2, b3, b4⟩
    · refine Or.inl ⟨m, k, x0, by rw [yxO_above h0]; exact a1, a2, a3, a4, a5, fun μ hμ hμl hx => ?_,
        by rw [yxO_above h0]; exact a7, by rw [yxO_above h0]; exact a8⟩
      have hμ0 : l0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt a4 hx)
      rw [yxO_above hμ0]; exact a6 μ hμ hμl hx
    · exact Or.inr ⟨o, b1, by rw [yxO_above h0]; exact b2, by rw [yxO_above h0]; exact b3, b4⟩
  · refine Or.inr ⟨0, ?_, zero_le, fun g hg => ?_, hin.1⟩
    · exact lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le
        (pos_iff_ne_zero.2 hl0.1) (le_self_add.trans le_self_add)))
    · have hg' : nuC < g := by
        refine lt_of_le_of_lt ?_ hg
        unfold yxO; rw [if_pos rfl]; exact le_add_self
      exact nuC_cap _ hν g hg'

/-- **The landing blocks below `υ_B` from a relative block specification on `[l₀, B)`.** -/
theorem yxLand_next {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B) :
    YxLand B :=
  (Ys.ysGood_B Sp).land_all (upsilon_normal.strictMono Sp.lt)

/-- **The caps below `X` from UPPER and CapV below `X`.** -/
theorem yxCaps_of_UV {X : Ordinal.{0}} (h : ∀ μ, CdRange S μ → upsilon μ < X → CdUpper S μ ∧ CdCapV S μ) :
    ∀ μ, CdRange S μ → upsilon μ < X → CdCapAt S μ := fun μ hr hX =>
  cdCapAt_of_upper (h μ hr hX).1 (h μ hr hX).2

/-- **CAP-0 from the caps below `L(0)`.** -/
theorem yxCAP0 (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdCapAt S μ) : CdCAP0 S :=
  fun μ hμ hB hlev => h μ (cdRange_level1 hμ hB hlev) (hlev.trans_le (cdMstar_le_L S 0))

/-- **The pair-free input of a supply restart** from UPPER, LOWER and the long reach `υ_{μ+ω²} ≤ r(μ)` (no pair
datum: `Ys.ysGiven_of_supply` without `Ys.YsNostrIn`). -/
theorem yxGiven_of_supply {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hU : CdUpper S μ) (hL : CdLower S μ)
    (hlong : upsilon (μ + ω * ω) ≤ cdR S μ) : YxGivenIn (Ys.ysO S) μ := by
  have hδ : upsilon (μ + ω + 1) ≤ cdR S μ := cdR_ge S μ
  have hle : le1 (upsilon μ) (upsilon (μ + ω * ω)) :=
    le1_of_le_of_le1 (upsilon_normal.strictMono.monotone le_self_add) hlong hL
  refine ⟨0, lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le
    (pos_iff_ne_zero.2 hμ.1) (le_self_add.trans le_self_add))), zero_le, ?_, Ys.ysReach_long hle⟩
  intro g hg h
  rw [Ys.ysO_eq] at hg
  exact hU (le1_of_le_of_le1 ((cdRho_lt_R S μ).le.trans le_self_add) (Order.add_one_le_of_lt hg) h)

/-- **W_k with the fixed bound**: `L(k+1) ≤ ν_C` and the relative block specification. -/
theorem yxWin_full (k : ℕ)
    (hin : YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (h0 : CdCAP0 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ) :
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  have hlt := yxIdx_lt (S := S) (yxL_lt_succ (S := S) k)
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < nuC := by
    rw [yxUps_base]
    refine yxNu_gt (Pp.ppL_mono (S := S) (le_of_lt (by exact_mod_cast (natCast_lt_omega0 k)))) h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (((Pp.ppL_mono (S := S) (le_of_lt
      (natCast_lt_omega0 k))).trans_lt (Qq.qqL_lt_succ S))), hc⟩ hlX
  have Sp := yxSpec_ofIn (yxBase_ri k) (yxBase_ri (k + 1)) hlt (yxIdx_cnt _)
    (land_C (yxBase_ri k) hρ.le) hin hρ.le
  exact yxWin_spec k Sp h0 hb (fun μ h => yxO_above h) hV

/-- **W_ω with the fixed bound**: `L(ω+1) ≤ ν_C` and the relative block specification. -/
theorem yxTop_full
    (hin : YxIn S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (h0 : CdCAP0 S) (hLw : YxLwNo2 S) (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  have hlt := yxIdx_lt (S := S) (Qq.qqL_lt_succ S)
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [yxUps_base]
    refine yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have Sp := yxSpec_ofIn yxBaseW_ri yxBaseW1_ri hlt (yxIdx_cnt _) (land_C yxBaseW_ri hρ.le) hin hρ.le
  exact yxTop_spec Sp h0 hLw hb (fun μ h => yxO_above h) hV

/-- The RS input of `Ys.ysWin_UL` depends on the bound only at and above the restart. -/
theorem yxRsIn_congr {l0 : Ordinal.{0}} {O O' : Ordinal.{0} → Ordinal.{0}} (h : ∀ μ, l0 < μ → O μ = O' μ)
    {l : Ordinal.{0}} (hl : l0 < l)
    (hin : le1 (upsilon l) (upsilon (l + ω + 1) + O' l) ∨ (cL l < 2 ∧ O' l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O' l ∧ Ys.YsRsIn O' l)) :
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ Ys.YsRsIn O l) := by
  rw [h l hl]
  rcases hin with h1 | h1 | ⟨h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨h2, h3, fun z hz => ?_⟩)
    have hz' : z < O' l := by rw [← h l hl]; exact hz
    obtain ⟨T, hT1, hT2, hT3⟩ := h4 z hz'
    refine ⟨T, hT1, hT2, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, hνμ, hμl, hTμ⟩ := hT3 (max ν l0) (max_lt hν hl)
    exact ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, by
      rw [h μ ((le_max_right _ _).trans_lt hνμ)]; exact hTμ⟩

/-- Every point of `[L(0), L(k))` lies in some `[L(j), L(j+1))`, `j < k`. -/
theorem yxWinOf (k : ℕ) {x : Ordinal.{0}} (h0 : Nc.ncL S 0 ≤ x) (hk : x < Nc.ncL S (k : Ordinal.{0})) :
    ∃ j : ℕ, j < k ∧ Nc.ncL S (j : Ordinal.{0}) ≤ x ∧ x < Nc.ncL S ((j + 1 : ℕ) : Ordinal.{0}) := by
  induction k with
  | zero => exact absurd (h0.trans_lt hk) (by simp)
  | succ n IH =>
    rcases lt_or_ge x (Nc.ncL S (n : Ordinal.{0})) with h | h
    · obtain ⟨j, hj, h1, h2⟩ := IH h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, h, hk⟩

/-- **The caps below `L(k)`** from UPPER ∧ CapV below `L(0)` and in the windows `W_j`, `j < k`. -/
theorem yxCaps_below (k : ℕ)
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ)
    (hwin : ∀ j : ℕ, j < k → ∀ μ, CdRange S μ → Wj.WjWin S j μ → CdUpper S μ ∧ CdCapV S μ) :
    ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → CdCapAt S μ := by
  intro μ hr hk
  rcases lt_or_ge (upsilon μ) (Nc.ncL S 0) with h | h
  · exact cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2
  obtain ⟨j, hj, h1, h2⟩ := yxWinOf k h hk
  rcases h1.lt_or_eq with h1 | h1
  · exact cdCapAt_of_upper (hwin j hj μ hr ⟨h1, h2⟩).1 (hwin j hj μ hr ⟨h1, h2⟩).2
  · have e : μ = Bt.iota S (Om ω + Nc.ncPp S * (j : Ordinal.{0})) :=
      upsilon_normal.strictMono.injective (h1.symm.trans (yxUps_base (S := S) _).symm)
    exact absurd (e ▸ hr) (yxL_notRange j)

/-- **ALL WINDOWS `W_k` BY ONE INDUCTION ON `k`.** -/
theorem yxWins
    (hin : ∀ k : ℕ, YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l)) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have h0 : CdCAP0 S := yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  have hb := yxCaps_below k hlow fun j hj μ hr hw =>
    ⟨((IH j hj).2.2 μ hr hw).1, hV j μ hr hw⟩
  obtain ⟨hν, Sp⟩ := yxWin_full k (hin k) h0 hb (hV k)
  refine ⟨hν, Sp, Ys.ysWin_UL k (fun μ h => yxO_above h) Sp fun l hl h1 h2 =>
    yxRsIn_congr (fun μ h => yxO_above h) h1 (hrs k l hl h1 h2)⟩

/-- **The landing blocks below `L(ω)` from all windows.** -/
theorem yxLand_top
    (hw : ∀ k : ℕ, ∃ O, Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    YxLand (Bt.iota S (Om ω + Nc.ncPp S * ω)) := by
  intro c' hc'
  rw [yxUps_base] at hc'
  obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) c' hc'
  obtain ⟨O, Sp⟩ := hw n
  obtain ⟨σ, σ', h1, h2, h3, h4, h5⟩ := yxLand_next Sp c' (by rw [yxUps_base]; exact hn)
  refine ⟨σ, σ', h1, h2, h3, h4.trans ?_, h5⟩
  rw [yxUps_base, yxUps_base]
  exact (Pp.ppL_lt_omega (S := S) n)

/-- **THE TOP WINDOW `W_ω` after all windows**: `L(ω+1) ≤ ν_C`, the relative block specification and
UPPER ∧ LOWER on `W_ω`, from the hypotheses of `yxWins`, the top window input, CapV and the RS input on
`W_ω`, and the pair hypothesis `Yx.YxLwNo2 S` at `L(ω)`. -/
theorem yxTopAll
    (hin : ∀ k : ℕ, YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l))
    (hinT : YxIn S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l))
    (hLw : YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := yxWins hin hlow hV hrs
  have h0 : CdCAP0 S := yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact yxCaps_below (n + 1) hlow (fun j _ μ hr hw => ⟨((W j).2.2 μ hr hw).1, hV j μ hr hw⟩) μ hr hn
  obtain ⟨hν, Sp⟩ := yxTop_full hinT h0 hLw hb hVT
  exact ⟨hν, Sp, Ys.ysTop_UL (fun μ h => yxO_above h) Sp fun l hl h1 h2 =>
    yxRsIn_congr (fun μ h => yxO_above h) h1 (hrsT l hl h1 h2)⟩

end Googology.Trans.PoR.InaccPsi.R2.Yx
