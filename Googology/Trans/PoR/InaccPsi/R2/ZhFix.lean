import Googology.Trans.PoR.InaccPsi.R2.ZhCapW

/-!
# Zh: below `ν_C` every restart that is no `υ`-fixed point is short; the window inputs at the fixed points only

A restart index `λ` with `ω² < λ < υ_λ` is `λ₀ + z` with `0 < z < ρ_{λ₀}`, `ω² ∣ z` (`Cp.cpDecomp`); its name is
`η_{λ₀} + z` and its code is `-1 + e(z)` (`Cp.cpCode_add`), which is the offset `c(λ) = cL λ` (`zh_cL_eq`).  So:

* `zh_cL_eq`: `cL λ = -1 + e(λ)` at every restart index;
* `zh_code_cL` (**the code of a non-fixed restart is its offset**): `m_λ = cL λ` (`λ < υ_λ`, `ρ_λ < P(η₁)`);
* `zhR_nonfix` (**the predicted reach of a non-fixed restart below `ν_C`**): `r(λ) = δ_λ + cL λ`;
* `zhSup_fix` (**every supply restart below `ν_C` is a `υ`-fixed point**): `υ_{λ+ω²} ≤ r(λ)` ⇒ `υ_λ = λ`;
* `zhRsIn_nonfix` (**the RS input at every non-fixed restart below `ν_C`**: `Zc.ZcRsIn`): the successor case
  `O = cL λ = 1`, or the term input with the constant terms `w < cL λ`, realized at the restarts `μ` with
  `cL μ ≥ w` cofinal below `λ` (`R2.cL_dense`);
* `zh_short_of_nonfix`, `zhCapV_nonfix` (**CapV at every non-fixed restart below `ν_C`**);
* `zhWins6`, `zhTopAll6` (**the windows with the RS input and CapV asked only at the `υ`-fixed restarts**);
  `zhVL_of_fix`, `zhVLT_of_fix`: the long-exponent CapV input from its part at the fixed restarts.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem zh_dvd2 {x : Ordinal.{0}} (h : ω ^ 2 ∣ x) : ω ^ (2 : Ordinal.{0}) ∣ x := by
  rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, opow_natCast]; exact h

/-- **`cL λ = -1 + e(λ)`** at every restart index. -/
theorem zh_cL_eq {l : Ordinal.{0}} (hl : IsRestartIdx l) : cL l = cdOff (cdExp l) := by
  have hl0 : l ≠ 0 := hl.1
  have he2 : (2 : Ordinal.{0}) ≤ cdExp l := cdExp_max hl0 (zh_dvd2 hl.2)
  have he1 : (1 : Ordinal.{0}) ≤ cdExp l := one_le_two.trans he2
  have hA : 1 + cL l ≤ cdExp l := cdExp_max hl0 (cL_dvd hl)
  have hB : 1 + cdOff (cdExp l) ≤ cdExp l := by
    unfold cdOff
    split_ifs with h
    · rw [Ordinal.add_sub_cancel_of_le he1]
    · exact (one_add_of_omega0_le (not_lt.1 h)).le
  refine le_antisymm ?_ (le_cL hl0 (dvd_of_le_dvd hB (cdExp_dvd hl0)))
  unfold cdOff
  split_ifs with h
  · have : 1 + cL l - 1 ≤ cdExp l - 1 := by
      rw [Ordinal.sub_le, Ordinal.add_sub_cancel_of_le he1]; exact hA
    rwa [Ordinal.add_sub_cancel] at this
  · exact le_add_self.trans hA

/-- **The code of `λ₀ + z` is its offset** (`z < ρ_{λ₀}`). -/
theorem zh_code_cL_dec {l0 z η1 : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hz0 : 0 < z)
    (hzρ : z < upsilon l0) (hzd : ω * ω ∣ z) (hn : upsilon l0 < Nm.Pv S η1) :
    cdCode S (l0 + z) = cL (l0 + z) := by
  have hri : IsRestartIdx (l0 + z) := zh_ri_add hl0 (by rw [pow_two]; exact hzd)
  rw [Cp.cpCode_add hl0.1 hn hzρ hz0.ne', zh_cL_eq hri, Cp.cpExp_add l0 hz0.ne']

/-- **The code of a non-fixed restart is its offset.** -/
theorem zh_code_cL {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (hn : upsilon l < Nm.Pv S η1) : cdCode S l = cL l := by
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, rfl⟩ := Cp.cpDecomp hl hww hfix
  exact zh_code_cL_dec hl0 hz0 hzρ hzd
    ((upsilon_normal.strictMono.monotone le_self_add).trans_lt hn)

/-- **The predicted reach of a non-fixed restart below `ν_C`**: `r(λ) = δ_λ + cL λ`. -/
theorem zhR_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) : cdR S l = cdDelta l + cL l := by
  have hc := zh_code_cL hl hww hfix hn
  rw [zhR_short_all hl hν (hc ▸ cL_le_ups hl), hc]

/-- **Every supply restart below `ν_C` is a `υ`-fixed point.** -/
theorem zhSup_fix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hlong : upsilon (l + ω ^ 2) ≤ cdR S l) : upsilon l = l := by
  by_contra hne
  have hfix : l < upsilon l := lt_of_le_of_ne upsilon_normal.strictMono.le_apply (Ne.symm hne)
  have h1 := zhLong_code hl hν hlong
  rw [zh_code_cL hl hww hfix hn] at h1
  exact absurd (cL_le_ups hl) (not_le.2 h1)

/-- **The RS input at every non-fixed restart below `ν_C`.** -/
theorem zhRsIn_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) : Zc.ZcRsIn (Ys.ysO S) l := by
  have hm := upsilon_normal.strictMono
  have hO : ∀ μ, IsRestartIdx μ → upsilon μ < nuC → cdCode S μ = cL μ → Ys.ysO S μ = cL μ := by
    intro μ hμ hμν hc
    have hR := zhR_short_all hμ hμν (hc ▸ cL_le_ups hμ)
    unfold Ys.ysO
    rw [hR, hc]
    exact Ordinal.add_sub_cancel _ _
  have hOl : Ys.ysO S l = cL l := hO l hl hν (zh_code_cL hl hww hfix hn)
  have h1c : 1 ≤ cL l := le_cL hl.1 (by
    have := zh_dvd2 hl.2
    rwa [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] at this)
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, hlz⟩ := Cp.cpDecomp hl hww hfix
  have hl0l : l0 < l := by rw [hlz]; exact lt_add_of_pos_right l0 hz0
  have hn0 : upsilon l0 < Nm.Pv S η1 := (hm hl0l).trans hn
  unfold Zc.ZcRsIn
  rw [hOl]
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · refine Or.inr (Or.inl ⟨h2, le_antisymm ?_ h1c⟩)
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] at h2
    exact Order.lt_add_one_iff.1 h2
  · refine Or.inr (Or.inr ⟨h2, h1c, fun w hw => ?_⟩)
    rw [hOl] at hw
    refine ⟨OT.k w, show w < upsilon l from hw.trans_le (cL_le_ups hl), le_rfl, fun ν' hν' => ?_⟩
    have hw1 : max w 1 < cL l := max_lt hw (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hwμ⟩ := cL_dense hl (le_max_right _ _) hw1 (max ν' l0) (max_lt hν' hl0l)
    have hl0μ : l0 < μ := (le_max_right _ _).trans_lt hνμ
    obtain ⟨z', rfl⟩ := exists_add_of_le hl0μ.le
    have hz'0 : 0 < z' := by
      rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ z') with h | h
      · rw [← h, add_zero] at hl0μ; exact absurd hl0μ (lt_irrefl _)
      · exact h
    have hz'z : z' < z := by rw [hlz] at hμl; exact (add_lt_add_iff_left l0).1 hμl
    have hz'd : ω * ω ∣ z' := by
      have h1 : ω ^ 2 ∣ l0 + z' := hμ.2
      rw [pow_two] at h1
      exact (dvd_add_iff (by rw [← pow_two]; exact hl0.2) (c := z')).1 h1
    have hcμ := zh_code_cL_dec hl0 hz'0 (hz'z.trans hzρ) hz'd hn0
    have hOμ := hO (l0 + z') hμ ((hm hμl).trans hν) hcμ
    refine ⟨l0 + z', hμ, (le_max_left _ _).trans_lt hνμ, hμl, ?_⟩
    rw [hOμ]
    exact (le_max_left _ _).trans hwμ

/-- **A non-fixed restart has a short last exponent** (`2 ≤ e(η_λ) < ρ_λ`). -/
theorem zh_short_of_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hn : upsilon l < Nm.Pv S η1) : ZhShortExp S l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, rfl⟩ := Cp.cpDecomp hl hww hfix
  have hn0 : upsilon l0 < Nm.Pv S η1 := (hm.monotone le_self_add).trans_lt hn
  have he : cdEta S (l0 + z) = cdEta S l0 + z := (Cp.cpEta_add hl0.1 hn0 hzρ).1
  unfold ZhShortExp
  rw [he, Cp.cpExp_add _ hz0.ne']
  have h2 : (2 : Ordinal.{0}) ≤ cdExp z := cdExp_max hz0.ne' (zh_dvd2 (by rw [pow_two]; exact hzd))
  refine ⟨?_, (Cp.cpExp_le hz0.ne').trans_lt (hzρ.trans_le (hm.monotone le_self_add))⟩
  have := opow_le_opow_right omega0_pos h2
  rwa [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, opow_natCast] at this

/-- **CapV at every non-fixed restart below `ν_C`.** -/
theorem zhCapV_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) : CdCapV S l := by
  have h := zh_short_of_nonfix hl hww hfix hn
  exact zhCapV_short hl hν hn h.1 h.2

/-- A window restart is above `ω²`. -/
theorem zh_ww_lt {l0 l : Ordinal.{0}} (hl0 : IsRestartIdx l0) (h : l0 < l) : ω * ω < l := by
  have : ω * ω ≤ l0 := by rw [← pow_two]; exact le_of_dvd hl0.1 hl0.2
  exact this.trans_lt h

/-- **ALL WINDOWS `W_k`** with the RS input and CapV asked only at the `υ`-fixed restarts. -/
theorem zhWins6
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVF : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hm := upsilon_normal.strictMono
  refine zhWins5 hin hlow (fun k μ hr hw hns => ?_) (fun k l hl h1 h2 hνB => ?_)
  · rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hVF k μ hr hw he.symm hns
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
      have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
        rw [← Lw.lw_L_eq S]; exact hw.2
      exact hns (zh_short_of_nonfix hr.1 hww hfix hn)
  · rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hrsF k l hl h1 h2 he.symm
    · have hww := zh_ww_lt (Yx.yxBase_ri k) h1
      have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
        rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
      exact Or.inl (zhRsIn_nonfix hl hww hfix ((hm h2).trans_le hνB) hn)

/-- **THE TOP WINDOW `W_ω`** with the RS input and CapV asked only at the `υ`-fixed restarts. -/
theorem zhTopAll6
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hVF : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVFT : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ = μ → ¬ ZhShortExp S μ → CdCapV S μ)
    (hrsFT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have hm := upsilon_normal.strictMono
  have hVL : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → ¬ ZhShortExp S μ → CdCapV S μ := by
    intro k μ hr hw hns
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hVF k μ hr hw he.symm hns
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
      have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
        rw [← Lw.lw_L_eq S]; exact hw.2
      exact hns (zh_short_of_nonfix hr.1 hww hfix hn)
  refine zhTopAll5 hin hlow hVL (fun k l hl h1 h2 hνB => ?_) hinT (fun μ hr hw hns => ?_)
    (fun l hl h1 h2 hνB => ?_) hLw
  · rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hrsF k l hl h1 h2 he.symm
    · have hww := zh_ww_lt (Yx.yxBase_ri k) h1
      have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
        rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
      exact Or.inl (zhRsIn_nonfix hl hww hfix ((hm h2).trans_le hνB) hn)
  · rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hVFT μ hr hw he.symm hns
    · exfalso
      have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ := by
        rw [Yx.yxUps_base]; exact hw.1
      have hww := zh_ww_lt Yx.yxBaseW_ri (hm.lt_iff_lt.1 h0)
      have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
        rw [← Lw.lw_L_eq S]; exact hw.2
      exact hns (zh_short_of_nonfix hr.1 hww hfix hn)
  · rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hrsFT l hl h1 h2 he.symm
    · have hww := zh_ww_lt Yx.yxBaseW_ri h1
      have hn : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
        rw [← Lw.lw_L_eq S, ← Yx.yxUps_base (S := S)]; exact hm h2
      exact Or.inl (zhRsIn_nonfix hl hww hfix ((hm h2).trans_le hνB) hn)

/-- The long-exponent CapV input of `W_k` from its part at the `υ`-fixed restarts. -/
theorem zhVL_of_fix (k : ℕ)
    (hVF : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → ¬ ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → ¬ ZhShortExp S μ → CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  intro μ hr hw hns
  rcases eq_or_lt_of_le hm.le_apply with he | hfix
  · exact hVF μ hr hw he.symm hns
  · exfalso
    have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ := by
      rw [Yx.yxUps_base]; exact hw.1
    have hww := zh_ww_lt (Yx.yxBase_ri k) (hm.lt_iff_lt.1 h0)
    have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact hns (zh_short_of_nonfix hr.1 hww hfix hn)

/-- The long-exponent CapV input of `W_ω` from its part at the `υ`-fixed restarts. -/
theorem zhVLT_of_fix
    (hVF : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon μ = μ → ¬ ZhShortExp S μ → CdCapV S μ) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → ¬ ZhShortExp S μ → CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  intro μ hr hw hns
  rcases eq_or_lt_of_le hm.le_apply with he | hfix
  · exact hVF μ hr hw he.symm hns
  · exfalso
    have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ := by
      rw [Yx.yxUps_base]; exact hw.1
    have hww := zh_ww_lt Yx.yxBaseW_ri (hm.lt_iff_lt.1 h0)
    have hn : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
      rw [← Lw.lw_L_eq S]; exact hw.2
    exact hns (zh_short_of_nonfix hr.1 hww hfix hn)

end Googology.Trans.PoR.InaccPsi.R2.Zh
