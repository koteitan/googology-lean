import Googology.Trans.PoR.InaccPsi.R2.LsNamedR
import Googology.Trans.PoR.InaccPsi.R2.LsGamma

/-!
# The road with the realizers at `m*` and `L(n+1)` asked only at the uncovered targets above `υ_{a+a}`

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`.  `m*` and every `L(n+1)` are named points `a = ι(η_a) = P(η_a)`
(`η_a = Ω_ω + P'·ξ`, `Lw.lw_iota_L`, `Lw.lw_GP_L`), and `υ_{a+a} = P(η_a + a) ≤ P(η_a + P')`, which is `L(1)`,
resp. `L(n+2)`.  So `lsReal_named` realizes every target below `υ_{a+a}`:

* `lsM_named`, `lsL_named` (the named data of `m*` and of `L(n+1)`), `lsAA_le` (`υ_{a+a} ≤ b`);
* `lsNamed_R` (**every target below `υ_{a+a}` at `m*` and every `L(n+1)`**, given `L(ω) ≤ ν_C`,
  `CxStdPairTop`, `LsSupCode S k`, UPPER and LOWER at the `Rz.RzRest` Range restarts);
* `lsLe1_of_gapCof` (`a ≤₁ b` from LOWER, `CvNoPair a b`, realizers cofinal below `c` and `Lr.LrGap S a b c`),
  `lsGap_mono` (`LrGap` is weaker for a larger `c`), `lsNamed_gapR`, `lsRoad_gapR` (**the road**),
  `lsRoadGapR_hyp_of_gap2`, `lsRoadGapR_hyp_of_lr` (the realizer hypotheses of `lsRoad_gap2` and of
  `Lr.lrRoad_gap` give those of `lsRoad_gapR`);
* `LsGammaCode S k` (**LC-STRICT in the `Γ`-form** at the Range restarts with the code `G_{k+1} + 1`:
  `ψ_{Ω₁}(A_{η_μ} + G_k) ≤ Γ(ξ₀ + 1 + τ_μ(G_{k+1}))` for `Γ(ξ₀) = ρ_μ`), `lsStrictCode_iff_gamma`
  (**`LsStrictCode S k ↔ LsGammaCode S k`**), `lsFam_ne` (the family is not empty).

No new axiom.  New definition: `LsGammaCode`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

theorem lsOmW_div : ω ^ Om (1 : Ordinal.{0}) ∣ Om ω := by
  rw [← Low.opow_eq_self_of_SC (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
  exact opow_dvd_opow ω (Om_le_Om.2 one_lt_omega0.le)

theorem lsPp_div (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : ω ^ Om (1 : Ordinal.{0}) ∣ Nc.ncPp S * ξ := by
  rw [← Lw.lw_Pp_opow]
  exact (opow_dvd_opow ω (Lw.lw_Om1_lt_Pp S).le).mul_right _

theorem lsCpB1_lt {a : Ordinal.{0}} (h : upsilon Cp.cpB1 < a) : Rz.rzLam < a :=
  lt_of_le_of_lt upsilon_normal.strictMono.le_apply h

/-- The named data of `m*`. -/
theorem lsM_named : Bt.Good S (Om ω) ∧ Bt.iota S (Om ω) = Nc.ncL S 0 ∧ Nm.Pv S (Om ω) = Nc.ncL S 0 ∧
    ω ^ Om (1 : Ordinal.{0}) ∣ Om (ω : Ordinal.{0}) ∧ IsRestartIdx (Nc.ncL S 0) ∧ Rz.rzLam < Nc.ncL S 0 := by
  have hg := Lw.lw_good_L (S := S) (Lw.lw_lt_L_of_le (zero_le : (0 : Ordinal.{0}) ≤ ω + 1))
  rw [mul_zero, add_zero] at hg
  have hι := Lw.lw_iota_L (S := S) (Cv.cvM_GP (S := S))
  rw [mul_zero, add_zero] at hι
  refine ⟨hg, hι, lsM_eq.symm, lsOmW_div, ?_, lsCpB1_lt (Ph.phFr_order (S := S) 0).1.1⟩
  have := lsM_ri (S := S); rwa [hι] at this

/-- The named data of `L(n+1)`. -/
theorem lsL_named (n : ℕ) :
    Bt.Good S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) ∧
    Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    ω ^ Om 1 ∣ Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) ∧
    IsRestartIdx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ∧
    Rz.rzLam < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hle : ((n + 1 : ℕ) : Ordinal.{0}) ≤ ω + 1 := (Ordinal.natCast_lt_omega0 _).le.trans le_self_add
  have hg := Lw.lw_good_L (S := S) (Lw.lw_lt_L_of_le hle)
  have hGP : IsGP (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_GP_L (by exact_mod_cast Nat.succ_ne_zero n) fun β hβ =>
      Lw.lw_lt_L_of_le (hβ.le.trans hle)
  have hι := Lw.lw_iota_L (S := S) hGP
  refine ⟨hg, hι, (Lw.lw_L_eq S _).symm, dvd_add lsOmW_div (lsPp_div S _), ?_,
    lsCpB1_lt (Ph.phFr_order (S := S) n).2.1.1⟩
  have := Pp.ppIota_succ_restart (S := S) n; rwa [hι] at this

/-- **`υ_{a+a} ≤ b`**: `υ(ι(η) + a) = P(η + a) ≤ P(η + P')`. -/
theorem lsAA_le {ηa a : Ordinal.{0}} (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) :
    upsilon (a + a) ≤ Nm.Pv S (ηa + Nc.ncPp S) := by
  have hsh := Rz.rz_iota_shift hg (show a ≤ Nm.Pv S ηa by rw [hP])
  rw [hι] at hsh
  rw [← hsh, Bt.ups_iota]
  refine Nm.Pv_mono (add_le_add le_rfl ?_)
  have ha1 : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  exact (ha1.trans (Lw.lw_Om1_lt_Pp S)).le

/-- The realizers below `υ_{a+a}` at a named point `a`, for a bound `b ≥ υ_{a+a}` below `L(ω)`. -/
theorem lsReal_named_cof {a ηa b : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hab : upsilon (a + a) ≤ b) (hbL : b ≤ Nc.ncL S ω) (hlow : Nc.ncL S ω ≤ nuC)
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ cdCode S μ = lsG S (k + 1) + 1)
    (hk : LsSupCode S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : CxStdPairTop S) :
    ∀ y < upsilon (a + a), ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t := by
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have haE : InE a := by rw [← hua]; exact upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hri.1))
  have hw2a : (ω : Ordinal.{0}) ^ 2 ≤ a := Ordinal.le_of_dvd hri.1 hri.2
  have hωa : (ω : Ordinal.{0}) ≤ a := by
    refine le_trans ?_ hw2a
    rw [pow_two]; exact Ordinal.le_mul_left ω omega0_pos
  have hww : (ω : Ordinal.{0}) ^ 2 < a := by
    have e : (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ ((2 : ℕ) : Ordinal.{0}) := (opow_natCast _ _).symm
    have h2 : ((2 : ℕ) : Ordinal.{0}) < a := (Ordinal.natCast_lt_omega0 2).trans_le hωa
    rw [e]
    calc ω ^ ((2 : ℕ) : Ordinal.{0}) < ω ^ a := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      _ = a := haE
  have h1a : (1 : Ordinal.{0}) < a := one_lt_omega0.trans_le hωa
  have hLw : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  have haa : a < upsilon (a + a) := by
    calc a = upsilon a := hua.symm
      _ < upsilon (a + a) := hm (lt_add_of_pos_right a (pos_iff_ne_zero.2 hri.1))
  have hν : a < nuC := haa.trans_le (hab.trans (hbL.trans hlow))
  have haL : a ≤ Nc.ncL S (ω + 1) := (haa.le.trans (hab.trans hbL)).trans hLw.le
  intro y hy
  have hlim : IsSuccLimit (a + a) := isSuccLimit_add _ (ri_lim hri)
  obtain ⟨ζ, hζ, hyζ⟩ := (upsilon_normal.lt_iff_exists_lt hlim).1 hy
  obtain ⟨d, hd, hζd⟩ : ∃ d < a, ζ ≤ a + d := by
    rcases le_or_gt ζ a with h | h
    · exact ⟨0, pos_iff_ne_zero.2 hri.1, by rw [add_zero]; exact h⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le h.le
      exact ⟨d, (add_lt_add_iff_left a).1 hζ, le_rfl⟩
  set β := ω ^ 2 * (d + 1) with hβdef
  have hβa : β < a := haE.mul_lt hww (haE.add_lt hd h1a)
  have hdβ : d < β := (lt_add_one d).trans_le (Ordinal.le_mul_right (d + 1) (pow_pos omega0_pos 2))
  have hβb : upsilon (a + β) ≤ b := (hm (lr_addL (a := a) hβa)).le.trans hab
  refine ⟨upsilon (a + β), hyζ.trans_le (hm.monotone (hζd.trans (lr_addLe (a := a) hdβ.le))), hβb, ?_⟩
  exact lsReal_named hg hι hP hdiv hri hzl hν (hβb.trans (hbL.trans hlow))
    (hβb.trans_lt (hbL.trans_lt hLw)) (dvd_mul_right _ _) hβa hcof hk hU hL hstd haL

/-! ## At `m*` and every `L(n+1)` -/

/-- **Every target below `υ_{a+a}` at `m*` and at every `L(n+1)` is realized.** -/
theorem lsNamed_R {k : ℕ} (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S) (hk : LsSupCode S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    ((∀ y < upsilon (Nc.ncL S 0 + Nc.ncL S 0), ∃ t, y < t ∧ t ≤ Nc.ncL S 1 ∧ LrReal S (Nc.ncL S 0) t) ∧
      upsilon (Nc.ncL S 0 + Nc.ncL S 0) ≤ Nc.ncL S 1) ∧
    ∀ n : ℕ, (∀ y < upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})),
        ∃ t, y < t ∧ t ≤ Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
          LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) t) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := lsM_named (S := S)
    have hb : upsilon (Nc.ncL S 0 + Nc.ncL S 0) ≤ Nc.ncL S 1 := by
      have := lsAA_le hg hι hP
      rwa [← mul_one (Nc.ncPp S), ← Lw.lw_L_eq] at this
    exact ⟨lsReal_named_cof hg hι hP hdiv hri hzl hb (Pp.ppL_mono one_lt_omega0.le) hlow
      (lsNames_M (S := S) k) hk hU hL hstd, hb⟩
  · obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := lsL_named (S := S) n
    have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have := lsAA_le hg hι hP
      have e : Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncPp S =
          Om ω + Nc.ncPp S * ((n + 2 : ℕ) : Ordinal.{0}) := (Rm.rm_eta_succ (S := S) (n + 1)).symm
      rwa [e, ← Lw.lw_L_eq] at this
    exact ⟨lsReal_named_cof hg hι hP hdiv hri hzl hb (Pp.ppL_lt_omega (n + 1)).le hlow
      (lsNames_L (S := S) n k) hk hU hL hstd, hb⟩

/-- **`a ≤₁ b` from LOWER, `CvNoPair a b`, realizers cofinal below `c` and the uncovered targets above `c`.** -/
theorem lsLe1_of_gapCof (hL : CdLOWER S) {a b c : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hc : ∀ y < c, ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t) (h : LrGap S a b c) : le1 a b := by
  refine lrLe1_of_cover hL hab hP fun y hay hyb hy => ?_
  by_cases hcov : ∃ l', CdRange S l' ∧ a ≤ upsilon l' ∧ upsilon l' ≤ y ∧ y < cdR S l'
  · exact Or.inl hcov
  · right
    by_cases hcy : c ≤ y
    · exact h y hay hcy hyb hy hcov
    · exact hc y (not_le.1 hcy)

/-- `LrGap` is weaker for a larger `c`. -/
theorem lsGap_mono {a b c c' : Ordinal.{0}} (hcc : c ≤ c') (h : LrGap S a b c) : LrGap S a b c' :=
  fun y hay hcy => h y hay (hcc.trans hcy)

/-- **The crossing relations at the named restarts from the uncovered targets above `υ_{a+a}`.** -/
theorem lsNamed_gapR {k : ℕ} (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S) (hk : LsSupCode S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S := by
  have hL' := Rz.rzLOWER_of_rest hL
  obtain ⟨⟨r0, -⟩, rn⟩ := lsNamed_R (S := S) hlow hstd hk hU hL
  refine ⟨?_, fun n => ?_, lrLe1_of_realCof hL' (Qq.qqL_lt_succ S).le hP hw⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    exact lsLe1_of_gapCof hL' (Pp.ppL_mono zero_le)
      (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) r0 h0
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact lsLe1_of_gapCof hL' (Pp.ppL_lt_succ n).le
      (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (rn n).1 (hn n)

/-- **The road with the realizers at `m*` and `L(n+1)` asked only at the targets `≥ υ_{a+a}` that no restart
reach covers**, given LC-STRICT at the Range restarts with the code `G_{k+1} + 1`. -/
theorem lsRoad_gapR {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hk : LsSupCode S k)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (lsNamed_gapR (cdLow_enum hU' hV') hstd hk hU hL h0 hn hP hw) hmove hstd

theorem lsIx_named {a : Ordinal.{0}} (h : upsilon a = a) : lrIx a = a := by
  have := lrIx_up a; rwa [h] at this

/-- **The realizer hypotheses of `lsRoad_gap2` give those of `lsRoad_gapR`** (`υ_{ι(a)+ω²} ≤ υ_{a+a}`). -/
theorem lsRoadGapR_hyp_of_gap2
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2))) :
    LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)) ∧
    ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) := by
  have key : ∀ a, upsilon a = a → IsRestartIdx a →
      upsilon (lrIx a + ω ^ 2) ≤ upsilon (a + a) := fun a hfix hri => by
    rw [lsIx_named hfix]
    exact upsilon_normal.strictMono.monotone (add_le_add le_rfl (Ordinal.le_of_dvd hri.1 hri.2))
  have hfix : ∀ ηa a : Ordinal.{0}, Bt.iota S ηa = a → Nm.Pv S ηa = a → upsilon a = a :=
    fun ηa a hι hP => by have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨-, hι, hP, -, hri, -⟩ := lsM_named (S := S)
    exact lsGap_mono (key _ (hfix _ _ hι hP) hri) h0
  · obtain ⟨-, hι, hP, -, hri, -⟩ := lsL_named (S := S) n
    exact lsGap_mono (key _ (hfix _ _ hι hP) hri) (hn n)

/-- **The realizer hypotheses of `Lr.lrRoad_gap` give those of `lsRoad_gapR`.** -/
theorem lsRoadGapR_hyp_of_lr
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1))) :
    LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)) ∧
    ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) := by
  have hw : ω + 1 ≤ ω ^ 2 := by
    have h := lr_omega_mul_add_one_lt 1
    rw [Nat.cast_one, mul_one] at h
    exact h.le
  have hmono : ∀ a, upsilon (lrIx a + ω + 1) ≤ upsilon (lrIx a + ω ^ 2) := fun a =>
    upsilon_normal.strictMono.monotone (by rw [add_assoc]; exact add_le_add le_rfl hw)
  exact lsRoadGapR_hyp_of_gap2 (lsGap_mono (hmono _) h0) fun n => lsGap_mono (hmono _) (hn n)

/-- **LC-STRICT in the `Γ`-form** at the Range restarts with the code `G_{k+1} + 1`. -/
def LsGammaCode (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = lsG S (k + 1) + 1 → ∀ ξ0, gamma ξ0 = upsilon μ →
    S.psi (ConjT.Aη S (cdEta S μ) + lsG S k) (Om 1) ≤
      gamma (ξ0 + 1 + cdOtp (lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ)) (lsG S (k + 1)))

/-- **`LsStrictCode S k ↔ LsGammaCode S k`.** -/
theorem lsStrictCode_iff_gamma {k : ℕ} : LsStrictCode S k ↔ LsGammaCode S k := by
  constructor
  · intro h μ hR hc ξ0 hξ
    exact (lsStrict_iff_gamma (lsPv_range hR) hξ).1 (h μ hR hc)
  · intro h μ hR hc
    obtain ⟨ξ0, hξ⟩ := lsGamma_idx (lsPv_range hR)
    exact (lsStrict_iff_gamma (lsPv_range hR) hξ).2 (h μ hR hc ξ0 hξ)

/-- The family of `LsStrictCode S k` is not empty. -/
theorem lsFam_ne (k : ℕ) : ∃ μ, CdRange S μ ∧ cdCode S μ = lsG S (k + 1) + 1 := by
  obtain ⟨μ, hR, -, -, hc⟩ := lsNames_M (S := S) k 0 (Lw.lw_L_SC S 0).1
  exact ⟨μ, hR, hc⟩

/-- **The supply target is below the upper bound of the reading** (a check of `LsSupCode`):
`υ_{μ+ρ_μ} = ψ_{Ω₁}(A + θ·ρ_μ) < ψ_{Ω₁}(A + m_μ)`, and `Θ_μ(m_μ) ≤ ψ_{Ω₁}(A + m_μ)` (`lsTheta_le_psi`). -/
theorem lsSup_ub {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = lsG S (k + 1) + 1)
    (hown : ConjT.Aη S (cdEta S μ) ∈ S.CSet (ConjT.Aη S (cdEta S μ)) (Nm.Pv S (cdEta S μ))) :
    upsilon (μ + upsilon μ) < S.psi (ConjT.Aη S (cdEta S μ) + cdCode S μ) (Om 1) := by
  have hpv := lsPv_range hR
  obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
    (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
  set A := ConjT.Aη S (cdEta S μ) with hA
  set G := lsG S (k + 1)
  have hsh := Rz.rz_iota_shift hgμ (show upsilon μ ≤ Nm.Pv S (cdEta S μ) by rw [hpv])
  rw [hιμ] at hsh
  have e1 : upsilon (μ + upsilon μ) = S.psi (A + ConjT.th S * upsilon μ) (Om 1) := by
    rw [← hsh, Bt.ups_iota, hA]
    unfold ConjT.Aη; rw [mul_add, add_assoc]
  rw [e1, hc]
  have hGSC : SC G := lsG_SC _
  have hθG : ConjT.th S < G := lsTh_lt_G (lsThw_ne (k + 1))
  have hρ1 : upsilon μ < Om 1 := by rw [← hpv]; exact Nm.Pv_lt_Om1 S _
  have hρG : upsilon μ < G := hρ1.trans (lsG_Om1 _)
  have hGE : ω ^ G = G := Low.opow_eq_self_of_SC hGSC
  have hθρ : ConjT.th S * upsilon μ < G := by
    have hp := isPrincipal_mul_omega0_opow_opow G
    rw [hGE, hGE] at hp
    exact hp hθG hρG
  set d := A + (G + 1) with hd
  have hAd : A ≤ d := le_self_add
  have hρm : upsilon μ ∈ S.CSet d (S.psi d (Om 1)) := by
    rw [← hpv]
    exact CSet.psi_mem ((lt_add_one A).trans_le (add_le_add le_rfl (Order.one_le_iff_ne_zero.2
      (lt_of_lt_of_le hGSC.1 le_self_add).ne'))) Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _))
      ((psi_mono (S := S) Low.InR_Om_one hAd).2 hown)
  have hθm : ConjT.th S ∈ S.CSet d (S.psi d (Om 1)) := by
    have hw : Om ω < d := by
      have h1 : Om ω ≤ A := by rw [hA]; unfold ConjT.Aη; exact le_self_add
      exact h1.trans_lt (lt_add_of_pos_right A (Order.lt_add_one_iff.2 zero_le))
    exact CSet.psi_mem hw (InR_Om_succ 1) (Mx.mxOm2_mem _ _) (ConjT.OmW_mem S _ _)
  have hthE : ω ^ ConjT.th S = ConjT.th S := Low.opow_eq_self_of_SC (SC_psi (InR_Om_succ 1) _)
  have hρE : ω ^ upsilon μ = upsilon μ := by rw [← hpv]; exact Low.opow_eq_self_of_SC (Nm.Pv_SC S _)
  have hpm : ConjT.th S * upsilon μ ∈ S.CSet d (S.psi d (Om 1)) := by
    rw [← hρE, lsMul_opow hthE]
    exact lsOpow_mem (CSet.add_mem hθm hρm)
  refine psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 (hθρ.trans (lt_add_one G))) ?_
  exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hAd).2 hown) hpm

end Googology.Trans.PoR.InaccPsi.R2.Ls
