import Googology.Trans.PoR.InaccPsi.R2.RaNamed

/-!
# `T` at `L(ω)` by the realizer technique: exactly what it needs

`L(ω) = P(Ω_ω + P'·ω)` is a named point (`ι(Ω_ω + P'·ω) = L(ω)`, a restart, `ω^{Ω₁} ∣ Ω_ω + P'·ω`), and
`υ_{L(ω)+L(ω)} ≤ P(Ω_ω + P'·(ω+1)) = L(ω+1)`.  The realizer technique (`raReal_upto`) needs the targets below
`ν_C` (the short reaches `r = δ + m` of the inner restarts are read below `ν_C`).  So:

* `raLw_named` (the named data of `L(ω)`), `raLw_AA` (`υ_{L(ω)+L(ω)} ≤ L(ω+1)`), `raSupAt_Lw` (**`LsSupCode S k`
  gives `RaSupAt S L(ω)`**: the family is cofinal below every `L(n+1)`, hence below `L(ω)`);
* `raReal_Lw` (**every target below `υ_{L(ω)+L(ω)}` is realized at `L(ω)`**, given `L(ω) < ν_C`,
  `υ_{L(ω)+L(ω)} ≤ ν_C`, `RaSupAt S L(ω)`, UPPER/LOWER at the `Rz.RzRest` Range restarts, `CxStdPairTop`);
* `raT_of_Lw` (**`T: L(ω) ≤₁ L(ω+1)`** from those, `CvNoPair L(ω) L(ω+1)` and the uncovered targets
  `LrGap S L(ω) L(ω+1) υ_{L(ω)+L(ω)}`), `raRoad_Lw` (**the road** with `T` replaced by these);
* `raNu_need` (**the two lower bounds of `ν_C` asked by the technique follow from the road's conclusion**
  `ν_C = L(ω+1)`): `L(ω) < ν_C` and `υ_{L(ω)+L(ω)} ≤ ν_C` are exactly the a-priori part, satisfiable.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ra

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Ls

variable {S : InaccSeq.{0}}

/-- The named data of `L(ω)`. -/
theorem raLw_named :
    Bt.Good S (Om ω + Nc.ncPp S * ω) ∧ Bt.iota S (Om ω + Nc.ncPp S * ω) = Nc.ncL S ω ∧
    Nm.Pv S (Om ω + Nc.ncPp S * ω) = Nc.ncL S ω ∧ ω ^ Om 1 ∣ Om ω + Nc.ncPp S * ω ∧
    IsRestartIdx (Nc.ncL S ω) ∧ Rz.rzLam < Nc.ncL S ω := by
  have hι := Lw.lw_iota_L_omega S
  refine ⟨Lw.lw_good_L_omega S, hι, (Lw.lw_L_eq S _).symm, dvd_add lsOmW_div (lsPp_div S _), ?_,
    lsCpB1_lt (Ph.phFr_order (S := S) 0).2.1.2.1⟩
  have := Pp.ppIota_omega_restart (S := S); rwa [hι] at this

/-- `υ_{L(ω)+L(ω)} ≤ L(ω+1)`. -/
theorem raLw_AA : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ Nc.ncL S (ω + 1) := by
  obtain ⟨hg, hι, hP, -⟩ := raLw_named (S := S)
  have := lsAA_le hg hι hP
  have e : Om ω + Nc.ncPp S * ω + Nc.ncPp S = Om ω + Nc.ncPp S * (ω + 1) := by
    rw [mul_add_one, add_assoc]
  rwa [e, ← Lw.lw_L_eq] at this

theorem raLw_lt_AA : Nc.ncL S ω < upsilon (Nc.ncL S ω + Nc.ncL S ω) := by
  obtain ⟨-, hι, hP, -, hri, -⟩ := raLw_named (S := S)
  have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ω); rw [hι] at h
  calc Nc.ncL S ω = upsilon (Nc.ncL S ω) := (h.trans hP).symm
    _ < _ := upsilon_normal.strictMono (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hri.1))

/-- **`LsSupCode S k` gives `RaSupAt S L(ω)`.** -/
theorem raSupAt_Lw {k : ℕ} (hk : LsSupCode S k) : RaSupAt S (Nc.ncL S ω) := by
  refine raSupAt_of_code (k := k) (fun γ hγ => ?_) hk
  obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) γ hγ
  obtain ⟨μ, hR, h1, h2, hc⟩ := lsNames_L (S := S) n k γ hn
  exact ⟨μ, hR, h1, h2.trans (Pp.ppL_lt_omega n), hc⟩

/-- **Every target below `υ_{L(ω)+L(ω)}` is realized at `L(ω)`**, given `L(ω) < ν_C` and
`υ_{L(ω)+L(ω)} ≤ ν_C`. -/
theorem raReal_Lw (hν : Nc.ncL S ω < nuC) (hνa : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC)
    (hsup : RaSupAt S (Nc.ncL S ω))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : CxStdPairTop S) :
    ∀ y < upsilon (Nc.ncL S ω + Nc.ncL S ω), ∃ t, y < t ∧ t ≤ upsilon (Nc.ncL S ω + Nc.ncL S ω) ∧
      LrReal S (Nc.ncL S ω) t := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := raLw_named (S := S)
  exact raReal_upto hg hι hP hdiv hri hzl hν hνa raLw_AA hsup hU hL hstd

/-- **`T` by the realizer technique at `L(ω)`**: from `CvNoPair L(ω) L(ω+1)`, `L(ω) < ν_C`,
`υ_{L(ω)+L(ω)} ≤ ν_C`, `RaSupAt S L(ω)` and the uncovered targets above `υ_{L(ω)+L(ω)}`. -/
theorem raT_of_Lw (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hν : Nc.ncL S ω < nuC) (hνa : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC)
    (hsup : RaSupAt S (Nc.ncL S ω))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : CxStdPairTop S)
    (hgap : LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) : CxT S := by
  refine lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Qq.qqL_lt_succ S).le hP (fun y hy => ?_) hgap
  obtain ⟨t, h1, h2, h3⟩ := raReal_Lw hν hνa hsup hU hL hstd y hy
  exact ⟨t, h1, h2.trans raLw_AA, h3⟩

/-- **The road with `T` from the realizer technique at `L(ω)`.** -/
theorem raRoad_Lw (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hs0 : RaSupAt S (Nc.ncL S 0)) (hsn : ∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hsw : RaSupAt S (Nc.ncL S ω))
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hν : Nc.ncL S ω < nuC) (hνa : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC)
    (hgap : LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  raRoad_T hU hO hL hV hEQ htop hups hs0 hsn h0 hn
    (raT_of_Lw hP hν hνa hsw hU hL hstd hgap) hmove hstd

/-- **The lower bounds of `ν_C` asked at `L(ω)` follow from `ν_C = L(ω+1)`** (so they are satisfiable
exactly when the road's conclusion holds). -/
theorem raNu_need (h : nuC = Nc.ncL S (ω + 1)) :
    Nc.ncL S ω < nuC ∧ upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC := by
  rw [h]
  exact ⟨raLw_lt_AA.trans_le raLw_AA, raLw_AA⟩

end Googology.Trans.PoR.InaccPsi.R2.Ra
