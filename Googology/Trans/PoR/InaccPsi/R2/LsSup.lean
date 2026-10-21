import Googology.Trans.PoR.InaccPsi.R2.LsName
import Googology.Trans.PoR.InaccPsi.R2.LrCover

/-!
# The restart supply from one uniform LC-STRICT, and the roads

`G' = G_{k+1} = G(θ_{k+1}·ω²)`, `L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `ι(u) = Lr.lrIx u`.  `Lr.LrStrictCof S a`
asks, for every `γ < a`, a Range restart `μ ∈ (γ, a)` with LC-STRICT at `μ, k` (some `k`) and `m_μ ≥ G_{k+1}`.
`lsNames_M`, `lsNames_L` give the restarts with `m_μ = G_{k+1} + 1` for every `k`; so one statement about
the restarts of that code is enough:

* `LsStrictCode S k`: LC-STRICT at `μ, k` for every Range restart `μ` with `m_μ = G_{k+1} + 1`;
  `LsCoverCode S k`: the covering `LsCover S μ k` there; `lsStrictCode_of_cover` (`LsStrict.lsStrict_of_cover`);
* `lsStrictCof_M`, `lsStrictCof_L` (**`LsStrictCode S k → Lr.LrStrictCof` at `m*` and at every `L(n+1)`**),
  `lsSup_named` (**the supply `Lr.LrSup S a ω²` at `m*` and every `L(n+1)`**, `Lr.lrSup_of_strict`);
* `LsSupCode S k` (**the supply at the family**: `υ_{μ+ρ_μ} ≤ r(μ)` at every Range restart with the code
  `G_{k+1} + 1`), `lsSupCode_of_strict` (**`LsStrictCode → LsSupCode`**), `lsSup_named_sup`;
* `lsNamed_shift2` (**the realizers at `m*` and every `L(n+1)` up to the next restart `υ_{ι(a)+ω²}`**, from
  `L(ω) ≤ ν_C`, `CxStdPairTop` and `LsSupCode S k`: no supply hypothesis);
* `lsRoad_strict` (`Lr.lrRoad_strict` with its two supply hypotheses replaced by `LsStrictCode S k`),
  `lsRoad_cover` (the same from `LsCoverCode S k`), `lsRoad_gap2` (**the road with the realizers asked only at
  the targets above `υ_{ι(a)+ω²}` that no restart reach covers**, `Lr.LrGap`).

No new axiom.  New definitions: `LsStrictCode`, `LsCoverCode`, `LsSupCode`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **LC-STRICT at `k` at every Range restart with the code `G_{k+1} + 1`.** -/
def LsStrictCode (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = lsG S (k + 1) + 1 → Lc.LcStrictAt S μ k

/-- **The covering at `k` at every Range restart with the code `G_{k+1} + 1`.** -/
def LsCoverCode (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = lsG S (k + 1) + 1 → LsCover S μ k

/-- `ρ_μ = P(η_μ)` at a Range restart. -/
theorem lsPv_range {μ : Ordinal.{0}} (h : CdRange S μ) : Nm.Pv S (cdEta S μ) = upsilon μ :=
  cdEta_pv h.1.1 (by rw [← Lw.lw_L_eq]; exact h.2.2.1)

theorem lsStrictCode_of_cover {k : ℕ} (h : LsCoverCode S k) : LsStrictCode S k :=
  fun μ hR hc => lsStrict_of_cover (lsPv_range hR) (h μ hR hc)

/-- **`LsStrictCode S k → Lr.LrStrictCof` at `m*`.** -/
theorem lsStrictCof_M {k : ℕ} (h : LsStrictCode S k) : LrStrictCof S (Nc.ncL S 0) := by
  intro γ hγ
  obtain ⟨μ, hR, h1, h2, hc⟩ := lsNames_M (S := S) k γ hγ
  exact ⟨μ, hR, h1, h2, k, h μ hR hc, by rw [hc]; exact le_self_add⟩

/-- **`LsStrictCode S k → Lr.LrStrictCof` at every `L(n+1)`.** -/
theorem lsStrictCof_L {k : ℕ} (h : LsStrictCode S k) (n : ℕ) :
    LrStrictCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  intro γ hγ
  obtain ⟨μ, hR, h1, h2, hc⟩ := lsNames_L (S := S) n k γ hγ
  exact ⟨μ, hR, h1, h2, k, h μ hR hc, by rw [hc]; exact le_self_add⟩

/-- **The supply `LrSup S a ω²` at `m*` and every `L(n+1)`.** -/
theorem lsSup_named {k : ℕ} (h : LsStrictCode S k) :
    LrSup S (Nc.ncL S 0) (ω ^ 2) ∧ ∀ n : ℕ, LrSup S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ω ^ 2) :=
  ⟨lrSup_of_strict (lsStrictCof_M h), fun n => lrSup_of_strict (lsStrictCof_L h n)⟩

/-- **The supply at the family**: every Range restart `μ` with `m_μ = G_{k+1} + 1` reaches `υ_{μ+ρ_μ}`. -/
def LsSupCode (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = lsG S (k + 1) + 1 → upsilon (μ + upsilon μ) ≤ cdR S μ

/-- **`LsStrictCode S k → LsSupCode S k`**: `υ_{μ+ρ_μ} = P(η_μ + ρ_μ) ≤ H(η_μ + G_k) ≤ r(μ)`. -/
theorem lsSupCode_of_strict {k : ℕ} (h : LsStrictCode S k) : LsSupCode S k := by
  intro μ hR hc
  have hpv := lsPv_range hR
  obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
    (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
  refine Lc.lcR_of_strict (h μ hR hc) (by rw [hc]; exact le_self_add) ?_
  have hsh := Rz.rz_iota_shift hgμ (show upsilon μ ≤ Nm.Pv S (cdEta S μ) by rw [hpv])
  rw [hιμ] at hsh
  rw [← hsh, Bt.ups_iota]
  refine (Nm.Pv_mono (add_le_add le_rfl ?_)).trans le_add_self
  have h1 : upsilon μ < Om 1 := by rw [← hpv]; exact Nm.Pv_lt_Om1 S _
  exact (h1.trans (lsG_Om1 (S := S) k)).le

/-- **The supply `LrSup S a ω²` at `m*` and every `L(n+1)` from `LsSupCode S k`.** -/
theorem lsSup_named_sup {k : ℕ} (h : LsSupCode S k) :
    LrSup S (Nc.ncL S 0) (ω ^ 2) ∧ ∀ n : ℕ, LrSup S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ω ^ 2) := by
  have key : ∀ μ, CdRange S μ → cdCode S μ = lsG S (k + 1) + 1 → upsilon (μ + ω ^ 2) ≤ cdR S μ :=
    fun μ hR hc => (upsilon_normal.strictMono.monotone (add_le_add le_rfl
      ((Ordinal.le_of_dvd hR.1.1 hR.1.2).trans upsilon_normal.strictMono.le_apply))).trans (h μ hR hc)
  refine ⟨fun γ hγ => ?_, fun n γ hγ => ?_⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := lsNames_M (S := S) k γ hγ
    exact ⟨μ, hR, h1, h2, key μ hR hc⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := lsNames_L (S := S) n k γ hγ
    exact ⟨μ, hR, h1, h2, key μ hR hc⟩

/-- **The realizers at `m*` and every `L(n+1)` up to `υ_{ι(a)+ω²}`**, without a supply hypothesis. -/
theorem lsNamed_shift2 {k : ℕ} (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S) (h : LsSupCode S k) :
    (LrReal S (Nc.ncL S 0) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)) ∧
      upsilon (lrIx (Nc.ncL S 0) + ω ^ 2) ≤ Nc.ncL S 1) ∧
    ∀ n : ℕ, LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)) ∧
      upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) :=
  lrNamed_shift2 hlow hstd (lsSup_named_sup h).1 (lsSup_named_sup h).2

/-- **`Lr.lrRoad_strict` with its supply hypotheses replaced by `LsStrictCode S k`.** -/
theorem lsRoad_strict {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hk : LsStrictCode S k)
    (h0 : LrRealAbove S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)))
    (hn : ∀ n : ℕ, LrRealAbove S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lrRoad_strict hU hO hL hV hEQ htop hups (lsStrictCof_M hk) (lsStrictCof_L hk) h0 hn hP hw hmove hstd

/-- **The road from the covering `LsCoverCode S k`.** -/
theorem lsRoad_cover {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hk : LsCoverCode S k)
    (h0 : LrRealAbove S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)))
    (hn : ∀ n : ℕ, LrRealAbove S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lsRoad_strict hU hO hL hV hEQ htop hups (lsStrictCode_of_cover hk) h0 hn hP hw hmove hstd

/-- **The crossing relations at the named restarts from realizers at the uncovered targets above
`υ_{ι(a)+ω²}`.** -/
theorem lsNamed_gap2 {k : ℕ} (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S)
    (hk : LsSupCode S k)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S := by
  obtain ⟨⟨r0, b0⟩, rn⟩ := lsNamed_shift2 (S := S) hlow hstd hk
  refine ⟨?_, fun n => ?_, lrLe1_of_realCof hL (Qq.qqL_lt_succ S).le hP hw⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    exact lrLe1_of_gap hL (Pp.ppL_mono zero_le)
      (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) r0 b0 h0
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact lrLe1_of_gap hL (Pp.ppL_lt_succ n).le
      (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (rn n).1 (rn n).2 (hn n)

/-- **The road with the realizers at `m*` and `L(n+1)` asked only at the targets above `υ_{ι(a)+ω²}` that no
restart reach covers**, and the supply from `LsStrictCode S k`. -/
theorem lsRoad_gap2 {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hk : LsSupCode S k)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)))
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
  have hL' := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (lsNamed_gap2 hL' (cdLow_enum hU' hV') hstd hk h0 hn hP hw) hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Ls
