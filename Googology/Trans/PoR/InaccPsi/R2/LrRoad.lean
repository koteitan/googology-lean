import Googology.Trans.PoR.InaccPsi.R2.LrShift
import Googology.Trans.PoR.InaccPsi.R2.FpB0
import Googology.Trans.PoR.InaccPsi.R2.RzName
import Googology.Trans.PoR.InaccPsi.R2.LcCap

/-!
# The road with the realizer hypotheses asked only above the shift targets, and the supply from LC-STRICT

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `ι(u) = lrIx u` (the `υ`-index), `δ_λ = υ_{λ+ω+1}`.  `lrRoad_rz` asks
for realizers (`LrRealCof`) at `m*` and `L(n+1)` for targets cofinal in `L(1)`, `L(n+2)`.  By
`Lr.lrReal_shift0` the targets up to `υ_{ι(a)+ω+1}` are free at `a = m*, L(n+1)`; their Range restarts are
cofinal (`Rm.rmNamed_cof_iff` with `Fp.fpB0_lt_M`: `ρ_{B₀} < m*` is proved), and `a < L(ω) ≤ ν_C` on the
road.  With the supply `LrSup S a ω²` (Range restarts `μ` cofinal below `a` with `υ_{μ+ω²} ≤ r(μ)`) the
targets up to the next restart `υ_{ι(a)+ω²}` are free too (`Lr.lrReal_shift`, with `CxStdPairTop`).

* `LrRealAbove S a b c`: realizers for targets cofinal in `b`, asked only above `c`;
  `lrRealCof_of_above`, `lrAbove_of_cof`;
* `LrSup S a β` (**the supply**), `lrSup_of_cof` (`β = ω + 1` from `RmCof`, as `δ_μ ≤ r(μ)`);
* `lrSup_of_strict` (**clause (ii) from LC-STRICT**): Range restarts `μ` cofinal below `a` with
  LC-STRICT at `μ`, `k` and `m_μ ≥ G(θ_{k+1}·ω²)` give `LrSup S a ω²` (`r(μ) ≥ δ_μ + H(η_μ + G(θ_k·ω²))
  ≥ H(η_μ + ω²) = υ_{μ+ω²}`, `Rz.rz_iota_shift`, Theorem GEN `Bt.ups_iota`);
* `lrNamed_shift0`, `lrNamed_shift2`: the shift realizers at `m*` and every `L(n+1)`;
* `lrRoad_shift` (**the road with `h0`, `hn` asked only above `υ_{ι(a)+ω+1}`**, no hypothesis
  `ρ_{B₀} < m*`), `lrRoad_shift2` (**only above `υ_{ι(a)+ω²}`, given the supply**), `lrRoad_strict`
  (**the supply from LC-STRICT**); `lrRoadShift_hyp_of_rl`: every instance of `Rl.rlRoad_rz` gives one of
  `lrRoad_shift`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Rm Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv

variable {S : InaccSeq.{0}}

/-- Realizer maps for targets cofinal in `b`, asked only above `c`. -/
def LrRealAbove (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → c ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t

theorem lrAbove_of_cof {a b c : Ordinal.{0}} (h : LrRealCof S a b) : LrRealAbove S a b c :=
  fun y hay _ hyb => h y hay hyb

/-- **The targets below `c` are free** when `LrReal S a c` holds. -/
theorem lrRealCof_of_above {a b c : Ordinal.{0}} (hc : LrReal S a c) (hcb : c ≤ b)
    (h : LrRealAbove S a b c) : LrRealCof S a b := by
  intro y hay hyb
  by_cases hy : c ≤ y
  · exact h y hay hy hyb
  · exact ⟨c, not_le.1 hy, hcb, hc⟩

/-- **The supply**: Range restarts `μ` cofinal below `a` with `υ_{μ+β} ≤ r(μ)`. -/
def LrSup (S : InaccSeq.{0}) (a β : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ upsilon (μ + β) ≤ cdR S μ

theorem lrSup_of_cof {a : Ordinal.{0}} (hc : RmCof S a) : LrSup S a (ω + 1) := by
  intro γ hγ
  obtain ⟨μ, hμR, h1, h2⟩ := hc γ hγ
  exact ⟨μ, hμR, h1, h2, by rw [← add_assoc]; exact cdR_ge S μ⟩

/-- `ω² ≤ G(ζ)`. -/
theorem lr_ww_le_G (ζ : Ordinal.{0}) : ω ^ 2 ≤ Lc.lcG S ζ := by
  have h1 : (ω * ω : Ordinal.{0}) < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact ww_lt_Om1
  rw [pow_two]
  exact (h1.trans (psiS_bounds _ 1).1).le

/-- **`υ_{μ+ω²} = H(η_μ + ω²)`** for a restart `μ` of the Range. -/
theorem lr_ups_ww {μ : Ordinal.{0}} (hμR : CdRange S μ) :
    upsilon (μ + ω ^ 2) = Nm.Pv S (cdEta S μ + ω ^ 2) := by
  have hR := hμR.2.2.1
  rw [Lw.lw_L_eq S] at hR
  obtain ⟨hg, hι, -, hPv⟩ := cdEta_pv_spec hμR.1.1 hR
  have hμw : ω ^ 2 ≤ μ := by
    obtain ⟨p, hp⟩ := hμR.1.2
    have hp0 : p ≠ 0 := fun h => hμR.1.1 (by rw [hp, h, mul_zero])
    rw [hp]; exact Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hp0)
  have hω2 : ω ^ 2 ≤ Nm.Pv S (cdEta S μ) := by
    rw [hPv]; exact hμw.trans upsilon_normal.strictMono.le_apply
  have hsh := Rz.rz_iota_shift hg hω2
  rw [hι] at hsh
  rw [← hsh]
  exact Bt.ups_iota S _

/-- **Clause (ii) from LC-STRICT: the supply `LrSup S a ω²`.** -/
theorem lrSup_of_strict {a : Ordinal.{0}}
    (h : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ∃ k : ℕ,
      Lc.LcStrictAt S μ k ∧ Lc.lcG S (Lc.lcTh S (k + 1) * ω ^ 2) ≤ cdCode S μ) :
    LrSup S a (ω ^ 2) := by
  intro γ hγ
  obtain ⟨μ, hμR, h1, h2, k, hk, hcode⟩ := h γ hγ
  refine ⟨μ, hμR, h1, h2, Lc.lcR_of_strict hk hcode ?_⟩
  rw [lr_ups_ww hμR]
  exact (Nm.Pv_mono (lr_addLe (lr_ww_le_G _))).trans le_add_self

/-! ## The named restarts -/

theorem lr_idx_bound {l l1 : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : IsRestartIdx l1)
    (h : upsilon l < upsilon l1) : upsilon (l + ω ^ 2) ≤ upsilon l1 ∧
      upsilon (l + ω + 1) ≤ upsilon l1 := by
  have hm := upsilon_normal.strictMono
  have h2 : l + ω ^ 2 ≤ l1 := lr_dvd_add_le hl.2 hl1.2 (hm.lt_iff_lt.1 h)
  refine ⟨hm.monotone h2, hm.monotone ((le_of_lt ?_).trans h2)⟩
  have h3 := lr_omega_mul_add_one_lt 1
  rw [Nat.cast_one, mul_one] at h3
  rw [add_assoc]; exact lr_addL h3

theorem lr_L_lt_nu {ξ : Ordinal.{0}} (hξ : ξ < ω) (hlow : Nc.ncL S ω ≤ nuC) : Nc.ncL S ξ < nuC := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hξ
  rcases n with _ | n
  · exact (rlM_lt_L1.trans_le (Pp.ppL_mono one_lt_omega0.le)).trans_le hlow
  · exact (Pp.ppL_lt_omega n).trans_le hlow

/-- **The shift realizers at `m*` and every `L(n+1)`, up to `υ_{ι(a)+ω+1}`.** -/
theorem lrNamed_shift0 (hlow : Nc.ncL S ω ≤ nuC) :
    (LrReal S (Nc.ncL S 0) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)) ∧
      upsilon (lrIx (Nc.ncL S 0) + ω + 1) ≤ Nc.ncL S 1) ∧
    ∀ n : ℕ, LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1)) ∧
      upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨c0, cn, -⟩ := rmNamed_cof_iff.1 (Fp.fpB0_lt_M (S := S))
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    obtain ⟨l1, hl1, e1⟩ := Pp.ppL_succ_restart (S := S) 0
    have e1' : Nc.ncL S 1 = upsilon l1 := by simpa using e1
    have hν := lr_L_lt_nu (S := S) omega0_pos hlow
    rw [e] at c0 hν ⊢
    rw [lrIx_up, e1']
    refine ⟨lrReal_shift0 hl (by rw [← e]; exact Lc.lc_L_lt_Om1 _) hν c0 le_rfl,
      (lr_idx_bound hl hl1 ?_).2⟩
    rw [← e, ← e1']; exact rlM_lt_L1
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    obtain ⟨l1, hl1, e1⟩ := Pp.ppL_succ_restart (S := S) (n + 1)
    have e1' : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) = upsilon l1 := e1
    have hν : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < nuC := (Pp.ppL_lt_omega n).trans_le hlow
    have c := cn n
    have hlt := Pp.ppL_lt_succ (S := S) n
    rw [e] at c hν hlt ⊢
    rw [lrIx_up, e1']
    rw [e1'] at hlt
    refine ⟨lrReal_shift0 hl (by rw [← e]; exact Lc.lc_L_lt_Om1 _) hν c le_rfl,
      (lr_idx_bound hl hl1 hlt).2⟩

/-- **The shift realizers at `m*` and every `L(n+1)`, up to the next restart `υ_{ι(a)+ω²}`**, given the
supply and `CxStdPairTop`. -/
theorem lrNamed_shift2 (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S)
    (hS0 : LrSup S (Nc.ncL S 0) (ω ^ 2))
    (hSn : ∀ n : ℕ, LrSup S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ω ^ 2)) :
    (LrReal S (Nc.ncL S 0) (upsilon (lrIx (Nc.ncL S 0) + ω ^ 2)) ∧
      upsilon (lrIx (Nc.ncL S 0) + ω ^ 2) ≤ Nc.ncL S 1) ∧
    ∀ n : ℕ, LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2)) ∧
      upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω ^ 2) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    obtain ⟨l1, hl1, e1⟩ := Pp.ppL_succ_restart (S := S) 0
    have e1' : Nc.ncL S 1 = upsilon l1 := by simpa using e1
    have hν := lr_L_lt_nu (S := S) omega0_pos hlow
    have hLw : Nc.ncL S 0 ≤ Nc.ncL S (ω + 1) := Pp.ppL_mono zero_le
    have hS := hS0
    rw [e] at hS hν hLw ⊢
    rw [lrIx_up, e1']
    refine ⟨lrReal_shift hl (by rw [← e]; exact Lc.lc_L_lt_Om1 _) hν le_rfl le_rfl hS
      (Or.inr ⟨hstd, hLw⟩), (lr_idx_bound hl hl1 ?_).1⟩
    rw [← e, ← e1']; exact rlM_lt_L1
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    obtain ⟨l1, hl1, e1⟩ := Pp.ppL_succ_restart (S := S) (n + 1)
    have e1' : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) = upsilon l1 := e1
    have hν : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < nuC := (Pp.ppL_lt_omega n).trans_le hlow
    have hLw : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) :=
      Pp.ppL_mono ((Ordinal.natCast_lt_omega0 _).le.trans le_self_add)
    have hS := hSn n
    have hlt := Pp.ppL_lt_succ (S := S) n
    rw [e] at hS hν hlt hLw ⊢
    rw [lrIx_up, e1']
    rw [e1'] at hlt
    exact ⟨lrReal_shift hl (by rw [← e]; exact Lc.lc_L_lt_Om1 _) hν le_rfl le_rfl hS
      (Or.inr ⟨hstd, hLw⟩), (lr_idx_bound hl hl1 hlt).1⟩

/-! ## The roads -/

/-- **The road with the realizer hypotheses at `m*` and `L(n+1)` asked only above `υ_{ι(a)+ω+1}`.** -/
theorem lrRoad_shift (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : LrRealAbove S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)))
    (hn : ∀ n : ℕ, LrRealAbove S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC :=
    cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)
  obtain ⟨⟨r0, b0⟩, rn⟩ := lrNamed_shift0 (S := S) hlow
  exact lrRoad_rz hU hO hL hV hEQ htop hups (lrRealCof_of_above r0 b0 h0)
    (fun n => lrRealCof_of_above (rn n).1 (rn n).2 (hn n)) hP hw hmove hstd

/-- **The road with the realizer hypotheses at `m*` and `L(n+1)` asked only above the next restart
`υ_{ι(a)+ω²}`, given the supply.** -/
theorem lrRoad_shift2 (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hS0 : LrSup S (Nc.ncL S 0) (ω ^ 2))
    (hSn : ∀ n : ℕ, LrSup S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ω ^ 2))
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
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC :=
    cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)
  obtain ⟨⟨r0, b0⟩, rn⟩ := lrNamed_shift2 (S := S) hlow hstd hS0 hSn
  exact lrRoad_rz hU hO hL hV hEQ htop hups (lrRealCof_of_above r0 b0 h0)
    (fun n => lrRealCof_of_above (rn n).1 (rn n).2 (hn n)) hP hw hmove hstd

/-- LC-STRICT at Range restarts cofinal below `a` with large codes (the hypothesis of
`lrSup_of_strict`). -/
def LrStrictCof (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ∃ k : ℕ,
    Lc.LcStrictAt S μ k ∧ Lc.lcG S (Lc.lcTh S (k + 1) * ω ^ 2) ≤ cdCode S μ

/-- **The road with the supply from LC-STRICT.** -/
theorem lrRoad_strict (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hS0 : LrStrictCof S (Nc.ncL S 0))
    (hSn : ∀ n : ℕ, LrStrictCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
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
  lrRoad_shift2 hU hO hL hV hEQ htop hups (lrSup_of_strict hS0) (fun n => lrSup_of_strict (hSn n))
    h0 hn hP hw hmove hstd

/-- **Every instance of `Rl.rlRoad_rz` gives one of `lrRoad_shift`** (its realizer hypotheses are
weaker, and `ρ_{B₀} < m*` is not asked). -/
theorem lrRoadShift_hyp_of_rl (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    LrRealAbove S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)) ∧
      (∀ n : ℕ, LrRealAbove S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1))) ∧
      LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
  ⟨lrAbove_of_cof (lrRealCof_of_rl h0), fun n => lrAbove_of_cof (lrRealCof_of_rl (hn n)),
    lrRealCof_of_rl hw⟩

/-- `a^∞ ≤ υ_{ι(a)+ω+1}` for a `υ`-point `a = υ_λ`. -/
theorem lr_next_le {l : Ordinal.{0}} (hl : 0 < l) :
    Lc.lcNext (upsilon l) ≤ upsilon (l + ω + 1) := by
  have hm := upsilon_normal.strictMono
  refine csInf_le (OrderBot.bddBelow _) ⟨hm ?_, upsPt_upsilon (lt_of_lt_of_le hl ?_)⟩
  · exact lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add
  · exact le_self_add.trans le_self_add

/-- **`Lc.RlRealHi` gives `LrRealAbove`** above any `c ≥ a^∞`. -/
theorem lrAbove_of_hi {a b c : Ordinal.{0}} (hc : Lc.lcNext a ≤ c) (h : Lc.RlRealHi S a b) :
    LrRealAbove S a b c := fun y hay hcy hyb => by
  obtain ⟨t, h1, h2, h3⟩ := h y hay (hc.trans hcy) hyb
  exact ⟨t, h1, h2, lrReal_of_rl h3⟩

/-- **Every instance of `Lc.lcRoad_rz` gives one of `lrRoad_shift`.** -/
theorem lrRoadShift_hyp_of_lc (h0 : Lc.RlRealHi S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, Lc.RlRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    LrRealAbove S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)) ∧
      (∀ n : ℕ, LrRealAbove S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1))) ∧
      LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) := by
  refine ⟨?_, fun n => ?_, lrRealCof_of_rl hw⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    have h := h0
    rw [e] at h ⊢
    rw [lrIx_up]
    exact lrAbove_of_hi (lr_next_le (pos_iff_ne_zero.2 hl.1)) h
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have h := hn n
    rw [e] at h ⊢
    rw [lrIx_up]
    exact lrAbove_of_hi (lr_next_le (pos_iff_ne_zero.2 hl.1)) h

end Googology.Trans.PoR.InaccPsi.R2.Lr
