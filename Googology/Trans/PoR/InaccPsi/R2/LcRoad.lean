import Googology.Trans.PoR.InaccPsi.R2.LcBlk

/-!
# The road with the realizer hypotheses at `m*` and `L(n+1)` reduced to the targets above the first block

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `a^∞ = lcNext a`, `B₀ = Cd.cdB0`.  `Rl.rlRoad_rz` asks for
`RlRealCof S m* L(1)` and `RlRealCof S L(n+1) L(n+2)`: realizer maps for targets cofinal in `L(1)`,
`L(n+2)`.  By `Lc.lcReal_blk` the targets up to `a^∞` are free once Range restarts are cofinal below `a`
and `a^∞ ≤ ν_C`; on the road `L(ω) ≤ ν_C` (`Cd.cdLow_enum`), and `ρ_{B₀} < m*` gives the cofinality
(`Rm.rmNamed_cof_iff`).

* `RlRealHi S a b`: realizer maps for targets cofinal in `b`, asked only above `a^∞`;
* `lcRealCof_of_hi`, `lcRealCof_iff_hi` (**`RlRealCof S a b ↔ RlRealHi S a b`** for a countable
  `υ`-point `a` with `RmCof S a`, `a^∞ ≤ ν_C`, `a^∞ ≤ b`);
* `lcRoad_rz` (**`Rl.rlRoad_rz` with `h0`, `hn` replaced by `ρ_{B₀} < m*` and the targets above the
  first block**); its new hypotheses follow from the old ones (`lcRoad_hyp_of_old`), so it is a
  strengthening of `Rl.rlRoad_rz`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Rm Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv

variable {S : InaccSeq.{0}}

/-- Realizer maps for targets cofinal in `b`, asked only above `a^∞`. -/
def RlRealHi (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → lcNext a ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ RlReal S a t

theorem lcHi_of_cof {a b : Ordinal.{0}} (h : RlRealCof S a b) : RlRealHi S a b :=
  fun y hay _ hyb => h y hay hyb

/-- **The targets below `a^∞` are free.** -/
theorem lcRealCof_of_hi {a b : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1) (hc : RmCof S a)
    (hν : lcNext a ≤ nuC) (hb : lcNext a ≤ b) (h : RlRealHi S a b) : RlRealCof S a b := by
  intro y hay hyb
  by_cases hy : lcNext a ≤ y
  · exact h y hay hy hyb
  · exact ⟨lcNext a, not_le.1 hy, hb, lcReal_blk ha ha1 hc (lcNext_spec ha ha1) le_rfl hν⟩

theorem lcRealCof_iff_hi {a b : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1) (hc : RmCof S a)
    (hν : lcNext a ≤ nuC) (hb : lcNext a ≤ b) : RlRealCof S a b ↔ RlRealHi S a b :=
  ⟨lcHi_of_cof, lcRealCof_of_hi ha ha1 hc hν hb⟩

/-- **The new hypotheses follow from the old ones** (`Rm.rmNamed_need`). -/
theorem lcRoad_hyp_of_old (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    upsilon cdB0 < Nc.ncL S 0 ∧ RlRealHi S (Nc.ncL S 0) (Nc.ncL S 1) ∧
      ∀ n : ℕ, RlRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :=
  ⟨(rmNamed_need h0 hn hw).2.2.2, lcHi_of_cof h0, fun n => lcHi_of_cof (hn n)⟩

/-- **The reduced road (`Rl.rlRoad_rz`) with the realizer hypotheses at `m*` and `L(n+1)` asked only for
the targets above the first block**, and `ρ_{B₀} < m*`. -/
theorem lcRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hB : upsilon cdB0 < Nc.ncL S 0)
    (h0 : RlRealHi S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC :=
    cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)
  obtain ⟨c0, cn, -⟩ := rmNamed_cof_iff.1 hB
  obtain ⟨u0, un⟩ := lc_named_ups (S := S)
  obtain ⟨x0, xn⟩ := lc_named_next (S := S)
  have h0' : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1) :=
    lcRealCof_of_hi u0 (lc_L_lt_Om1 0) c0 (x0.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) x0 h0
  have hn' : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) := fun n =>
    lcRealCof_of_hi (un n) (lc_L_lt_Om1 _) (cn n)
      ((xn n).trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (xn n) (hn n)
  exact rlRoad_rz hU hO hL hV hEQ htop hups h0' hn' hP hw hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Lc
