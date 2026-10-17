import Googology.Trans.PoR.InaccPsi.R2.XtFam
import Googology.Trans.PoR.InaccPsi.R2.XtChain

/-!
# Below `Λ_ω = sup_n Λ_n⁺`: BLK^O, ENUM-REACH off the fixed points, the values at `Λ_n⁺`, and the road

The layers `xtLayN n` (top `B(x)·x^n`, `R2.XtLay`) with `Λ_n⁺ = xtLamN n` and `O_n = xtOrec (xtLayN n).sys`
(`R2.XtChain`) form an increasing family of offset specifications (`xtFamW : XtFam`, `R2.XtFam`); `Λ_ω = xtFamW.famSup`.
So every theorem of `R2.XtFam` holds with `Λ = Λ_ω`: BLK^O below `υ_{Λ_ω}` (`xtFamW.famBlk`), CORE-C, `υ_{Λ_ω} ≤ ρ_L`,
UPPER and LOWER at every non-fixed restart of the range below `Λ_ω` (`xtFamW.famInit`), the caps, and the roads with
the rest asked only outside `Λ_ω`.  Here in addition:

* `xtLayN_nonfix`, `xtFamW`, `xtFamW_sup` (`Λ_ω = sup_n Λ_n⁺`), `xtFamW_iso` (`O_n(F) = F` at isolated fixed points);
* `xtW_atB1` (**ENUM-REACH at `Λ_n⁺`: UPPER iff `B(ρ)·ρ^n + 1 ≤ Θ(m)`, LOWER iff `Θ(m) ≤ B(ρ)·ρ^n + 1`**),
  `xtW_cpB1` (the case `n = 0`, `Λ_0⁺ = cpB1`: `B(ρ) + 1`);
* `xtW_of_cp` (**the hypotheses of `xtFamW.famRoad3` follow from those of `cpRoad3`**).

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

theorem xtLamN_lt_Om1 (n : ℕ) : xtLamN n < Om1 := xtB1_lt_Om1 (xtLayN n).topPkg

/-- `O_n(μ) = -1 + e(μ)` off the fixed points of `υ` below `Λ_n⁺`. -/
theorem xtLayN_nonfix (n : ℕ) : XtNonfix (xtOrec (xtLayN n).sys) (xtLamN n) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtLamN_lt_Om1 n))

/-- **The family of the layers `xtLayN n`**: bounds `Λ_n⁺`, offsets `O_n`. -/
noncomputable def xtFamW : XtFam where
  bd := xtLamN
  off := fun n => xtOrec (xtLayN n).sys
  spec := xtLamN_spec
  mono := xtLamN_lt
  nonfix := xtLayN_nonfix

/-- `Λ_ω = sup_n Λ_n⁺`. -/
theorem xtFamW_sup : xtFamW.famSup = ⨆ n : ℕ, xtLamN n := rfl

/-- At an isolated fixed point the offset of every layer is `F`. -/
theorem xtFamW_iso : xtFamW.famIsoOff := fun n _ hl hln hfix hiso =>
  xtIso hl hfix (hln.trans (xtLamN_lt_Om1 n)) hiso (X := (xtLayN n).sys)

/-- **ENUM-REACH at `Λ_n⁺`**: UPPER iff `B(ρ)·ρ^n + 1 ≤ Θ(m)`, LOWER iff `Θ(m) ≤ B(ρ)·ρ^n + 1`. -/
theorem xtW_atB1 (n : ℕ) :
    (CdUpper S (xtLamN n) ↔ VzB (upsilon (xtLamN n)) * upsilon (xtLamN n) ^ (n : Ordinal.{0}) + 1 ≤
        cdTheta S (xtLamN n) (cdCode S (xtLamN n))) ∧
      (CdLower S (xtLamN n) ↔ cdTheta S (xtLamN n) (cdCode S (xtLamN n)) ≤
        VzB (upsilon (xtLamN n)) * upsilon (xtLamN n) ^ (n : Ordinal.{0}) + 1) := by
  obtain ⟨hU, hL, -⟩ := xtFamW.famIff (S := S) (n + 1) (xtLamN_ri n) (xtLamN_lt n)
  have e : xtFamW.off (n + 1) (xtLamN n) = _ := xtLayN_atB1 n
  rw [e] at hU hL
  exact ⟨hU, hL⟩

/-- **ENUM-REACH at `Λ_B⁺ = cpB1`**: UPPER iff `B(ρ) + 1 ≤ Θ(m)`, LOWER iff `Θ(m) ≤ B(ρ) + 1`. -/
theorem xtW_cpB1 :
    (CdUpper S Cp.cpB1 ↔ VzB (upsilon Cp.cpB1) + 1 ≤ cdTheta S Cp.cpB1 (cdCode S Cp.cpB1)) ∧
      (CdLower S Cp.cpB1 ↔ cdTheta S Cp.cpB1 (cdCode S Cp.cpB1) ≤ VzB (upsilon Cp.cpB1) + 1) := by
  have h := xtW_atB1 (S := S) 0
  rw [xtLamN_zero] at h
  simpa using h

/-- **The hypotheses of `xtFamW.famRoad3` follow from those of `cpRoad3`.** -/
theorem xtW_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtFamW.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → xtFamW.famSup ≤ l → CdLower S l) ∧ xtFamW.famTHfix S := by
  have hc0 : Cp.cpB1 ≤ xtFamW.famSup := by
    have := xtFamW.famBd_lt 0
    exact (show xtLamN 0 < xtFamW.famSup from this).le.trans_eq' xtLamN_zero.symm
  refine xtFamW.famOf_cp hc0 (fun n μ hμ h1 _ => ?_) hU hL hT
  have h0 : μ < xtLamN 0 := xtLamN_zero ▸ h1
  show xtOrec (xtLayN n).sys μ = VzOrec μ
  rw [xtLayN_eq (Nat.zero_le n) hμ h0]
  show xtOrec vzSys μ = VzOrec μ
  rw [xtVz_orec]

end Googology.Trans.PoR.InaccPsi.R2.Xt
