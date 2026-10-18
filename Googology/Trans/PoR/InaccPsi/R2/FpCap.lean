import Googology.Trans.PoR.InaccPsi.R2.FpLoc

/-!
# The cap of the value at the `υ`-fixed points below `Λ⁺(lnSw)`, and the road with every range hypothesis above
`Λ⁺(lnSw) = ι(φ(ω+1, Ω₁+1)·ω)`

* `fpR_eq` (**`r(λ) = δ_λ + O(λ)` at every restart of the range below `Λ⁺(lnSw)`**: ENUM-REACH `Fp.fpEnum_lnSw` and
  the exact reach `Lt.lnSw_reach`);
* `fpCapV_fix` (**CapV at every `υ`-fixed point of the range below `Λ⁺(lnSw)`**: `O(F) ≤ top(F) < δ_F`, so
  `r(F) < υ_{F+ω+2} = P(η_F + ω + 2) ≤ P(η_F + ω^{e(η_F)})`, as `Fx.fxIso_capV`), `fpCapV` (**CapV at every restart
  of the range below `Λ⁺(lnSw)`**, with `Lt.lnSw_capV` off the fixed points);
* `fpRoad4` (**the road with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lnSw)`**, plus (CL), EQ,
  TCrest, (EMB2)), `fpRoad4_loc` (the same with `Λ⁺(lnSw)` written as `ι(φ(ω+1, Ω₁+1)·ω)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

/-- **`r(λ) = δ_λ + O(λ)`** at every restart of the range below `Λ⁺(lnSw)`. -/
theorem fpR_eq {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) :
    cdR S l = cdDelta l + xtOrec lnSw l :=
  reach_unique (cdExact_iff.1 (fpEnum_lnSw hr hl)) (lnSw_reach hr.1 hl)

/-- **CapV at every `υ`-fixed point of the range below `Λ⁺(lnSw)`.** -/
theorem fpCapV_fix {F : Ordinal.{0}} (hr : CdRange S F) (hl : F < xtB1 lnSw) (hfix : upsilon F = F) :
    CdCapV S F := by
  have hX := cp_name_L hr.2.2.1
  have hF1 : F < Om1 := hl.trans (xtB1_lt_Om1 lnSw_topPkg)
  have hR := fpR_eq hr hl
  have hOδ : xtOrec lnSw F < cdDelta F :=
    (xtOrec_le_top (X := lnSw) hr.1 hF1).trans_lt (lnSw.top_lt F hr.1 hF1)
  obtain ⟨hg', hι', -, hpv'⟩ := cdEta_pv_spec (S := S) hr.1.1 hX
  obtain ⟨-, hp, hww⟩ := cp_fix_facts hr.1 hfix
  have hω : ω < F := lt_of_le_of_lt (le_mul_left _ omega0_pos) hww
  have h1 : (1 : Ordinal.{0}) < F := one_lt_omega0.trans hω
  have hw2F : ω + 1 + 1 < F := hp (hp hω h1) h1
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S F) := by rw [hpv', hfix]; exact hw2F
  have hP : Pv S (cdEta S F + (ω + 1 + 1)) = upsilon (F + ω + 1 + 1) := by
    rw [Fx.fx_Pv_eq, cpIota_add hg' hw2, hι']; simp only [add_assoc]
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S F) :=
    (hw2F.le.trans (Fx.fxExp_fix hr.1 hfix hX)).trans (right_le_opow _ one_lt_omega0)
  unfold CdCapV cdCapB
  rw [hR]
  calc cdDelta F + xtOrec lnSw F < upsilon (F + ω + 1 + 1) := cp_delta_add_lt hOδ
    _ = Pv S (cdEta S F + (ω + 1 + 1)) := hP.symm
    _ ≤ Pv S (cdEta S F + ω ^ cdExp (cdEta S F)) := Pv_mono (add_le_add le_rfl hle)

/-- **CapV at every restart of the range below `Λ⁺(lnSw)`.** -/
theorem fpCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) : CdCapV S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lnSw_capV hr hl hnf
  · exact fpCapV_fix hr hl hfx.symm

/-- **The road with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lnSw)`.** -/
theorem fpRoad4 (hU : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → xtB1 lnSw ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine fpLnSwRoad3 hU hL (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases lt_or_ge l (xtB1 lnSw) with h | h
  · exact fpCapV hr h
  · exact hV l hr hlω h

/-- **`fpRoad4` with `Λ⁺(lnSw) = ι(φ(ω+1, Ω₁+1)·ω)`.** -/
theorem fpRoad4_loc (hU : ∀ l, CdRange S l → iota S (fpPc * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (fpPc * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (fpPc * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have e := (fpLoc_lnSw' (S := S)).1
  exact fpRoad4 (fun l hr h => hU l hr (e ▸ h)) (fun l hr h => hL l hr (e ▸ h))
    (fun l hr hlω h => hV l hr hlω (e ▸ h)) hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Fp
