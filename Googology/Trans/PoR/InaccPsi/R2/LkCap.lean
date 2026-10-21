import Googology.Trans.PoR.InaccPsi.R2.LvGRd
import Googology.Trans.PoR.InaccPsi.R2.FpCap

/-!
# The cap of the value at the `υ`-fixed points below `Λ⁺(lvgSys n)`, and the road with UPPER, LOWER and CapV asked
only at the range restarts `λ ≥ Λ⁺(lvgSys n)`

* `lkCapV_fix` (**generic**): for a term system `X` with the top package, at a `υ`-fixed restart `F < Λ⁺(X)` of the
  range where ENUM-REACH holds, `r(F) = δ_F + O_X(F)`, `O_X(F) ≤ top(F) < δ_F`, so
  `r(F) < υ_{F+ω+2} = P(η_F + ω + 2) ≤ P(η_F + ω^{e(η_F)})` (the argument of `Fp.fpCapV_fix` for any `X`);
* `lkR_eq_lvg` (**`r(λ) = δ_λ + O_n(λ)` at every range restart below `Λ⁺(lvgSys n)`**);
* `lkCapV_fix_lvg` (**CapV at every `υ`-fixed range restart below `Λ⁺(lvgSys n)`**, with `lvgEnum`), `lkCapV_lvg`
  (**CapV at every range restart below `Λ⁺(lvgSys n)`**, with `lvg_capV` off the fixed points);
* `lkRoadPh` (**the road with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lvgSys n)`**, plus (CL),
  EQ, TCrest, (EMB₂)).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

/-- **`r(λ) = δ_λ + O_X(λ)`** at a restart of the range below `Λ⁺(X)` with ENUM-REACH. -/
theorem lkR_eq {X : XtSys} (hP : XtTopPkg X) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 X)
    (hE : CdUpper S l ∧ CdLower S l) : cdR S l = cdDelta l + xtOrec X l :=
  reach_unique (cdExact_iff.1 hE) (xtReach1 hP hr.1 hl)

/-- **CapV at a `υ`-fixed restart of the range below `Λ⁺(X)` with ENUM-REACH**, for any term system `X` with the top
package. -/
theorem lkCapV_fix {X : XtSys} (hP : XtTopPkg X) {F : Ordinal.{0}} (hr : CdRange S F) (hl : F < xtB1 X)
    (hfix : upsilon F = F) (hE : CdUpper S F ∧ CdLower S F) : CdCapV S F := by
  have hX := cp_name_L hr.2.2.1
  have hF1 : F < Om1 := hl.trans (xtB1_lt_Om1 hP)
  have hR := lkR_eq hP hr hl hE
  have hOδ : xtOrec X F < cdDelta F :=
    (xtOrec_le_top (X := X) hr.1 hF1).trans_lt (X.top_lt F hr.1 hF1)
  obtain ⟨hg', hι', -, hpv'⟩ := cdEta_pv_spec (S := S) hr.1.1 hX
  obtain ⟨-, hp, hww⟩ := cp_fix_facts hr.1 hfix
  have hω : ω < F := lt_of_le_of_lt (le_mul_left _ omega0_pos) hww
  have h1 : (1 : Ordinal.{0}) < F := one_lt_omega0.trans hω
  have hw2F : ω + 1 + 1 < F := hp (hp hω h1) h1
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S F) := by rw [hpv', hfix]; exact hw2F
  have hPe : Pv S (cdEta S F + (ω + 1 + 1)) = upsilon (F + ω + 1 + 1) := by
    rw [Fx.fx_Pv_eq, cpIota_add hg' hw2, hι']; simp only [add_assoc]
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S F) :=
    (hw2F.le.trans (Fx.fxExp_fix hr.1 hfix hX)).trans (right_le_opow _ one_lt_omega0)
  unfold CdCapV cdCapB
  rw [hR]
  calc cdDelta F + xtOrec X F < upsilon (F + ω + 1 + 1) := cp_delta_add_lt hOδ
    _ = Pv S (cdEta S F + (ω + 1 + 1)) := hPe.symm
    _ ≤ Pv S (cdEta S F + ω ^ cdExp (cdEta S F)) := Pv_mono (add_le_add le_rfl hle)

/-- **`r(λ) = δ_λ + O_n(λ)`** at every restart of the range below `Λ⁺(lvgSys n)`. -/
theorem lkR_eq_lvg (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lvgSys n)) :
    cdR S l = cdDelta l + xtOrec (lvgSys n) l :=
  lkR_eq (lvgSys_topPkg n) hr hl (lvgEnum n hr hl)

/-- **CapV at every `υ`-fixed restart of the range below `Λ⁺(lvgSys n)`.** -/
theorem lkCapV_fix_lvg (n : ℕ) {F : Ordinal.{0}} (hr : CdRange S F) (hl : F < xtB1 (lvgSys n))
    (hfix : upsilon F = F) : CdCapV S F :=
  lkCapV_fix (lvgSys_topPkg n) hr hl hfix (lvgEnum n hr hl)

/-- **CapV at every restart of the range below `Λ⁺(lvgSys n)`.** -/
theorem lkCapV_lvg (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lvgSys n)) : CdCapV S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lvg_capV n hr hl hnf
  · exact lkCapV_fix_lvg n hr hl hfx.symm

/-- **The road with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lvgSys n)`.** -/
theorem lkRoadPh (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → xtB1 (lvgSys n) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine lvgRoadPh n hU hL (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases lt_or_ge l (xtB1 (lvgSys n)) with h | h
  · exact lkCapV_lvg n hr h
  · exact hV l hr hlω h

end Googology.Trans.PoR.InaccPsi.R2.Lk
