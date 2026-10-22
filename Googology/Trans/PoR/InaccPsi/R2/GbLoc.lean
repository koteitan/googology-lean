import Googology.Trans.PoR.InaccPsi.R2.GbFr
import Googology.Trans.PoR.InaccPsi.R2.GbLd
import Googology.Trans.PoR.InaccPsi.R2.GbLim

/-!
# Where the ladder over a base with a code of `R2.GbAt` ends, and the ordinal-offset limit layer as a code

`R2.GaLoc` with the codes `GxCl Z gbAt` and the bound `Γ_{Ω₁+ω·2}`: for a base `K` with `GbPoly K c`, `E_K = Θ(c)`,
`c = ω^c`, `Ω₁ ≤ c`, `ε_{x+1} < E_K(x)`, `c` a code over every strongly critical base:

* `gb_cQs_eq_H` (**`cQs c = gbH (k+1)` for `gbH k ≤ c < gbH (k+1)`**), `gb_cQ_le_V`;
* `gbB1_loc` (**`Λ⁺(lpSys B n) = ι(cQ c n·ω)`, `ρ` of it `= P(…) < L(0)`**), `gbT_fix` (**the notation hypothesis
  `Θ_F(m_F) = O_n(F)` at every fixed point of the range below `Λ⁺(lpSys B n)`**: `gbUniTh`), `gbLEnum` (**ENUM-REACH
  at every restart of the range below `Λ^B`, fixed points included**), `gbLCapV` (**CapV there**), `gbFam_loc`
  (**`Λ^B = ι(cQs c)`, `υ_{Λ^B} = P(cQs c) < L(0)`**), `gbBaseRoad`;
* `gq_sup` (**`gq η x = sup_n gP n x`** under `GqLimH B η`), `gbLim_top` (**`gq η y = Θ_y(cQs c)`**), `gbLim_poly`
  (**`GbPoly (gqUSys B η H) (cQs c)`**).

No new axiom.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Googology.Trans.PoR.InaccPsi.R2.Ga
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp

/-! ## The ladder codes below `Γ_{Ω₁+ω·2}` -/

/-- **`cQs c = gbH (k+1)`** for `gbH k ≤ c < gbH (k+1)`. -/
theorem gb_cQs_eq_H (S : InaccSeq.{0}) {c : Ordinal.{0}} {k : ℕ} (h1 : gbH k ≤ c) (h2 : c < gbH (k + 1)) :
    cQs c = gbH (k + 1) :=
  le_antisymm (cQs_min (gbH_SC S _) h2) (gbH_succ_le (cQs_SC c) (h1.trans_lt (cQ_lt_cQs c 0)))

theorem gb_cQ_le_V (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gbAt c) (n : ℕ) : cQ c n ≤ gbV :=
  (gbCl_lt_V S le_rfl (gbcQ_cl hc ph_SC_Om1 n)).le

/-! ## The frontiers of the stages, the notation hypothesis, ENUM-REACH and CapV -/

section Loc

variable (S : InaccSeq.{0}) {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gbAt c) (hcO : Om 1 ≤ c)
  (hcE : ω ^ c = c) (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = gxTh y gbAt c) (hKP : GbPoly B.K.sys c)
  (htopE : ∀ x, InE x → x < Om1 → eN x < B.K.E x)
include hc hcO hcE hKE hKP htopE

/-- **`Λ⁺(lpSys B n) = ι(cQ c n·ω)`, `ρ` of it `= P(cQ c n·ω) < L(0)`.** -/
theorem gbB1_loc (n : ℕ) : xtB1 (lpSys B n) = iota S (cQ c n * ω) ∧
    upsilon (xtB1 (lpSys B n)) = Pv S (cQ c n * ω) ∧ Pv S (cQ c n * ω) < Nc.ncL S 0 := by
  have h := gbB1_eq (S := S) (gb_cQ_le_V S hc n) (gbPoly S hc hcO hKE hKP n)
    (fun y hy hy1 => gbTop_th S hc hKE n y hy hy1) (fun _ hZ => gbcQ_cl hc hZ n) (cQ_Om1_le hcO n)
    (fun x hx hx1 => (htopE x hx hx1).trans_le (E_le_gP B hx hx1 n)) (lpSys_topPkg n)
  rwa [cQ_eps hcE n] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lpSys B n)`.** -/
theorem gbT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lpSys B n))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l := by
  have hlt : l < iota S (ω ^ cQ c n * ω) := by
    rw [cQ_eps hcE n, ← (gbB1_loc S hc hcO hcE hKE hKP htopE n).1]; exact hlB
  exact gbUniTh (gb_cQ_le_V S hc n) (gbPoly S hc hcO hKE hKP n) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `Λ^B = sup_n Λ⁺(lpSys B n)`**, fixed points included. -/
theorem gbLEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdUpper S l ∧ CdLower S l :=
  lpFamEnum B (fun n _ hr hln hfix => gbT_fix S hc hcO hcE hKE hKP htopE n hr hln hfix) hr hl

/-- **CapV at every restart of the range below `Λ^B`**, fixed points included. -/
theorem gbLCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdCapV S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact (lpFam B).famCapV hr hl hnf
  · obtain ⟨n, hn⟩ := (lpFam B).famLt hl
    exact Lk.lkCapV_fix (lpSys_topPkg n) hr hn hfx.symm (gbLEnum S hc hcO hcE hKE hKP htopE hr hl)

/-- **The successor road over the base**: UPPER, LOWER and CapV asked only at `λ ≥ Λ^B`, (CL), EQ, TCrest,
(EMB₂). -/
theorem gbBaseRoad (hU : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → (lpFam B).famSup ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine lpFamRoad3 B hU hL (fun n _ hr hln hfix => gbT_fix S hc hcO hcE hKE hKP htopE n hr hln hfix)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (lpFam B).famSup l with h | h
  · exact hV l hr hlω h
  · exact gbLCapV S hc hcO hcE hKE hKP htopE hr h

/-- **`Λ^B = ι(cQs c)`, `υ_{Λ^B} = P(cQs c) < L(0)`**: the ladder over the base ends at the least strongly critical
ordinal above `c`. -/
theorem gbFam_loc : (lpFam B).famSup = iota S (cQs c) ∧
    upsilon (lpFam B).famSup = Pv S (cQs c) ∧ Pv S (cQs c) < Nc.ncL S 0 := by
  have hSC := cQs_SC c
  have hlim : IsSuccLimit (cQs c) := hSC.isSuccLimit
  have hEs : ω ^ cQs c = cQs c := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ n : ℕ, cQ c n * ω < cQs c := fun n =>
    InE.mul_lt hEs (cQ_lt_cQs c n) (omega0_lt_inE hEs)
  have heq : (lpFam B).famSup = iota S (cQs c) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lpLam B n ≤ _
      rw [lpLam, (gbB1_loc S hc hcO hcE hKE hKP htopE n).1]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      obtain ⟨n, hn⟩ := cQs_lt e.2
      have h1 : e.1 < cQ c n * ω := hn.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (cQ c n * ω) := iota_mono _ _ h1.le
        _ = lpLam B n := (gbB1_loc S hc hcO hcE hKE hKP htopE n).1.symm
        _ ≤ (lpFam B).famSup := ((lpFam B).famBd_lt n).le
  have hups : upsilon (lpFam B).famSup = Pv S (cQs c) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ga_Pv_lt_L0 S ?_⟩
  exact (Ordinal.iSup_le fun n => gb_cQ_le_V S hc n).trans (gbV_lt_Om2 S).le

end Loc

/-! ## The limit layer with an ordinal offset as a code -/

/-- **`gq η x = sup_n gP n x`** under `GqLimH B η`. -/
theorem gq_sup {B : LpB} {η : Ordinal.{0}} (H : GqLimH B η) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    gq η x = ⨆ n, gP B n x :=
  le_antisymm (le_of_forall_lt fun v hv => by
      obtain ⟨n, hn⟩ := gq_lt_iff H hx hx1 v hv
      exact hn.trans_le (Ordinal.le_iSup (fun n => gP B n x) n))
    (Ordinal.iSup_le fun n => (gq_gP_lt H hx hx1 n).le)

section Lim

variable (S : InaccSeq.{0}) {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gbAt c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = gxTh y gbAt c) (hKP : GbPoly B.K.sys c) {η : Ordinal.{0}}
  (H : GqLimH B η)
include S hc hcO hKE H

omit hcO hKP in
/-- **The limit top reads the code `cQs c`**: `gq η y = Θ_y(cQs c)`. -/
theorem gbLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : gq η y = gxTh y gbAt (cQs c) := by
  rw [gq_sup H (gg_SC_eps hy) (lp_y1 hy1), cQs, gxTh_iSup]
  exact iSup_congr fun n => gbTop_th S hc hKE n y hy hy1

include hKP in
/-- **The limit layer has terms for every code below `cQs c`.** -/
theorem gbLim_poly : GbPoly (gqUSys B η H) (cQs c) := by
  intro Z d hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gbPoly S hc hcO hKE hKP n Z d hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Gb
