import Googology.Trans.PoR.InaccPsi.R2.GaFr
import Googology.Trans.PoR.InaccPsi.R2.GaLad
import Googology.Trans.PoR.InaccPsi.R2.LkCap

/-!
# Where the ladder over a base with any code `c` ends, and the limit layer as a code

For a base `K` with terms for the codes below `c` (`GaPoly K c`), top `E_K = Θ(c)`, `c = ω^c`, `Ω₁ ≤ c`, `ε_{x+1} <
E_K(x)` (`c` may be strongly critical; the codes `GxCl Z gaAt` of `R2.GaCl`):

* `gxTh_iSup` (**the reading is continuous**: `Θ_y(sup_n f(n)) = sup_n Θ_y(f(n))`), `ga_gk_sup` (**`gk k x = sup_n gP n
  x`** under `LpLimH B k`), `cQs_eq_G` (**`cQs c = gaG (k+1)` for `gaG k ≤ c < gaG (k+1)`**), `cQ_le_W`;
* `gaB1_loc` (**`Λ⁺(lpSys B n) = ι(cQ c n·ω)`, `ρ` of it `= P(…) < L(0)`**), `gaT_fix` (**the notation hypothesis
  `Θ_F(m_F) = O_n(F)` at every fixed point of the range below `Λ⁺(lpSys B n)`**: THEOREM UNI `gaUniTh`), `gaEnum`
  (**ENUM-REACH at every restart of the range below `Λ^B`, fixed points included**), `gaCapV` (**CapV at every restart
  of the range below `Λ^B`**), `gaFam_loc` (**`Λ^B = ι(cQs c)`, `υ_{Λ^B} = P(cQs c) < L(0)`**), `gaBaseRoad`;
* `gaLim` (**the limit layer is a code**: under `LpLimH B k`, `gk k y = Θ_y(cQs c)` and `GaPoly (lpUSys B k H)
  (cQs c)`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp

/-! ## Continuity of the reading, the limit top as a supremum -/

/-- **The reading is continuous**: `Θ_y(sup_n f(n)) = sup_n Θ_y(f(n))`. -/
theorem gxTh_iSup {y : Ordinal.{0}} {At : Set Ordinal.{0}} (f : ℕ → Ordinal.{0}) :
    gxTh y At (⨆ n, f n) = ⨆ n, gxTh y At (f n) := by
  classical
  refine le_antisymm ?_ (Ordinal.iSup_le fun n => gxTh_mono (Ordinal.le_iSup f n))
  unfold gxTh
  rw [cdOtp_eq]
  refine ciSup_le' fun e => ?_
  split_ifs with he
  · obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.1 e.2
    exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem he hn)).trans
      (Ordinal.le_iSup (fun n => cdOtp (gxSet y At) (f n)) n)
  · exact zero_le

/-- **`gk k x = sup_n gP n x`** under `LpLimH B k`. -/
theorem ga_gk_sup {B : LpB} {k : ℕ} (H : LpLimH B k) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    gk k x = ⨆ n, gP B n x :=
  le_antisymm (le_of_forall_lt fun v hv => by
      obtain ⟨n, hn⟩ := lp_lt_gk_iff H hx hx1 v hv
      exact hn.trans_le (Ordinal.le_iSup (fun n => gP B n x) n))
    (Ordinal.iSup_le fun n => (lp_gP_lt_gk H hx hx1 n).le)

/-- **`cQs c = gaG (k+1)`** for `gaG k ≤ c < gaG (k+1)`. -/
theorem cQs_eq_G (S : InaccSeq.{0}) {c : Ordinal.{0}} {k : ℕ} (h1 : gaG k ≤ c) (h2 : c < gaG (k + 1)) :
    cQs c = gaG (k + 1) :=
  le_antisymm (cQs_min (gaG_SC S _) h2) (gaG_succ_le (cQs_SC c) (h1.trans_lt (cQ_lt_cQs c 0)))

theorem cQ_le_W (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gaAt c) (n : ℕ) : cQ c n ≤ gaW :=
  (gaCl_lt_W S le_rfl (cQ_cl hc ph_SC_Om1 n)).le

theorem ga_Om2_good (S : InaccSeq.{0}) : Bt.Good S (Om (1 + 1)) := by
  have := Ls.lsOmNat_mem (S := S) (ConjT.Aη S (Om (1 + 1)) + 1) (S.psi (ConjT.Aη S (Om (1 + 1))) (Om 1)) 2
  have e : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
  rw [e] at this
  exact this

/-- `P(η) < L(0)` for every `η ≤ Ω₂`. -/
theorem ga_Pv_lt_L0 (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η ≤ Om (1 + 1)) : Pv S η < Nc.ncL S 0 := by
  have hlt : iota S (Om (1 + 1)) < iota S (Om ω) := cd_iota_lt_of_good (ga_Om2_good S) ph_Om2_lt_Omw
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  rw [show Pv S η = upsilon (iota S η) from (ups_iota S η).symm, hL0]
  exact upsilon_normal.strictMono ((iota_mono _ _ hη).trans_lt hlt)

/-! ## The frontiers of the stages, the notation hypothesis, ENUM-REACH and CapV -/

section Loc

variable (S : InaccSeq.{0}) {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gaAt c) (hcO : Om 1 ≤ c)
  (hcE : ω ^ c = c) (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = gxTh y gaAt c) (hKP : GaPoly B.K.sys c)
  (htopE : ∀ x, InE x → x < Om1 → eN x < B.K.E x)
include hc hcO hcE hKE hKP htopE

/-- **`Λ⁺(lpSys B n) = ι(cQ c n·ω)`, `ρ` of it `= P(cQ c n·ω) < L(0)`.** -/
theorem gaB1_loc (n : ℕ) : xtB1 (lpSys B n) = iota S (cQ c n * ω) ∧
    upsilon (xtB1 (lpSys B n)) = Pv S (cQ c n * ω) ∧ Pv S (cQ c n * ω) < Nc.ncL S 0 := by
  have h := gaB1_eq (S := S) (cQ_le_W S hc n) (gaPoly S hc hcO hKE hKP n)
    (fun y hy hy1 => gaTop_th S hc hKE n y hy hy1) (fun _ hZ => cQ_cl hc hZ n) (cQ_Om1_le hcO n)
    (fun x hx hx1 => (htopE x hx hx1).trans_le (E_le_gP B hx hx1 n)) (lpSys_topPkg n)
  rwa [cQ_eps hcE n] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lpSys B n)`.** -/
theorem gaT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lpSys B n))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l := by
  have hlt : l < iota S (ω ^ cQ c n * ω) := by
    rw [cQ_eps hcE n, ← (gaB1_loc S hc hcO hcE hKE hKP htopE n).1]; exact hlB
  exact gaUniTh (cQ_le_W S hc n) (gaPoly S hc hcO hKE hKP n) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `Λ^B = sup_n Λ⁺(lpSys B n)`**, fixed points included. -/
theorem gaEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdUpper S l ∧ CdLower S l :=
  lpFamEnum B (fun n _ hr hln hfix => gaT_fix S hc hcO hcE hKE hKP htopE n hr hln hfix) hr hl

/-- **CapV at every restart of the range below `Λ^B`**, fixed points included. -/
theorem gaCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdCapV S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact (lpFam B).famCapV hr hl hnf
  · obtain ⟨n, hn⟩ := (lpFam B).famLt hl
    exact Lk.lkCapV_fix (lpSys_topPkg n) hr hn hfx.symm (gaEnum S hc hcO hcE hKE hKP htopE hr hl)

/-- **The successor road over the base**: UPPER, LOWER and CapV asked only at `λ ≥ Λ^B`, (CL), EQ, TCrest,
(EMB₂). -/
theorem gaBaseRoad (hU : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → (lpFam B).famSup ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine lpFamRoad3 B hU hL (fun n _ hr hln hfix => gaT_fix S hc hcO hcE hKE hKP htopE n hr hln hfix)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (lpFam B).famSup l with h | h
  · exact hV l hr hlω h
  · exact gaCapV S hc hcO hcE hKE hKP htopE hr h

/-- **`Λ^B = ι(cQs c)`, `υ_{Λ^B} = P(cQs c) < L(0)`**: the ladder over the base ends at the least strongly critical
ordinal above `c`. -/
theorem gaFam_loc : (lpFam B).famSup = iota S (cQs c) ∧
    upsilon (lpFam B).famSup = Pv S (cQs c) ∧ Pv S (cQs c) < Nc.ncL S 0 := by
  have hSC := cQs_SC c
  have hlim : IsSuccLimit (cQs c) := hSC.isSuccLimit
  have hEs : ω ^ cQs c = cQs c := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ n : ℕ, cQ c n * ω < cQs c := fun n =>
    InE.mul_lt hEs (cQ_lt_cQs c n) (omega0_lt_inE hEs)
  have heq : (lpFam B).famSup = iota S (cQs c) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lpLam B n ≤ _
      rw [lpLam, (gaB1_loc S hc hcO hcE hKE hKP htopE n).1]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      obtain ⟨n, hn⟩ := cQs_lt e.2
      have h1 : e.1 < cQ c n * ω := hn.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (cQ c n * ω) := iota_mono _ _ h1.le
        _ = lpLam B n := (gaB1_loc S hc hcO hcE hKE hKP htopE n).1.symm
        _ ≤ (lpFam B).famSup := ((lpFam B).famBd_lt n).le
  have hups : upsilon (lpFam B).famSup = Pv S (cQs c) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ga_Pv_lt_L0 S ?_⟩
  exact (Ordinal.iSup_le fun n => cQ_le_W S hc n).trans (gaW_lt_Om2 S).le

end Loc

/-! ## The limit layer as a code -/

section Lim

variable (S : InaccSeq.{0}) {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gaAt c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = gxTh y gaAt c) (hKP : GaPoly B.K.sys c) {k : ℕ} (H : LpLimH B k)
include S hc hcO hKE H

omit hcO hKP in
/-- **The limit top reads the code `cQs c`**: `gk k y = Θ_y(cQs c)`. -/
theorem gaLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : gk k y = gxTh y gaAt (cQs c) := by
  rw [ga_gk_sup H (gg_SC_eps hy) (lp_y1 hy1), cQs, gxTh_iSup]
  exact iSup_congr fun n => gaTop_th S hc hKE n y hy hy1

include hKP in
/-- **The limit layer has terms for every code below `cQs c`.** -/
theorem gaLim_poly : GaPoly (lpUSys B k H) (cQs c) := by
  intro Z d hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gaPoly S hc hcO hKE hKP n Z d hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Ga
