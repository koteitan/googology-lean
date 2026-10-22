import Googology.Trans.PoR.InaccPsi.R2.LpPoly
import Googology.Trans.PoR.InaccPsi.R2.LsName

/-!
# Where the ladder over the base ends: the frontier jumps from the code `c` to its `Γ`-image

For a base `K` with terms for the codes below `c` (`LgPoly K c`), top `E_K = Θ'(c)`, `c = ω^c < φ(c, 0)`,
`Ω₁ ≤ c`, `ε_{x+1} < E_K(x)`:

* `lpB1_loc` (**`Λ⁺(lpSys B n) = ι(cP c n·ω)`, `ρ` of it `= P(…) < L(0)`**), `lpT_fix` (**the notation hypothesis
  `Θ_F(m_F) = O_n(F)` at every fixed point of the range below `Λ⁺(lpSys B n)`**: THEOREM UNI `lgUniTh`), `lpEnum`
  (**ENUM-REACH at every restart of the range below `Λ^B = sup_n Λ⁺(lpSys B n)`, fixed points included**),
  `lpBaseRoad` (the successor road: UPPER/LOWER only at `λ ≥ Λ^B`, CapV only at the outer restarts);
* `cPs c = sup_n cP c n`, `cPs_SC`, `cPs_min` (**`cPs c` is the least strongly critical ordinal above `c`: the
  `Γ`-image of `c`**), `lpFam_loc` (**`Λ^B = ι(cPs c)`, `υ_{Λ^B} = P(cPs c) < L(0)`**), `lpFam_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The `Γ`-image of a code -/

/-- `cPs c = sup_n cP c n`. -/
noncomputable def cPs (c : Ordinal.{0}) : Ordinal.{0} := ⨆ n : ℕ, cP c n

section Sup

variable {c : Ordinal.{0}} (hcv : c < veblen c 0)
include hcv

theorem cP_lt_cPs (n : ℕ) : cP c n < cPs c :=
  (cP_lt_succ hcv n).trans_le (Ordinal.le_iSup (fun k => cP c k) (n + 1))

theorem cP_strictMono : StrictMono (cP c) := strictMono_nat_of_lt_succ (cP_lt_succ hcv)

theorem cPs_lt {e : Ordinal.{0}} (he : e < cPs c) : ∃ n, e < cP c n := Ordinal.lt_iSup_iff.1 he

/-- **`cPs c` is strongly critical.** -/
theorem cPs_SC : SC (cPs c) := by
  refine ⟨lt_of_le_of_lt zero_le (cP_lt_cPs hcv 0), fun x hx x' hx' => ?_⟩
  obtain ⟨n, hn⟩ := cPs_lt hcv hx
  obtain ⟨m, hm⟩ := cPs_lt hcv hx'
  set k := max n m
  have hxk : x < cP c k := hn.trans_le ((cP_strictMono hcv).monotone (le_max_left n m))
  have hx'k : x' < cP c k := hm.trans_le ((cP_strictMono hcv).monotone (le_max_right n m))
  have h1 : veblen x (cP c (k + 1)) = cP c (k + 1) := veblen_veblen_of_lt hxk 0
  have h2 : veblen x x' < veblen x (cP c (k + 1)) :=
    veblen_lt_veblen_iff_right.2 (hx'k.trans (cP_lt_succ hcv k))
  rw [h1] at h2
  exact h2.trans (cP_lt_cPs hcv (k + 1))

/-- **`cPs c` is the least strongly critical ordinal above `c`**. -/
theorem cPs_min {s : Ordinal.{0}} (hs : SC s) (hcs : c < s) : cPs c ≤ s := by
  have : ∀ n, cP c n < s := by
    intro n
    induction n with
    | zero => exact hcs
    | succ n ih => exact hs.2 _ ih 0 hs.1
  exact Ordinal.iSup_le fun n => (this n).le

theorem c_lt_cPs : c < cPs c := cP_lt_cPs hcv 0

end Sup

/-! ## The frontiers of the stages and the notation hypothesis -/

section Loc

variable {S : InaccSeq.{0}} {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → LgCl Z c) (hcO : Om 1 ≤ c)
  (hcv : c < veblen c 0) (hcE : ω ^ c = c) (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = lgTh y c)
  (hKP : LgPoly B.K.sys c) (htopE : ∀ x, InE x → x < Om1 → eN x < B.K.E x)
include hc hcO hcv hcE hKE hKP htopE

omit hcO hcv hcE hKE hKP htopE in
theorem cP_le_Gam' (S : InaccSeq.{0}) (n : ℕ) : cP c n ≤ lgGam' :=
  (lgCl_lt_Gam' S (cP_cl hc ph_SC_Om1 n)).le

omit hc hcO hcv hKE hKP htopE in
theorem cP_eps : ∀ n : ℕ, ω ^ cP c n = cP c n
  | 0 => hcE
  | n + 1 => gg_veblen_eps (fun h => by
      have := cP_eps n
      rw [h, opow_zero] at this
      exact one_ne_zero this)

/-- **`Λ⁺(lpSys B n) = ι(cP c n·ω)`, `ρ` of it `= P(cP c n·ω) < L(0)`.** -/
theorem lpB1_loc (n : ℕ) : xtB1 (lpSys B n) = iota S (cP c n * ω) ∧
    upsilon (xtB1 (lpSys B n)) = Pv S (cP c n * ω) ∧ Pv S (cP c n * ω) < Nc.ncL S 0 := by
  have h := lgB1_eq2 (S := S) (cP_le_Gam' hc S n) (lpPoly hc hcO hcv hKE hKP n)
    (fun y hy hy1 => lpTop_th hc hcv hKE n y hy hy1) (fun _ hZ => cP_cl hc hZ n) (cP_Om1_le hcO n)
    (fun x hx hx1 => (htopE x hx hx1).trans_le (E_le_gP B hx hx1 n)) (lpSys_topPkg n)
  rwa [cP_eps hcE n] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lpSys B n)`.** -/
theorem lpT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lpSys B n)) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l := by
  have hlt : l < iota S (ω ^ cP c n * ω) := by
    rw [cP_eps hcE n, ← (lpB1_loc hc hcO hcv hcE hKE hKP htopE (S := S) n).1]; exact hlB
  exact lgUniTh (cP_le_Gam' hc S n) (lpPoly hc hcO hcv hKE hKP n) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `Λ^B = sup_n Λ⁺(lpSys B n)`**, fixed points included. -/
theorem lpEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdUpper S l ∧ CdLower S l :=
  lpFamEnum B (fun n _ hr hln hfix => lpT_fix hc hcO hcv hcE hKE hKP htopE n hr hln hfix) hr hl

/-- **The successor road over the base**: UPPER and LOWER asked only at `λ ≥ Λ^B`, the cap of the values only at the
outer restarts, (CL), EQ, TCrest, (EMB₂). -/
theorem lpBaseRoad (hU : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (lpFam B).famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lpFamRoad3 B hU hL (fun n _ hr hln hfix => lpT_fix hc hcO hcv hcE hKE hKP htopE n hr hln hfix) hV hC hEQ hrest
    hB2

/-- **`Λ^B = ι(cPs c)`, `υ_{Λ^B} = P(cPs c) < L(0)`**: the ladder over the base ends at the `Γ`-image of `c`. -/
theorem lpFam_loc : (lpFam B).famSup = iota S (cPs c) ∧
    upsilon (lpFam B).famSup = Pv S (cPs c) ∧ Pv S (cPs c) < Nc.ncL S 0 := by
  have hSC := cPs_SC hcv
  have hlim : IsSuccLimit (cPs c) := hSC.isSuccLimit
  have hEs : ω ^ cPs c = cPs c := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ n : ℕ, cP c n * ω < cPs c := fun n =>
    InE.mul_lt hEs (cP_lt_cPs hcv n) (omega0_lt_inE hEs)
  have heq : (lpFam B).famSup = iota S (cPs c) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lpLam B n ≤ _
      rw [lpLam, (lpB1_loc hc hcO hcv hcE hKE hKP htopE (S := S) n).1]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      obtain ⟨n, hn⟩ := cPs_lt hcv e.2
      have h1 : e.1 < cP c n * ω := hn.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (cP c n * ω) := iota_mono _ _ h1.le
        _ = lpLam B n := (lpB1_loc hc hcO hcv hcE hKE hKP htopE n).1.symm
        _ ≤ (lpFam B).famSup := ((lpFam B).famBd_lt n).le
  have hups : upsilon (lpFam B).famSup = Pv S (cPs c) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ?_⟩
  -- `cPs c ≤ Γ' < Ω₂`, and `Ω₂` is good: `ι(cPs c) ≤ ι(Ω₂) < ι(Ω_ω)`
  have hle : cPs c ≤ Om (1 + 1) :=
    (Ordinal.iSup_le fun n => cP_le_Gam' hc S n).trans (lgGam'_lt_Om2 S).le
  have hg2 : Bt.Good S (Om (1 + 1)) := by
    have := Ls.lsOmNat_mem (S := S) (ConjT.Aη S (Om (1 + 1)) + 1) (S.psi (ConjT.Aη S (Om (1 + 1))) (Om 1)) 2
    have e : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
    rw [e] at this
    exact this
  have hlt : iota S (Om (1 + 1)) < iota S (Om ω) := cd_iota_lt_of_good hg2 ph_Om2_lt_Omw
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  rw [← hups, hL0, heq]
  exact upsilon_normal.strictMono ((iota_mono _ _ hle).trans_lt hlt)

/-- **Where the ladder over the base lies**: `Λ⁺(K) < Λ⁺(lpSys B 1) < Λ^B`, `υ_{Λ^B} < L(0) = m* ≤ L(k+1) < L(ω) <
L(ω+1)`, and `Λ^B < L(ω+1)`. -/
theorem lpFam_fr_order (k : ℕ) :
    xtB1 B.K.sys < xtB1 (lpSys B 1) ∧ xtB1 (lpSys B 1) < (lpFam B).famSup ∧
    upsilon (lpFam B).famSup < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    (lpFam B).famSup < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lpFam_loc hc hcO hcv hcE hKE hKP htopE (S := S)
  have hU : upsilon (lpFam B).famSup < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨lpB1_gt_K 0, (lpFam B).famBd_lt 1, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Lp
