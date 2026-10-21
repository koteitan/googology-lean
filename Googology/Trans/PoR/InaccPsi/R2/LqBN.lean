import Googology.Trans.PoR.InaccPsi.R2.LqBig

/-!
# The layers `lyBig^{n+1}(lgLay)` (tops `Γ(x)·B(x)^{n+1}`) and their supremum `ι(ω^{ω^{Γ_{Ω₁+1}+phB·ω}})`

`lqBN n = lyBig^{n+1}(lgLay)` (`lqBN 0 = lqBig`): `E_n(x) = Γ(x) + B(x)·(n+1)`, top `ω^{Γ(x) + B(x)·(n+1)} =
Γ(x)·B(x)^{n+1}`, codes below `ω^{Γ_{Ω₁+1} + phB·(n+1)}` (`lqBigPoly` at every step).  For every `n`:

* `lqBN_E`, `lqBN_poly` (**`LgPoly (lqBN n) (ω^{Γ_{Ω₁+1} + phB·(n+1)})`**, top `Θ'` of it);
* `lqBN_loc` (**`Λ⁺(lqBN n) = ι(ω^{ω^{Γ_{Ω₁+1} + phB·(n+1)}}·ω)`, `ρ` of it `< L(0)`**), `lqBNT_fix`, `lqBNEnum`
  (**ENUM-REACH at every restart of the range below `Λ⁺(lqBN n)`**, fixed points included), `lqBN_capV`, `lqBN_blk`,
  `lqBNRoadPh`;
* the chain (`lqBN_topIn`, `lqLamB_lt`, `lqBN_eq`), the family `lqFamB`, `lqFamB_loc` (**`sup_n Λ⁺(lqBN n) =
  ι(ω^{ω^{Γ_{Ω₁+1} + phB·ω}})`, `ρ` of it `< L(0)`**), `lqFamBEnum` (**ENUM-REACH below the supremum**), `lqFamB_capV`,
  `lqFamB_blk`, `lqFamBRoad`, `lqFamB_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The layers -/

/-- The layers `lyBig^{n+1}(lgLay)` with the bound `B(x) ≤ E(x)`. -/
noncomputable def lqBNp : ℕ → {L : XtLay // ∀ x, InE x → x < Om1 → VzB x ≤ L.E x}
  | 0 => ⟨lqBig, lyBig_EB lgLay lqBig_EB⟩
  | n + 1 => ⟨lyBig (lqBNp n).1 (lqBNp n).2, lyBig_EB (lqBNp n).1 (lqBNp n).2⟩

/-- **The `n`-th layer `lyBig^{n+1}(lgLay)`**: top `Γ(x)·B(x)^{n+1}`. -/
noncomputable def lqBN (n : ℕ) : XtLay := (lqBNp n).1

theorem lqBN_succ (n : ℕ) : lqBN (n + 1) = lyBig (lqBN n) (lqBNp n).2 := rfl

theorem lqBN_zero : lqBN 0 = lqBig := rfl

theorem lqBN_E (n : ℕ) (x : Ordinal.{0}) : (lqBN n).E x = lgG x + VzB x * ((n : Ordinal.{0}) + 1) := by
  induction n with
  | zero => show lgG x + VzB x = _; rw [Nat.cast_zero, zero_add, mul_one]
  | succ n ih =>
    show (lqBN n).E x + VzB x = _
    rw [ih, add_assoc, ← mul_add_one, Nat.cast_succ]

/-- The exponent code `Γ_{Ω₁+1} + phB·(n+1)` of `E_n`. -/
noncomputable def lqBNe (n : ℕ) : Ordinal.{0} := ggGam + phB * ((n : Ordinal.{0}) + 1)

theorem lq_cl_Bmul (k : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (phB * (k : Ordinal.{0})) :=
  lgCl_of_GgCl (GgCl.mul_nat hZ.1 (ph_cl_B hZ) k)

theorem lqTh_Bmul {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ∀ k : ℕ, lgTh y (phB * (k : Ordinal.{0})) = VzB y * (k : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, lgTh_zero]
  | k + 1 => by
    rw [Nat.cast_succ, mul_add_one, mul_add_one, lgTh_add hy (lq_cl_Bmul k hy), lqTh_Bmul hy hy1 k,
      lgTh_eq_ggTh lq_B_lt_Gam.le, phTh_B hy hy1]

theorem lq_cl_BNe (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (lqBNe n) := by
  have := lq_cl_Bmul (n + 1) hZ
  rw [Nat.cast_succ] at this
  exact LgCl.add LgCl.gam this

theorem lqBN_Eth (n : ℕ) : ∀ y, SC y → y < Om 1 → (lqBN n).E y = lgTh y (lqBNe n) := by
  intro y hy hy1
  have := lqTh_Bmul hy hy1 (n + 1)
  rw [Nat.cast_succ] at this
  rw [lqBN_E, lqBNe, lgTh_add hy LgCl.gam, lgTh_Gam hy hy1, this]

theorem lqBNe_succ (n : ℕ) : lqBNe n + phB = lqBNe (n + 1) := by
  unfold lqBNe
  rw [add_assoc, ← mul_add_one, Nat.cast_succ]

/-- **`LgPoly (lqBN n) (ω^{Γ_{Ω₁+1} + phB·(n+1)})`**, top `Θ'` of it. -/
theorem lqBN_poly : ∀ n : ℕ, LgPoly (lqBN n).sys (ω ^ lqBNe n) ∧
    ∀ y, SC y → y < Om 1 → (lqBN n).sys.top y = lgTh y (ω ^ lqBNe n)
  | 0 => by
    have e : lqBNe 0 = lqBe := by unfold lqBNe lqBe; rw [Nat.cast_zero, zero_add, mul_one]
    rw [e]; exact ⟨lqBig_poly, lqBig_top⟩
  | n + 1 => by
    have h := lqBN_poly n
    rw [← lqBNe_succ]
    exact ⟨lqBigPoly (lqBN n) (lqBNp n).2 (fun _ hZ => lq_cl_BNe n hZ) (lqBN_Eth n) h.1,
      lqBigTop (lqBN n) (lqBNp n).2 (fun _ hZ => lq_cl_BNe n hZ) (lqBN_Eth n)⟩

theorem lq_cl_BN (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ lqBNe n) := LgCl.opow hZ.1 (lq_cl_BNe n hZ)

theorem lq_Om1_le_BN (n : ℕ) : Om 1 ≤ ω ^ lqBNe n :=
  ggGam_spec.2.le.trans (lg_Gam_eps.symm.le.trans (opow_le_opow_right omega0_pos le_self_add))

theorem lqBN_topE (n : ℕ) (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < (lqBN n).sys.top x := by
  rw [(lqBN n).top_eq x hx hx1, lqBN_E]
  have hGE : ω ^ lgG x = lgG x := lgG_inE x hx hx1
  refine (gT_lt_lgG hx hx1 0).trans_le ?_
  calc lgG x = ω ^ lgG x := hGE.symm
    _ ≤ ω ^ (lgG x + VzB x * ((n : Ordinal.{0}) + 1)) := opow_le_opow_right omega0_pos le_self_add

variable {S : InaccSeq.{0}}

theorem lq_BN_le_Gam' (S : InaccSeq.{0}) (n : ℕ) : ω ^ lqBNe n ≤ lgGam' :=
  (lgCl_lt_Gam' S (lq_cl_BN n ph_SC_Om1)).le

/-- **`Λ⁺(lqBN n) = ι(ω^{ω^{Γ_{Ω₁+1} + phB·(n+1)}}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lqBN_loc (n : ℕ) : xtB1 (lqBN n).sys = iota S (ω ^ ω ^ lqBNe n * ω) ∧
    upsilon (xtB1 (lqBN n).sys) = Pv S (ω ^ ω ^ lqBNe n * ω) ∧ Pv S (ω ^ ω ^ lqBNe n * ω) < Nc.ncL S 0 :=
  lgB1_eq2 (lq_BN_le_Gam' S n) (lqBN_poly n).1 (lqBN_poly n).2 (fun _ hZ => lq_cl_BN n hZ) (lq_Om1_le_BN n)
    (lqBN_topE n) (lqBN n).topPkg

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lqBN n)`.** -/
theorem lqBNT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lqBN n).sys)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lqBN n).sys l := by
  have hlt : l < iota S (ω ^ ω ^ lqBNe n * ω) := by rw [← (lqBN_loc (S := S) n).1]; exact hlB
  exact lgUniTh (lq_BN_le_Gam' S n) (lqBN_poly n).1 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem lqBN_nonfix (n : ℕ) : XtNonfix (xtOrec (lqBN n).sys) (xtB1 (lqBN n).sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lqBN n).topPkg))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lqBN n)`**, fixed points of `υ` included. -/
theorem lqBNEnum (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lqBN n).sys) :
    CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (lqBN n).topPkg) (lqBN_nonfix n) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (lqBN n).topPkg) hr.1 hl).2 (lqBNT_fix n hr hl hfx.symm)

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lqBN n)`.** -/
theorem lqBN_capV (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lqBN n).sys)
    (hfix : l < upsilon l) : CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 (lqBN n).topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lqBN_nonfix n l hr.1 hww hfix hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(lqBN n)}`** in `R₂^C`. -/
theorem lqBN_blk (n : ℕ) :
    (∀ c d, c < d → d < upsilon (xtB1 (lqBN n).sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (lqBN n).sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (lqBN n).sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lqBN n).sys l)) ∧
    (∀ α < upsilon (xtB1 (lqBN n).sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (lqBN n).topPkg

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lqBN n)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lqBNRoadPh (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lqBN n).sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lqBN n).sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lqBN n).sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 (lqBN n).topPkg) (lqBN_nonfix n) hU hL (fun _ hr hlB hfix => lqBNT_fix n hr hlB hfix) hV hC hEQ
    hrest hB2

/-! ## The chain and its supremum -/

theorem lqBN_topIn (n : ℕ) : LyTopIn (lqBN (n + 1)).sys (lqBN n).sys := lyBig_topIn (lqBN n) (lqBNp n).2

/-- `Λ⁺(lqBN n)`. -/
noncomputable def lqLamB (n : ℕ) : Ordinal.{0} := xtB1 (lqBN n).sys

theorem lqLamB_lt (n : ℕ) : lqLamB n < lqLamB (n + 1) :=
  lyB1_lt (lqBN (n + 1)).topPkg (lqBN n).topPkg (lqBN_topIn n)

theorem lqLamB_strictMono : StrictMono lqLamB := strictMono_nat_of_lt_succ lqLamB_lt

/-- `O_{lqBN m} = O_{lqBN n}` below `Λ⁺(lqBN n)` for `n ≤ m`. -/
theorem lqBN_eq {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < lqLamB n) :
    xtOrec (lqBN m).sys μ = xtOrec (lqBN n).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact lyEq (lqBN m).topPkg (lqBN_topIn m) hμ (hμn.trans_le (lqLamB_strictMono.monotone hnm))

/-- **The family of the layers `lqBN n`**: bounds `Λ⁺(lqBN n)`, offsets `O_{lqBN n}`. -/
noncomputable def lqFamB : XtFam where
  bd := lqLamB
  off := fun n => xtOrec (lqBN n).sys
  spec := fun n => xtSpec1 (lqBN n).topPkg
  mono := lqLamB_lt
  nonfix := lqBN_nonfix

theorem lqFamB_sup : lqFamB.famSup = ⨆ n : ℕ, lqLamB n := rfl

/-- **ENUM-REACH at every restart of the range below `sup_n Λ⁺(lqBN n)`**, fixed points of `υ` included. -/
theorem lqFamBEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lqFamB.famSup) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, hn⟩ := lqFamB.famLt hl
  exact lqBNEnum n hr hn

/-- **The cap of the values at every non-fixed restart of the range below `sup_n Λ⁺(lqBN n)`.** -/
theorem lqFamB_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lqFamB.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lqFamB.famCapV hr hl hfix

/-- **Theorem BLK^O below `υ_{sup_n Λ⁺(lqBN n)}`** in `R₂^C`. -/
theorem lqFamB_blk :
    (∀ c d, c < d → d < upsilon lqFamB.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lqFamB.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lqLamB k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lqBN k).sys l)) ∧
    (∀ α < upsilon lqFamB.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lqFamB.famBlk

/-- **The road with UPPER and LOWER asked only at `λ ≥ sup_n Λ⁺(lqBN n)`**: the rest is CapV at the outer restarts
below `L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lqFamBRoad (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lqFamB.famRoad3 hU hL (fun n _ hr hln hfix => lqBNT_fix n hr hln hfix) hV hC hEQ hrest hB2

/-- The exponent `Γ_{Ω₁+1} + phB·ω` of the supremum. -/
noncomputable def lqBNw : Ordinal.{0} := ggGam + phB * ω

theorem lq_cl_BNw {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ ω ^ lqBNw) := by
  have h1 : LgCl Z (phB * ω) := by
    rw [show phB * ω = ω ^ (phB + 1) by rw [opow_add, opow_one, ph_B_eps]]
    exact LgCl.opow hZ.1 (LgCl.add (lgCl_of_GgCl (ph_cl_B hZ)) (LgCl.small (gg_one_lt_of_SC hZ)))
  exact LgCl.opow hZ.1 (LgCl.opow hZ.1 (LgCl.add LgCl.gam h1))

theorem lqLamB_loc (n : ℕ) : lqLamB n = iota S (ω ^ ω ^ lqBNe n * ω) := (lqBN_loc n).1

/-- **`sup_n Λ⁺(lqBN n) = ι(ω^{ω^{Γ_{Ω₁+1} + phB·ω}})`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lqFamB_loc : lqFamB.famSup = iota S (ω ^ ω ^ lqBNw) ∧
    upsilon lqFamB.famSup = Pv S (ω ^ ω ^ lqBNw) ∧ Pv S (ω ^ ω ^ lqBNw) < Nc.ncL S 0 := by
  have hB0 : (0 : Ordinal.{0}) < phB := lt_of_le_of_lt zero_le ((lt_add_one (Om 1)).trans_le (right_le_veblen _ _))
  have hstep : ∀ n : ℕ, ω ^ ω ^ lqBNe n * ω < ω ^ ω ^ lqBNw := by
    intro n
    have hk : lqBNe n < lqBNw := by
      unfold lqBNe lqBNw
      refine (add_lt_add_iff_left _).2 ?_
      refine (mul_lt_mul_iff_right₀ hB0).2 ?_
      have := natCast_lt_omega0 (n + 1); rwa [Nat.cast_succ] at this
    have h1 : ω ^ lqBNe n + 1 < ω ^ lqBNw := by
      have hp : ω ^ lqBNe n < ω ^ lqBNw := (opow_lt_opow_iff_right one_lt_omega0).2 hk
      have hlim := ph_opow_lim (c := lqBNw) (lt_of_le_of_lt zero_le hk).ne'
      exact hlim.add_one_lt hp
    rw [show ω ^ ω ^ lqBNe n * ω = ω ^ (ω ^ lqBNe n + 1) by rw [opow_add, opow_one]]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 h1
  have hlim : IsSuccLimit (ω ^ ω ^ lqBNw) := ph_opow_lim (opow_pos _ omega0_pos).ne'
  have heq : lqFamB.famSup = iota S (ω ^ ω ^ lqBNw) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lqLamB n ≤ _
      rw [lqLamB_loc (S := S) n]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      have he := e.2
      rcases eq_or_ne e.1 0 with h0 | h0
      · rw [h0]
        exact (iota_mono _ _ zero_le).trans ((lqLamB_loc (S := S) 0).symm.le.trans (lqFamB.famBd_lt 0).le)
      have hL : log ω e.1 < ω ^ lqBNw := (lt_opow_iff_log_lt one_lt_omega0 h0).1 he
      have hL2 : ∃ n : ℕ, log ω e.1 < ω ^ lqBNe n := by
        rcases eq_or_ne (log ω e.1) 0 with hl0 | hl0
        · exact ⟨0, by rw [hl0]; exact opow_pos _ omega0_pos⟩
        have hLL : log ω (log ω e.1) < lqBNw := (lt_opow_iff_log_lt one_lt_omega0 hl0).1 hL
        have hm : ∃ n : ℕ, log ω (log ω e.1) < lqBNe n := by
          rcases lt_or_ge (log ω (log ω e.1)) ggGam with h | h
          · exact ⟨0, h.trans_le le_self_add⟩
          · obtain ⟨t, ht⟩ := exists_add_of_le h
            have hLL' := hLL
            unfold lqBNw at hLL'
            rw [ht] at hLL'
            have ht' : t < phB * ω := (add_lt_add_iff_left _).1 hLL'
            obtain ⟨m, hm, htm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 ht'
            obtain ⟨n, rfl⟩ := lt_omega0.1 hm
            refine ⟨n, ?_⟩
            unfold lqBNe; rw [ht]
            refine (add_lt_add_iff_left _).2 (htm.trans_le ?_)
            exact mul_le_mul_right (le_self_add) _
        obtain ⟨n, hn⟩ := hm
        exact ⟨n, (lt_opow_succ_log_self one_lt_omega0 _).trans_le
          (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hn))⟩
      obtain ⟨n, hn⟩ := hL2
      have h1 : e.1 < ω ^ ω ^ lqBNe n * ω := by
        refine (lt_opow_succ_log_self one_lt_omega0 _).trans_le ?_
        rw [show ω ^ ω ^ lqBNe n * ω = ω ^ (ω ^ lqBNe n + 1) by rw [opow_add, opow_one]]
        exact opow_le_opow_right omega0_pos ((Order.succ_le_of_lt hn).trans le_self_add)
      calc iota S e.1 ≤ iota S (ω ^ ω ^ lqBNe n * ω) := iota_mono _ _ h1.le
        _ = lqLamB n := (lqLamB_loc n).symm
        _ ≤ lqFamB.famSup := (lqFamB.famBd_lt n).le
  have hups : upsilon lqFamB.famSup = Pv S (ω ^ ω ^ lqBNw) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ?_⟩
  rw [← hups]
  have := (lgIota_lt_L0 (S := S) (fun Z hZ => lq_cl_BNw hZ)).2
  rwa [← heq] at this

/-- **Where the supremum lies**: `ρ(Λ⁺(lqBN n)) < ρ(sup_n Λ⁺(lqBN n)) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and
`sup_n Λ⁺(lqBN n) < L(ω+1)`, unconditionally. -/
theorem lqFamB_fr_order (n k : ℕ) :
    upsilon (lqLamB n) < upsilon lqFamB.famSup ∧ upsilon lqFamB.famSup < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    lqFamB.famSup < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lqFamB_loc (S := S)
  have hU : upsilon lqFamB.famSup < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono (lqFamB.famBd_lt n), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
