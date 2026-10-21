import Googology.Trans.PoR.InaccPsi.R2.LgPBc

/-!
# The layers `lyPoly^{n+1}(lgLay)` over `Γ` (tops `Γ(x)·x^{x·(n+1)}`) and their supremum

`lqPP n = lyPoly^{n+1}(lgLay)` (`lqPP 0 = lgPB`): the layer of all constant exponents taken `n + 1` times over `Γ(x)`,
top `Γ(x)·x^{x·(n+1)}`, codes below `ω^{Γ_{Ω₁+1} + Ω₁·Ω₁·(n+1)}` (`R2.LgPBc`, `lgPoly_poly`).  For every `n`:

* `lqPP_top`, `lqPP_poly` (**`LgPoly (lqPP n) (ω^{e_n})`**, `e_n = Γ_{Ω₁+1} + Ω₁·Ω₁·(n+1)`, top `Θ'_y(ω^{e_n})`);
* `lqPP_loc` (**`Λ⁺(lqPP n) = ι(ω^{ω^{e_n}}·ω)`, `ρ` of it `= P(…) < L(0)`**), `lqPPT_fix` (**the notation hypothesis
  at every fixed point of the range below `Λ⁺(lqPP n)`**), `lqPPEnum` (**ENUM-REACH at every restart of the range
  below `Λ⁺(lqPP n)`**, fixed points included), `lqPP_capV` (CapV at the non-fixed ones), `lqPP_blk` (BLK^O below
  `υ_{Λ⁺(lqPP n)}`), `lqPPRoadPh` (the road with UPPER/LOWER asked only at `λ ≥ Λ⁺(lqPP n)`);
* the chain: `lqPP_topIn` (`lqPP n` lies in `lqPP (n+1)`), `lqLamP_lt`, `lqPP_eq` (the offsets agree), the family
  `lqFamP` (bounds `Λ⁺(lqPP n)`), `lqFamP_loc` (**`sup_n Λ⁺(lqPP n) = ι(ω^{ω^{Γ_{Ω₁+1}+Ω₁·Ω₁·ω}})`, `ρ` of it
  `< L(0)`**),
  `lqFamPEnum` (**ENUM-REACH at every restart of the range below the supremum**), `lqFamP_capV`, `lqFamP_blk`,
  `lqFamPRoad` (the road with UPPER/LOWER asked only above the supremum), `lqFamP_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The layers -/

/-- **`lqPP n = lyPoly^{n+1}(lgLay)`** (top `Γ(x)·x^{x·(n+1)}`). -/
noncomputable def lqPP : ℕ → XtLay
  | 0 => lgPB
  | n + 1 => lyPoly (lqPP n)

theorem lqPP_top (n : ℕ) (x : Ordinal.{0}) : (lqPP n).sys.top x = lgG x * x ^ (x * ((n : Ordinal.{0}) + 1)) := by
  induction n with
  | zero => show lgG x * x ^ x = _; rw [Nat.cast_zero, zero_add, mul_one]
  | succ n ih =>
    show (lqPP n).sys.top x * x ^ x = _
    rw [ih, mul_assoc, ← opow_add, Nat.cast_succ, mul_add_one x ((n : Ordinal.{0}) + 1)]

/-- The exponent `e_n = Γ_{Ω₁+1} + Ω₁·Ω₁·(n+1)` of the top code of `lqPP n`. -/
noncomputable def lqPPe (n : ℕ) : Ordinal.{0} := ggGam + Om 1 * Om 1 * ((n : Ordinal.{0}) + 1)

theorem lq_cl_PPe (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (lqPPe n) := by
  have h1 : LgCl Z ((n : Ordinal.{0}) + 1) := by
    refine LgCl.small (lt_of_lt_of_le ?_ (Lw.lw_omega_lt_SC hZ).le)
    have := natCast_lt_omega0 (n + 1); rwa [Nat.cast_succ] at this
  have h2 : LgCl Z (Om 1 * Om 1 * ((n : Ordinal.{0}) + 1)) := by
    rw [mul_assoc]; exact lg_cl_Om1_mul hZ (lg_cl_Om1_mul hZ h1)
  exact LgCl.add LgCl.gam h2

theorem lqPPe_succ (n : ℕ) : lqPPe n + Om 1 * Om 1 = lqPPe (n + 1) := by
  unfold lqPPe
  rw [add_assoc, ← mul_add_one, Nat.cast_succ]

/-- **`LgPoly (lqPP n) (ω^{e_n})`**, top `Θ'_y(ω^{e_n})`. -/
theorem lqPP_poly : ∀ n : ℕ, LgPoly (lqPP n).sys (ω ^ lqPPe n) ∧
    ∀ y, SC y → y < Om 1 → (lqPP n).sys.top y = lgTh y (ω ^ lqPPe n)
  | 0 => by
    have e : lqPPe 0 = ggGam + Om 1 * Om 1 := by unfold lqPPe; rw [Nat.cast_zero, zero_add, mul_one]
    rw [e]; exact lgPB_poly
  | n + 1 => by
    have h := lqPP_poly n
    rw [← lqPPe_succ]
    exact ⟨lgPoly_poly (lqPP n) (fun _ hZ => lq_cl_PPe n hZ) h.2 h.1,
      lgTop_poly (lqPP n) (fun _ hZ => lq_cl_PPe n hZ) h.2⟩

theorem lq_cl_PP (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ lqPPe n) := LgCl.opow hZ.1 (lq_cl_PPe n hZ)

theorem lq_Om1_le_PP (n : ℕ) : Om 1 ≤ ω ^ lqPPe n :=
  ggGam_spec.2.le.trans (lg_Gam_eps.symm.le.trans (opow_le_opow_right omega0_pos le_self_add))

theorem lqPP_topE (n : ℕ) (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < (lqPP n).sys.top x := by
  rw [lqPP_top]
  exact (gT_lt_lgG hx hx1 0).trans_le (le_mul_of_one_le_right zero_le (one_le_iff_pos.2 (opow_pos _ hx.pos)))

variable {S : InaccSeq.{0}}

theorem lq_PP_le_Gam' (S : InaccSeq.{0}) (n : ℕ) : ω ^ lqPPe n ≤ lgGam' :=
  (lgCl_lt_Gam' S (lq_cl_PP n ph_SC_Om1)).le

/-- **`Λ⁺(lqPP n) = ι(ω^{ω^{e_n}}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lqPP_loc (n : ℕ) : xtB1 (lqPP n).sys = iota S (ω ^ ω ^ lqPPe n * ω) ∧
    upsilon (xtB1 (lqPP n).sys) = Pv S (ω ^ ω ^ lqPPe n * ω) ∧ Pv S (ω ^ ω ^ lqPPe n * ω) < Nc.ncL S 0 :=
  lgB1_eq2 (lq_PP_le_Gam' S n) (lqPP_poly n).1 (lqPP_poly n).2 (fun _ hZ => lq_cl_PP n hZ) (lq_Om1_le_PP n)
    (lqPP_topE n) (lqPP n).topPkg

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lqPP n)`.** -/
theorem lqPPT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lqPP n).sys)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lqPP n).sys l := by
  have hlt : l < iota S (ω ^ ω ^ lqPPe n * ω) := by rw [← (lqPP_loc (S := S) n).1]; exact hlB
  exact lgUniTh (lq_PP_le_Gam' S n) (lqPP_poly n).1 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem lqPP_nonfix (n : ℕ) : XtNonfix (xtOrec (lqPP n).sys) (xtB1 (lqPP n).sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lqPP n).topPkg))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lqPP n)`**, fixed points of `υ` included. -/
theorem lqPPEnum (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lqPP n).sys) :
    CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (lqPP n).topPkg) (lqPP_nonfix n) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (lqPP n).topPkg) hr.1 hl).2 (lqPPT_fix n hr hl hfx.symm)

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lqPP n)`.** -/
theorem lqPP_capV (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lqPP n).sys)
    (hfix : l < upsilon l) : CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 (lqPP n).topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lqPP_nonfix n l hr.1 hww hfix hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(lqPP n)}`** in `R₂^C`. -/
theorem lqPP_blk (n : ℕ) :
    (∀ c d, c < d → d < upsilon (xtB1 (lqPP n).sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (lqPP n).sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (lqPP n).sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lqPP n).sys l)) ∧
    (∀ α < upsilon (xtB1 (lqPP n).sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (lqPP n).topPkg

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lqPP n)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lqPPRoadPh (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lqPP n).sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lqPP n).sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lqPP n).sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 (lqPP n).topPkg) (lqPP_nonfix n) hU hL (fun _ hr hlB hfix => lqPPT_fix n hr hlB hfix) hV hC hEQ
    hrest hB2

/-! ## The chain and its supremum -/

/-- `lqPP n` lies in `lqPP (n+1)`: the term `T_n(x)·x^0` and the gap `T_n(ρ) + 1 < T_n(ρ)·ρ^ρ`. -/
theorem lqPP_topIn (n : ℕ) : LyTopIn (lqPP (n + 1)).sys (lqPP n).sys := by
  refine ⟨lyPowTm (lqPP n) 0, fun x hx _ => ⟨lyPowTm_cb (lqPP n) hx (upsPt_inE hx).pos, ?_⟩, fun l hl hl1 => ?_⟩
  · show (lyPoly (lqPP n)).sys.val (lyPowTm (lqPP n) 0) x = _
    rw [lyPowTm_val, opow_zero, mul_one]
  · have hρE := ups_inE hl
    have h := lyGap (lqPP n) hρE (ups_lt_Om1 l hl1) hρE.pos
    rw [opow_zero, mul_one] at h
    exact h

/-- `Λ⁺(lqPP n)`. -/
noncomputable def lqLamP (n : ℕ) : Ordinal.{0} := xtB1 (lqPP n).sys

theorem lqLamP_lt (n : ℕ) : lqLamP n < lqLamP (n + 1) :=
  (lyLamGt (lqPP n).topPkg (lqPP_topIn n)).trans (lqPP (n + 1)).xtLamLt

theorem lqLamP_strictMono : StrictMono lqLamP := strictMono_nat_of_lt_succ lqLamP_lt

theorem lqLamP_lt_Om1 (n : ℕ) : lqLamP n < Om1 := xtB1_lt_Om1 (lqPP n).topPkg

theorem lqLamP_zero : lqLamP 0 = xtB1 lgPB.sys := rfl

/-- `O_{lqPP m} = O_{lqPP n}` below `Λ⁺(lqPP n)` for `n ≤ m`. -/
theorem lqPP_eq {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < lqLamP n) :
    xtOrec (lqPP m).sys μ = xtOrec (lqPP n).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact lyEq (lqPP m).topPkg (lqPP_topIn m) hμ (hμn.trans_le (lqLamP_strictMono.monotone hnm))

/-- **The family of the layers `lqPP n`**: bounds `Λ⁺(lqPP n)`, offsets `O_{lqPP n}`. -/
noncomputable def lqFamP : XtFam where
  bd := lqLamP
  off := fun n => xtOrec (lqPP n).sys
  spec := fun n => xtSpec1 (lqPP n).topPkg
  mono := lqLamP_lt
  nonfix := lqPP_nonfix

theorem lqFamP_sup : lqFamP.famSup = ⨆ n : ℕ, lqLamP n := rfl

theorem lqPB_lt_FamP : xtB1 lgPB.sys < lqFamP.famSup := lqFamP.famBd_lt 0

/-- **ENUM-REACH at every restart of the range below `sup_n Λ⁺(lqPP n)`**, fixed points of `υ` included. -/
theorem lqFamPEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lqFamP.famSup) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, hn⟩ := lqFamP.famLt hl
  exact lqPPEnum n hr hn

/-- **The cap of the values at every non-fixed restart of the range below `sup_n Λ⁺(lqPP n)`.** -/
theorem lqFamP_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lqFamP.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lqFamP.famCapV hr hl hfix

/-- **Theorem BLK^O below `υ_{sup_n Λ⁺(lqPP n)}`** in `R₂^C`. -/
theorem lqFamP_blk :
    (∀ c d, c < d → d < upsilon lqFamP.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lqFamP.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lqLamP k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lqPP k).sys l)) ∧
    (∀ α < upsilon lqFamP.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lqFamP.famBlk

/-- **The road with UPPER and LOWER asked only at `λ ≥ sup_n Λ⁺(lqPP n)`**: the rest is CapV at the outer restarts
below `L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lqFamPRoad (hU : ∀ l, CdRange S l → lqFamP.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamP.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamP.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lqFamP.famRoad3 hU hL (fun n _ hr hln hfix => lqPPT_fix n hr hln hfix) hV hC hEQ hrest hB2

/-- The exponent `Γ_{Ω₁+1} + Ω₁·Ω₁·ω` of the supremum. -/
noncomputable def lqPPw : Ordinal.{0} := ggGam + Om 1 * Om 1 * ω

theorem lq_cl_PPw {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ ω ^ lqPPw) := by
  have h1 : LgCl Z (Om 1 * Om 1 * ω) := by
    rw [show Om 1 * Om 1 * ω = ω ^ (Om 1 + Om 1 + 1) by rw [opow_add, opow_add, opow_one, Om1_opow]]
    exact LgCl.opow hZ.1 (LgCl.add (LgCl.add LgCl.om LgCl.om) (LgCl.small (gg_one_lt_of_SC hZ)))
  exact LgCl.opow hZ.1 (LgCl.opow hZ.1 (LgCl.add LgCl.gam h1))

theorem lqLamP_loc (n : ℕ) : lqLamP n = iota S (ω ^ ω ^ lqPPe n * ω) := (lqPP_loc n).1

/-- **`sup_n Λ⁺(lqPP n) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·Ω₁·ω}})`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lqFamP_loc : lqFamP.famSup = iota S (ω ^ ω ^ lqPPw) ∧
    upsilon lqFamP.famSup = Pv S (ω ^ ω ^ lqPPw) ∧ Pv S (ω ^ ω ^ lqPPw) < Nc.ncL S 0 := by
  have hOO : (0 : Ordinal.{0}) < Om 1 * Om 1 := mul_pos (Om_pos one_ne_zero) (Om_pos one_ne_zero)
  have hstep : ∀ n : ℕ, ω ^ ω ^ lqPPe n * ω < ω ^ ω ^ lqPPw := by
    intro n
    have hk : lqPPe n < lqPPw := by
      unfold lqPPe lqPPw
      refine (add_lt_add_iff_left _).2 ?_
      refine (mul_lt_mul_iff_right₀ hOO).2 ?_
      have := natCast_lt_omega0 (n + 1); rwa [Nat.cast_succ] at this
    have h1 : ω ^ lqPPe n + 1 < ω ^ lqPPw := by
      have hp : ω ^ lqPPe n < ω ^ lqPPw := (opow_lt_opow_iff_right one_lt_omega0).2 hk
      have hlim := ph_opow_lim (c := lqPPw) (lt_of_le_of_lt zero_le hk).ne'
      exact hlim.add_one_lt hp
    rw [show ω ^ ω ^ lqPPe n * ω = ω ^ (ω ^ lqPPe n + 1) by rw [opow_add, opow_one]]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 h1
  have hlim : IsSuccLimit (ω ^ ω ^ lqPPw) := ph_opow_lim (opow_pos _ omega0_pos).ne'
  have heq : lqFamP.famSup = iota S (ω ^ ω ^ lqPPw) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lqLamP n ≤ _
      rw [lqLamP_loc (S := S) n]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      have he := e.2
      rcases eq_or_ne e.1 0 with h0 | h0
      · rw [h0]
        exact (iota_mono _ _ zero_le).trans ((lqLamP_loc (S := S) 0).symm.le.trans (lqFamP.famBd_lt 0).le)
      have hL : log ω e.1 < ω ^ lqPPw := (lt_opow_iff_log_lt one_lt_omega0 h0).1 he
      have hL2 : ∃ n : ℕ, log ω e.1 < ω ^ lqPPe n := by
        rcases eq_or_ne (log ω e.1) 0 with hl0 | hl0
        · exact ⟨0, by rw [hl0]; exact opow_pos _ omega0_pos⟩
        have hLL : log ω (log ω e.1) < lqPPw := (lt_opow_iff_log_lt one_lt_omega0 hl0).1 hL
        have hm : ∃ n : ℕ, log ω (log ω e.1) < lqPPe n := by
          rcases lt_or_ge (log ω (log ω e.1)) ggGam with h | h
          · exact ⟨0, h.trans_le le_self_add⟩
          · obtain ⟨t, ht⟩ := exists_add_of_le h
            have hLL' := hLL
            unfold lqPPw at hLL'
            rw [ht] at hLL'
            have ht' : t < Om 1 * Om 1 * ω := (add_lt_add_iff_left _).1 hLL'
            obtain ⟨m, hm, htm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 ht'
            obtain ⟨n, rfl⟩ := lt_omega0.1 hm
            refine ⟨n, ?_⟩
            unfold lqPPe; rw [ht]
            refine (add_lt_add_iff_left _).2 (htm.trans_le ?_)
            exact mul_le_mul_right (le_self_add) _
        obtain ⟨n, hn⟩ := hm
        exact ⟨n, (lt_opow_succ_log_self one_lt_omega0 _).trans_le
          (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hn))⟩
      obtain ⟨n, hn⟩ := hL2
      have h1 : e.1 < ω ^ ω ^ lqPPe n * ω := by
        refine (lt_opow_succ_log_self one_lt_omega0 _).trans_le ?_
        rw [show ω ^ ω ^ lqPPe n * ω = ω ^ (ω ^ lqPPe n + 1) by rw [opow_add, opow_one]]
        exact opow_le_opow_right omega0_pos ((Order.succ_le_of_lt hn).trans le_self_add)
      calc iota S e.1 ≤ iota S (ω ^ ω ^ lqPPe n * ω) := iota_mono _ _ h1.le
        _ = lqLamP n := (lqLamP_loc n).symm
        _ ≤ lqFamP.famSup := (lqFamP.famBd_lt n).le
  have hups : upsilon lqFamP.famSup = Pv S (ω ^ ω ^ lqPPw) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ?_⟩
  rw [← hups]
  have := (lgIota_lt_L0 (S := S) (fun Z hZ => lq_cl_PPw hZ)).2
  rwa [← heq] at this

/-- **Where the supremum lies**: `ρ(Λ⁺(lgPB)) = ρ(Λ⁺(lqPP 0)) < ρ(Λ⁺(lqPP (n+1)))`, `ρ(Λ⁺(lqPP n)) <
ρ(sup_n Λ⁺(lqPP n)) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and `sup_n Λ⁺(lqPP n) < L(ω+1)`, unconditionally. -/
theorem lqFamP_fr_order (n k : ℕ) :
    upsilon (lqLamP 0) < upsilon (lqLamP (n + 1)) ∧ upsilon (lqLamP n) < upsilon lqFamP.famSup ∧
    upsilon lqFamP.famSup < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    lqFamP.famSup < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lqFamP_loc (S := S)
  have hU : upsilon lqFamP.famSup < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono (lqLamP_strictMono (Nat.succ_pos n)),
    upsilon_normal.strictMono (lqFamP.famBd_lt n), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
