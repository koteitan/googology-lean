import Googology.Trans.PoR.InaccPsi.R2.CvCopy
import Googology.Trans.PoR.InaccPsi.R2.CxRoad

/-!
# The crossing relations at the named restarts by copy maps (the realizer step of CROSS-LIM)

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `P' = Nc.ncPp S`, `ρ_λ = υ_λ`, `r(λ) = cdR S λ`, Range = `CdRange`,
LOWER = `CdLOWER`.  The docs' proof of CROSS-LIM copies every finite configuration above a named restart
`a` to a configuration just below `a`, whose bottom is a restart `ρ_μ` of the range of ENUM-REACH
(code `< P'`) and whose top lies below `r(μ)`.  This file states that step with the copying principle
`Cv.cvLe1_of_maps` and proves what is left of it in `R₂^C`:

* `cvM_GP`, `cvM_restart`: `m* = P(Ω_ω)` is a `Γ`-point, hence a restart;
* `cvStd_left`: a restart `ρ_λ` is never the left end of a standard pair;
  `CvNoPair a b`: no `≤₂`-pair `(x, y)` with `x < a ≤ y < b` and none `(a, y)` with `a < y < b`;
  `cvNoPair_of_nu`: `CvNoPair a b` holds at every restart `a = ρ_λ` with `b ≤ ν_C` (below `ν_C` every
  `<₂`-pair is standard, and no standard pair straddles or starts at a restart);
* `CvReal S a b` (**the realizer maps** for `a ≤₁ b`): maps `D_k` as in `Cv.cvLe1_of_maps` with
  `D_k(a) = ρ_{μ_k}` for a restart `μ_k` of the range, `D_k(y) ≤ r(μ_k)` on `[a, b)`, keeping `≤₁`,
  `≤₂` on the pairs of `(a, b)`; `cvLe1_of_real`: LOWER, `CvNoPair a b` and `CvReal S a b` give
  `a ≤₁ b` (the pairs `(a, y)` of `≤₁` are carried by LOWER at `μ_k`); `CvRealCof`: realizer maps for
  cofinally many targets `t ≤ b`, and `cvLe1_of_realCof`;
* `cvCL_of_real` (**(CL)**), `cvCROSS_of_real` (**CROSS**, the targets `P(Ω_ω + P'·(n+1) + c')`),
  `cvM_of_real` (**`m* ≤₁ L(1)`**), `cvT_of_real` (**T**), `cvNamed_of_real` (**`CxNamed`**);
* `cvRoad_front`, `cvRoad_rz`: `Cx.cxRoad_front` and `Cx.cxRoad_rz` with `CxNamed` replaced by the
  realizer maps at `m*`, `L(n+1)`, `L(ω)` and `CvNoPair` at `L(ω)`
  (`L(ω) ≤ ν_C` comes from `Cd.cdLow_enum`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cx

/-- **A restart is not the left end of a standard pair.** -/
theorem cvStd_left {c d lam : Ordinal.{0}} (hs : IsStd c d) (hl : IsRestartIdx lam)
    (hc : c = upsilon lam) : False := by
  obtain ⟨L, -, hnd, hcL, -⟩ := hs.parts
  have e : L = lam := upsilon_normal.strictMono.injective (hcL.symm.trans hc)
  subst e
  exact hnd (ri_iff.1 hl).2

/-- No `≤₂`-pair `(x, y)` with `x < a ≤ y < b`, and none `(a, y)` with `a < y < b`. -/
def CvNoPair (a b : Ordinal.{0}) : Prop :=
  (∀ x y, x < a → a ≤ y → y < b → ¬ le2 x y) ∧ (∀ y, a < y → y < b → ¬ le2 a y)

theorem cvNoPair_mono {a b b' : Ordinal.{0}} (h : CvNoPair a b) (hb : b' ≤ b) : CvNoPair a b' :=
  ⟨fun x y hx hy hyb => h.1 x y hx hy (hyb.trans_le hb), fun y hy hyb => h.2 y hy (hyb.trans_le hb)⟩

/-- **`CvNoPair` at a restart below `ν_C`.** -/
theorem cvNoPair_of_nu {a b lam : Ordinal.{0}} (hl : IsRestartIdx lam) (ha : a = upsilon lam)
    (hb : b ≤ nuC) : CvNoPair a b := by
  subst ha
  refine ⟨fun x y hx hy hyb h2 => ?_, fun y hy hyb h2 => ?_⟩
  · exact cxStd_straddle (std_of_lt_nuC (hyb.trans_le hb) (hx.trans_le hy) h2) hl hx hy
  · exact cvStd_left (std_of_lt_nuC (hyb.trans_le hb) hy h2) hl rfl

variable {S : InaccSeq.{0}}

/-- **`m* = L(0) = P(Ω_ω)` is a `Γ`-point** (`P(Ω_ω) = sup_n P(Ω_{n+2} + W)`, `Lw.lw_GP_Pv`,
`Lw.lw_GP_step`). -/
theorem cvM_GP : IsGP (Nc.ncL S 0) := by
  have e0 : Nc.ncL S 0 = Pv S (0 + Om ω) := by
    rw [Lw.lw_L_eq S, mul_zero, add_zero, zero_add]
  rw [e0]
  refine Lw.lw_GP_Pv (Om_isSuccLimit omega0_ne_zero) fun c hc => ?_
  rw [Om_of_ne_zero omega0_ne_zero] at hc
  obtain ⟨c', hc', hcc'⟩ := (isNormal_omega.lt_iff_exists_lt isSuccLimit_omega0).1 hc
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc'
  set η1 : Ordinal.{0} := Om (((n + 2 : ℕ)) : Ordinal.{0}) with hη1
  have hne : (((n + 2 : ℕ)) : Ordinal.{0}) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hSC : SC η1 := SC_Om hne
  have h1 : Om (1 : Ordinal.{0}) < η1 := Om_lt_Om.2 (by exact_mod_cast (by omega : 1 < n + 2))
  have hg : Bt.Good S η1 := by
    unfold Bt.Good; exact CSet.Om_mem (Lw.lw_nat_mem _ _ (n + 2))
  have hlt : η1 < Om ω := Om_lt_Om.2 (natCast_lt_omega0 _)
  have hW : W < Om ω := Lw.lw_W_lt_SC (SC_Om omega0_ne_zero) (Om_lt_Om.2 one_lt_omega0)
  refine ⟨η1 + W, ?_, ?_, Lw.lw_GP_step hg (Lw.lw_W_dvd_SC hSC h1)⟩
  · rw [zero_add]
    refine (hcc'.le.trans ?_).trans le_self_add
    rw [hη1, Om_of_ne_zero hne]
    exact omega_le_omega.2 (Nat.cast_le.2 (by omega))
  · rw [zero_add]
    exact ((SC_Om omega0_ne_zero).isPrincipal hlt hW).le

/-- **`m*` is a restart**: `m* = ρ_λ` with `λ = ι(Ω_ω)` a restart index. -/
theorem cvM_restart : ∃ l, IsRestartIdx l ∧ Nc.ncL S 0 = upsilon l := by
  have h := cvM_GP (S := S)
  rw [Lw.lw_L_eq S, mul_zero, add_zero] at h ⊢
  exact ⟨_, (Lw.lw_restart_of_GP h).1, (Lw.lw_restart_of_GP h).2⟩


/-- **The realizer maps for `a ≤₁ b`**: `c_k < a` cofinal in `a`; maps `D_k` that fix `[0, c_k)`, send
`[a, b)` strictly increasingly into `[c_k, a)`, keep and reflect `+` on `[0, c_k) ∪ [a, b)`, reflect
decomposability on `[a, b)`; `D_k(a) = ρ_{μ_k}` for a restart `μ_k` of the range with `D_k(y) ≤ r(μ_k)`
on `[a, b)`; and `D_k` keeps `≤₁` and `≤₂` on the pairs `a < y < y' < b`. -/
def CvReal (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∃ (c : ℕ → Ordinal.{0}) (D : ℕ → Ordinal.{0} → Ordinal.{0}) (μ : ℕ → Ordinal.{0}),
    (∀ k, c k < a) ∧ (∀ γ < a, ∃ k, γ < c k) ∧
    (∀ k, StrictMonoOn (D k) (Ico a b)) ∧
    (∀ k, ∀ x ∈ CvDom (c k) a b, ∀ y ∈ CvDom (c k) a b, ∀ z ∈ CvDom (c k) a b,
      (x + y = z ↔ D k x + D k y = D k z)) ∧
    (∀ k, ∀ y, a ≤ y → y < b → DecompR0 (D k y) → DecompR0 y) ∧
    (∀ k, ∀ x < c k, D k x = x) ∧
    (∀ k, ∀ y, a ≤ y → y < b → c k ≤ D k y ∧ D k y < a) ∧
    (∀ k, D k a = upsilon (μ k) ∧ CdRange S (μ k) ∧ ∀ y, a ≤ y → y < b → D k y ≤ cdR S (μ k)) ∧
    (∀ k, ∀ y y', a < y → y < y' → y' < b →
      (le1 y y' → le1 (D k y) (D k y')) ∧ (le2 y y' → le2 (D k y) (D k y')))

/-- **`a ≤₁ b` from the realizer maps**, LOWER and `CvNoPair a b`. -/
theorem cvLe1_of_real (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : CvReal S a b) : le1 a b := by
  obtain ⟨c, D, μ, hca, hcof, hDm, hDadd, hDdec, hDfix, hDwin, hDμ, hin⟩ := hR
  refine cvLe1_of_maps hab hca hcof hDm hDadd hDdec hDfix hDwin ?_ ?_ ?_
  · intro k y y' hy hyy' hy' h1
    rcases eq_or_lt_of_le hy with hya | hay
    · rw [← hya] at hyy' ⊢
      obtain ⟨e, hrange, hle⟩ := hDμ k
      have hlow : le1 (upsilon (μ k)) (cdR S (μ k)) := hL _ hrange
      have hmono : D k a < D k y' :=
        hDm k ⟨le_rfl, hyy'.trans hy'⟩ ⟨hyy'.le, hy'⟩ hyy'
      rw [e] at hmono ⊢
      exact le1_of_le_of_le1 hmono.le (hle y' hyy'.le hy') hlow
    · exact (hin k y y' hay hyy' hy').1 h1
  · intro k y y' hy hyy' hy' h2
    rcases eq_or_lt_of_le hy with hya | hay
    · rw [← hya] at hyy' h2
      exact absurd h2 (hP.2 y' hyy' hy')
    · exact (hin k y y' hay hyy' hy').2 h2
  · intro k x hx y hy hyb h2
    exact absurd h2 (hP.1 x y (hx.trans (hca k)) hy hyb)

/-- Realizer maps for cofinally many targets `t ≤ b`. -/
def CvRealCof (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ CvReal S a t

/-- **`a ≤₁ b` from realizer maps for cofinal targets.** -/
theorem cvLe1_of_realCof (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : CvRealCof S a b) : le1 a b :=
  le1_of_cofinal hab fun y hay hyb => by
    obtain ⟨t, hyt, htb, hRt⟩ := hR y hay hyb
    exact ⟨t, hyt, cvLe1_of_real hL (hay.trans hyt.le) (cvNoPair_mono hP htb) hRt⟩

/-- **(CL) from the realizer maps at the restarts `L(n+1)`** (targets cofinal in `L(n+2)`). -/
theorem cvCL_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : ∀ n : ℕ, CvRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) : CdCL S := by
  intro n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact cvLe1_of_realCof hL (Pp.ppL_lt_succ n).le
    (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (h n)

/-- **CROSS from the realizer maps at `L(n+1)` with the targets `P(Ω_ω + P'·(n+1) + c')`**, `c'`
cofinal in `P'`; hence (CL) by `Cx.cxCROSS_iff`. -/
theorem cvCROSS_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : ∀ n : ℕ, ∀ c < Nc.ncPp S, ∃ c', c ≤ c' ∧ c' < Nc.ncPp S ∧
      CvReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c'))) :
    CdCROSS S ∧ CdCL S := by
  have hX : CdCROSS S := by
    intro n c hc
    obtain ⟨c', hcc', hc'P, hR⟩ := h n c hc
    obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have h1 : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤
        Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') := by
      rw [Lw.lw_L_eq S]; exact Pv_mono le_self_add
    have h2 : Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have e2 : ((n + 2 : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) + 1 := Nat.cast_succ (n + 1)
      rw [e2, Pp.ppL_succ_eq]
      exact Pv_mono (add_le_add_right hc'P.le _)
    refine ⟨c', hcc', hc'P, cvLe1_of_real hL h1 (cvNoPair_of_nu hl e ?_) hR⟩
    exact h2.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)
  exact ⟨hX, cxCROSS_iff.1 hX⟩

/-- **`m* ≤₁ L(1)` from the realizer maps at `m*`.** -/
theorem cvM_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : CvRealCof S (Nc.ncL S 0) (Nc.ncL S 1)) : le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
  exact cvLe1_of_realCof hL (Pp.ppL_mono zero_le)
    (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) h

/-- **`T` from the realizer maps at `L(ω)`** and `CvNoPair` there. -/
theorem cvT_of_real (hL : CdLOWER S) (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (h : CvRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxT S :=
  cvLe1_of_realCof hL (Qq.qqL_lt_succ S).le hP h

/-- `CvNoPair` at `L(ω)` holds if `L(ω+1) ≤ ν_C`. -/
theorem cvNoPair_T_of_nu (h : Nc.ncL S (ω + 1) ≤ nuC) :
    CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)) := by
  obtain ⟨l, hl, e⟩ := Pp.ppL_omega_restart (S := S)
  exact cvNoPair_of_nu hl e h

/-- **The crossing relations at the named restarts from the realizer maps.** -/
theorem cvNamed_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h0 : CvRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, CvRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : CvRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S :=
  ⟨cvM_of_real hL hlow h0, cvCL_of_real hL hlow hn, cvT_of_real hL hP hw⟩

/-- **The road with `CxNamed` replaced by the realizer maps** (`Cx.cxRoad_front`). -/
theorem cvRoad_front (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : CvRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, CvRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : CvRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cxRoad_front hU hL hV hEQ htop hups
    (cvNamed_of_real hL (cdLow_enum hU hV) h0 hn hP hw) hmove hstd

/-- **The reduced road (`Cx.cxRoad_rz`) with `CxNamed` replaced by the realizer maps.** -/
theorem cvRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : CvRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, CvRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : CvRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hL' := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (cvNamed_of_real hL' (cdLow_enum hU' hV') h0 hn hP hw) hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Cv
