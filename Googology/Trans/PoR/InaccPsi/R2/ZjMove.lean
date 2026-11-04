import Googology.Trans.PoR.InaccPsi.R2.ZjRead
import Googology.Trans.PoR.InaccPsi.R2.XsTop

/-!
# The reading move over the base `Ω_ω`: every window code `θ⁺ ≤ m_λ < T*` moves (given the wall)

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `A' = A_{η_{λ'}}`, `θ = ψ_{Ω₂}(Ω_ω)`,
`θ⁺ = ψ_{Ω₂}(Ω_ω + 1)`, `T* = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂})` (`Rn.rnTW S Ω_ω`), `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂²) = sup_j K_j`.
A window `(n, λ, λ')` is `R2Skel.SkEX.SkWin S n λ λ'`.

* `zjB_W2`, `zjB_Kw`, `zjB_T` (**`B_n` fixes `Ω₂²`, `K_ω` and `T*`**);
* `zjKw_move` (**REFUTE-FIRST record (the move at the plateau)**: in every window `B_n Θ_λ(K_ω) = Θ_{λ'}(K_ω)`,
  with no wall: both readings are `ψ_{Ω₁}(· + θ + Ω₁²)`);
* `zjAtMove` (**every atom `θ < s < T*` moves** once the codes below it move: `Le.leDigMoveE` at the base `Ω_ω`,
  `Zj.zjTh` at `λ` and `λ'`, `Wr.wrWin` for `ψ_{Ω₁}(A + d)`);
* `zjMove` (**THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < T*`**, from `Wr.WrWallCF`: `Ld.ldGxStepRec` with the bound
  `T*`; extends `Xs.xsMove` from `K_{J+1}` to `T*`);
* `ZjTopW S` (**the reading move at every window code `m_λ ≥ T*`**, the new leaf), `zjTopK_of` (**`WrWallCF ∧ ZjTopW ⇒
  Xs.XsTopK`**), `zjTopW_of_xs` (`XsTopK ⇒ ZjTopW`), `zjTopW_of_target` (**NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧
  SkEX.SkKFar ⇒ ZjTopW`).

No new axiom.  New definition: the statement name `ZjTopW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

/-! ## Fixed points of `B_n` -/

/-- `B_n(Ω₂·Ω₂) = Ω₂·Ω₂`. -/
theorem zjB_W2 {n : ℕ} : MvD S (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) ∧
    Bc.bcB S n (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  have hne : ω ^ (Om (1 + 1 : Ordinal.{0}) + Om (1 + 1)) ≠ Om (1 + 1) + Om (1 + 1) := by
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om (1 + 1) * ω := by
      have e2 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) = Om (1 + 1) * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
      rw [e2]; exact (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (by exact_mod_cast natCast_lt_omega0 2)
    have h2 : Om (1 + 1 : Ordinal.{0}) * ω ≤ ω ^ (Om (1 + 1) + Om (1 + 1)) := by
      rw [ldW2_eq]; exact opow_le_opow_right omega0_pos (add_le_add_right (Order.one_le_iff_ne_zero.2
        ldOm2_SC.1.ne') _)
    rw [h] at h2
    exact absurd h1 (not_lt.2 h2)
  obtain ⟨hDo, hBo⟩ := mvB_opow (k := n) hDs hne
  rw [ldOm2sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB2]⟩

/-- `B_n(K_ω) = K_ω`, `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂·Ω₂)`. -/
theorem zjB_Kw {n : ℕ} : MvD S (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) =
      S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := zjB_W2 (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hD2
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa
    (CSet.add_mem (zjOmW_own _) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _)))
  exact ⟨hDs, by rw [hBs, hBa, hBW, hB2]⟩

/-- `B_n(T*) = T*`. -/
theorem zjB_T {n : ℕ} : MvD S (rnTW S (Om ω)) ∧ Bc.bcB S n (rnTW S (Om ω)) = rnTW S (Om ω) := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := zjB_W2 (S := S) (n := n)
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hD2
  rw [hB2] at hBo
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDo
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (CSet.add_mem (zjOmW_own _) (leWe_mem (mxOm2_mem _ _)))
  refine ⟨hDs, ?_⟩
  unfold rnTW leWe; rw [hBs, hBa, hBW, hBo]

theorem zjB_two {n : ℕ} : MvD S (1 + 1 : Ordinal.{0}) ∧ Bc.bcB S n (1 + 1 : Ordinal.{0}) = 1 + 1 := by
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD, hB⟩ := mvB_add (k := n) hD1 hD1
  exact ⟨hD, by rw [hB, Mw.mwB_one]⟩

/-- `θ + x ≤ θ·ω` for `x < θ`. -/
theorem zjTh_add_le {x : Ordinal.{0}} (hx : x < ConjT.th S) : ConjT.th S + x ≤ ConjT.th S * ω := by
  have h1 : ConjT.th S + x < ConjT.th S * 2 := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    exact (add_lt_add_iff_left _).2 hx
  exact h1.le.trans (mul_le_mul_right (natCast_lt_omega0 2).le _)

theorem zjOe2_lt_th : leOe (1 + 1 : Ordinal.{0}) < ConjT.th S := by
  rw [zjOe2_eq]
  have hθSC := ConjT.SC_th S
  have hΩθ : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have e : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  rw [e]
  conv_rhs => rw [← gg_SC_eps hθSC]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (hθSC.isPrincipal hΩθ hΩθ)

/-! ## The window data -/

theorem zjWin_A {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    Om ω + Om ω ≤ ConjT.Aη S (cdEta S l) ∧ Om ω + Om ω ≤ ConjT.Aη S (cdEta S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨-, hX', -, hown', -, -, -, -, -⟩ := Wr.wrWin hR h1 hr hl' hB
  have hL0 := Xs.xsL0_lt (S := S) n
  have h0' : Pv S (Om ω) ≤ upsilon l' := by
    rw [← hB, ← Bc.bcB_fix' (S := S) n _ hL0]
    exact (Bc.bcB_mono' (S := S) n (show Pv S (Om ω) ∈ Set.Iio (Bc.bcC S (n + 1)) from (hL0.trans h1).trans h2)
      (show upsilon l ∈ Set.Iio (Bc.bcC S (n + 1)) from h2) (hL0.trans h1)).le
  exact ⟨Xs.xsA_win hl h1 h2, Xs.xsA_ge hl' hX' hown' h0'⟩

/-- **REFUTE-FIRST record (the move at the plateau)**: in every window, `B_n K_ω = K_ω` and
`B_n Θ_λ(K_ω) = Θ_{λ'}(K_ω)` (no wall). -/
theorem zjKw_move {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    Bc.bcB S n (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) =
        S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) ∧
      Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)))) =
        gxTh (upsilon l') (ldAtR S l') (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  refine ⟨zjB_Kw.2, ?_⟩
  rw [zjKw_read hl hX hown hAW, zjKw_read hl' hX' hown' hAW']
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  obtain ⟨hD2, hB2⟩ := zjB_two (S := S) (n := n)
  have h2L : (1 + 1 : Ordinal.{0}) < Bc.bcC S (n + 1) := by
    rw [one_add_one_eq_two]
    exact_mod_cast (natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
  obtain ⟨hDO, hBO⟩ := leB_Oe1 (S := S) (n := n) (h2L.trans hc1) h2L
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDO
  have hÂ := zjHat hl hX hown hAW
  have hlt2 : (1 + 1 : Ordinal.{0}) < S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + leOe (1 + 1))) (Om 1) := by
    rw [one_add_one_eq_two]
    exact_mod_cast (natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC (SC_psi Low.InR_Om_one _))
  have hownd : ConjT.Aη S (cdEta S l) + (ConjT.th S + leOe (1 + 1)) ∈
      S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + leOe (1 + 1)))
        (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + leOe (1 + 1))) (Om 1)) := by
    rw [← add_assoc] at hlt2 ⊢
    exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leOe_mem (CSet.of_lt hlt2))
  have hbd : S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + leOe (1 + 1))) (Om 1) < Bc.bcC S (n + 1) :=
    (Xs.xsLt_delta hl hX (zjTh_add_le zjOe2_lt_th)).trans hδr
  rw [add_assoc, hBψ _ hDd hownd hbd, hBd, hBθ, hBO, hB2, ← add_assoc]

/-! ## The atom move over `Ω_ω` -/

/-- **Every atom `θ < s < T*` moves** once the codes below it move. -/
theorem zjAtMove {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    ∀ s ∈ ldAtR S l, ConjT.th S < s → s < rnTW S (Om ω) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < rnTW S (Om ω) ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < rnTW S (Om ω) ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  intro s hs hθs hsT IHx
  obtain ⟨e, c, v, heT, hownc, rfl, hth, hownv, hv, -⟩ := zjTh hl hX hown hAW s hs hθs hsT
  have hb := zjBaseE hl hX hown hAW heT
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDe, hDc, hDs, hBs, hDv, hBown⟩ := leDigMoveE (n := n) (l' := l') hl hX hownc hb hDW
    (fun x hx hxs => by
      obtain ⟨h1, h2, -, h4, h5⟩ := IHx x hx hxs
      exact ⟨h1, h2, h4, h5⟩)
  rw [hBW] at hBown hBs
  have hownα := leOwnH_own hl hX hownc hb
  obtain ⟨hDa, hBa⟩ := mxB_atom (n := n) hDs hownα
  obtain ⟨hDT, hBT⟩ := zjB_T (S := S) (n := n)
  have hBeT : Bc.bcB S n e < rnTW S (Om ω) := by
    have := (mvB_lt_iff (k := n) hDe hDT).2 heT; rwa [hBT] at this
  have hb' := zjBaseE hl' hX' hown' hAW' hBeT
  obtain ⟨hBH, hBA⟩ := leOwnH_mem hl' hX' hBown hb'
  have hownB := leOwnH_own hl' hX' hBown hb'
  obtain ⟨hth', -, -, hBcW⟩ := zjOwn_read hl' hX' hown' hAW' hBown hBeT
  have hBcWW : Bc.bcB S n c < leWe (Om (1 + 1)) :=
    hBcW.trans_le (leWe_mono (hBeT.trans zjT_lt_Om2).le)
  -- `v < θ`
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hΘe1 : gxTh (upsilon l) (ldAtR S l) e < Om 1 := by
    rcases eq_or_ne e 0 with rfl | he0
    · rw [gxTh_zero]; exact Om_pos one_ne_zero
    have hec := leOwnH_code hl hX hownc (heT.trans zjT_lt_Om2)
    have hT := zjTop_read hl hX hown hAW hec (Order.one_le_iff_ne_zero.2 he0) heT
    have heTe : e < leTe S e (Om ω) := hb.2.2.2.2 e hec le_rfl
    refine (gxTh_lt hec heTe).trans ?_
    rw [hT]; exact psi_lt Low.InR_Om_one _
  have hvG : v < S.psi 0 (Om (1 + 1)) := hv.trans (leOe_lt_SC hG1 hΩG1 (hΘe1.trans hΩG1)).1
  have hvθ : v < ConjT.th S := hvG.trans_le (psi_mono (S := S) (InR_Om_succ 1) zero_le).1
  have hdθ := zjTh_add_le hvθ
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDv
  have hownd : ConjT.Aη S (cdEta S l) + (ConjT.th S + v) ∈ S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + v))
      (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1)) := by
    rw [← add_assoc]; exact hownv
  have hbd : S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1) < Bc.bcC S (n + 1) :=
    (Xs.xsLt_delta hl hX hdθ).trans hδr
  refine ⟨hDa, ?_, ?_, ?_, ?_⟩
  · rw [hBa, hBs]; exact ⟨_, hBH, hBA, rfl⟩
  · rw [hBa, hBs]
    have hlt : Om ω + Bc.bcB S n c < Om ω + leWe (Om (1 + 1)) := (add_lt_add_iff_left _).2 hBcWW
    unfold rnTW
    exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt ((psi_mono (S := S) (InR_Om_succ 1) hlt.le).2 hownB)
  · rw [hth, add_assoc]; exact hbd
  · rw [hBa, hBs, hth', hth, add_assoc (ConjT.Aη S (cdEta S l)), hBψ _ hDd hownd hbd, hBd, hBθ, add_assoc]

/-! ## The reading move at the codes `θ⁺ ≤ m_λ < T*` -/

/-- The atom move above `θ` below a bound `K` (a statement name for the generic reading move). -/
def ZjAtK (S : InaccSeq.{0}) (K : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, ConjT.th S < s → s < K →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < K ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < K ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **THE GENERIC READING MOVE**: for an SC bound `θ⁺ ≤ K ≤ P′` at which the atoms above `θ` move (`ZjAtK S K`),
the wall gives the reading move at every window code `θ⁺ ≤ m_λ < K`. -/
theorem zjMoveGen (hW : Wr.WrWallCF S) {K : Ordinal.{0}} (hKSC : SC K) (hPK : ljThP S ≤ K)
    (hKP : K ≤ Nc.ncPp S) (hAK : ZjAtK S K) : ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ljThP S ≤ cdCode S l → cdCode S l < K →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  intro n l l' hR h1 hr hl' hB hP hK
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hX, hX', hown, hown', hpv, hpv', -, -, -⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hg, -, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  obtain ⟨hAW, -⟩ := zjWin_A hR h1 hr hl' hB
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  set e := cdExp η with he_def
  have hK2 : K < Om (1 + 1) := hKP.trans_lt (psi_lt (InR_Om_succ 1) _)
  have hΩP : Om (1 : Ordinal.{0}) < ljThP S := ljOm1_lt_ThP
  -- the code is the last exponent
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : K ≤ cdPi S η := hKP.trans (psi_mono (S := S) (InR_Om_succ 1) hAW).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hωe : (ω : Ordinal.{0}) ≤ e := by
    by_contra h
    push Not at h
    have hc : cdCode S l = e - 1 := by
      show cdCodeOf S η = _; rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_pos h]
    have h3 : cdCode S l < ω := hc ▸ (Ordinal.sub_le_self _ _).trans_lt h
    exact absurd (h3.trans ((Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans hΩP)) (not_lt.2 hP)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heK : e < K := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hpv] at this
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨η', -, hBη', hη', hexp'⟩ := ljExp_move hl.1 h1 h2 hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hρ'SC : SC (upsilon l') := hpv' ▸ SC_psi Low.InR_Om_one _
  have hρ'1 : upsilon l' < Om 1 := hpv' ▸ psi_lt Low.InR_Om_one _
  have hatom : ∀ s ∈ ldAtR S l, s < K →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < K ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < K ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
    intro s hs hsK IHx
    rcases lt_or_ge s (ljThP S) with hsP | hsP
    · have hsθ := ljAt_le_th hs hsP
      obtain ⟨a1, a2, a3, a4, a5⟩ := Wr.wrAtLow hW hR h1 hr hl' hB s hs hsP (fun x hx hxs => by
        obtain ⟨b1, b2, -, b4, b5⟩ := IHx x hx hxs
        refine ⟨b1, b2, ?_, b4, b5⟩
        obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
        exact (((mvB_lt_iff b1 hDθ).2 (hxs.trans_le hsθ)).trans_eq hBθ).trans Lj.ljTh_lt_ThP)
      exact ⟨a1, a2, a3.trans_le hPK, a4, a5⟩
    · exact hAK n l l' hR h1 hr hl' hB s hs (Lj.ljTh_lt_ThP.trans_le hsP) hsK IHx
  obtain ⟨hDe, -, hBeK, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw hKSC (ljOm1_lt_ThP.le.trans hPK) hatom e hge heK
  have hΩe : Om (1 : Ordinal.{0}) < e := hΩP.trans_le (hcode ▸ hP)
  have hΩBe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 hΩe
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩBe.le
  have hBe2 : Bc.bcB S n e < Om (1 + 1) := hBeK.trans hK2
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBe2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' hBe2.le]
  exact hEq.symm

theorem zjT_le_Pp : rnTW S (Om ω) ≤ Nc.ncPp S :=
  (psi_mono (S := S) (InR_Om_succ 1) zjWW_lt.le).1

/-- **THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < T*`**, from the code-free wall. -/
theorem zjMove (hW : Wr.WrWallCF S) : ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ljThP S ≤ cdCode S l → cdCode S l < rnTW S (Om ω) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') :=
  zjMoveGen hW (rnTW_SC _) zjThP_le_T zjT_le_Pp fun _ _ _ hR h1 hr hl' hB => zjAtMove hR h1 hr hl' hB

/-! ## The top: the codes `≥ T*` -/

/-- **The reading move at every window code `m_λ ≥ T* = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂})`** (the new leaf). -/
def ZjTopW (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → rnTW S (Om ω) ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`WrWallCF ∧ ZjTopW ⇒ Xs.XsTopK`.** -/
theorem zjTopK_of (hW : Wr.WrWallCF S) (hT : ZjTopW S) : Xs.XsTopK S := by
  intro n l l' hW' hK
  by_cases hm : cdCode S l < rnTW S (Om ω)
  · obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW'
    have hP : ljThP S ≤ cdCode S l := by
      refine rnThP_le_MW.trans ?_
      rw [← Xs.xsK_one]; exact hK 1
    exact zjMove hW n l l' hR h1 hr hl' hB hP hm
  · exact hT n l l' hW' (not_lt.1 hm)

/-- `XsTopK ⇒ ZjTopW` (`K_j < K_ω < T*`). -/
theorem zjTopW_of_xs (h : Xs.XsTopK S) : ZjTopW S := fun n l l' hW' hT =>
  h n l l' hW' fun j => ((zjK_lt_Kw j).trans zjKw_lt_T).le.trans hT

/-- **NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧ SkEX.SkKFar ⇒ ZjTopW` (the road's target gives the leaf). -/
theorem zjTopW_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : R2Skel.SkEX.SkKFar S) :
    ZjTopW S :=
  zjTopW_of_xs (Xs.xsTopK_of_target hν hEQ hK)

/-- The reading move at the codes `K_ω ≤ m_λ < T*` (the part of `Xs.XsTopK` now proved, given the wall). -/
theorem zjTopK_below (hW : Wr.WrWallCF S) :
    ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → (∀ j, Xs.xsK S j ≤ cdCode S l) →
      cdCode S l < rnTW S (Om ω) →
      Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  intro n l l' hW' hK hm
  obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW'
  have hP : ljThP S ≤ cdCode S l := by
    refine rnThP_le_MW.trans ?_
    rw [← Xs.xsK_one]; exact hK 1
  exact zjMove hW n l l' hR h1 hr hl' hB hP hm

end Googology.Trans.PoR.InaccPsi.R2.Zj
