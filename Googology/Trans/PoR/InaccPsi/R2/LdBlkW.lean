import Googology.Trans.PoR.InaccPsi.R2.LdBlk

/-!
# The blocks `ψ_{Ω₂}(Ω₂·k + c)`, `k < ω`, and the reading moves below `F_ω = ψ_{Ω₂}(Ω₂·ω)`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)`
(`= Θ_λ` below `Ω₂`), `β_k = Ω₂·k`, `F_k = ψ_{Ω₂}(β_k)` (`F_0 = Γ_{Ω₁+1}`, `F_1 = sup_j K_j`), `F_ω = ψ_{Ω₂}(Ω₂·ω)`
(`ldFw`), `m_λ` the code of `λ`.

* `ldBlkW_base` (**`Θ_λ(ψ_{Ω₂}(Ω₂·k)) = ψ_{Ω₁}(A + 1 + Ω₁·k)`** for every `k < ω` and every own `A` with
  `ψ_{Ω₁}(A) = ρ_λ`), `ldBlkW_th` (**`Θ_λ(ψ_{Ω₂}(Ω₂·k + c)) = ψ_{Ω₁}(A + 1 + Ω₁·k + Θ_λ(c))`** for every code
  `c < F_{k+1}`);
* `ldAtR_lt_Fw` (**every atom of `H_λ` below `F_ω` is `ψ_{Ω₂}(Ω₂·k + c)`** with `c ∈ H_λ`, `c < F_{k+1}`): this
  describes `H_λ ∩ F_ω` and `Θ_λ` on it completely;
* `ldAtMove_Fw` (**every atom below `F_ω` moves** once the codes below it move: `B_n(ψ_{Ω₂}(Ω₂·k + c)) =
  ψ_{Ω₂}(Ω₂·k + B_n c)` and `B_n(ψ_{Ω₁}(A + 1 + Ω₁·k + Θ c)) = ψ_{Ω₁}(A' + 1 + Ω₁·k + B_n(Θ c))`);
* `ldThMove_Fw` (**`MxThMove` at every long code `m_λ < F_ω`**, no hypothesis);
* `LdThMoveQ S` (a hypothesis name): `MxThMove` at the codes `F_ω ≤ m_λ ≤ θ`; `ldThMoveW_of_Q` (**`LdThMoveQ` gives
  `Mx.MxThMoveW`**), `ldThMoveQ_of_W` (the converse), `ldRoadQ`.

No new axiom.  New definitions: `ldB2`, `ldFw`, the hypothesis name `LdThMoveQ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- The base `β_k = Ω₂·k`. -/
noncomputable def ldB2 (k : ℕ) : Ordinal.{0} := Om (1 + 1) * (k : Ordinal.{0})

/-- `F_ω = ψ_{Ω₂}(Ω₂·ω)`. -/
noncomputable def ldFw (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1) * ω) (Om (1 + 1))

/-! ## Arithmetic of the bases -/

theorem ldMulNat_lt {p x : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (hx : x < p) :
    ∀ k : ℕ, x * (k : Ordinal.{0}) < p
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact lt_of_le_of_lt zero_le hx
  | k + 1 => by rw [Nat.cast_succ, mul_add_one]; exact hp (ldMulNat_lt hp hx k) hx

theorem ldB2_mem (k : ℕ) (a b : Ordinal.{0}) : ldB2 k ∈ S.CSet a b := mul_nat_mem (mxOm2_mem a b) k

theorem ldB2_succ (k : ℕ) : ldB2 k + Om (1 + 1) = ldB2 (k + 1) := by
  unfold ldB2; rw [Nat.cast_succ, mul_add_one]

theorem ldB2_dvd (k : ℕ) : Om (1 + 1) ∣ ldB2 k := dvd_mul_right _ _

theorem ldB2_own (k : ℕ) : ∀ d, d ≤ Om (1 + 1) → ldB2 k ∈ S.CSet (ldB2 k + d) (S.psi (ldB2 k + d) (Om (1 + 1))) :=
  fun _ _ => ldB2_mem k _ _

theorem ldB2_lt_OmW (k : ℕ) : ldB2 k < Om ω :=
  ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW k

theorem ldB2_top_lt (l : Ordinal.{0}) (k : ℕ) : ldB2 k + Om (1 + 1) < ConjT.Aη S (cdEta S l) := by
  rw [ldB2_succ]; exact (ldB2_lt_OmW (k + 1)).trans_le le_self_add

theorem ldTop_B2 (k : ℕ) : ldTop S (ldB2 k) = S.psi (ldB2 (k + 1)) (Om (1 + 1)) := by
  unfold ldTop; rw [ldB2_succ]

/-! ## The readings of the blocks -/

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂·k)) = ψ_{Ω₁}(A + 1 + Ω₁·k)`.** -/
theorem ldBlkW_base {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ k : ℕ, gxTh (upsilon l) (ldAtR S l) (S.psi (ldB2 k) (Om (1 + 1))) =
      S.psi (A + 1 + Om 1 * (k : Ordinal.{0})) (Om 1)
  | 0 => by
    rw [show ldB2 0 = 0 by unfold ldB2; rw [Nat.cast_zero, mul_zero], Nat.cast_zero, mul_zero, add_zero]
    exact ldBlk_zero hA hρ
  | k + 1 => by
    have hÂ : A + 1 + Om 1 * (k : Ordinal.{0}) ∈
        S.CSet (A + 1 + Om 1 * (k : Ordinal.{0})) (S.psi (A + 1 + Om 1 * (k : Ordinal.{0})) (Om 1)) :=
      CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA)
        (CSet.one_mem _ _)) (mul_nat_mem (CSet.Om_mem (CSet.one_mem _ _)) k)
    have h := ldBlk_next hl hX (ldB2_own k) (ldB2_dvd k) (ldB2_mem k _ _) (ldB2_top_lt l k) hÂ
      (ldBlkW_base hl hX hA hρ k)
    rw [ldTop_B2, add_assoc, ← mul_add_one, ← Nat.cast_succ] at h
    exact h

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂·k + c)) = ψ_{Ω₁}(A + 1 + Ω₁·k + Θ_λ(c))`** for every code `c < F_{k+1}`. -/
theorem ldBlkW_th {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (k : ℕ) {c : Ordinal.{0}}
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S (ldB2 k)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (ldB2 k + c) (Om (1 + 1))) =
      S.psi (A + 1 + Om 1 * (k : Ordinal.{0}) + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hÂ : A + 1 + Om 1 * (k : Ordinal.{0}) ∈
      S.CSet (A + 1 + Om 1 * (k : Ordinal.{0})) (S.psi (A + 1 + Om 1 * (k : Ordinal.{0})) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA)
      (CSet.one_mem _ _)) (mul_nat_mem (CSet.Om_mem (CSet.one_mem _ _)) k)
  exact ldBlk_step hl hX (ldB2_own k) (ldB2_dvd k) (ldB2_mem k _ _) (ldB2_top_lt l k) hÂ
    (ldBlkW_base hl hX hA hρ k) c hc hcF

/-! ## `F_ω` -/

theorem ldW2_eq : Om (1 + 1 : Ordinal.{0}) * ω = ω ^ (Om (1 + 1) + 1) := by
  rw [opow_add, opow_one, Low.opow_eq_self_of_SC ldOm2_SC]

theorem ldW2_mem (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) * ω ∈ S.CSet a b := by
  rw [ldW2_eq]
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.succ_mem (mxOm2_mem (S := S) a b))
  rwa [veblen_zero_apply] at this

theorem ldW2_lt_OmW : Om (1 + 1 : Ordinal.{0}) * ω < Om ω := by
  rw [ldW2_eq, ← Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 ((Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW
    (one_lt_omega0.trans (omega0_lt_Om omega0_ne_zero)))

theorem ldB2_lt_W2 (k : ℕ) : ldB2 k < Om (1 + 1) * ω :=
  (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (natCast_lt_omega0 k)

theorem ldFw_SC : SC (ldFw S) := SC_psi (InR_Om_succ 1) _
theorem ldFw_lt_Om2 : ldFw S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ldOm1_lt_Fw : Om (1 : Ordinal.{0}) < ldFw S := (psiS_bounds (S := S) _ 1).1

theorem ldFk_lt_Fw (k : ℕ) : S.psi (ldB2 k) (Om (1 + 1)) < ldFw S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (ldB2_lt_W2 k) (ldB2_mem k _ _)

theorem ldTopB2_lt_Fw (k : ℕ) : ldTop S (ldB2 k) < ldFw S := by rw [ldTop_B2]; exact ldFk_lt_Fw (k + 1)

theorem ldFw_lt_th : ldFw S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ldW2_lt_OmW (ldW2_mem _ _)

/-- **Every atom of `H_λ` below `F_ω` is `ψ_{Ω₂}(Ω₂·k + c)` with `c ∈ H_λ`, `c < F_{k+1}`.** -/
theorem ldAtR_lt_Fw {l ηx s : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hs : s ∈ ldAtR S l) (hsF : s < ldFw S) :
    ∃ k : ℕ, ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S (ldB2 k) ∧
      s = S.psi (ldB2 k + c) (Om (1 + 1)) := by
  obtain ⟨a, ha, -, rfl⟩ := hs
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have haW : a < Om (1 + 1) * ω := by
    by_contra h
    push Not at h
    exact absurd hsF (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  obtain ⟨k, hk⟩ := lt_omega0.1 ((Ordinal.lt_mul_iff_div_lt hΩ0).1 haW)
  have hdec : a = ldB2 k + a % Om (1 + 1) := by
    unfold ldB2; rw [← hk]; exact (Ordinal.div_add_mod a _).symm
  have hcH : a % Om (1 + 1) ∈ cdHull S l := ldModK_mem ldOm2_SC ha
  have hc2 : a % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt a hΩ0
  rcases lt_or_ge (a % Om (1 + 1)) (ldTop S (ldB2 k)) with hcF | hcF
  · exact ⟨k, _, (ldHull_iff hl hX hc2).1 hcH, hcF, by rw [← hdec]⟩
  · refine ⟨k + 1, 0, GxCl.zero (mvUps_pos hl), (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), ?_⟩
    rw [add_zero]
    apply le_antisymm
    · rw [hdec, ← ldB2_succ]
      exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hc2.le)).1
    · rw [← ldTop_B2, hdec]; exact ldTop_ge (ldB2_own k) (ldB2_dvd k) hcF

/-! ## `B_n` on the bases and the move of the atoms below `F_ω` -/

theorem ldB_mulNat {n : ℕ} {x : Ordinal.{0}} (hD : MvD S x) (hB : Bc.bcB S n x = x) :
    ∀ k : ℕ, MvD S (x * (k : Ordinal.{0})) ∧ Bc.bcB S n (x * (k : Ordinal.{0})) = x * (k : Ordinal.{0})
  | 0 => by
    rw [Nat.cast_zero, mul_zero]
    exact ⟨mvD_of_lt (lt_of_le_of_lt zero_le (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))), Bc.bcB_zero n⟩
  | k + 1 => by
    obtain ⟨hDk, hBk⟩ := ldB_mulNat hD hB k
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDk hD
    rw [Nat.cast_succ, mul_add_one]
    exact ⟨hDs, by rw [hBs, hBk, hB]⟩

theorem ldB_B2 {n : ℕ} (k : ℕ) : MvD S (ldB2 k) ∧ Bc.bcB S n (ldB2 k) = ldB2 k :=
  ldB_mulNat (ldOm2_D (k := n)).1 (ldOm2_D (k := n)).2 k

theorem ldB_top {n : ℕ} (k : ℕ) : MvD S (ldTop S (ldB2 k)) ∧ Bc.bcB S n (ldTop S (ldB2 k)) = ldTop S (ldB2 k) := by
  obtain ⟨hD, hB⟩ := ldB_B2 (S := S) (n := n) (k + 1)
  obtain ⟨hD', hB'⟩ := mxB_atom (n := n) hD (ldB2_mem (S := S) (k + 1) _ _)
  rw [ldTop_B2]
  exact ⟨hD', by rw [hB', hB]⟩

/-- **Every atom below `F_ω` moves** once the codes below it move. -/
theorem ldAtMove_Fw {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hl' : IsRestartIdx l')
    (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ s ∈ ldAtR S l, s < ldFw S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ldFw S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ldFw S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hθ1 : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hθp : IsPrincipal (· + ·) (ConjT.th S) := (SC_psi (InR_Om_succ 1) _).isPrincipal
  intro s hs hsF IHx
  obtain ⟨k, c, hc, hcF, rfl⟩ := ldAtR_lt_Fw hl hX hs hsF
  have hcs : c < S.psi (ldB2 k + c) (Om (1 + 1)) := ldTop_gt (ldB2_own k) (ldB2_dvd k) hcF
  obtain ⟨hDc, hBc, -, hΘcX, hΘc⟩ := IHx c hc hcs
  obtain ⟨hDβ, hBβ⟩ := ldB_B2 (S := S) (n := n) k
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDc
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (ldOwn (ldB2_own k) (ldB2_dvd k) hcF)
  obtain ⟨hDT, hBT⟩ := ldB_top (S := S) (n := n) k
  have hBcF : Bc.bcB S n c < ldTop S (ldB2 k) := by rw [← hBT]; exact (mvB_lt_iff hDc hDT).2 hcF
  -- the reading of `s`
  have hth := ldBlkW_th hl hX hA hρ k hc hcF
  set γ := gxTh (upsilon l) (ldAtR S l) c with hγ
  set d := 1 + Om 1 * (k : Ordinal.{0}) + γ with hd
  have hAd : A + 1 + Om 1 * (k : Ordinal.{0}) + γ = A + d := by rw [hd, add_assoc, add_assoc, add_assoc]
  rw [hAd] at hth
  have hγs : γ < S.psi (A + d) (Om 1) := by rw [← hth]; exact gxTh_lt hc hcs
  have hγ1 : γ < Om 1 := hγs.trans (psi_lt Low.InR_Om_one _)
  have hdθ : d ≤ ConjT.th S :=
    (hθp (hθp (one_lt_Om1.trans hθ1) (ldMulNat_lt hθp hθ1 k)) (hγ1.trans hθ1)).le
  have hownd : A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) := by
    rw [← hAd]
    refine CSet.add_mem (CSet.add_mem (CSet.add_mem ?_ (CSet.one_mem _ _))
      (mul_nat_mem (CSet.Om_mem (CSet.one_mem _ _)) k)) (CSet.of_lt (hAd ▸ hγs))
    exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans (le_self_add.trans le_self_add))).2 hA
  -- `B_n d`
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDk1, hBk1⟩ := ldB_mulNat (n := n) (mvB_Om1 (S := S) (k := n)).1 (mvB_Om1 (S := S) (k := n)).2 k
  obtain ⟨hD1k, hB1k⟩ := mvB_add (k := n) hD1 hDk1
  have hDγ : MvD S γ := mvD_of_lt (hΘcX.trans hLw)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1k hDγ
  refine ⟨hDs, ?_, ?_, ?_, ?_⟩
  · rw [hBs, hBa, hBβ]
    exact ldBlk_atom hl' hX' (ldB2_mem k _ _) (ldB2_top_lt l' k) hBc hBcF
  · rw [hBs, hBa, hBβ]; exact (ldTop_lt (ldB2_own k) hBcF).trans (ldTopB2_lt_Fw k)
  · rw [hth]; exact hbX d hdθ
  · rw [hBs, hBa, hBβ, ldBlkW_th hl' hX' hA' hρ' k hBc hBcF, hΘc, hth, hBψ d hDd hownd hdθ, hd, hBd,
      hB1k, mwB_one, hBk1]
    simp only [add_assoc]

/-! ## The reading moves below `F_ω` -/

/-- **`MxThMove` at every long code `m_λ < F_ω`.** -/
theorem ldThMove_Fw {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < ldFw S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have hWA : Om ω ≤ A := le_self_add
  -- the code is `e`
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : ldFw S ≤ cdPi S η := (psi_mono (S := S) (InR_Om_succ 1) (ldW2_lt_OmW.le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heF : e < ldFw S := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heF.trans ldFw_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the bounds `ψ_{Ω₁}(A + d) < L(n+2)` for `d ≤ θ`
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hρSC : SC (upsilon l) := hρA ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDe, -, hBeF, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw ldFw_SC ldOm1_lt_Fw.le
    (ldAtMove_Fw hl hl' hX hX' hown hA' hρA hρA' hbX hBψ) e hge heF
  -- the image code is `B_n e`
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeF.trans ldFw_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeF.trans ldFw_lt_Om2).le]
  exact hEq.symm

/-- `MxThMove` at the long codes with `F_ω ≤ m_λ ≤ θ`. -/
def LdThMoveQ (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l ≤ ConjT.th S → ldFw S ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`LdThMoveQ` gives `MxThMoveW`.** -/
theorem ldThMoveW_of_Q (h : LdThMoveQ S) : MxThMoveW S := by
  intro n l l' hR h1 hr hl' hB hm he hθ _
  by_cases hK : cdCode S l < ldFw S
  · exact ldThMove_Fw hR h1 hr hl' hB he hK
  · exact h n l l' hR h1 hr hl' hB hm he hθ (not_lt.1 hK)

theorem ldKs_lt_Fw (j : ℕ) : mxKs S j < ldFw S := by
  have h := ldFk_lt_Fw (S := S) 1
  have e : ldB2 1 = Om (1 + 1) := by unfold ldB2; rw [Nat.cast_one, mul_one]
  rw [e] at h
  exact (ldKs_lt_F j).trans h

/-- `MxThMoveW` gives `LdThMoveQ` (so `LdThMoveQ` is not the stronger hypothesis). -/
theorem ldThMoveQ_of_W (h : MxThMoveW S) : LdThMoveQ S :=
  fun n l l' hR h1 hr hl' hB hm he hθ hF => h n l l' hR h1 hr hl' hB hm he hθ
    fun j => (ldKs_lt_Fw j).le.trans hF

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LdThMoveQ` and `L(ω+1) ≤ ν_C → MxEQth`.** -/
theorem ldRoadQ (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LdThMoveQ S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad5 hU hO hL hV hN hlh (fun hν => ldThMoveW_of_Q (hth hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Ld
