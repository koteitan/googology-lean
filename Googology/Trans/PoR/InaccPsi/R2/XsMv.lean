import Googology.Trans.PoR.InaccPsi.R2.XsRd

/-!
# The reading move past `M_W`: every window code `m_λ < K_{J+1}` moves (given the wall), far codes are `≥ K_ω`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `A' = A_{η_{λ'}}`, `θ = ψ_{Ω₂}(Ω_ω)`,
`β_γ = Ω_ω + Ω₂·γ` (`Xs.xsB`), `K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(β_{K_j})` (`Xs.xsK`, `K_1 = M_W`),
"window" = `CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart, `B_n ρ_λ = ρ_{λ'}`.

* `xsK_lt_succ`, `xsK_D` (**`B_n K_j = K_j`**), `xsK_code`, `xsK_read` (`Θ(K_{j+1}) = ψ_{Ω₁}(A + θ + Ω₁·Θ(K_j))`);
* `xsLt_delta` (`ψ_{Ω₁}(A + x) < δ_λ` for `x ≤ θ·ω`), `xsRead_lt` (**every block reading is below `δ_λ`**);
* `xsFar_ge` (**GUARD: a far window has `K_j ≤ m_λ` for every `j`**, unconditional beyond the window);
* `xsAt_cls` (**every atom `θ < s < K_{J+1}` is `ψ_{Ω₂}(β_γ + c)`, `γ < K_{J+1}`, `c < F^{β_γ}` codes**);
* `xsAtMove` (**the block atoms move**: `B_n ψ_{Ω₂}(β_γ + c) = ψ_{Ω₂}(β_{B_n γ} + B_n c)` and
  `Θ_{λ'}(B_n s) = B_n Θ_λ(s)`, by `Xs.xsBlk` at `λ` and `λ'` and `Ld.ldB_psi_add`, once the codes below move);
* `xsMove` (**THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < K_{J+1}`**, every `J`, from `Wr.WrWallCF`:
  `Ld.ldGxStepRec` with the bound `K_{J+1}`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

/-! ## The layers `K_j` -/

theorem xsK_lt_succ : ∀ j, xsK S j < xsK S (j + 1)
  | 0 => (gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := xsK_lt_succ j
    have hle : xsK S (j + 1) ≤ xsK S (j + 2) := (psi_mono (S := S) (InR_Om_succ 1) (xsB_mono IH.le)).1
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (xsB_lt IH) (xsB_mem (CSet.of_lt (IH.trans_le hle)))

theorem xsK_mono {j j' : ℕ} (h : j ≤ j') : xsK S j ≤ xsK S j' :=
  (strictMono_nat_of_lt_succ (fun k => xsK_lt_succ (S := S) k)).monotone h

theorem xsK_SC (j : ℕ) : SC (xsK S (j + 1)) := SC_psi (InR_Om_succ 1) _

theorem xsK_Om1 (j : ℕ) : Om (1 : Ordinal.{0}) < xsK S (j + 1) := (psiS_bounds (S := S) _ 1).1

theorem xsK_ownK (j : ℕ) : XsOwn S (xsK S j) := xsK_lt_succ j

theorem xsMW_le (J : ℕ) : rnMW S ≤ xsK S (J + 1) := by
  rw [← xsK_one]; exact xsK_mono (Nat.le_add_left 1 J)

/-- **`B_n K_j = K_j`.** -/
theorem xsK_D (n : ℕ) : ∀ j, MvD S (xsK S j) ∧ Bc.bcB S n (xsK S j) = xsK S j
  | 0 => ⟨mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))), Mw.mwB_one n⟩
  | j + 1 => by
    obtain ⟨hDK, hBK⟩ := xsK_D n j
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    have h0D : MvD S 0 := mvD_of_lt (Lw.lw_L_SC S ω).1
    have hmul := ldB_mulK (n := n) ldOm2_SC hD2 hB2 (fun x => x = xsK S j ∨ x = 0)
      (fun x hx => by rcases hx with rfl | rfl; exacts [hDK, h0D])
      (fun x hx hx0 => by
        rcases hx with rfl | rfl
        · rcases j with _ | i
          · have h1 : xsK S 0 = 1 := rfl
            rw [h1, Ordinal.log_one_right, opow_zero, Ordinal.sub_self]
            exact ⟨Or.inr rfl, Or.inr rfl⟩
          · have hE : ω ^ xsK S (i + 1) = xsK S (i + 1) := gg_SC_eps (xsK_SC i)
            have hl : log ω (xsK S (i + 1)) = xsK S (i + 1) := by
              conv_lhs => rw [← hE]
              exact Ordinal.log_opow one_lt_omega0 _
            rw [hl, hE, Ordinal.sub_self]
            exact ⟨Or.inl rfl, Or.inr rfl⟩
        · exact absurd rfl hx0)
      (fun x hx => by rcases hx with rfl | rfl; exacts [xsK_lt_Om2 j, ldOm2_SC.1]) (xsK S j) (Or.inl rfl)
    obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hmul.1
    have hown : xsB (xsK S j) ∈ S.CSet (xsB (xsK S j)) (S.psi (xsB (xsK S j)) (Om (1 + 1))) := by
      have := xsB_own (xsK_ownK (S := S) j) 0 zero_le; rwa [add_zero] at this
    obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psi2 (n := n) hDa hown
    refine ⟨hDs, ?_⟩
    show Bc.bcB S n (S.psi (Om ω + Om (1 + 1) * xsK S j) (Om (1 + 1))) =
      S.psi (Om ω + Om (1 + 1) * xsK S j) (Om (1 + 1))
    rw [hBs, hBa, hBW, hmul.2, hBK]

/-! ## Readings below `δ_λ` -/

/-- `θ + Ω₁·y + z ≤ θ·ω` for countable `y`, `z`. -/
theorem xsTail_le {y z : Ordinal.{0}} (hy : y < Om 1) (hz : z < Om 1) :
    ConjT.th S + Om 1 * y + z ≤ ConjT.th S * ω := by
  have hθSC := ConjT.SC_th S
  have hΩθ : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hOO : Om (1 : Ordinal.{0}) * Om 1 < ConjT.th S := by
    have e : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
    rw [e]
    conv_rhs => rw [← gg_SC_eps hθSC]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (hθSC.isPrincipal hΩθ hΩθ)
  have h1 : Om 1 * y + z < Om 1 * Om 1 := by
    have h2 : Om 1 * y + z < Om 1 * (y + 1) := by
      rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hz
    exact h2.trans_le (mul_le_mul_right (Order.add_one_le_of_lt hy) _)
  have h3 : ConjT.th S + Om 1 * y + z < ConjT.th S * 2 := by
    rw [add_assoc, show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    exact (add_lt_add_iff_left _).2 (h1.trans hOO)
  exact h3.le.trans (mul_le_mul_right (natCast_lt_omega0 2).le _)

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `ψ_{Ω₁}(A + x) < δ_λ` for `x ≤ θ·ω`. -/
theorem xsLt_delta {x : Ordinal.{0}} (hx : x ≤ ConjT.th S * ω) :
    S.psi (ConjT.Aη S (cdEta S l) + x) (Om 1) < cdDelta l := by
  obtain ⟨-, hιl, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hι : Bt.iota S (cdEta S l + ω) ≤ l + ω := by
    have := ldIota_add_le (S := S) (cdEta S l) ω
    rwa [hιl] at this
  have h1 : S.psi (ConjT.Aη S (cdEta S l) + x) (Om 1) ≤ upsilon (l + ω) := by
    calc S.psi (ConjT.Aη S (cdEta S l) + x) (Om 1)
          ≤ S.psi (ConjT.Aη S (cdEta S l + ω)) (Om 1) := by
            rw [Bt.A_add]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 hx)).1
      _ = upsilon (Bt.iota S (cdEta S l + ω)) := (Bt.ups_iota S _).symm
      _ ≤ upsilon (l + ω) := upsilon_normal.monotone hι
  exact h1.trans_lt (upsilon_normal.strictMono (lt_add_one _))

end Rst

section Win

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAb : Om ω + Om (1 + 1) * Om (1 + 1) ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAb

/-- The layers `K_j` are codes of `λ`. -/
theorem xsK_code : ∀ j, GxCl (upsilon l) (ldAtR S l) (xsK S j)
  | 0 => GxCl.small (gg_one_lt_of_SC (leRho hl hX).1)
  | j + 1 => GxCl.atom ⟨xsB (xsK S j), xsB_mem ((ldHull_iff hl hX (xsK_lt_Om2 j)).2 (xsK_code j)),
      le_self_add.trans_lt (xsB_A (xsK_lt_Om2 j) hAb), rfl⟩

/-- `Θ(K_{j+1}) = ψ_{Ω₁}(A + θ + Ω₁·Θ(K_j))`. -/
theorem xsK_read (j : ℕ) : gxTh (upsilon l) (ldAtR S l) (xsK S (j + 1)) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) (xsK S j)) (Om 1) :=
  xsBase hl hX hown hAb (xsK S j) (xsK_code hl hX hown hAb j) (xsK_lt_Om2 j)
    (fun γ' _ h' => xsK_own (j + 1) γ' (h'.trans_lt (xsK_lt_succ j)))

/-- **Every block reading is below `δ_λ`.** -/
theorem xsRead_lt {γ c : Ordinal.{0}} (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγ2 : γ < Om (1 + 1))
    (hown' : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → XsOwn S γ')
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S (xsB γ)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ + c) (Om (1 + 1))) < cdDelta l := by
  have hb := xsBlk hl hX hown hAb hγ hγ2 hown' c hc hcF
  have hs := hb
  have hγs : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := by
    have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hγ (hown' γ hγ le_rfl)
    rw [xsBase hl hX hown hAb γ hγ hγ2 hown'] at h1
    exact h1.trans (psi_lt Low.InR_Om_one _)
  have hcs : gxTh (upsilon l) (ldAtR S l) c < Om 1 := by
    have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc
      (ldTop_gt (xsB_own (hown' γ hγ le_rfl)) (xsB_dvd γ) hcF)
    rw [hb] at h1
    exact h1.trans (psi_lt Low.InR_Om_one _)
  rw [hs, add_assoc (ConjT.Aη S (cdEta S l) + ConjT.th S), add_assoc]
  exact xsLt_delta hl hX (by rw [← add_assoc]; exact xsTail_le hγs hcs)

/-- **GUARD: a far window code is at least every `K_j`**: if `δ_λ·ω ≤ Θ_λ(m)` then `K_j ≤ m` for every `j`. -/
theorem xsFar_ge {m : Ordinal.{0}} (hm2 : m ≤ Om (1 + 1)) (hw : cdDelta l * ω ≤ cdTheta S l m) :
    ∀ j, xsK S j ≤ m := by
  intro j
  by_contra hc
  push Not at hc
  have hK := (xsK_mono (S := S) (Nat.le_succ j))
  have h1 : cdTheta S l m ≤ gxTh (upsilon l) (ldAtR S l) (xsK S (j + 1)) := by
    rw [ldTheta hl hX hm2]; exact gxTh_mono (hc.le.trans hK)
  have hγ := xsK_code hl hX hown hAb j
  have h2 : gxTh (upsilon l) (ldAtR S l) (xsK S (j + 1)) < cdDelta l := by
    have := xsRead_lt hl hX hown hAb hγ (xsK_lt_Om2 j)
      (fun γ' _ h' => xsK_own (j + 1) γ' (h'.trans_lt (xsK_lt_succ j))) (GxCl.zero (leRho hl hX).1.1)
      ((Om_pos one_ne_zero).trans (ldOm1_lt_Top _))
    rwa [add_zero] at this
  have h3 := (h1.trans_lt h2).trans_le (le_mul_left _ omega0_pos)
  exact absurd hw (not_le.2 h3)

/-- **Every atom `θ < s < K_{J+1}` is a block atom** `ψ_{Ω₂}(β_γ + c)`, `γ < K_{J+1}`, `c < F^{β_γ}` codes. -/
theorem xsAt_cls (J : ℕ) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hθs : ConjT.th S < s)
    (hsK : s < xsK S (J + 1)) :
    ∃ γ c, GxCl (upsilon l) (ldAtR S l) γ ∧ γ < xsK S (J + 1) ∧ GxCl (upsilon l) (ldAtR S l) c ∧
      c < ldTop S (xsB γ) ∧ s = S.psi (xsB γ + c) (Om (1 + 1)) := by
  obtain ⟨a, ha, -, rfl⟩ := hs
  rcases lt_or_ge a (Om ω) with haW | haW
  · exact absurd hθs (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) haW.le).1)
  obtain ⟨d, rfl⟩ := exists_add_of_le haW
  have hKJ2 := xsK_lt_Om2 (S := S) J
  have hdK : d < Om (1 + 1) * xsK S J := by
    by_contra hc
    push Not at hc
    exact absurd hsK (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hc)).1)
  have hdP : d < ω ^ (Om (1 + 1) + Om (1 + 1)) := by
    rw [← xsW2_eq]; exact hdK.trans ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hKJ2)
  have hmod : (Om ω + d) % ω ^ (Om (1 + 1) + Om (1 + 1)) = d := by
    obtain ⟨k, hk⟩ := xsW2_dvd
    rw [hk, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdP]
  have hdmem : d ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
    have := leModP_mem (S := S) (Om (1 + 1) + Om (1 + 1)) ha; rwa [hmod] at this
  have hqmem : d / Om (1 + 1) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
    have := leDivOp_mem (S := S) (K := Om (1 + 1)) (dvd_refl _) hdmem hdP
    rwa [gg_SC_eps ldOm2_SC] at this
  have hcmem : d % Om (1 + 1) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := ldModK_mem ldOm2_SC hdmem
  set q := d / Om (1 + 1) with hq_def
  set c := d % Om (1 + 1) with hc_def
  have hqK : q < xsK S J := (Ordinal.div_lt ldOm2_SC.1.ne').2 hdK
  have hqK1 : q < xsK S (J + 1) := hqK.trans (xsK_lt_succ J)
  have hq2 : q < Om (1 + 1) := hqK.trans hKJ2
  have hc2 : c < Om (1 + 1) := Ordinal.mod_lt _ ldOm2_SC.1.ne'
  have hqc : GxCl (upsilon l) (ldAtR S l) q := (ldHull_iff hl hX hq2).1 hqmem
  have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hcmem
  have hdec : Om ω + d = xsB q + c := by
    unfold xsB; rw [add_assoc, hq_def, hc_def, Ordinal.div_add_mod]
  have hoq : XsOwn S q := xsK_own (J + 1) q hqK1
  rw [hdec]
  rcases lt_or_ge c (ldTop S (xsB q)) with hcF | hcF
  · exact ⟨q, c, hqc, hqK1, hcc, hcF, rfl⟩
  · -- the atom is the next base
    have hq12 : q + 1 < Om (1 + 1) := ldOm2_SC.isPrincipal hq2 (gg_one_lt_of_SC ldOm2_SC)
    have hq1K : q + 1 < xsK S (J + 1) :=
      (xsK_SC J).isPrincipal hqK1 (gg_one_lt_of_SC (xsK_SC J))
    have he : S.psi (xsB q + c) (Om (1 + 1)) = S.psi (xsB (q + 1) + 0) (Om (1 + 1)) := by
      rw [add_zero, ← xsB_succ]
      refine le_antisymm ?_ (ldTop_ge (xsB_own hoq) (xsB_dvd q) hcF)
      exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hc2.le)).1
    refine ⟨q + 1, 0, Rq.rqCode_succ hl hX hqc hq12, hq1K, GxCl.zero (leRho hl hX).1.1,
      (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), he⟩

end Win


/-! ## The move -/

theorem xsK_mem {a b : Ordinal.{0}} (ha : Om ω + Om ω ≤ a) : ∀ j, xsK S j ∈ S.CSet a b
  | 0 => CSet.one_mem a b
  | j + 1 => by
    have h1 : xsB (xsK S j) < a := by
      refine lt_of_lt_of_le ?_ ha
      unfold xsB
      exact (add_lt_add_iff_left _).2
        (((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (xsK_lt_Om2 j)).trans xsW2_lt)
    exact CSet.psi_mem h1 (InR_Om_succ 1) (mxOm2_mem _ _) (xsB_mem (xsK_mem ha j))

theorem xsL0_lt (n : ℕ) : Pv S (Om ω) < Bc.bcC S n := by
  have h := Rl.rlM_lt_L1 (S := S)
  rw [Lw.lw_L_eq, mul_zero, add_zero] at h
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  exact h.trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))

/-- **The block atoms move** at every window, once the codes below them move (bound `K_{J+1}`). -/
theorem xsAtMove (J : ℕ) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {γ c : Ordinal.{0}} (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγK : γ < xsK S (J + 1))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S (xsB γ))
    (hsK : S.psi (xsB γ + c) (Om (1 + 1)) < xsK S (J + 1))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (xsB γ + c) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < xsK S (J + 1) ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (xsB γ + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (xsB γ + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (xsB γ + c) (Om (1 + 1))) < xsK S (J + 1) ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ + c) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (xsB γ + c) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ + c) (Om (1 + 1)))) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAb := xsAb_of (xsA_win hl h1 h2)
  have hL0 := xsL0_lt (S := S) n
  have h0' : Pv S (Om ω) ≤ upsilon l' := by
    rw [← hB, ← Bc.bcB_fix' (S := S) n _ hL0]
    exact (Bc.bcB_mono' (S := S) n (show Pv S (Om ω) ∈ Set.Iio (Bc.bcC S (n + 1)) from (hL0.trans h1).trans h2)
      (show upsilon l ∈ Set.Iio (Bc.bcC S (n + 1)) from h2) (hL0.trans h1)).le
  have hAb' := xsAb_of (xsA_ge hl' hX' hown' h0')
  have hKJ := xsK_lt_Om2 (S := S) (J + 1)
  have hγ2 : γ < Om (1 + 1) := hγK.trans hKJ
  have hown_γ : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → XsOwn S γ' :=
    fun γ' _ h' => xsK_own (J + 1) γ' (h'.trans_lt hγK)
  have hoγ := hown_γ γ hγ le_rfl
  have hβown := xsB_own hoγ
  have hcs : c < S.psi (xsB γ + c) (Om (1 + 1)) := ldTop_gt hβown (xsB_dvd γ) hcF
  have hγs : γ < S.psi (xsB γ + c) (Om (1 + 1)) :=
    hoγ.trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1
  have hs2 : S.psi (xsB γ + c) (Om (1 + 1)) < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  obtain ⟨hDγ, hγ', hBγK, hΘγ, hEγ⟩ := IH γ hγ hγs
  obtain ⟨hDc, hc', -, hΘc, hEc⟩ := IH c hc hcs
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hmul := ldB_mulK (n := n) ldOm2_SC hD2 hB2
    (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (xsB γ + c) (Om (1 + 1)))
    (fun x hx => (IH x hx.1 hx.2).1)
    (fun x hx hx0 => by
      obtain ⟨hdx, hlx⟩ := gxDec hρSC hAt x hx.1
      have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlx, (log_le_self ω x).trans_lt hx.2⟩,
        ⟨hdx _ (GxCl.opow hρSC.1 hlx) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩)
    (fun x hx => hx.2.trans hs2) γ ⟨hγ, hγs⟩
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDb, hBb⟩ := mvB_add (k := n) hDW hmul.1
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDb hDc
  have hBα : Bc.bcB S n (xsB γ + c) = xsB (Bc.bcB S n γ) + Bc.bcB S n c := by
    unfold xsB; rw [hBa, hBb, hBW, hmul.2]
  have hαown := ldOwn hβown (xsB_dvd γ) hcF
  obtain ⟨hDs, hBs0, -⟩ := Ug.ugB_psi2 (n := n) hDa hαown
  have hBs : Bc.bcB S n (S.psi (xsB γ + c) (Om (1 + 1))) =
      S.psi (xsB (Bc.bcB S n γ) + Bc.bcB S n c) (Om (1 + 1)) := by
    rw [← hBα]; exact hBs0
  obtain ⟨hDK, hBK⟩ := xsK_D (S := S) n (J + 1)
  have hBγ2 : Bc.bcB S n γ < Om (1 + 1) := hBγK.trans hKJ
  have hown_γ' : ∀ γ', GxCl (upsilon l') (ldAtR S l') γ' → γ' ≤ Bc.bcB S n γ → XsOwn S γ' :=
    fun γ' _ h' => xsK_own (J + 1) γ' (h'.trans_lt hBγK)
  -- the top of the block moves
  obtain ⟨hDa2, hBa2⟩ := mvB_add (k := n) hDb hD2
  have hα2own : xsB γ + Om (1 + 1) ∈ S.CSet (xsB γ + Om (1 + 1)) (S.psi (xsB γ + Om (1 + 1)) (Om (1 + 1))) :=
    CSet.add_mem (hβown _ le_rfl) (mxOm2_mem _ _)
  obtain ⟨hDt, hBt, -⟩ := Ug.ugB_psi2 (n := n) hDa2 hα2own
  have hBtop : Bc.bcB S n (ldTop S (xsB γ)) = ldTop S (xsB (Bc.bcB S n γ)) := by
    have e2 : Bc.bcB S n (xsB γ + Om (1 + 1)) = xsB (Bc.bcB S n γ) + Om (1 + 1) := by
      unfold xsB; rw [hBa2, hBb, hBW, hmul.2, hB2]
    unfold ldTop; rw [← e2]; exact hBt
  have hBcF : Bc.bcB S n c < ldTop S (xsB (Bc.bcB S n γ)) := by
    rw [← hBtop]; exact (mvB_lt_iff hDc hDt).2 hcF
  have hBc2 : Bc.bcB S n c < Om (1 + 1) := hBcF.trans (ldTop_lt_Om2 _)
  -- the readings at `λ` and `λ'`
  have hΘs := xsBlk hl hX hown hAb hγ hγ2 hown_γ c hc hcF
  have hΘs' := xsBlk hl' hX' hown' hAb' hγ' hBγ2 hown_γ' _ hc' hBcF
  have hΘlt := xsRead_lt hl hX hown hAb hγ hγ2 hown_γ hc hcF
  refine ⟨hDs, ?_, ?_, hΘlt.trans hδr, ?_⟩
  · rw [hBs]
    exact ⟨xsB (Bc.bcB S n γ) + Bc.bcB S n c,
      CSet.add_mem (xsB_mem ((ldHull_iff hl' hX' hBγ2).2 hγ')) ((ldHull_iff hl' hX' hBc2).2 hc'),
      ((add_lt_add_iff_left _).2 hBc2).trans (xsB_A hBγ2 hAb'), rfl⟩
  · rw [← hBK]; exact (mvB_lt_iff hDs hDK).2 hsK
  · set y := gxTh (upsilon l) (ldAtR S l) γ with hy_def
    set z := gxTh (upsilon l) (ldAtR S l) c with hz_def
    have hys : y < S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * y + z) (Om 1) := by
      rw [← hΘs]; exact gxTh_lt hγ hγs
    have hzs : z < S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * y + z) (Om 1) := by
      rw [← hΘs]; exact gxTh_lt hc hcs
    have hy1 : y < Om 1 := hys.trans (psi_lt Low.InR_Om_one _)
    obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
    obtain ⟨hDO, hBO⟩ := Le.leB_mulOm1 (S := S) (n := n) hy1 hΘγ
    have hDz : MvD S z := mvD_of_lt (hΘc.trans hLw)
    obtain ⟨hD1, hB1⟩ := mvB_add (k := n) hDθ hDO
    obtain ⟨hD3, hB3⟩ := mvB_add (k := n) hD1 hDz
    have eA : ∀ X a b : Ordinal.{0}, X + ConjT.th S + Om 1 * a + b = X + (ConjT.th S + Om 1 * a + b) := by
      intro X a b; simp only [add_assoc]
    have hownd : ConjT.Aη S (cdEta S l) + (ConjT.th S + Om 1 * y + z) ∈
        S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + Om 1 * y + z))
          (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + Om 1 * y + z)) (Om 1)) := by
      rw [← eA]
      have hm := xsAθ_mem hl hX hown hAb (Om 1 * y + z)
      rw [← add_assoc] at hm
      exact CSet.add_mem (CSet.add_mem hm (xsMulO_mem (CSet.of_lt hys))) (CSet.of_lt hzs)
    have hbd : S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + Om 1 * y + z)) (Om 1) < Bc.bcC S (n + 1) := by
      rw [← eA, ← hΘs]; exact hΘlt.trans hδr
    have hmv := hBψ _ hD3 hownd hbd
    rw [hBs, hΘs', hΘs, hEγ, hEc, eA (ConjT.Aη S (cdEta S l)), hmv, hB3, hB1, hBθ, hBO, eA]

/-- **THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < K_{J+1}`** (every `J`), from the code-free wall. -/
theorem xsMove (hW : Wr.WrWallCF S) (J : ℕ) : ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ljThP S ≤ cdCode S l → cdCode S l < xsK S (J + 1) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  intro n l l' hR h1 hr hl' hB hP hK
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hX, hX', hown, hown', hpv, hpv', -, -, -⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hg, -, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hAW := xsA_win hl h1 h2
  have hAb := xsAb_of hAW
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  set e := cdExp η with he_def
  set K := xsK S (J + 1) with hK_def
  have hK2 : K < Om (1 + 1) := xsK_lt_Om2 (J + 1)
  have hΩP : Om (1 : Ordinal.{0}) < ljThP S := ljOm1_lt_ThP
  -- the code is the last exponent
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hxA : xsB (xsK S J) < A := by
      refine lt_of_lt_of_le ?_ hAW
      unfold xsB
      exact (add_lt_add_iff_left _).2
        (((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (xsK_lt_Om2 J)).trans xsW2_lt)
    have hlt : K < cdPi S η :=
      psi_lt_psi_of_mem (InR_Om_succ 1) hxA (xsB_mem (xsK_mem hAW J))
    exact absurd (hc ▸ hK) (not_lt.2 hlt.le)
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
  have hΩe : Om (1 : Ordinal.{0}) < e := hΩP.trans_le (hcode ▸ hP)
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
  have hPK : ljThP S ≤ K := rnThP_le_MW.trans (xsMW_le J)
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
    · have hθs : ConjT.th S < s := Lj.ljTh_lt_ThP.trans_le hsP
      obtain ⟨γ, c, hγ, hγK, hc, hcF, rfl⟩ := xsAt_cls hl hX hown hAb J hs hθs hsK
      exact xsAtMove J hR h1 hr hl' hB hγ hγK hc hcF hsK IHx
  obtain ⟨hDe, -, hBeK, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw (xsK_SC J) (xsK_Om1 J).le hatom e hge heK
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

end Googology.Trans.PoR.InaccPsi.R2.Xs
