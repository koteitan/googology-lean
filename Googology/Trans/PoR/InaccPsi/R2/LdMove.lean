import Googology.Trans.PoR.InaccPsi.R2.LdFix

/-!
# The reading moves below `F⁺ = ψ_{Ω₂}(Ω₂ + 1)`, past `sup_j K_j`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `K_j` the layers, `F = ψ_{Ω₂}(Ω₂) = sup_j K_j`, `F⁺ = ψ_{Ω₂}(Ω₂ + 1)`,
`H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ_λ(m) = otp(H_λ ∩ m) = gxTh ρ_λ (ldAtR λ) m` (`R2.LdHull`),
`m_λ` the code of `λ`.

* `ldAtMove_Fp` (**every atom of `H_λ` below `F⁺` moves**: the layer atoms by `Mx.mxAtL_move`, the atom `F` by
  `B_n F = F`, `Θ_λ(F) = ψ_{Ω₁}(A + Ω₁)` and `B_n(ψ_{Ω₁}(A + Ω₁)) = ψ_{Ω₁}(A' + Ω₁)`);
* `ldThMove_Fp` (**`MxThMove` at every long code `m_λ < F⁺`**, no hypothesis; `Mx.mxThMove_L` stopped at
  `sup_j K_j = F`);
* `LdThMoveP S` (a hypothesis name): `MxThMove` at the codes `F⁺ ≤ m_λ ≤ θ`; `ldThMoveW_of_P` (**`LdThMoveP` gives
  `Mx.MxThMoveW`**), `ldThMoveP_of_W` (the converse, so `LdThMoveP` is not stronger), `ldRoad`.

No new axiom.  New definition: the hypothesis name `LdThMoveP`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **Every atom of the hull below `F⁺` moves.** -/
theorem ldAtMove_Fp {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hl' : IsRestartIdx l')
    (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hρX : upsilon l < Bc.bcC S (n + 1))
    (hbX : ∀ d, d ≤ Om 1 → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, d < Om 1 → d < S.psi (A + d) (Om 1) →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1))
    (hBΩ : Bc.bcB S n (S.psi (A + Om 1) (Om 1)) = S.psi (A' + Om 1) (Om 1)) :
    ∀ s ∈ ldAtR S l, s < ldFp S → MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ldFp S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hρ'1 : upsilon l' < Om 1 := hρ' ▸ psi_lt Low.InR_Om_one A'
  intro s hs hsFp
  rcases (ldAt_le_F (ldAt_GxAt _ _) hs hsFp).lt_or_eq with hsF | rfl
  · obtain ⟨j, a, ha, haK, rfl⟩ := ldAtR_lt_F hl hX hs hsF
    have hsj : GxCl (upsilon l) (mxAtL S (upsilon l) (j + 1)) (S.psi a (Om (1 + 1))) := GxCl.atom ⟨a, ha, haK, rfl⟩
    have hsK : S.psi a (Om (1 + 1)) < mxKs S (j + 1) := mxPsi2_ltL haK (mxKs_lt_succ j)
    have hmv := mxAtL_move (n := n) hA hA' hρ hρ' hB (Lw.lw_L_SC S _) hρX hLw
      (fun d hd => hbX d hd.le) hBψ
    obtain ⟨hD, hBs, hBsK, hth, heq⟩ := hmv (j + 1) _ hsj hsK
    obtain ⟨hDa, -, -, -, -⟩ := hmv j a ha haK
    obtain ⟨-, hBa⟩ := mxB_atom (n := n) hDa (CSet.of_lt (mxPsi2_gt j a haK))
    have hBsSC : SC (Bc.bcB S n (S.psi a (Om (1 + 1)))) := by rw [hBa]; exact SC_psi (InR_Om_succ 1) _
    have hBsΩ : Om 1 < Bc.bcB S n (S.psi a (Om (1 + 1))) := by rw [hBa]; exact (psiS_bounds _ 1).1
    have hmem : Bc.bcB S n (S.psi a (Om (1 + 1))) ∈ ldAtR S l' :=
      gxSC_atom hρ'1 ((ldLay_iff hl' hX' (j + 1) hBsK).2 hBs) hBsSC hBsΩ
    refine ⟨hD, hmem, hBsK.trans ((ldKs_lt_F _).trans ldF_lt_Fp), ?_, ?_⟩
    · rw [ldLay_th hl hX (j + 1) hsK.le]; exact hth
    · rw [ldLay_th hl' hX' (j + 1) hBsK.le, ldLay_th hl hX (j + 1) hsK.le]; exact heq
  · obtain ⟨hDF, hBF⟩ := ldB_F (S := S) (k := n)
    refine ⟨hDF, by rw [hBF]; exact ldF_mem, by rw [hBF]; exact ldF_lt_Fp, ?_, ?_⟩
    · rw [ldTh_F hl hX hA hρ]; exact hbX _ le_rfl
    · rw [hBF, ldTh_F hl' hX' hA' hρ', ldTh_F hl hX hA hρ, hBΩ]

/-- **`MxThMove` at every long code `m_λ < F⁺`.** -/
theorem ldThMove_Fp {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < ldFp S) :
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
    have hle : ldFp S ≤ cdPi S η :=
      (psi_mono (S := S) (InR_Om_succ 1) (Order.add_one_le_of_lt (ldOm2_lt_OmW.trans_le hWA))).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heFp : e < ldFp S := hcode ▸ hK
  -- `e` is a code of the full hull
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heFp.trans ldFp_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the bounds `ψ_{Ω₁}(A + d) < L(n+2)` for `d ≤ Ω₁`
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hθ1 : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hdθ : ∀ d, d ≤ Om 1 → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 (hd.trans hθ1.le))).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, d < Om 1 → d < S.psi (A + d) (Om 1) →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hd1 hdA
    obtain ⟨A'', hA'', hBP'', hBd⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) hdA (hdθ d hd1.le)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hBΩ : Bc.bcB S n (S.psi (A + Om 1) (Om 1)) = S.psi (A' + Om 1) (Om 1) := by
    obtain ⟨hDΩ, hBΩ1⟩ := mvB_Om1 (S := S) (k := n)
    have hownΩ : A + Om 1 ∈ S.CSet (A + Om 1) (S.psi (A + Om 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + Om 1)).2 hown)
        (CSet.Om_mem (CSet.one_mem _ _))
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDΩ hownΩ (hdθ _ le_rfl)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this, hBΩ1]
  -- the move of `e`
  have hρSC : SC (upsilon l) := hρA ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDe, -, hBeFp, -, hEq⟩ := mxGxStep (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _) (ldAt_GxAt _ _) hB
    (Lw.lw_L_SC S _) h2 hLw ldFp_SC ldOm1_lt_Fp.le
    (ldAtMove_Fp hl hl' hX hX' hown hA' hρA hρA' hB h2 hdθ hBψ hBΩ) e hge heFp
  -- the image code is `B_n e`
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeFp.trans ldFp_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeFp.trans ldFp_lt_Om2).le]
  exact hEq.symm

/-- `MxThMove` at the long codes with `F⁺ ≤ m_λ ≤ θ`. -/
def LdThMoveP (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l ≤ ConjT.th S → ldFp S ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`LdThMoveP` gives `MxThMoveW`.** -/
theorem ldThMoveW_of_P (h : LdThMoveP S) : MxThMoveW S := by
  intro n l l' hR h1 hr hl' hB hm he hθ _
  by_cases hK : cdCode S l < ldFp S
  · exact ldThMove_Fp hR h1 hr hl' hB he hK
  · exact h n l l' hR h1 hr hl' hB hm he hθ (not_lt.1 hK)

/-- `MxThMoveW` gives `LdThMoveP` (so `LdThMoveP` is not the stronger hypothesis). -/
theorem ldThMoveP_of_W (h : MxThMoveW S) : LdThMoveP S :=
  fun n l l' hR h1 hr hl' hB hm he hθ hF => h n l l' hR h1 hr hl' hB hm he hθ
    fun j => ((ldKs_lt_F j).trans ldF_lt_Fp).le.trans hF

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LdThMoveP` and `L(ω+1) ≤ ν_C → MxEQth`.** -/
theorem ldRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LdThMoveP S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad5 hU hO hL hV hN hlh (fun hν => ldThMoveW_of_P (hth hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Ld
