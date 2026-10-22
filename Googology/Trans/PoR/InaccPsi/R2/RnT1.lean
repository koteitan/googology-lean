import Googology.Trans.PoR.InaccPsi.R2.RnGMove

/-!
# The top `T₁ = ψ_{Ω₂}(Ω₂^{Ω₂+1})`: `Θ_λ(T₁) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁+1})`, its move, and the road with the atoms in
`(T₁, θ]`

`μ = Ω₂^{Ω₂}`, `O = Ω₁^{Ω₁}`, `T₁ = ψ_{Ω₂}(μ·Ω₂)` (`Rn.rnT1`), `O·Ω₁ = Ω₁^{Ω₁+1}`.

* `rnTopT1` (**`Θ_λ(T₁) = ψ_{Ω₁}(A + 1 + O·Ω₁)`**: "`≤`" from `Rn.rnCls_g` and `Rn.rnThG`, "`≥`" from `Le.lePsi1_le`
  and the digit bound `Le.leCl_boundY`: the leading digit of a code below `O·Ω₁` is the reading of a code `γ < T₁`);
* `rnB_OW` (`B_n(O·Ω₁) = O·Ω₁`), `rnAtMove_T1` (**`T₁` moves**);
* `RnAtMove2 S` (a hypothesis name): **`Lj.LjAtMove` for the atoms `T₁ < s ≤ θ`**; `rnLjAtMove2` (**`RnAtMove2`
  gives `LjAtMove`**), `rnAtMove2_of`, `rnRoadD` (**the road** with `RnAtMove2`, `Rn.RnThMoveM`, `Rn.RnEQhi2`),
  `rnRoadD_hyps` (its hypotheses follow from those of `Lj.ljRoadA`).

No new axiom.  New definition: the hypothesis name `RnAtMove2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

theorem rnOW_eq : leOe (Om 1) * Om 1 = ω ^ (Om 1 * Om 1 + Om 1) := by
  unfold leOe; rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]

theorem rnT1_atom {l : Ordinal.{0}} : rnT1 S ∈ ldAtR S l :=
  ⟨leWe (Om (1 + 1)) * Om (1 + 1), leMulWe_mem (mxOm2_mem _ _) (mxOm2_mem _ _),
    rnMuW_lt_OmW.trans_le le_self_add, rfl⟩

/-- **`Θ_λ(T₁) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁}·Ω₁)`.** -/
theorem rnTopT1 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (rnT1 S) = S.psi (A + 1 + leOe (Om 1) * Om 1) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hÂ : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hbase : gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) = S.psi (A + 1) (Om 1) := ldBlk_zero hA hρ
  have hβat : S.psi 0 (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨0, CSet.zero_mem _ _, (Om_pos (by simp)).trans_le le_self_add, rfl⟩
  have hρÂ : upsilon l < S.psi (A + 1) (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  set X := S.psi (A + 1 + leOe (Om 1) * Om 1) (Om 1) with hX_def
  have hÂX : A + 1 ∈ S.CSet (A + 1 + leOe (Om 1) * Om 1) X := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi (A + 1) (Om 1) < X :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right _ (mul_pos (leOe_pos _) (Om_pos one_ne_zero))) hÂX
  -- the sub-bases `μ·γ` read below `X`
  have hsub : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < rnT1 S →
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1))) < X := by
    intro γ hγ hγT
    obtain ⟨e1, own1⟩ := rnThG hl hX hA hρ γ hγ hγT
    have hγs := rnT1_gt hγT
    have hΘγ1 : gxTh (upsilon l) (ldAtR S l) γ < Om 1 :=
      (gxTh_lt hγ hγs).trans (by rw [e1]; exact psi_lt Low.InR_Om_one _)
    have hlt : A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ < A + 1 + leOe (Om 1) * Om 1 :=
      (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 hΘγ1)
    rw [e1]
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)
  have hup : gxTh (upsilon l) (ldAtR S l) (rnT1 S) ≤ X := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨g, hgc, hgT, -, hg2⟩ := rnCls_g hl hX t ht hts
    have hg1T : g + 1 < rnT1 S := rnT1_SC.isSuccLimit.succ_lt hgT
    exact (gxTh_mono hg2).trans_lt (hsub _ (hcode1 g hgc (hg1T.trans rnT1_lt_Om2)) hg1T)
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt (rnT1_atom (l := l))
  have hβs : S.psi 0 (Om (1 + 1)) < rnT1 S :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (mul_pos (leWe_pos _) ldOm2_SC.1) (CSet.zero_mem _ _)
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x (A + 1) with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Om 1) * Om 1 := (add_lt_add_iff_left _).1 hx
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hOWG : leOe (Om 1) * Om 1 < S.psi 0 (Om (1 + 1)) := ldMul_lt_SC hG1 rnOO_lt_G hΩG1
  have hOWd : leOe (Om 1) * Om 1 ∣ S.psi 0 (Om (1 + 1)) := by
    rw [rnOW_eq]
    conv_rhs => rw [← gg_SC_eps hG1]
    exact opow_dvd_opow ω (hG1.isPrincipal (ldMul_lt_SC hG1 hΩG1 hΩG1) hΩG1).le
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * Om 1 + Om 1) hc
  rw [← rnOW_eq, Ordinal.mod_mod_of_dvd _ hOWd] at hc2
  have hr' : r < ω ^ (Om 1 * Om 1 + Om 1) := by rw [← rnOW_eq]; exact hr
  have hmod : (A + 1 + r) % (leOe (Om 1) * Om 1) = (A + 1) % (leOe (Om 1) * Om 1) + r := by
    rw [rnOW_eq]; exact leMod_add_lt _ (A + 1) hr'
  rw [hmod] at hc2
  set y := (A + 1) % (leOe (Om 1) * Om 1) + r with hy_def
  have hyP : y < leOe (Om 1) * Om 1 := by
    rw [hy_def, rnOW_eq]
    exact isPrincipal_add_omega0_opow _ (Ordinal.mod_lt _ (opow_pos _ omega0_pos).ne') hr'
  have hry : r ≤ y := le_add_self
  have hbd := leCl_boundY hTSC Ph.ph_SC_Om1 (LeCl.om (κ := Om 1) (Q := gxTh (upsilon l) (ldAtR S l) (rnT1 S)))
    y hc2 (by rw [← rnOW_eq]; exact hyP)
  change y < leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) (rnT1 S) at hbd
  have hO0 : leOe (Om 1) ≠ 0 := (leOe_pos _).ne'
  have hδT := (Ordinal.lt_mul_iff_div_lt hO0).1 hbd
  obtain ⟨γ, hγc, hγT, hγx⟩ := gxTh_onto hδT
  have hγ1T : γ + 1 < rnT1 S := rnT1_SC.isSuccLimit.succ_lt hγT
  have hγ1c := hcode1 γ hγc (hγ1T.trans rnT1_lt_Om2)
  obtain ⟨e1, -⟩ := rnThG hl hX hA hρ (γ + 1) hγ1c hγ1T
  have hyg : y ≤ leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) (γ + 1) := by
    rw [hΘsucc γ hγc, hγx, mul_add_one]
    exact (Ordinal.lt_mul_div_add y hO0).le
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 (hry.trans hyg))).1 ?_
  rw [← e1]
  exact hTs _ (rnMuG_atom hl hX hγ1c (hγ1T.trans rnT1_lt_Om2))
    (psi_lt_psi_of_mem (InR_Om_succ 1) (leMulWe_lt (hγ1T.trans rnT1_lt_Om2))
      (leMulWe_mem (mxOm2_mem _ _) (CSet.of_lt hγ1T)))

/-- `B_n(Ω₁^{Ω₁}·Ω₁) = Ω₁^{Ω₁}·Ω₁`. -/
theorem rnB_OW {n : ℕ} : MvD S (leOe (Om 1) * Om 1) ∧ Bc.bcB S n (leOe (Om 1) * Om 1) = leOe (Om 1) * Om 1 := by
  obtain ⟨hD1, hB1⟩ := rnB_O2 (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD1 hD2
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [hBs, hB1, hB2] at hBo
  rw [rnOW_eq]; exact ⟨hDo, hBo⟩

/-- **`T₁` moves.** -/
theorem rnAtMove_T1 {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl' : IsRestartIdx l') (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    MvD S (rnT1 S) ∧ Bc.bcB S n (rnT1 S) ∈ ldAtR S l' ∧ Bc.bcB S n (rnT1 S) = rnT1 S ∧
      gxTh (upsilon l) (ldAtR S l) (rnT1 S) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (rnT1 S)) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (rnT1 S)) := by
  obtain ⟨hDT, hBT⟩ := rnB_T1 (S := S) (n := n)
  obtain ⟨hDO, hBO⟩ := rnB_OW (S := S) (n := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1 hDO
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hdG : 1 + leOe (Om 1) * Om 1 < S.psi 0 (Om (1 + 1)) :=
    hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) (ldMul_lt_SC hG1 rnOO_lt_G hΩG1)
  have hdθ : 1 + leOe (Om 1) * Om 1 ≤ ConjT.th S := hdG.le.trans rnG_le_th
  have hownd : A + (1 + leOe (Om 1) * Om 1) ∈
      S.CSet (A + (1 + leOe (Om 1) * Om 1)) (S.psi (A + (1 + leOe (Om 1) * Om 1)) (Om 1)) := by
    refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) ?_
    exact CSet.add_mem (CSet.one_mem _ _) (leMulOe_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.Om_mem (CSet.one_mem _ _)))
  have e1 := rnTopT1 hl hX hA hρ
  have e1' := rnTopT1 hl' hX' hA' hρ'
  refine ⟨hDT, by rw [hBT]; exact rnT1_atom, hBT, by rw [e1, add_assoc]; exact hbX _ hdθ, ?_⟩
  rw [hBT, e1', e1, add_assoc A, hBψ _ hDd hownd hdθ, hBd, mwB_one, hBO, add_assoc]

/-- **`LjAtMove` for the atoms `T₁ < s ≤ θ`.** -/
def RnAtMove2 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, rnT1 S < s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RnAtMove2` gives `RnAtMove1`, hence `LjAtMove`.** -/
theorem rnAtMove1_of2 (h : RnAtMove2 S) : RnAtMove1 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH
  rcases hs1.lt_or_eq with hlt | rfl
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hlt hsθ IH
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  obtain ⟨hDs, hBs, hBT, hth, hEq⟩ := rnAtMove_T1 (n := n) hR.1 hl' hX hX' hA hA' hρ hρ' hbX hBψ
  exact ⟨hDs, hBs, by rw [hBT]; exact rnT1_lt_th.trans ljTh_lt_ThP, hth, hEq⟩

theorem rnLjAtMove2 (h : RnAtMove2 S) : LjAtMove S := rnLjAtMove1 (rnAtMove1_of2 h)

/-- **`LjAtMove` gives `RnAtMove2`.** -/
theorem rnAtMove2_of (h : LjAtMove S) : RnAtMove2 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (rnFWW_le_T1.trans hs1.le) hsθ IH

/-- **The road with `RnAtMove2`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rnRoadD (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rnRoadC hU hO hL hV hN hlh (fun hν => rnAtMove1_of2 (hat hν)) hM hhi

/-- **Satisfiability**: the hypotheses of `rnRoadD` follow from those of `Lj.ljRoadA`, so `rnRoadD` asks no more. -/
theorem rnRoadD_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → LjAtMove S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → LjEQhi S) :
    (Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) ∧
      (Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :=
  ⟨fun hν => rnAtMove2_of (hat hν), fun hν => rnThMoveM_of hν (hhi hν), fun hν => rnEQhi2_of (hhi hν)⟩

end Googology.Trans.PoR.InaccPsi.R2.Rn
