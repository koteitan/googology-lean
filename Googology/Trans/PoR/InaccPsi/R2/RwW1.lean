import Googology.Trans.PoR.InaccPsi.R2.RwAt

/-!
# The first code exponent: the top law at the shift `W^{Ω₁}` (image `Ω₁^{ρ_λ}`), and the atom `F_1` moves

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `F_1 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})`,
`B_n = Bc.bcB S n`.  The shift `X = W^{Ω₁} = Ω₂^{Ω₁}` has the code exponent `Ω₁ ≥ ρ_λ`; its image is
`X̂ = Ω^{Θ Ω₁} = Ω₁^{ρ_λ}`.

* `rwShW1` (**`(W^{Ω₁}, Ω₁^{ρ_λ})` is a shift own relative to every base**);
* `rwTopW1` (**THE TOP LAW AT `W^{Ω₁}` at every base: `Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^{Ω₁}})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{ρ_λ}})`**,
  a limit shift: every exponent below it lies below some `W^{f+1}`, `f < ρ_λ`, of the family `Rw.RwF`);
* `rwTh_W1` (**`Θ_λ(F_1) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^{ρ_λ}})`**), `rwB_F1` (`B_n F_1 = F_1`), `rwAtMoveF1` (**the atom
  `F_1` moves**);
* `RwAtMove8 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_1 < s ≤ θ`; `rwAtMove7_of8`, `rwAtMove8_of7`,
  `rwRoadJ` (**the road**), `rwRoadJ_hyps`.

No new axiom.  New definition: the hypothesis name `RwAtMove8`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

theorem rwW1_lt_OmW : leWe (Om 1) < Om (ω : Ordinal.{0}) := roWe_lt_OmW (gg_Om1_lt_Om2.trans ldOm2_lt_OmW)

/-- `Ω₂·W^{Ω₁} = W^{Ω₁}`, `Ω₁·Ω^{ρ} = Ω^{ρ}` for an infinite `ρ`. -/
theorem rwW_mul_W1 : Om (1 + 1 : Ordinal.{0}) * leWe (Om 1) = leWe (Om 1) := by
  rw [rvWe_mul, Ordinal.one_add_of_omega0_le (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le]

theorem rwO_mul_Oe {ρ : Ordinal.{0}} (hρ : ω ≤ ρ) : Om (1 : Ordinal.{0}) * leOe ρ = leOe ρ := by
  rw [rvOe_mul, Ordinal.one_add_of_omega0_le hρ]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`(W^{Ω₁}, Ω₁^{ρ_λ})` is a shift own relative to every base.** -/
theorem rwShW1 (b : Ordinal.{0}) : RvSh S l b (leWe (Om 1)) (leOe (upsilon l)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hΩC : ∀ a c, Om (1 : Ordinal.{0}) ∈ S.CSet a c := fun a c => CSet.Om_mem (CSet.one_mem a c)
  have hρT : upsilon l < gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (leWe (Om 1))) (Om (1 + 1))) := by
    have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om
      (psiS_bounds (S := S) (b + leWe (leWe (Om 1))) 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at h
  have hΩQ : ∀ Q, S.psi (b + leWe (leWe (Om 1))) (Om (1 + 1)) ≤ Q → Om (1 : Ordinal.{0}) < Q :=
    fun Q hQ => (psiS_bounds (S := S) _ 1).1.trans_le hQ
  refine ⟨(leWe_pos _).ne', ?_, leWe_mem (hΩC _ _), leWe_mem (hΩC _ _), leOe_mem (CSet.of_lt hρT), ?_, ?_,
    fun Q hQ hb => LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (LeCl.small (hΩQ Q hb))),
    fun Q hQ hb => LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (LeCl.small (hρT.trans_le hb)))⟩
  · have h := leWe_dvd (Order.one_le_iff_pos.2 (Om_pos one_ne_zero) : (1 : Ordinal.{0}) ≤ Om 1)
    rwa [leWe_one] at h
  · exact hG3.isPrincipal (leWe_lt_SC hG3 hWG3 ((gg_Om1_lt_Om2).trans hWG3)).1 hWG3
  · exact hG1.isPrincipal (leOe_lt_SC hG1 hΩG1 (hρ1.trans hΩG1)).1 hΩG1

/-- The members `W^{e}` (`1 ≤ e < ρ_λ`) of the family at every base, with their top laws. -/
theorem rwLevMem {b e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) :
    RwF S l b (leWe e) (leOe e) e ∧ RvSh S l b (leWe e) (leOe e) ∧ RvTop S l b (leWe e) (leOe e) 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1Ω : (1 : Ordinal.{0}) < Om 1 := one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)
  have hF := RwF.one (S := S) (l := l) (β := b) (ζ := 1) he1 heρ (GxCl.small (gg_one_lt_of_SC hρSC))
    one_ne_zero (by rw [gxTh_small (gg_one_lt_of_SC hρSC).le]; exact h1Ω) ⟨0, h1Ω⟩
  rw [gxTh_small (gg_one_lt_of_SC hρSC).le, mul_one, mul_one] at hF
  exact ⟨hF, rwF_sh hl hX hF⟩

/-- **THE TOP LAW AT `W^{Ω₁}` at every base.** -/
theorem rwTopW1 (b : Ordinal.{0}) : RvTop S l b (leWe (Om 1)) (leOe (upsilon l)) 0 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  refine rvTopLimSh hl hX (rwShW1 hl hX b) (fun x hxH hx => ?_) (fun z hz => ?_)
  · set f := log ω x / Om (1 + 1) with hf_def
    have hfH : f ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    have hfΩ : f < Om 1 := by
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [hf_def, log_zero_right, Ordinal.zero_div]; exact Om_pos one_ne_zero
      have hlogx : log ω x < Om (1 + 1) * Om 1 :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx)
      exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogx
    have hfρ : f < upsilon l :=
      rwCode_lt_rho hl hX ((ldHull_iff hl hX (hfΩ.trans gg_Om1_lt_Om2)).1 hfH) hfΩ
    have hf1ρ : f + 1 < upsilon l := hρSC.isSuccLimit.succ_lt hfρ
    obtain ⟨-, hs, ht⟩ := rwLevMem (b := b) hl hX le_add_self hf1ρ
    exact ⟨_, _, leWe_mono (Order.add_one_le_of_lt hfΩ), roLt_We_log x,
      leOe_lt hf1ρ, hs, ht⟩
  · obtain ⟨e', h1, he', hze'⟩ := rvLt_Oe_lim hρSC.isSuccLimit hz
    obtain ⟨-, hs, ht⟩ := rwLevMem (b := b) hl hX h1 he'
    exact ⟨_, _, leWe_lt (he'.trans hρ1), hze', hs, ht⟩

/-- **`Θ_λ(F_1) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^{ρ_λ}})`.** -/
theorem rwTh_W1 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe (upsilon l))) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hb : RoBaseE S l (leWe (Om 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW rwW1_lt_OmW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have h := rwTopW1 hl hX 0 0 (A + 1) hb le_rfl hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

/-- **`B_n F_1 = F_1`**, `F_1 ∈ MvD`. -/
theorem rwB_F1 {n : ℕ} : MvD S (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) = S.psi (leWe (leWe (Om 1))) (Om (1 + 1)) := by
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hΩSC : SC (Om (1 : Ordinal.{0})) := Ph.ph_SC_Om1
  have hΩE : ω ^ Om (1 : Ordinal.{0}) = Om 1 := Low.opow_eq_self_of_SC hΩSC
  have hlog : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
    conv_lhs => rw [← hΩE]
    exact log_opow one_lt_omega0 _
  obtain ⟨hDK, hBK⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 (fun x => x = 0 ∨ x = Om 1)
    (fun x hx => by rcases hx with rfl | rfl; exacts [hD0, hDO])
    (fun x hx hx0 => by
      rcases hx with rfl | rfl
      · exact absurd rfl hx0
      · refine ⟨Or.inr hlog, Or.inl ?_⟩
        rw [hlog, hΩE, Ordinal.sub_self])
    (fun x hx => by rcases hx with rfl | rfl; exacts [ldOm2_SC.1, gg_Om1_lt_Om2]) (Om 1) (Or.inr rfl)
  rw [hBO] at hBK
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBW
  -- `W^{W^{Ω₁}} = ω^{W^{Ω₁}}`
  have e1 : leWe (leWe (Om 1)) = ω ^ leWe (Om 1) := by
    unfold leWe; congr 1; exact rwW_mul_W1
  have hDW' : MvD S (leWe (Om 1)) := hDW
  have hBW' : Bc.bcB S n (leWe (Om 1)) = leWe (Om 1) := hBW
  obtain ⟨hDWW, hBWW⟩ := ldB_opow (n := n) hDW'
  rw [hBW'] at hBWW
  have hown : leWe (leWe (Om 1)) ∈ S.CSet (leWe (leWe (Om 1))) (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) :=
    leWe_mem (leWe_mem (CSet.Om_mem (CSet.one_mem _ _)))
  rw [e1] at hown ⊢
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDWW hown
  exact ⟨hDT, by rw [hBT, hBWW]⟩

/-- **The atom `F_1` moves.** -/
theorem rwAtMoveF1 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    MvD S (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (leWe (leWe (Om 1))) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om 1))) (Om (1 + 1)))) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans ((cdR_ge S l).trans_lt hr)
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDF, hBF⟩ := rwB_F1 (S := S) (n := n)
  have e1 := rwTh_W1 hl hX hA hρ
  have e1' := rwTh_W1 hl' hX' hA' hρ'
  have hρω : ω ≤ upsilon l := (Lw.lw_omega_lt_SC hρSC).le
  have hρ'ω : ω ≤ upsilon l' := (Lw.lw_omega_lt_SC (leRho hl' hX').1).le
  -- `B_n(1 + Ω₁^{Ω₁^ρ}) = 1 + Ω₁^{Ω₁^{ρ'}}`
  obtain ⟨hDOρ, hBOρ⟩ := leB_mulOm1 (S := S) (n := n) hρ1 h2
  obtain ⟨hDe, hBe⟩ := ldB_opow (n := n) hDOρ
  rw [hBOρ, hB] at hBe
  have eO : ∀ y, ω ≤ y → leOe (leOe y) = ω ^ leOe y := fun y hy => by
    unfold leOe; congr 1; exact rwO_mul_Oe hy
  have hDe' : MvD S (leOe (upsilon l)) := hDe
  have hBe' : Bc.bcB S n (leOe (upsilon l)) = leOe (upsilon l') := hBe
  obtain ⟨hDee, hBee⟩ := ldB_opow (n := n) hDe'
  rw [hBe'] at hBee
  obtain ⟨hD1d, hB1d⟩ := mvB_add (k := n) hD1 hDee
  rw [mwB_one, hBee] at hB1d
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hdG : 1 + leOe (leOe (upsilon l)) < S.psi 0 (Om (1 + 1)) :=
    hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1))
      (leOe_lt_SC hG1 hΩG1 (leOe_lt_SC hG1 hΩG1 (hρ1.trans hΩG1)).1).1
  have hdθ : 1 + leOe (leOe (upsilon l)) ≤ ConjT.th S := hdG.le.trans rnG_le_th
  have hown : A + (1 + leOe (leOe (upsilon l))) ∈
      S.CSet (A + (1 + leOe (leOe (upsilon l)))) (S.psi (A + (1 + leOe (leOe (upsilon l)))) (Om 1)) := by
    refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA)
      (CSet.add_mem (CSet.one_mem _ _) (leOe_mem (leOe_mem (CSet.of_lt ?_))))
    exact hρ ▸ psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right A (by
      exact (zero_lt_one.trans_le le_self_add))) ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA)
  rw [eO _ hρω] at hdθ hown
  refine ⟨hDF, ?_, ?_, ?_, ?_⟩
  · rw [hBF]
    exact ⟨_, leWe_mem (leWe_mem (CSet.Om_mem (CSet.one_mem _ _))), (roWe_lt_OmW rwW1_lt_OmW).trans_le
      le_self_add, rfl⟩
  · rw [hBF]; exact rwF1_lt_th.trans ljTh_lt_ThP
  · rw [e1, add_assoc, eO _ hρω]; exact hbX _ hdθ
  · rw [hBF, e1', e1, add_assoc A, eO _ hρω, hBψ _ hD1d hown hdθ, hB1d, eO _ hρ'ω, add_assoc]

/-- **`LjAtMove` for the atoms `F_1 < s ≤ θ`.** -/
def RwAtMove8 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (Om 1))) (Om (1 + 1)) < s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RwAtMove8` gives `RwAtMove7`** (hence `Rq.RqAtMove6`). -/
theorem rwAtMove7_of8 (h : RwAtMove8 S) : RwAtMove7 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  rcases hsF.lt_or_eq with hlt | rfl
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hlt hsθ IH
  · exact rwAtMoveF1 hR h1 hr hl' hB

/-- **`RwAtMove7` gives `RwAtMove8`.** -/
theorem rwAtMove8_of7 (h : RwAtMove7 S) : RwAtMove8 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH => h n l l' hR h1 hr hl' hB hm hF hK s hs hsF.le hsθ IH

/-- **The road with `RwAtMove8`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rwRoadJ (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RwAtMove8 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rwRoadI hU hO hL hV hN hlh (fun hν => rwAtMove7_of8 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `rwRoadJ` follows from that of `Rq.rqRoadH`. -/
theorem rwRoadJ_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RqAtMove6 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RwAtMove8 S :=
  fun hν => rwAtMove8_of7 (rwAtMove7_of6 (hat hν))

end Googology.Trans.PoR.InaccPsi.R2.Rw
