import Googology.Trans.PoR.InaccPsi.R2.ZiChainR

/-!
# THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`, `ξ < ψ_{Ω₁}(0)`, AND THE MOVES ABOVE ITS TOP ATOMS

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdSh`, `Zd.ZdLaw`, `Zd.ZdMv`, `Zd.ZdHL`, `X_ξ = Zd.zdX k ξ = Ω_{k+3} + Ω₂·ξ`,
`K_ξ = Zd.zdK k ξ = Ω_{k+2} + Ω₁·ξ` as in `Zd.zdChain`; `G₀ = ziG S = ψ_{Ω₁}(0)`, `K₃ = ziK3 S`.

`Zd.zdChain` asks `ξ < ε₀` only to have `ξ` in every closure, `Θ_λ ξ = ξ` and `B_n ξ = ξ`; every `ξ < G₀` has these
(`Zi.ziG_mem`, `Zi.ziCst_le_rho`, `Zi.ziG_lt_C`), and `ε₀ < G₀`.

* `ziSh_cst` (every `X_ξ`, `ξ < G₀`, is a shift in every closure, `T X_ξ = K_ξ`), `ziLimSh` (the limit step),
* `ziChain` (**THE TOP LAW AT EVERY EXPONENT `X_ξ + e`, `ξ < ψ_{Ω₁}(0)`**:
  `Θ(ψ₂(β + W^{Ω_{k+3}+Ω₂·ξ+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+Ω₂·ξ+e})))`),
* `ziMv_cst`, `ziHL_cst` (the move data and the law at every restart),
* `ziTopMoveCst`, `ziTopBaseCst` (every top atom of `X_ξ` moves and is a base with a law at both ends),
* `ziTopMoveCstY3K` (the ψ₃-offsets below `W^{Y₃+Ω₂·K₃}` above every top atom of every `X_ξ`).

These generalize `Zd.zdSh_chain`, `Zd.zdLimSh`, `Zd.zdChain`, `Zd.zdMv_chain`, `Zd.zdHL_chain`,
`Zd.zdTopMoveChainY3E0` from the bound `ε₀` to `ψ_{Ω₁}(0)` (the proofs are those, with the lemmas of `ZiCst`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd
  Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ψ_{Ω₁}(0)`, is a shift in every closure**, `T X_ξ = K_ξ = Ω_{k+2} + Ω₁·ξ`. -/
theorem ziSh_cst (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) : ZdSh S l (zdX k ξ) (zdK k ξ) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs0 := zdSh_Om hl hX (S := S) k
  have hξ1 : ξ < Om 1 := hξ.trans ziG_lt_Om1
  have hξ2 : ξ < Om (1 + 1) := hξ1.trans (Om_lt_Om.2 (lt_add_one 1))
  have hξm : ∀ a c : Ordinal.{0}, ξ ∈ S.CSet a c := ziG_mem hξ
  have hξρ : ξ ≤ upsilon l := hξ.le.trans (ziCst_le_rho zero_le hl hX)
  have hρ1 : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1 (fun a b => CSet.one_mem a b)
  have hWξD : VbD S l (leWe 1 * ξ + 0) := by
    rw [leWe_one, add_zero]
    exact ⟨ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hξm _ _), ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hξm _ _),
      zdMul2_lt hξ2⟩
  have hT2 : vbT S l (Om (1 + 1) * ξ) = Om 1 * ξ := by
    have e1 : Om (1 + 1) * ξ = leWe 1 * ξ + 0 := by rw [leWe_one, add_zero]
    rw [e1, Vh.vhT_cnfW hl hX h1D (Xi.xiD_zero l) (hξm _ _) hξ2, Vh.vhT_zero hl hX, add_zero, hT1, leOe_one,
      gxTh_small hξρ]
  have hD2 : VbD S l (Om (1 + 1) * ξ) := by
    have h := hWξD; rwa [leWe_one, add_zero] at h
  refine ⟨fun a c => CSet.add_mem (hs0.mem a c) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hξm _ _)),
    vkOmW.1.isPrincipal hs0.lt (zdMul2_lt hξ2), ?_, fun a c => ?_, fun a c => ?_,
    hs0.Kpos.trans_le le_self_add⟩
  · unfold zdX zdK; rw [Vh.vhT_add hl hX hs0.D hD2, hs0.T, hT2]
  · unfold zdK
    exact CSet.add_mem (hs0.Km a c) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξm _ _))
  · unfold zdK; rw [mul_add]
    exact CSet.add_mem (hs0.Km1 a c) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξm _ _)))

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT STEP OF THE SHIFTS**: for a limit `ξ < ψ_{Ω₁}(0)`, the law at `X_{ξ'} + 0` for every `ξ' < ξ` (on every
base of exponent `0`) gives the law at `X_ξ + 0`. -/
theorem ziLimSh (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) (hlim : IsSuccLimit ξ)
    (IH : ∀ ξ', ξ' < ξ → ∀ β, VbD S l β → Ro.RoBaseE S l (zdX k ξ') 0 β → ZdLaw S l A (zdX k ξ') 0 β)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (zdX k ξ) 0 β) : ZdLaw S l A (zdX k ξ) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs := ziSh_cst hl hX k hξ
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  have h0θ : (0 : Ordinal.{0}) < ConjT.th S := (ConjT.SC_th S).1
  have hT0 : ∀ ξ', ξ' ≤ ξ → VbD S l (β + leWe (zdX k ξ')) ∧
      vbT S l (β + leWe (zdX k ξ')) = vbT S l β + leOe (zdK k ξ') := by
    intro ξ' hξ'
    have h := zdT_top hl hX (ziSh_cst hl hX k (hξ'.trans_lt hξ)) hβD h0H ldOm2_SC.1 h0θ
    simp only [gxTh_zero, add_zero] at h
    exact h
  have hWle : ∀ ξ', ξ' ≤ ξ → leWe (zdX k ξ') ≤ leWe (zdX k ξ) := fun ξ' hξ' => leWe_mono (zdX_mono k hξ')
  -- the bases of the smaller shifts
  unfold Ro.RoBaseE at hB
  simp only [add_zero] at hB
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hB
  have hB' : ∀ ξ', ξ' < ξ → Ro.RoBaseE S l (zdX k ξ') 0 β := by
    intro ξ' hξ'
    unfold Ro.RoBaseE
    simp only [add_zero]
    refine ⟨(leWe_dvd (zdX_mono k hξ'.le)).trans hβd, hβH,
      lt_of_le_of_lt ((add_le_add_iff_left β).2 (hWle ξ' hξ'.le)) hβA,
      fun d hd => hβown d (hd.trans (hWle ξ' hξ'.le)), fun e'' _ he'' => ?_⟩
    rw [nonpos_iff_eq_zero.1 he'']
    exact (SC_psi hκ2 _).1
  obtain ⟨hD, hTξ⟩ := hT0 ξ le_rfl
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold ZdLaw leTe
  simp only [add_zero]
  refine le_antisymm hup ?_
  rw [hTξ]
  -- the readings of the smaller shifts
  have hread : ∀ ξ', ξ' < ξ →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (zdK k ξ')) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (zdX k ξ)) (Om (1 + 1))) := by
    intro ξ' hξ'
    have h := IH ξ' hξ' β hβD (hB' ξ' hξ')
    unfold ZdLaw leTe at h
    simp only [add_zero] at h
    rw [(hT0 ξ' hξ'.le).2] at h
    rw [← h]
    exact gxTh_mono (psi_mono hκ2 ((add_le_add_iff_left β).2 (hWle ξ' hξ'.le))).1
  set L := vbT S l β + leOe (zdK k ξ) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hξ0 : (0 : Ordinal.{0}) < ξ := pos_iff_ne_zero.2 hlim.ne_bot
  have hr0 := hread 0 hξ0
  refine ciSup_le' fun ζ => ?_
  rcases lt_or_ge ζ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ζ.1 = A + 1 + (ζ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ζ.1 - (A + 1) < P := Ry.rySub_lt h1 ζ.2
    have hKpos : 0 < Om 1 * zdK k ξ := mul_pos (Om_pos one_ne_zero) hs.Kpos
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hKpos.ne')
    have hlt2 : ζ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < T β + Ω^{K₀ + Ω₁·ξ}` gives `z < T β + Ω^{K₀ + Ω₁·ξ'}` for some `ξ' < ξ`
    have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
    have hy0 : 0 < Om 1 * ξ := mul_pos (Om_pos one_ne_zero) hξ0
    have hylim : ∀ y', y' < Om 1 * ξ → y' + 1 < Om 1 * ξ := fun y' hy' =>
      (isSuccLimit_mul_right (Om_pos one_ne_zero) hlim).add_one_lt hy'
    have hz' : z.1 < vbT S l β + leOe (Om ((k : Ordinal.{0}) + 1 + 1) + Om 1 * ξ) := z.2
    obtain ⟨y', hy', hzy⟩ := xmCofL hy0 hylim hz'
    set q := y' / Om 1 with hq
    have hqξ : q < ξ := (Ordinal.div_lt hO1).2 hy'
    have hq1 : q + 1 < ξ := hlim.add_one_lt hqξ
    have hyq : y' < Om 1 * (q + 1) := by
      have := Ordinal.lt_mul_succ_div y' hO1; rwa [Order.succ_eq_add_one] at this
    have hzq : z.1 < vbT S l β + leOe (zdK k (q + 1)) := by
      unfold zdK
      exact hzy.trans_le ((add_le_add_iff_left _).2 (Yy.yyOe_mono ((add_le_add_iff_left _).2 hyq.le)))
    have h2 := hread (q + 1) hq1
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzq.le).1))).1.trans h2

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`** (`ξ < ψ_{Ω₁}(0)`, `e` a code, `β ∈ D` a base of exponent `e`). -/
theorem ziChain (k : ℕ) :
    ∀ ξ, ξ < ziG S → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (zdX k ξ) e β → ZdLaw S l A (zdX k ξ) e β := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    intro e hec he2 β hβD hB
    rw [zdX_zero] at hB ⊢
    exact xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'0 : ξ' < ziG S := (lt_add_one ξ').trans hξ
    have hs' := ziSh_cst hl hX k hξ'0
    have h := zdNext hl hX hA hρ hs' (IHξ ξ' (lt_add_one ξ') hξ'0)
    intro e hec he2 β hβD hB
    rw [zdX_succ] at hB ⊢
    exact h e hec he2 β hβD hB
  · refine zdTopUp hl hX hA hρ (ziSh_cst hl hX k hξ) fun β hβD hB => ?_
    exact ziLimSh hl hX hA hρ k hξ hlim (fun ξ' hξ' β' hβ'D hB' =>
      IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β' hβ'D hB') hβD hB

end Main

/-- **`X_ξ = Ω_{k+3} + Ω₂·ξ` has the move data `ZdMv`** for every `ξ < ψ_{Ω₁}(0)`. -/
theorem ziMv_cst (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) : ZdMv S (zdX k ξ) := by
  have hξ2 : ξ < Om (1 + 1) := (hξ.trans ziG_lt_Om1).trans (Om_lt_Om.2 (lt_add_one 1))
  refine ⟨fun a c => CSet.add_mem (Vn.vnOmK3_mem k a c) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _)
      (ziG_mem hξ a c)), vkOmW.1.isPrincipal (Wv.wvOmK_lt_W k) (zdMul2_lt hξ2), ?_, one_ne_zero,
    fun n => ?_⟩
  · unfold zdX
    exact (add_pos_of_pos_of_nonneg (Om_pos (add_pos_of_right zero_lt_one _).ne') zero_le).ne'
  obtain ⟨hD3, hB3, hD1, hB1⟩ := (Xv.xvShB (S := S) k).2 n
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDp, hBp⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBp
  obtain ⟨hDq, hBq⟩ := ziB_opowMul (n := n) hDp hBp ξ (hξ.trans (ziG_lt_C n))
  have e1 : Om (1 + 1) * zdX k ξ = Om (1 + 1) * Om ((k : Ordinal.{0}) + 1 + 1 + 1) +
      ω ^ (Om (1 + 1) + Om (1 + 1)) * ξ := by
    unfold zdX
    rw [mul_add, opow_add, gg_SC_eps ldOm2_SC, mul_assoc]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD3 hDq
  rw [hB3, hBq] at hBs
  rw [e1]
  exact ⟨hDs, hBs, hD1, hB1⟩

/-- **`ZdHL S X_ξ`**: the top law at every code exponent of `X_ξ`, at every restart (`Zi.ziChain`). -/
theorem ziHL_cst (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) : ZdHL S (zdX k ξ) :=
  fun _ _ _ hl hX hA hρ e β hec he2 hβD hb => ziChain hl hX hA hρ k ξ hξ e hec he2 β hβD hb


section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY TOP ATOM `ψ₂(β + W^{X_ξ+e})`, `ξ < ψ_{Ω₁}(0)`, MOVES** at every window under IH below it. -/
theorem ziTopMoveCst (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (zdX k ξ + Bc.bcB S n e)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)))) :=
  zdTopMove (ziMv_cst k hξ) hR h1 hr hl' hB (ziHL_cst k hξ) hec hβD hbe IH

/-- **EVERY TOP ATOM `t = β + W^{X_ξ+e}`, `ξ < ψ_{Ω₁}(0)`, IS A BASE WITH A LAW AT BOTH ENDS**. -/
theorem ziTopBaseCst (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (β + leWe (zdX k ξ + e)) (1 + S.psi (vbT S l (β + leWe (zdX k ξ + e))) (Om (1 + 1))) ∧
      Bc.bcB S n (β + leWe (zdX k ξ + e)) = Bc.bcB S n β + leWe (zdX k ξ + Bc.bcB S n e) :=
  zdTopBase (ziMv_cst k hξ) hR h1 hr hl' hB (ziHL_cst k hξ) hA' hρ' hec hβD hbe IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·K₃})` ABOVE EVERY TOP ATOM `t = β + W^{X_ξ+e}` MOVES**, `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ψ_{Ω₁}(0)` (`Zd.zdTopMoveChainY3E0` is `ξ < ε₀` and the offsets below `W^{Y₃+Ω₂·ε₀}`). -/
theorem ziTopMoveCstY3K (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (zdX k ξ + e) + leWe (zdXr S (ziK3 S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := zdX k ξ with hXdef
  have hm : ZdMv S X := ziMv_cst k hξ
  have HL : ZdHL S X := ziHL_cst k hξ
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := zdTopBase hm hR h1 hr hl' hB HL hA' hρ' hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((zdOm3_le_X k ξ).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := (le_self_add : X ≤ X + e).trans
      ((Ordinal.le_mul_right _ ldOm2_SC.1).trans (Ordinal.right_le_opow _ one_lt_omega0))
    exact (zdOm3_le_X k ξ).trans (hXle.trans le_add_self)
  exact ziPsi3OffK hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zi
