import Googology.Trans.PoR.InaccPsi.R2.ZdOm2
import Googology.Trans.PoR.InaccPsi.R2.GcAt

/-!
# THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`, `ξ < ε₀`, `e` a code

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdSh`, `Zd.ZdLaw` as in `Zd.zdSucc`.  `X_ξ = zdX k ξ = Ω_{k+3} + Ω₂·ξ`,
`K_ξ = zdK k ξ = Ω_{k+2} + Ω₁·ξ` (so `T X_ξ = K_ξ`).

* `zdSh_chain` (**every `X_ξ`, `ξ < ε₀`, is a shift in every closure** with `T X_ξ = K_ξ`),
* `zdLimSh` (**THE LIMIT STEP OF THE SHIFTS**: the law at `X_{ξ'} + 0` for every `ξ' < ξ`, `ξ` a limit, gives the law
  at `X_ξ + 0`; continuity of `ψ₁`, `ψ₂` and `Xm.xmCofL`),
* `zdChain` (**THE TOP LAW AT EVERY EXPONENT `X_ξ + e`**: for every level `k`, every `ξ < ε₀`, every code `e < Ω₂` and
  every base `β ∈ D` of exponent `e` of the shift `X_ξ`:
  `Θ(ψ₂(β + W^{Ω_{k+3}+Ω₂·ξ+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+Ω₂·ξ+e})))`, and
  `T(β + W^{Ω_{k+3}+Ω₂·ξ+e}) = T β + Ω^{Ω_{k+2}+Ω₁·ξ+Θe}`, `zdT_top`).
  `ξ = 0` is `Xm.xmTopUp`; `ξ = 1` contains the exponent `X + Ω₂` of `Yy.yyLawOm2` and the REFUTE-FIRST point
  `E = Ω₂ + 1` (`zdTestOm2p1`).

No new axiom.  New definitions: `zdX`, `zdK` (abbreviations of the shift and its image).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm

variable {S : InaccSeq.{0}}

/-- The shift `X_ξ = Ω_{k+3} + Ω₂·ξ`. -/
noncomputable def zdX (k : ℕ) (ξ : Ordinal.{0}) : Ordinal.{0} := Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1) * ξ

/-- Its image `K_ξ = Ω_{k+2} + Ω₁·ξ`. -/
noncomputable def zdK (k : ℕ) (ξ : Ordinal.{0}) : Ordinal.{0} := Om ((k : Ordinal.{0}) + 1 + 1) + Om 1 * ξ

theorem zdX_zero (k : ℕ) : zdX k 0 = Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by unfold zdX; rw [mul_zero, add_zero]

theorem zdX_succ (k : ℕ) (ξ : Ordinal.{0}) : zdX k (ξ + 1) = zdX k ξ + Om (1 + 1) := by
  unfold zdX; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem zdK_succ (k : ℕ) (ξ : Ordinal.{0}) : zdK k (ξ + 1) = zdK k ξ + Om 1 := by
  unfold zdK; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem zdX_mono (k : ℕ) {ξ ξ' : Ordinal.{0}} (h : ξ' ≤ ξ) : zdX k ξ' ≤ zdX k ξ := by
  unfold zdX; exact (add_le_add_iff_left _).2 (mul_le_mul_left' h _)

theorem zdMul2_lt {ξ : Ordinal.{0}} (hξ : ξ < Om (1 + 1)) : Om (1 + 1) * ξ < Om ω := by
  have h22 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
    rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]
  refine (mul_lt_mul_of_pos_left hξ ldOm2_SC.1).trans ?_
  rw [h22]
  exact vkOmW.1.2 0 vkOmW.1.1 _ (vkOmW.1.isPrincipal ldOm2_lt_OmW ldOm2_lt_OmW)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ε₀`, is a shift in every closure**, `T X_ξ = K_ξ = Ω_{k+2} + Ω₁·ξ`. -/
theorem zdSh_chain (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) : ZdSh S l (zdX k ξ) (zdK k ξ) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs0 := zdSh_Om hl hX (S := S) k
  have hξ1 : ξ < Om 1 := hξ.trans_le Gc.gc_eps0_le_Om1
  have hξ2 : ξ < Om (1 + 1) := hξ1.trans (Om_lt_Om.2 (lt_add_one 1))
  have hξm : ∀ a c : Ordinal.{0}, ξ ∈ S.CSet a c := fun a c => Gc.gc_cst_mem a c ξ hξ
  have hξρ : ξ ≤ upsilon l := hξ.le.trans (epsilon_zero_le_of_omega0_opow_le (gg_SC_eps hρSC).le)
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

/-- **THE LIMIT STEP OF THE SHIFTS**: for a limit `ξ < ε₀`, the law at `X_{ξ'} + 0` for every `ξ' < ξ` (on every
base of exponent `0`) gives the law at `X_ξ + 0`. -/
theorem zdLimSh (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) (hlim : IsSuccLimit ξ)
    (IH : ∀ ξ', ξ' < ξ → ∀ β, VbD S l β → Ro.RoBaseE S l (zdX k ξ') 0 β → ZdLaw S l A (zdX k ξ') 0 β)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (zdX k ξ) 0 β) : ZdLaw S l A (zdX k ξ) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs := zdSh_chain hl hX k hξ
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  have h0θ : (0 : Ordinal.{0}) < ConjT.th S := (ConjT.SC_th S).1
  have hT0 : ∀ ξ', ξ' ≤ ξ → VbD S l (β + leWe (zdX k ξ')) ∧
      vbT S l (β + leWe (zdX k ξ')) = vbT S l β + leOe (zdK k ξ') := by
    intro ξ' hξ'
    have h := zdT_top hl hX (zdSh_chain hl hX k (hξ'.trans_lt hξ)) hβD h0H ldOm2_SC.1 h0θ
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

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`** (`ξ < ε₀`, `e` a code, `β ∈ D` a base of exponent `e`). -/
theorem zdChain (k : ℕ) :
    ∀ ξ, ξ < ε₀ → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
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
    have hξ'0 : ξ' < ε₀ := (lt_add_one ξ').trans hξ
    have hs' := zdSh_chain hl hX k hξ'0
    have h := zdNext hl hX hA hρ hs' (IHξ ξ' (lt_add_one ξ') hξ'0)
    intro e hec he2 β hβD hB
    rw [zdX_succ] at hB ⊢
    exact h e hec he2 β hβD hB
  · refine zdTopUp hl hX hA hρ (zdSh_chain hl hX k hξ) fun β hβD hB => ?_
    exact zdLimSh hl hX hA hρ k hξ hlim (fun ξ' hξ' β' hβ'D hB' =>
      IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β' hβ'D hB') hβD hB

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zd
