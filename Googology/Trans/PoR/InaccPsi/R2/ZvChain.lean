import Googology.Trans.PoR.InaccPsi.R2.ZdChain
import Googology.Trans.PoR.InaccPsi.R2.ZuRef

/-!
# Zv: THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e` WITH A COUNTABLE COEFFICIENT `ξ < ρ_λ`

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdSh`, `Zd.ZdLaw`, `X_ξ = Zd.zdX k ξ = Ω_{k+3} + Ω₂·ξ`, `K_ξ = Zd.zdK k ξ =
Ω_{k+2} + Ω₁·ξ` as in `Zd.zdChain`.  The shift data `Zd.ZdSh` (round 140) asks `X` only in the closures `Cl(a, c)`
with `Ω₁ ≤ c` and in `H_λ`, and `K`, `Ω₁·K` only in the closures with `ρ_λ ≤ c`; every countable `ξ < ρ_λ` meets
these (`ξ < ρ_λ ≤ c`), and `Θ ξ = ξ`.  `Zd.zdChain` (`ξ < ε₀`) and `Zi.ziChain` (`ξ < ψ_{Ω₁}(0)`) are the cases of
coefficients in every closure.

* `zvSh_cnt` (**every `X_ξ`, `ξ < ρ_λ`, is a shift**, `T X_ξ = K_ξ`), `zvLimSh` (the limit step),
* `zvChain` (**THE TOP LAW AT EVERY EXPONENT `X_ξ + e`, `ξ < ρ_λ`**:
  `Θ(ψ₂(β + W^{Ω_{k+3}+Ω₂·ξ+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+Ω₂·ξ+e})))`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ρ_λ`, is a shift**, `T X_ξ = K_ξ = Ω_{k+2} + Ω₁·ξ`. -/
theorem zvSh_cnt (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < upsilon l) : ZdSh S l (zdX k ξ) (zdK k ξ) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hs0 := zdSh_Om hl hX (S := S) k
  have hξ1 : ξ < Om 1 := hξ.trans hρ1
  have hξ2 : ξ < Om (1 + 1) := hξ1.trans (Om_lt_Om.2 (lt_add_one 1))
  have hξc : ∀ a c : Ordinal.{0}, upsilon l ≤ c → ξ ∈ S.CSet a c := fun a c h => CSet.of_lt (hξ.trans_le h)
  have hξH : ξ ∈ cdHull S l := CSet.of_lt hξ
  have hξθ : ξ ∈ S.CSet (Om ω) (ConjT.th S) := CSet.of_lt (hξ1.trans_le zd_Om1_le_th)
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  have hD2 : VbD S l (Om (1 + 1) * ξ) :=
    ⟨ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH, ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξθ, zdMul2_lt hξ2⟩
  have hT2 : vbT S l (Om (1 + 1) * ξ) = Om 1 * ξ := by
    have e1 : Om (1 + 1) * ξ = leWe 1 * ξ + 0 := by rw [leWe_one, add_zero]
    rw [e1, Vh.vhT_cnfW hl hX h1D (Xi.xiD_zero l) hξH hξ2, Vh.vhT_zero hl hX, add_zero, hT1, leOe_one,
      gxTh_small hξ.le]
  refine ⟨fun a c h => CSet.add_mem (hs0.mem a c h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _)
      (CSet.of_lt (hξ1.trans_le h))),
    vkOmW.1.isPrincipal hs0.lt (zdMul2_lt hξ2), ?_, fun a c h => ?_, fun a c h => ?_,
    hs0.Kpos.trans_le le_self_add, CSet.add_mem hs0.memH (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH)⟩
  · unfold zdX zdK; rw [Vh.vhT_add hl hX hs0.D hD2, hs0.T, hT2]
  · unfold zdK
    exact CSet.add_mem (hs0.Km a c h) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξc a c h))
  · unfold zdK; rw [mul_add]
    exact CSet.add_mem (hs0.Km1 a c h) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξc a c h)))

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT STEP OF THE SHIFTS**: for a limit `ξ < ρ_λ`, the law at `X_{ξ'} + 0` for every `ξ' < ξ` (on every
base of exponent `0`) gives the law at `X_ξ + 0`. -/
theorem zvLimSh (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < upsilon l) (hlim : IsSuccLimit ξ)
    (IH : ∀ ξ', ξ' < ξ → ∀ β, VbD S l β → Ro.RoBaseE S l (zdX k ξ') 0 β → ZdLaw S l A (zdX k ξ') 0 β)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (zdX k ξ) 0 β) : ZdLaw S l A (zdX k ξ) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs := zvSh_cnt hl hX k hξ
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  have h0θ : (0 : Ordinal.{0}) < ConjT.th S := (ConjT.SC_th S).1
  have hT0 : ∀ ξ', ξ' ≤ ξ → VbD S l (β + leWe (zdX k ξ')) ∧
      vbT S l (β + leWe (zdX k ξ')) = vbT S l β + leOe (zdK k ξ') := by
    intro ξ' hξ'
    have h := zdT_top hl hX (zvSh_cnt hl hX k (hξ'.trans_lt hξ)) hβD h0H ldOm2_SC.1 h0θ
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

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`** (every countable `ξ < ρ_λ`, `e` a code, `β ∈ D` a base of exponent `e`). -/
theorem zvChain (k : ℕ) :
    ∀ ξ, ξ < upsilon l → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
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
    have hξ'0 : ξ' < upsilon l := (lt_add_one ξ').trans hξ
    have hs' := zvSh_cnt hl hX k hξ'0
    have h := zdNext hl hX hA hρ hs' (IHξ ξ' (lt_add_one ξ') hξ'0)
    intro e hec he2 β hβD hB
    rw [zdX_succ] at hB ⊢
    exact h e hec he2 β hβD hB
  · refine zdTopUp hl hX hA hρ (zvSh_cnt hl hX k hξ) fun β hβD hB => ?_
    exact zvLimSh hl hX hA hρ k hξ hlim (fun ξ' hξ' β' hβ'D hB' =>
      IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β' hβ'D hB') hβD hB

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zv
