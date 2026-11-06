import Googology.Trans.PoR.InaccPsi.R2.ZvChain

/-!
# Zw: THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e` WITH A CODE COEFFICIENT `ξ < θ`

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdLaw`, `X_ξ = Zd.zdX k ξ = Ω_{k+3} + Ω₂·ξ` as in `Zd.zdChain`.  Here `ξ` is any
code of `λ` below `θ` (it may be uncountable: `Ω₁`, `ψ₂(…)`, …), and `T X_ξ = K_ξ = Ω_{k+2} + Ω₁·Θ ξ` (`zwK`).
The shift `X_ξ` carries the threshold code `ξ` (`Zd.ZdShQ`): `X_ξ ∈ Cl(a, c)` once `ξ < c`, and `K_ξ ∈ Cl(a, c)` once
`Θ ξ < c`.  The bases carry the condition

  `ZwQ λ k ξ β :  ξ' < ψ₂(β + W^{X_{ξ'}})` for every code `ξ' ≤ ξ`

(the coefficients lie below the collapse of their own base; it is upward closed in `β`), which puts `Θ ξ` below the
first plateau iterate `Θ(ψ₂(β + W^{X_ξ}))` (`Zd.zdSuccQ`, `Zd.zdLawWQ`).

* `zwSh` (**every `X_ξ`, `ξ` a code below `θ`, is a shift with threshold `ξ`**, `T X_ξ = K_ξ`),
* `zwLimSh` (**THE LIMIT STEP OF THE SHIFTS** at a limit code `ξ`: `Θ ξ` is a limit and every reading below it is
  the reading of a code below `ξ`, `gxTh_onto`),
* `zwChain` (**THE TOP LAW AT EVERY EXPONENT `X_ξ + e`, `ξ < θ` a code**, on the bases with `ZwQ`:
  `Θ(ψ₂(β + W^{Ω_{k+3}+Ω₂·ξ+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+Ω₂·ξ+e})))`).

`Zv.zvChain` is the case `ξ < ρ_λ` (there `Θ ξ = ξ` and `ZwQ` always holds).

No new axiom.  New definitions: `zwK` (the image of the shift), `ZwQ` (the base condition).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

/-- The image of the shift: `K_ξ = Ω_{k+2} + Ω₁·Θ ξ`. -/
noncomputable def zwK (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) (ξ : Ordinal.{0}) : Ordinal.{0} :=
  Om ((k : Ordinal.{0}) + 1 + 1) + Om 1 * gxTh (upsilon l) (ldAtR S l) ξ

/-- The base condition: every code `ξ' ≤ ξ` lies below `ψ₂(β + W^{X_{ξ'}})`. -/
def ZwQ (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) (ξ β : Ordinal.{0}) : Prop :=
  ∀ ξ', GxCl (upsilon l) (ldAtR S l) ξ' → ξ' ≤ ξ → ξ' < S.psi (β + leWe (zdX k ξ')) (Om (1 + 1))

theorem zwQ_up {l : Ordinal.{0}} {k : ℕ} {ξ β β' : Ordinal.{0}} (h : β ≤ β') (hQ : ZwQ S l k ξ β) :
    ZwQ S l k ξ β' := fun ξ' hc hle =>
  (hQ ξ' hc hle).trans_le (psi_mono (InR_Om_succ 1) (add_le_add h le_rfl)).1

theorem zwQ_mono {l : Ordinal.{0}} {k : ℕ} {ξ ξ₁ β : Ordinal.{0}} (h : ξ₁ ≤ ξ) (hQ : ZwQ S l k ξ β) :
    ZwQ S l k ξ₁ β := fun ξ' hc hle => hQ ξ' hc (hle.trans h)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ` a code below `θ`, is a shift with threshold `ξ`**, `T X_ξ = K_ξ`. -/
theorem zwSh (k : ℕ) {ξ : Ordinal.{0}} (hξc : GxCl (upsilon l) (ldAtR S l) ξ) (hξθ : ξ < ConjT.th S) :
    ZdShQ S l (zdX k ξ) (zwK S l k ξ) ξ := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs0 := zdSh_Om hl hX (S := S) k
  have hξ2 : ξ < Om (1 + 1) := hξθ.trans (psi_lt (InR_Om_succ 1) _)
  have hξH : ξ ∈ cdHull S l := (ldHull_iff hl hX hξ2).2 hξc
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  have hD2 : VbD S l (Om (1 + 1) * ξ) :=
    ⟨ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH, ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hξθ),
      zdMul2_lt hξ2⟩
  have hT2 : vbT S l (Om (1 + 1) * ξ) = Om 1 * gxTh (upsilon l) (ldAtR S l) ξ := by
    have e1 : Om (1 + 1) * ξ = leWe 1 * ξ + 0 := by rw [leWe_one, add_zero]
    rw [e1, Vh.vhT_cnfW hl hX h1D (Xi.xiD_zero l) hξH hξ2, Vh.vhT_zero hl hX, add_zero, hT1, leOe_one]
  refine ⟨fun a c h hq => CSet.add_mem (hs0.mem a c h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hq)),
    vkOmW.1.isPrincipal hs0.lt (zdMul2_lt hξ2), ?_, fun a c h hq => ?_, fun a c h hq => ?_,
    hs0.Kpos.trans_le le_self_add, CSet.add_mem hs0.memH (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH), hξc, hξθ⟩
  · unfold zdX zwK; rw [Vh.vhT_add hl hX hs0.D hD2, hs0.T, hT2]
  · unfold zwK
    exact CSet.add_mem (hs0.Km a c h) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt hq))
  · unfold zwK; rw [mul_add]
    exact CSet.add_mem (hs0.Km1 a c h) (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt hq)))

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT STEP OF THE SHIFTS** at a limit code `ξ < θ`: the law at `X_{ξ'} + 0` for every code `ξ' < ξ` over
the base `β` gives the law at `X_ξ + 0`. -/
theorem zwLimSh (k : ℕ) {ξ : Ordinal.{0}} (hξc : GxCl (upsilon l) (ldAtR S l) ξ) (hξθ : ξ < ConjT.th S)
    (hlim : IsSuccLimit ξ) {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (zdX k ξ) 0 β)
    (IH : ∀ ξ', GxCl (upsilon l) (ldAtR S l) ξ' → ξ' < ξ → Ro.RoBaseE S l (zdX k ξ') 0 β →
      ZdLaw S l A (zdX k ξ') 0 β) :
    ZdLaw S l A (zdX k ξ) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs := zwSh hl hX k hξc hξθ
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  have h0θ : (0 : Ordinal.{0}) < ConjT.th S := (ConjT.SC_th S).1
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hξ2 : ξ < Om (1 + 1) := hξθ.trans (psi_lt hκ2 _)
  have hT0 : ∀ ξ', GxCl (upsilon l) (ldAtR S l) ξ' → ξ' ≤ ξ → VbD S l (β + leWe (zdX k ξ')) ∧
      vbT S l (β + leWe (zdX k ξ')) = vbT S l β + leOe (zwK S l k ξ') := by
    intro ξ' hc hξ'
    have h := zdT_topQ hl hX (zwSh hl hX k hc (hξ'.trans_lt hξθ)) hβD h0H ldOm2_SC.1 h0θ
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
  obtain ⟨hD, hTξ⟩ := hT0 ξ hξc le_rfl
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold ZdLaw leTe
  simp only [add_zero]
  refine le_antisymm hup ?_
  rw [hTξ]
  -- the readings of the smaller shifts
  have hread : ∀ ξ', GxCl (upsilon l) (ldAtR S l) ξ' → ξ' < ξ →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (zwK S l k ξ')) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (zdX k ξ)) (Om (1 + 1))) := by
    intro ξ' hc hξ'
    have h := IH ξ' hc hξ' (hB' ξ' hξ')
    unfold ZdLaw leTe at h
    simp only [add_zero] at h
    rw [(hT0 ξ' hc hξ'.le).2] at h
    rw [← h]
    exact gxTh_mono (psi_mono hκ2 ((add_le_add_iff_left β).2 (hWle ξ' hξ'.le))).1
  set L := vbT S l β + leOe (zwK S l k ξ) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hξ0 : (0 : Ordinal.{0}) < ξ := pos_iff_ne_zero.2 hlim.ne_bot
  have hr0 := hread 0 h0c hξ0
  refine ciSup_le' fun ζ => ?_
  rcases lt_or_ge ζ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ζ.1 = A + 1 + (ζ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ζ.1 - (A + 1) < P := Ry.rySub_lt h1 ζ.2
    have hKpos : 0 < Om 1 * zwK S l k ξ := mul_pos (Om_pos one_ne_zero) hs.Kpos
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hKpos.ne')
    have hlt2 : ζ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < T β + Ω^{Ω_{k+2} + Ω₁·Θ ξ}` gives `z < T β + Ω^{Ω_{k+2} + Ω₁·Θ c}` for some code `c < ξ`
    have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) ξ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c hξ0; rwa [gxTh_zero] at this
    have hy0 : 0 < Om 1 * gxTh (upsilon l) (ldAtR S l) ξ := mul_pos (Om_pos one_ne_zero) hΘ0
    have hylim : ∀ y', y' < Om 1 * gxTh (upsilon l) (ldAtR S l) ξ →
        y' + 1 < Om 1 * gxTh (upsilon l) (ldAtR S l) ξ := fun y' hy' => by
      have hq : y' / Om 1 < gxTh (upsilon l) (ldAtR S l) ξ := (Ordinal.lt_mul_iff_div_lt hO1).1 hy'
      have h1' : y' < Om 1 * (y' / Om 1 + 1) := by
        have := Ordinal.lt_mul_succ_div y' hO1; rwa [Order.succ_eq_add_one] at this
      have hL1 : IsSuccLimit (Om 1 * (y' / Om 1 + 1)) := by
        rw [mul_add_one]; exact isSuccLimit_add _ Ph.ph_SC_Om1.isSuccLimit
      exact (hL1.add_one_lt h1').trans_le (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
    have hz' : z.1 < vbT S l β + leOe (Om ((k : Ordinal.{0}) + 1 + 1) +
        Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) := z.2
    obtain ⟨y', hy', hzy⟩ := xmCofL hy0 hylim hz'
    set t := y' / Om 1 with ht
    have htξ : t < gxTh (upsilon l) (ldAtR S l) ξ := (Ordinal.lt_mul_iff_div_lt hO1).1 hy'
    have ht1 : t + 1 < gxTh (upsilon l) (ldAtR S l) ξ := xmTh_lim hl hX hξ2 hlim t htξ
    obtain ⟨c, hc, hcξ, hct⟩ := gxTh_onto ht1
    have hyq : y' < Om 1 * (t + 1) := by
      have := Ordinal.lt_mul_succ_div y' hO1; rwa [Order.succ_eq_add_one] at this
    have hzq : z.1 < vbT S l β + leOe (zwK S l k c) := by
      unfold zwK; rw [hct]
      exact hzy.trans_le ((add_le_add_iff_left _).2 (Yy.yyOe_mono ((add_le_add_iff_left _).2 hyq.le)))
    have h2 := hread c hc hcξ
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzq.le).1))).1.trans h2

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`** (every code `ξ < θ`, `e` a code below `Ω₂`, `β ∈ D` a
base of exponent `e` with `ZwQ`). -/
theorem zwChain (k : ℕ) :
    ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → ξ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (zdX k ξ) e β → ZwQ S l k ξ β →
        ZdLaw S l A (zdX k ξ) e β := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξc hξθ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    intro e hec he2 β hβD hB _
    rw [zdX_zero] at hB ⊢
    exact xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'2 : ξ' + 1 < Om (1 + 1) := hξθ.trans (psi_lt (InR_Om_succ 1) _)
    have hξ'c : GxCl (upsilon l) (ldAtR S l) ξ' :=
      (ldHull_iff hl hX ((lt_add_one ξ').trans hξ'2)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hξ'2).2 hξc))
    have hξ'θ : ξ' < ConjT.th S := (lt_add_one ξ').trans hξθ
    have h := zdNextQ hl hX hA hρ (zwSh hl hX k hξ'c hξ'θ) (ZwQ S l k (ξ' + 1))
      (fun _ hQ => hQ ξ' hξ'c (lt_add_one ξ').le) (fun _ _ h hQ => zwQ_up h hQ)
      (fun e hec he2 β hβD hB hQ => IHξ ξ' (lt_add_one ξ') hξ'c hξ'θ e hec he2 β hβD hB
        (zwQ_mono (lt_add_one ξ').le hQ))
    intro e hec he2 β hβD hB hQ
    rw [zdX_succ] at hB ⊢
    exact h e hec he2 β hβD hB hQ
  · refine zdTopUpQ hl hX hA hρ (zwSh hl hX k hξc hξθ) (ZwQ S l k ξ) (fun _ hQ => hQ ξ hξc le_rfl)
      (fun _ _ h hQ => zwQ_up h hQ) fun β hβD hB hQ => ?_
    exact zwLimSh hl hX hA hρ k hξc hξθ hlim hβD hB fun ξ' hξ'c hξ' hB' =>
      IHξ ξ' hξ' hξ'c (hξ'.trans hξθ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β hβD hB'
        (zwQ_mono hξ'.le hQ)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zw

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zw.zwChain
