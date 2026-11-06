import Googology.Trans.PoR.InaccPsi.R2.ZxTwo

/-!
# Zy: THE COEFFICIENT CHAIN `X₀ + W^h·ζ` OVER ANY SHIFT `X₀`, and every finite power `W^n`

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdShQ`, `Zd.ZdLaw` as in `Zd.zdSuccQ`, `Zx.ZxEx` as in `Zx.zxLawJ`.
`X₀` is a shift with threshold `q₀` and a base condition `Q₀` (upward closed, `Q₀ β ⇒ q₀ < ψ₂(β + W^{X₀})`), `h ∈ D`
an exponent with `T h = H > 0` and threshold `q_h`.  The chain's base condition is

  `ZyQ … ζ β :  Q₀ β ∧ q_h < ψ₂(β + W^{X₀ + W^h}) ∧ ζ' < ψ₂(β + W^{X₀ + W^h·ζ'})` for every code `ζ' ≤ ζ`

(round 145: `q_h` is asked below the collapse at the first use of `h`, `X₀ + W^h`, which every normal base meets;
`ψ₂(β + W^{X₀})` may equal `h`).

* `zySh` (**`X₀ + W^h·ζ` is a shift**, `T = K₀ + Ω^H·Θζ`, threshold `max q₀ (max q_h ζ)`),
* `zyLimSh` (**the limit step** at a limit code `ζ`: the readings `Θζ'` of the codes `ζ' < ζ` are cofinal in `Θζ`),
* `zyChain` (**THE CHAIN**: given the law at every `X₀ + e` and the successor step `X₀ + W^h·ζ → X₀ + W^h·(ζ+1)` as a
  hypothesis, the law at every `X₀ + W^h·ζ + e`, `ζ < θ` and `e < Ω₂` codes, on the bases with `ZyQ`),
* `zyChain1` (**`h = 1`**: the successor step is `Zd.zdNextQ`), `zxEx_nat` (the exponent `n`),
* `zyChainN` (**EVERY FINITE POWER**: for every `n ≥ 1` and every shift `X₀` with the law at every `X₀ + e`, the law
  at every `X₀ + W^n·ζ + e`; the successor step is the jump `Zx.zxLawJ` at `h = n - 1` over the chain of `W^{n-1}`),
  `zyTopN` (**the top law at every exponent `Ω_{k+3} + W^n·ζ + e`**, the case `X₀ = Ω_{k+3}`).

No new axiom.  New definition: `ZyQ` (the base condition of the chain).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx

variable {S : InaccSeq.{0}}

/-- **The base condition of the chain.** -/
def ZyQ (S : InaccSeq.{0}) (l X₀ h qh : Ordinal.{0}) (Q₀ : Ordinal.{0} → Prop) (ζ β : Ordinal.{0}) : Prop :=
  Q₀ β ∧ qh < S.psi (β + leWe (X₀ + leWe h)) (Om (1 + 1)) ∧
    ∀ ζ', GxCl (upsilon l) (ldAtR S l) ζ' → ζ' ≤ ζ → ζ' < S.psi (β + leWe (X₀ + leWe h * ζ')) (Om (1 + 1))

theorem zyQ_up {l X₀ h qh : Ordinal.{0}} {Q₀ : Ordinal.{0} → Prop} (hQup : ∀ β β', β ≤ β' → Q₀ β → Q₀ β')
    {ζ β β' : Ordinal.{0}} (hle : β ≤ β') (hQ : ZyQ S l X₀ h qh Q₀ ζ β) : ZyQ S l X₀ h qh Q₀ ζ β' :=
  ⟨hQup β β' hle hQ.1, hQ.2.1.trans_le (psi_mono (InR_Om_succ 1) (add_le_add hle le_rfl)).1,
    fun ζ' hc h' => (hQ.2.2 ζ' hc h').trans_le (psi_mono (InR_Om_succ 1) (add_le_add hle le_rfl)).1⟩

theorem zyQ_mono {l X₀ h qh : Ordinal.{0}} {Q₀ : Ordinal.{0} → Prop} {ζ ζ₁ β : Ordinal.{0}} (hle : ζ₁ ≤ ζ)
    (hQ : ZyQ S l X₀ h qh Q₀ ζ β) : ZyQ S l X₀ h qh Q₀ ζ₁ β :=
  ⟨hQ.1, hQ.2.1, fun ζ' hc h' => hQ.2.2 ζ' hc (h'.trans hle)⟩

theorem zy_max_code {Z : Ordinal.{0}} {At : Set Ordinal.{0}} {a b : Ordinal.{0}} (ha : GxCl Z At a)
    (hb : GxCl Z At b) : GxCl Z At (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- The threshold of `X₀ + W^h·ζ` lies below `ψ₂(β + W^{X₀ + W^h·ζ})` on the bases with `ZyQ`, once `q_h` does. -/
theorem zyThr {l X₀ q₀ h qh : Ordinal.{0}} {Q₀ : Ordinal.{0} → Prop}
    (hQq : ∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) {ζ β : Ordinal.{0}}
    (hQ : ZyQ S l X₀ h qh Q₀ ζ β) (hc : GxCl (upsilon l) (ldAtR S l) ζ)
    (hqh : qh < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1))) :
    max q₀ (max qh ζ) < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) := by
  have hmono : S.psi (β + leWe X₀) (Om (1 + 1)) ≤ S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) :=
    (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono le_self_add))).1
  exact max_lt ((hQq β hQ.1).trans_le hmono) (max_lt hqh (hQ.2.2 ζ hc le_rfl))

/-- On the bases with `ZyQ`, `q_h < ψ₂(β + W^{X₀ + W^h·ζ})` for every `ζ > 0`. -/
theorem zyQh {l X₀ h qh : Ordinal.{0}} {Q₀ : Ordinal.{0} → Prop} {ζ β : Ordinal.{0}}
    (hQ : ZyQ S l X₀ h qh Q₀ ζ β) (hpos : 0 < ζ) :
    qh < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) :=
  hQ.2.1.trans_le (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono (add_le_add le_rfl
    (Ordinal.le_mul_left _ hpos))))).1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The exponent `n`: `T n = n`, threshold `0`. -/
theorem zxEx_nat (n : ℕ) : ZxEx S l (n : Ordinal.{0}) (n : Ordinal.{0}) 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hnω : (n : Ordinal.{0}) < ω := natCast_lt_omega0 n
  have hn2 : (n : Ordinal.{0}) < Om (1 + 1) := hnω.trans (Lw.lw_omega_lt_SC ldOm2_SC)
  have hnH : (n : Ordinal.{0}) ∈ cdHull S l := Sc.scNat_mem _ _ n
  refine ⟨⟨hnH, Sc.scNat_mem _ _ n, hnω.trans (Lw.lw_omega_lt_SC vkOmW.1)⟩, ?_,
    fun a c _ _ => Sc.scNat_mem a c n, fun a c _ _ => Sc.scNat_mem a c n, GxCl.zero hρSC.1, (ConjT.SC_th S).1⟩
  rw [vbT_code hl hX hn2 hnH]
  exact gxTh_small (hnω.trans (Lw.lw_omega_lt_SC hρSC)).le

/-- **`X₀ + W^h·ζ` is a shift**, with `T = K₀ + Ω^H·Θζ` and threshold `max q₀ (max q_h ζ)`. -/
theorem zySh {X₀ K₀ q₀ h H qh ζ : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀) (hx : ZxEx S l h H qh)
    (hζc : GxCl (upsilon l) (ldAtR S l) ζ) (hζθ : ζ < ConjT.th S) :
    ZdShQ S l (X₀ + leWe h * ζ) (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ) (max q₀ (max qh ζ)) := by
  have hζ2 : ζ < Om (1 + 1) := hζθ.trans (psi_lt (InR_Om_succ 1) _)
  have hζH : ζ ∈ cdHull S l := (ldHull_iff hl hX hζ2).2 hζc
  have hh1 : h + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hx.D.2.2
  have hWuD : VbD S l (leWe h * ζ) :=
    ⟨leMulWe_mem hx.D.1 hζH, leMulWe_mem hx.D.2.1 (CSet.of_lt hζθ),
      (leMulWe_mono hζ2.le).trans_lt (by rw [← leWe_succ]; exact (leWe_lt_SC vkOmW.1 vkOmW.2 hh1).1)⟩
  have hTWu : vbT S l (leWe h * ζ) = leOe H * gxTh (upsilon l) (ldAtR S l) ζ := by
    have h := Vh.vhT_cnfW hl hX hx.D (Xi.xiD_zero l) hζH hζ2
    rwa [add_zero, Vh.vhT_zero hl hX, add_zero, hx.T] at h
  have hmax : ∀ c, max q₀ (max qh ζ) < c → q₀ < c ∧ qh < c ∧ ζ < c := fun c h =>
    ⟨(le_max_left _ _).trans_lt h, ((le_max_left _ _).trans (le_max_right _ _)).trans_lt h,
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt h⟩
  have hmaxΘ : ∀ c, gxTh (upsilon l) (ldAtR S l) (max q₀ (max qh ζ)) < c →
      gxTh (upsilon l) (ldAtR S l) q₀ < c ∧ gxTh (upsilon l) (ldAtR S l) qh < c ∧
        gxTh (upsilon l) (ldAtR S l) ζ < c := fun c h =>
    ⟨(gxTh_mono (le_max_left _ _)).trans_lt h, (gxTh_mono ((le_max_left _ _).trans (le_max_right _ _))).trans_lt h,
      (gxTh_mono ((le_max_right _ _).trans (le_max_right _ _))).trans_lt h⟩
  have hKm : ∀ a c : Ordinal.{0}, upsilon l ≤ c →
      gxTh (upsilon l) (ldAtR S l) (max q₀ (max qh ζ)) < c →
        K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ ∈ S.CSet a c := fun a c h hq => by
    obtain ⟨h1, h2, h3⟩ := hmaxΘ c hq
    exact CSet.add_mem (hs0.Km a c h h1) (leMulOe_mem (hx.Hm a c h h2) (CSet.of_lt h3))
  refine ⟨fun a c h hq => ?_, vkOmW.1.isPrincipal hs0.lt hWuD.2.2, ?_, hKm,
    fun a c h hq => ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hKm a c h hq),
    hs0.Kpos.trans_le le_self_add, CSet.add_mem hs0.memH hWuD.1, zy_max_code hs0.qc (zy_max_code hx.qc hζc),
    max_lt hs0.qθ (max_lt hx.qθ hζθ)⟩
  · obtain ⟨h1, h2, h3⟩ := hmax c hq
    exact CSet.add_mem (hs0.mem a c h h1) (leMulWe_mem (hx.mem a c h h2) (CSet.of_lt h3))
  · rw [Vh.vhT_add hl hX hs0.D hWuD, hs0.T, hTWu]

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT STEP** of the chain at a limit code `ζ < θ`. -/
theorem zyLimSh {X₀ K₀ q₀ h H qh ζ : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀) (hx : ZxEx S l h H qh) (hH0 : 0 < H)
    (hζc : GxCl (upsilon l) (ldAtR S l) ζ) (hζθ : ζ < ConjT.th S) (hlim : IsSuccLimit ζ) {β : Ordinal.{0}}
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (X₀ + leWe h * ζ) 0 β)
    (IH : ∀ ζ', GxCl (upsilon l) (ldAtR S l) ζ' → ζ' < ζ → Ro.RoBaseE S l (X₀ + leWe h * ζ') 0 β →
      ZdLaw S l A (X₀ + leWe h * ζ') 0 β) :
    ZdLaw S l A (X₀ + leWe h * ζ) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hζ2 : ζ < Om (1 + 1) := hζθ.trans (psi_lt hκ2 _)
  have hT0 : ∀ ζ', GxCl (upsilon l) (ldAtR S l) ζ' → ζ' ≤ ζ → VbD S l (β + leWe (X₀ + leWe h * ζ')) ∧
      vbT S l (β + leWe (X₀ + leWe h * ζ')) =
        vbT S l β + leOe (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ') := by
    intro ζ' hc hζ'
    have hζ'2 : ζ' < Om (1 + 1) := hζ'.trans_lt hζ2
    exact zxT_shift hl hX hs0 hx hβD ((ldHull_iff hl hX hζ'2).2 hc) hζ'2 (hζ'.trans_lt hζθ)
  have hWle : ∀ ζ', ζ' ≤ ζ → leWe (X₀ + leWe h * ζ') ≤ leWe (X₀ + leWe h * ζ) := fun ζ' hζ' =>
    leWe_mono (add_le_add le_rfl (leMulWe_mono hζ'))
  have hXle : ∀ ζ', ζ' ≤ ζ → X₀ + leWe h * ζ' ≤ X₀ + leWe h * ζ := fun ζ' hζ' =>
    add_le_add le_rfl (leMulWe_mono hζ')
  -- the bases of the smaller shifts
  unfold Ro.RoBaseE at hB
  simp only [add_zero] at hB
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hB
  have hB' : ∀ ζ', ζ' < ζ → Ro.RoBaseE S l (X₀ + leWe h * ζ') 0 β := by
    intro ζ' hζ'
    unfold Ro.RoBaseE
    simp only [add_zero]
    refine ⟨(leWe_dvd (hXle ζ' hζ'.le)).trans hβd, hβH,
      lt_of_le_of_lt ((add_le_add_iff_left β).2 (hWle ζ' hζ'.le)) hβA,
      fun d hd => hβown d (hd.trans (hWle ζ' hζ'.le)), fun e'' _ he'' => ?_⟩
    rw [nonpos_iff_eq_zero.1 he'']
    exact (SC_psi hκ2 _).1
  obtain ⟨hD, hTζ⟩ := hT0 ζ hζc le_rfl
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold ZdLaw leTe
  simp only [add_zero]
  refine le_antisymm hup ?_
  rw [hTζ]
  -- the readings of the smaller shifts
  have hread : ∀ ζ', GxCl (upsilon l) (ldAtR S l) ζ' → ζ' < ζ →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ')) (Om (1 + 1)))
        (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1))) := by
    intro ζ' hc hζ'
    have hlw := IH ζ' hc hζ' (hB' ζ' hζ')
    unfold ZdLaw leTe at hlw
    simp only [add_zero] at hlw
    rw [(hT0 ζ' hc hζ'.le).2] at hlw
    rw [← hlw]
    exact gxTh_mono (psi_mono hκ2 ((add_le_add_iff_left β).2 (hWle ζ' hζ'.le))).1
  set L := vbT S l β + leOe (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hζ0 : (0 : Ordinal.{0}) < ζ := pos_iff_ne_zero.2 hlim.ne_bot
  have hr0 := hread 0 h0c hζ0
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hKpos : 0 < Om 1 * (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ) :=
      mul_pos (Om_pos one_ne_zero) (hs0.Kpos.trans_le le_self_add)
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hKpos.ne')
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < T β + Ω^{K₀ + Ω^H·Θζ}` gives `z < T β + Ω^{K₀ + Ω^H·Θc}` for some code `c < ζ`
    have hOH : leOe H ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hOHlim : IsSuccLimit (leOe H) :=
      isSuccLimit_opow_left isSuccLimit_omega0 (mul_pos (Om_pos one_ne_zero) hH0).ne'
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) ζ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c hζ0; rwa [gxTh_zero] at this
    have hy0 : 0 < leOe H * gxTh (upsilon l) (ldAtR S l) ζ := mul_pos (opow_pos _ omega0_pos) hΘ0
    have hylim : ∀ y', y' < leOe H * gxTh (upsilon l) (ldAtR S l) ζ →
        y' + 1 < leOe H * gxTh (upsilon l) (ldAtR S l) ζ := fun y' hy' => by
      have hq : y' / leOe H < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOH).1 hy'
      have h1' : y' < leOe H * (y' / leOe H + 1) := by
        have := Ordinal.lt_mul_succ_div y' hOH; rwa [Order.succ_eq_add_one] at this
      have hL1 : IsSuccLimit (leOe H * (y' / leOe H + 1)) := by
        rw [mul_add_one]; exact isSuccLimit_add _ hOHlim
      exact (hL1.add_one_lt h1').trans_le (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
    obtain ⟨y', hy', hzy⟩ := xmCofL hy0 hylim z.2
    set t := y' / leOe H with ht
    have htζ : t < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOH).1 hy'
    have ht1 : t + 1 < gxTh (upsilon l) (ldAtR S l) ζ := xmTh_lim hl hX hζ2 hlim t htζ
    obtain ⟨c, hc, hcζ, hct⟩ := gxTh_onto ht1
    have hyq : y' < leOe H * (t + 1) := by
      have := Ordinal.lt_mul_succ_div y' hOH; rwa [Order.succ_eq_add_one] at this
    have hzq : z.1 < vbT S l β + leOe (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) c) := by
      rw [hct]
      exact hzy.trans_le ((add_le_add_iff_left _).2 (Yy.yyOe_mono ((add_le_add_iff_left _).2 hyq.le)))
    have h2 := hread c hc hcζ
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzq.le).1))).1.trans h2

/-- **THE CHAIN `X₀ + W^h·ζ`** over a shift `X₀`, given the law at every `X₀ + e` and the successor step. -/
theorem zyChain {X₀ K₀ q₀ h H qh : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀) (hx : ZxEx S l h H qh) (hH0 : 0 < H)
    (Q₀ : Ordinal.{0} → Prop) (hQq : ∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1)))
    (hQup : ∀ β β', β ≤ β' → Q₀ β → Q₀ β')
    (H0 : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β)
    (Hs : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ β, VbD S l β →
      Ro.RoBaseE S l (X₀ + leWe h * ζ + leWe h) 0 β → ZyQ S l X₀ h qh Q₀ (ζ + 1) β →
      (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β', VbD S l β' →
        Ro.RoBaseE S l (X₀ + leWe h * ζ) e β' → ZyQ S l X₀ h qh Q₀ ζ β' → ZdLaw S l A (X₀ + leWe h * ζ) e β') →
      ZdLaw S l A (X₀ + leWe h * ζ + leWe h) 0 β) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe h * ζ) e β → ZyQ S l X₀ h qh Q₀ ζ β →
        ZdLaw S l A (X₀ + leWe h * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hQq' : ∀ ζ, ∀ β, ZyQ S l X₀ h qh Q₀ ζ β → GxCl (upsilon l) (ldAtR S l) ζ → 0 < ζ →
      max q₀ (max qh ζ) < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) := fun ζ β hQ hc hpos =>
    zyThr hQq hQ hc (zyQh hQ hpos)
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHζ =>
  intro hζc hζθ
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ', hζ'⟩ | hlim
  · subst h0
    intro e hec he2 β hβD hB hQ
    rw [mul_zero, add_zero] at hB ⊢
    exact H0 e hec he2 β hβD hB hQ.1
  · rw [succ_eq_add_one] at hζ'
    subst hζ'
    have hζ'2 : ζ' + 1 < Om (1 + 1) := hζθ.trans (psi_lt hκ2 _)
    have hζ'c : GxCl (upsilon l) (ldAtR S l) ζ' :=
      (ldHull_iff hl hX ((lt_add_one ζ').trans hζ'2)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hζ'2).2 hζc))
    have hζ'θ : ζ' < ConjT.th S := (lt_add_one ζ').trans hζθ
    have e1 : X₀ + leWe h * (ζ' + 1) = X₀ + leWe h * ζ' + leWe h := by rw [mul_add_one, add_assoc]
    refine zdTopUpQ hl hX hA hρ (zySh hl hX hs0 hx hζc hζθ) (ZyQ S l X₀ h qh Q₀ (ζ' + 1))
      (fun β hQ => hQq' (ζ' + 1) β hQ hζc (lt_of_le_of_lt zero_le (lt_add_one ζ')))
      (fun _ _ hle hQ => zyQ_up hQup hle hQ) fun β hβD hB hQ => ?_
    rw [e1] at hB ⊢
    exact Hs ζ' hζ'c hζ'θ β hβD hB hQ fun e hec he2 β' hβ'D hB' hQ' =>
      IHζ ζ' (lt_add_one ζ') hζ'c hζ'θ e hec he2 β' hβ'D hB' hQ'
  · refine zdTopUpQ hl hX hA hρ (zySh hl hX hs0 hx hζc hζθ) (ZyQ S l X₀ h qh Q₀ ζ)
      (fun β hQ => hQq' ζ β hQ hζc (pos_iff_ne_zero.2 hlim.ne_bot)) (fun _ _ hle hQ => zyQ_up hQup hle hQ)
      fun β hβD hB hQ => ?_
    exact zyLimSh hl hX hA hρ hs0 hx hH0 hζc hζθ hlim hβD hB fun ζ' hc hlt hB' =>
      IHζ ζ' hlt hc (hlt.trans hζθ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β hβD hB' (zyQ_mono hlt.le hQ)

/-- **THE CHAIN OF `Ω₂ = W¹`** over any shift `X₀`: the law at every `X₀ + Ω₂·ζ + e`. -/
theorem zyChain1 {X₀ K₀ q₀ : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀)
    (Q₀ : Ordinal.{0} → Prop) (hQq : ∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1)))
    (hQup : ∀ β β', β ≤ β' → Q₀ β → Q₀ β')
    (H0 : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe 1 * ζ) e β → ZyQ S l X₀ 1 0 Q₀ ζ β →
        ZdLaw S l A (X₀ + leWe 1 * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine zyChain hl hX hA hρ hs0 (zxEx_one hl hX) zero_lt_one Q₀ hQq hQup H0 fun ζ hc hθ β hβD hB hQ IHc => ?_
  have e2 : X₀ + leWe 1 * ζ + leWe 1 = X₀ + leWe 1 * ζ + Om (1 + 1) := by rw [leWe_one]
  rw [e2] at hB ⊢
  have hmono : S.psi (β + leWe X₀) (Om (1 + 1)) ≤ S.psi (β + leWe (X₀ + leWe 1 * ζ)) (Om (1 + 1)) :=
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1
  exact zdNextQ hl hX hA hρ (zySh hl hX hs0 (zxEx_one hl hX) hc hθ) (ZyQ S l X₀ 1 0 Q₀ (ζ + 1))
    (fun β' hQ' => max_lt ((hQq β' hQ'.1).trans_le (psi_mono hκ2 (add_le_add le_rfl
      (leWe_mono le_self_add))).1) (max_lt (SC_psi hκ2 _).1 (hQ'.2.2 ζ hc (lt_add_one ζ).le)))
    (fun _ _ hle hQ' => zyQ_up hQup hle hQ')
    (fun e hec he2 β' hβ'D hB' hQ' => IHc e hec he2 β' hβ'D hB' (zyQ_mono (lt_add_one ζ).le hQ'))
    0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β hβD hB hQ

/-- **EVERY FINITE POWER `W^n`, `n ≥ 1`**: over every shift `X₀` with the law at every `X₀ + e`, the law at every
`X₀ + W^n·ζ + e` on the bases with `ZyQ`. -/
theorem zyChainN : ∀ n : ℕ, 1 ≤ n → ∀ {X₀ K₀ q₀ : Ordinal.{0}}, ZdShQ S l X₀ K₀ q₀ →
    ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe (n : Ordinal.{0}) * ζ) e β →
        ZyQ S l X₀ (n : Ordinal.{0}) 0 Q₀ ζ β → ZdLaw S l A (X₀ + leWe (n : Ordinal.{0}) * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro X₀ K₀ q₀ hs0 Q₀ hQq hQup H0
    rw [Nat.cast_one]
    exact zyChain1 hl hX hA hρ hs0 Q₀ hQq hQup H0
  | succ n hn IHn =>
    intro X₀ K₀ q₀ hs0 Q₀ hQq hQup H0
    rw [Nat.cast_succ]
    have hxs : ZxEx S l ((n : Ordinal.{0}) + 1) ((n : Ordinal.{0}) + 1) 0 := by
      have h := zxEx_nat hl hX (S := S) (n + 1); rwa [Nat.cast_succ] at h
    refine zyChain hl hX hA hρ hs0 hxs (lt_of_le_of_lt zero_le (lt_add_one _)) Q₀ hQq hQup H0
      fun ζ hc hθ β hβD hB hQ IHc => ?_
    have hs' := zySh hl hX hs0 hxs hc hθ
    have hQζ : ZyQ S l X₀ ((n : Ordinal.{0}) + 1) 0 Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
    refine zxLawJ hl hX hA hρ hs' (zxEx_nat hl hX n) hβD hB (zyThr hQq hQζ hc (SC_psi hκ2 _).1) (SC_psi hκ2 _).1
      fun u hu huθ hown hBu => ?_
    exact IHn hs' (ZyQ S l X₀ ((n : Ordinal.{0}) + 1) 0 Q₀ ζ) (fun β' hQ' => zyThr hQq hQ' hc (SC_psi hκ2 _).1)
      (fun _ _ hle hQ' => zyQ_up hQup hle hQ') IHc u hu huθ 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β hβD hBu
      ⟨hQζ, (SC_psi hκ2 _).1, hown⟩

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^n·ζ + e`**, `n ≥ 1` (`ζ < θ`, `e < Ω₂` codes, on the bases with
`ZyQ`; the case `X₀ = Ω_{k+3}` of `zyChainN`, with `Xm.xmTopUp` at the codes). -/
theorem zyTopN (k n : ℕ) (hn : 1 ≤ n) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β →
        Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (n : Ordinal.{0}) * ζ) e β →
        ZyQ S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (n : Ordinal.{0}) 0 (fun _ => True) ζ β →
          ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (n : Ordinal.{0}) * ζ) e β :=
  zyChainN hl hX hA hρ n hn ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1) (fun _ => True)
    (fun _ _ => (SC_psi (InR_Om_succ 1) _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zy

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zy.zyChain
#print axioms Googology.Trans.PoR.InaccPsi.R2.Zy.zyChain1
#print axioms Googology.Trans.PoR.InaccPsi.R2.Zy.zyChainN
#print axioms Googology.Trans.PoR.InaccPsi.R2.Zy.zyTopN
