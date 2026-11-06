import Googology.Trans.PoR.InaccPsi.R2.ZyChain

/-!
# Zz: THE CHAIN OF `W^h` FOR EVERY CODE EXPONENT `1 ≤ h < θ`, over any shift

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdShQ`, `Zd.ZdLaw`, `Zx.ZxEx`, `Zy.ZyQ` as in `Zy.zyChain`.  A code
`h < θ` is an exponent with `T h = Θ h` and threshold `h` (`zxEx_code`).  At a limit code `h` the map `T` is
continuous (`Θ h` is a limit and every reading below it is the reading of a code below `h`), so the law at `X + W^h`
is the limit of the laws at `X + W^{h'}`, `h' < h` (`zzLimW`).

* `zzT_W` (`T(β + W^{X + W^g}) = Tβ + Ω^{K + Ω^{T g}}`), `zzBase0_mono` (a base of exponent `0` of `X` is one of
  every `X' ≤ X`), `zxEx_code`;
* `zzLimW` (**THE LIMIT EXPONENT**: if the readings `T h'` of exponents `h' ≤ h` with the law at `X + W^{h'}` are
  cofinal in `T h > 0`, the law holds at `X + W^h`);
* `zzChain` (**THE CHAIN OF `W^h` FOR EVERY CODE `1 ≤ h < θ`**: over every shift `X₀` with the law at every `X₀ + e`,
  the law at every `X₀ + W^h·ζ + e`, `ζ < θ`, `e < Ω₂` codes, on the bases with `ZyQ`; induction on `h`: `h = 1` is
  `Zy.zyChain1`, a successor `h' + 1` is `Zy.zyChain` with the jump `Zx.zxLawJ` at `h'`, a limit is `Zy.zyChain` with
  `zzLimW`), `zzTop` (**the top law at every exponent `Ω_{k+3} + W^h·ζ + e`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy

variable {S : InaccSeq.{0}}

/-- A base of exponent `0` of `X` is a base of exponent `0` of every `X' ≤ X`. -/
theorem zzBase0_mono {l X X' β : Ordinal.{0}} (hle : X' ≤ X) (hB : Ro.RoBaseE S l X 0 β) :
    Ro.RoBaseE S l X' 0 β := by
  unfold Ro.RoBaseE at hB ⊢
  simp only [add_zero] at hB ⊢
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hB
  refine ⟨(leWe_dvd hle).trans hβd, hβH, lt_of_le_of_lt (add_le_add le_rfl (leWe_mono hle)) hβA,
    fun d hd => hβown d (hd.trans (leWe_mono hle)), fun e'' _ he'' => ?_⟩
  rw [nonpos_iff_eq_zero.1 he'']
  exact (SC_psi (InR_Om_succ 1) _).1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T(β + W^{X + W^g}) = Tβ + Ω^{K + Ω^{T g}}`**, and `β + W^{X + W^g} ∈ D`. -/
theorem zzT_W {X K q g β : Ordinal.{0}} (hs : ZdShQ S l X K q) (hg : VbD S l g) (hβD : VbD S l β) :
    VbD S l (β + leWe (X + leWe g)) ∧
      vbT S l (β + leWe (X + leWe g)) = vbT S l β + leOe (K + leOe (vbT S l g)) := by
  obtain ⟨hWgD, hWgT⟩ := zxTW hl hX hg
  have hYD : VbD S l (X + leWe g) :=
    ⟨CSet.add_mem hs.memH hWgD.1, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) hWgD.2.1,
      vkOmW.1.isPrincipal hs.lt hWgD.2.2⟩
  have hTY : vbT S l (X + leWe g) = K + leOe (vbT S l g) := by rw [Vh.vhT_add hl hX hs.D hWgD, hs.T, hWgT]
  obtain ⟨hWD, hTW⟩ := zxTW hl hX hYD
  refine ⟨⟨CSet.add_mem hβD.1 hWD.1, CSet.add_mem hβD.2.1 hWD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWD.2.2⟩, ?_⟩
  rw [Vh.vhT_add hl hX hβD hWD, hTW, hTY]

/-- A code `h < θ` is an exponent: `T h = Θ h`, threshold `h`. -/
theorem zxEx_code {h : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) h) (hθ : h < ConjT.th S) :
    ZxEx S l h (gxTh (upsilon l) (ldAtR S l) h) h := by
  have h2 : h < Om (1 + 1) := hθ.trans (psi_lt (InR_Om_succ 1) _)
  have hH : h ∈ cdHull S l := (ldHull_iff hl hX h2).2 hc
  exact ⟨⟨hH, CSet.of_lt hθ, h2.trans ldOm2_lt_OmW⟩, vbT_code hl hX h2 hH, fun a c _ hq => CSet.of_lt hq,
    fun a c _ hq => CSet.of_lt hq, hc, hθ⟩

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT EXPONENT**: if the readings `T h'` of exponents `h' ≤ h` with the law at `X + W^{h'}` over `β`
are cofinal in `T h = H > 0`, the law holds at `X + W^h` over `β`. -/
theorem zzLimW {X K q h H qh : Ordinal.{0}} (hs : ZdShQ S l X K q) (hx : ZxEx S l h H qh) (hH0 : 0 < H)
    {β : Ordinal.{0}} (hβD : VbD S l β)
    (hfam : ∀ y, y < H → ∃ h', VbD S l h' ∧ h' ≤ h ∧ y < vbT S l h' ∧ ZdLaw S l A (X + leWe h') 0 β) :
    ZdLaw S l A (X + leWe h) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  obtain ⟨hD, hT⟩ := zzT_W hl hX hs hx.D hβD
  rw [hx.T] at hT
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  -- the law at a member of the family, read over `β + W^{X + W^h}`
  have hread : ∀ h', VbD S l h' → h' ≤ h → ZdLaw S l A (X + leWe h') 0 β →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (K + leOe (vbT S l h'))) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + leWe h)) (Om (1 + 1))) := by
    intro h' hD' hle hlw
    unfold ZdLaw leTe at hlw
    rw [add_zero, (zzT_W hl hX hs hD' hβD).2] at hlw
    rw [← hlw]
    exact gxTh_mono (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add le_rfl (leWe_mono hle))))).1
  unfold ZdLaw leTe
  rw [add_zero, hT]
  rw [hT] at hup
  refine le_antisymm hup ?_
  obtain ⟨h₀, hD₀, hle₀, -, hlw₀⟩ := hfam 0 hH0
  have hr0 := hread h₀ hD₀ hle₀ hlw₀
  set L := vbT S l β + leOe (K + leOe H) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hKpos : 0 < Om 1 * (K + leOe H) := mul_pos (Om_pos one_ne_zero) (hs.Kpos.trans_le le_self_add)
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hKpos.ne')
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < Tβ + Ω^{K + Ω^H}` gives `z < Tβ + Ω^{K + Ω^{T h'}}` for a member `h'` of the family
    have hOHlim : IsSuccLimit (leOe H) :=
      isSuccLimit_opow_left isSuccLimit_omega0 (mul_pos (Om_pos one_ne_zero) hH0).ne'
    have hy0 : 0 < leOe H := opow_pos _ omega0_pos
    obtain ⟨y', hy', hzy⟩ := xmCofL hy0 (fun y'' hy'' => hOHlim.add_one_lt hy'') z.2
    obtain ⟨h', hD', hle', hlw'⟩ : ∃ h', VbD S l h' ∧ h' ≤ h ∧ y' < leOe (vbT S l h') ∧
        ZdLaw S l A (X + leWe h') 0 β := by
      rcases eq_or_ne y' 0 with h0 | h0
      · obtain ⟨h'', hD'', hle'', -, hlw''⟩ := hfam 0 hH0
        exact ⟨h'', hD'', hle'', by rw [h0]; exact opow_pos _ omega0_pos, hlw''⟩
      · have hlog : log ω y' < Om 1 * H := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hy'
        have hyH : log ω y' / Om 1 < H := (Ordinal.lt_mul_iff_div_lt hO1).1 hlog
        obtain ⟨h'', hD'', hle'', hyh, hlw''⟩ := hfam _ hyH
        refine ⟨h'', hD'', hle'', (lt_opow_iff_log_lt one_lt_omega0 h0).2 ?_, hlw''⟩
        have := Ordinal.lt_mul_succ_div (log ω y') hO1
        rw [Order.succ_eq_add_one] at this
        exact this.trans_le (mul_le_mul_right (Order.add_one_le_of_lt hyh) _)
    have hzq : z.1 < vbT S l β + leOe (K + leOe (vbT S l h')) :=
      hzy.trans_le ((add_le_add_iff_left _).2 (Yy.yyOe_mono ((add_le_add_iff_left _).2 hlw'.1.le)))
    have h2 := hread h' hD' hle' hlw'.2
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzq.le).1))).1.trans h2

/-- **THE CHAIN OF `W^h` FOR EVERY CODE `1 ≤ h < θ`** over every shift `X₀` with the law at every `X₀ + e`. -/
theorem zzChain : ∀ h, GxCl (upsilon l) (ldAtR S l) h → 1 ≤ h → h < ConjT.th S →
    ∀ {X₀ K₀ q₀ : Ordinal.{0}}, ZdShQ S l X₀ K₀ q₀ →
    ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe h * ζ) e β →
        ZyQ S l X₀ h h Q₀ ζ β → ZdLaw S l A (X₀ + leWe h * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hΘpos : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 0 < c → 0 < gxTh (upsilon l) (ldAtR S l) c := fun c _ hc => by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c hc; rwa [gxTh_zero] at this
  intro h
  induction h using WellFoundedLT.induction with
  | ind h IH =>
  intro hc h1 hθ
  have h2 : h < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
  rcases zero_or_succ_or_isSuccLimit h with h0 | ⟨h', hh'⟩ | hlim
  · subst h0; intro X₀ K₀ q₀; exfalso; exact (not_le.2 zero_lt_one) h1
  · rw [succ_eq_add_one] at hh'
    subst hh'
    have hh'c : GxCl (upsilon l) (ldAtR S l) h' :=
      (ldHull_iff hl hX ((lt_add_one h').trans h2)).1 (mem_of_add_one_mem ((ldHull_iff hl hX h2).2 hc))
    have hh'θ : h' < ConjT.th S := (lt_add_one h').trans hθ
    rcases eq_or_ne h' 0 with rfl | hne
    · -- `h = 1`
      intro X₀ K₀ q₀ hs0 Q₀ hQq hQup H0 ζ hζc hζθ e hec he2 β hβD hB hQ
      rw [zero_add] at hB hQ ⊢
      exact zyChain1 hl hX hA hρ hs0 Q₀ hQq hQup H0 ζ hζc hζθ e hec he2 β hβD hB
        ⟨hQ.1, (SC_psi hκ2 _).1, hQ.2.2⟩
    · -- a successor `h' + 1`, `h' ≥ 1`: the jump at `h'`
      have hh'1 : 1 ≤ h' := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)
      intro X₀ K₀ q₀ hs0 Q₀ hQq hQup H0
      have hxs := zxEx_code hl hX hc hθ
      refine zyChain hl hX hA hρ hs0 hxs (hΘpos _ hc (lt_of_le_of_lt zero_le (lt_add_one h'))) Q₀ hQq hQup H0
        fun ζ hζc hζθ β hβD hB hQ IHc => ?_
      have hs' := zySh hl hX hs0 hxs hζc hζθ
      have hQζ : ZyQ S l X₀ (h' + 1) (h' + 1) Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
      have hmono : S.psi (β + leWe X₀) (Om (1 + 1)) ≤
          S.psi (β + leWe (X₀ + leWe (h' + 1) * ζ)) (Om (1 + 1)) :=
        (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1
      have hh'X : h' < S.psi (β + leWe (X₀ + leWe (h' + 1) * ζ)) (Om (1 + 1)) :=
        ((lt_add_one h').trans hQ.2.1).trans_le hmono
      refine zxLawJ hl hX hA hρ hs' (zxEx_code hl hX hh'c hh'θ) hβD hB (zyThr hQq hQζ hζc) hh'X
        fun u hu huθ hown hBu => ?_
      exact IH h' (lt_add_one h') hh'c hh'1 hh'θ hs' (ZyQ S l X₀ (h' + 1) (h' + 1) Q₀ ζ)
        (fun β' hQ' => zyThr hQq hQ' hζc) (fun _ _ hle hQ' => zyQ_up hQup hle hQ') IHc u hu huθ 0 h0c
        ldOm2_SC.1 β hβD hBu ⟨hQζ, hh'X, hown⟩
  · -- a limit code `h`: `T` is continuous at `h`
    intro X₀ K₀ q₀ hs0 Q₀ hQq hQup H0
    have hxs := zxEx_code hl hX hc hθ
    have hh0 : (0 : Ordinal.{0}) < h := pos_iff_ne_zero.2 hlim.ne_bot
    refine zyChain hl hX hA hρ hs0 hxs (hΘpos _ hc hh0) Q₀ hQq hQup H0 fun ζ hζc hζθ β hβD hB hQ IHc => ?_
    have hs' := zySh hl hX hs0 hxs hζc hζθ
    have hQζ : ZyQ S l X₀ h h Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
    have hmono : S.psi (β + leWe X₀) (Om (1 + 1)) ≤ S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) :=
      (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1
    refine zzLimW hl hX hA hρ hs' hxs (hΘpos _ hc hh0) hβD fun y hy => ?_
    obtain ⟨c, hcc, hch, hcy⟩ := gxTh_onto (xmTh_lim hl hX h2 hlim y hy)
    have hc0 : 0 < c := by
      rcases eq_or_ne c 0 with h0 | h0
      · exfalso; rw [h0, gxTh_zero] at hcy; exact absurd hcy.symm (lt_of_le_of_lt zero_le (lt_add_one y)).ne'
      · exact pos_iff_ne_zero.2 h0
    have hcθ : c < ConjT.th S := hch.trans hθ
    have hcx := zxEx_code hl hX hcc hcθ
    refine ⟨c, hcx.D, hch.le, by rw [hcx.T, hcy]; exact lt_add_one y, ?_⟩
    have hle : X₀ + leWe h * ζ + leWe c * 1 ≤ X₀ + leWe h * ζ + leWe h := by
      rw [mul_one]; exact add_le_add le_rfl (leWe_mono hch.le)
    have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
    have hlw := IH c hch hcc (Order.one_le_iff_pos.2 hc0) hcθ hs' (ZyQ S l X₀ h h Q₀ ζ)
      (fun β' hQ' => zyThr hQq hQ' hζc) (fun _ _ hle hQ' => zyQ_up hQup hle hQ') IHc 1 h1c h1θ 0 h0c
      ldOm2_SC.1 β hβD (zzBase0_mono hle hB) ⟨hQζ, (hch.trans hQ.2.1).trans_le hmono, fun u' _ hu' =>
        hu'.trans_lt ((gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1)⟩
    rwa [mul_one] at hlw

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^h·ζ + e`**, `h` a code with `1 ≤ h < θ` (`ζ < θ`, `e < Ω₂` codes, on
the bases with `ZyQ`; the case `X₀ = Ω_{k+3}` of `zzChain`, with `Xm.xmTopUp` at the codes). -/
theorem zzTop (k : ℕ) (h : Ordinal.{0}) (hc : GxCl (upsilon l) (ldAtR S l) h) (h1 : 1 ≤ h) (hθ : h < ConjT.th S) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β →
        Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ) e β →
        ZyQ S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) h h (fun _ => True) ζ β →
          ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ) e β :=
  zzChain hl hX hA hρ h hc h1 hθ ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1) (fun _ => True)
    (fun _ _ => (SC_psi (InR_Om_succ 1) _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zz.zzChain
#print axioms Googology.Trans.PoR.InaccPsi.R2.Zz.zzTop
