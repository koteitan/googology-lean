import Googology.Trans.PoR.InaccPsi.R2.KbJump

/-!
# Kc: THE CHAIN OF `W^h` FOR EVERY CODE EXPONENT `1 ≤ h < θ`, over any shift, with the thresholds at the first use

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdShQ`, `Zd.ZdLaw`, `Zx.ZxEx`, `Zy.ZyQ` as in `Zy.zyChain`.  The
exponents carry the cumulative condition

  `KcE λ X₀ h β :  h' < ψ₂(β + W^{X₀ + W^{h'}})` for every code `1 ≤ h' ≤ h`

(each exponent lies below the collapse at its first use; a normal base `β + W^{X₀ + W^h·ζ + e}` meets it, while
`ψ₂(β + W^{X₀})` may equal `h`).  The successor step is `Kb.kbLawJ` (the threshold of the jump exponent at its first
use), at `ζ = 0` over the shift `X₀` itself.

* `kcE_up`, `kcE_mono`, `kcE_shift`;
* `kcChain` (**THE CHAIN OF `W^h` FOR EVERY CODE `1 ≤ h < θ`**: over every shift `X₀` with the law at every `X₀ + e`
  on the bases with `Q₀` (`Q₀ ⇒ KcE … h`), the law at every `X₀ + W^h·ζ + e` on the bases with `ZyQ`; induction on `h`:
  `Zy.zyChain1`, `Zy.zyChain` with `Kb.kbLawJ`, `Zy.zyChain` with `Zz.zzLimW`),
* `kcTop` (**THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^h·ζ + e`**, `h`, `ζ`, `e` codes).

No new axiom.  New definition: `KcE` (the exponent condition).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz
  Googology.Trans.PoR.InaccPsi.R2.Kb

variable {S : InaccSeq.{0}}

/-- **The exponent condition**: every code `1 ≤ h' ≤ h` lies below `ψ₂(β + W^{X₀ + W^{h'}})`. -/
def KcE (S : InaccSeq.{0}) (l X₀ h β : Ordinal.{0}) : Prop :=
  ∀ h', GxCl (upsilon l) (ldAtR S l) h' → 1 ≤ h' → h' ≤ h → h' < S.psi (β + leWe (X₀ + leWe h')) (Om (1 + 1))

theorem kcE_up {l X₀ h β β' : Ordinal.{0}} (hle : β ≤ β') (hE : KcE S l X₀ h β) : KcE S l X₀ h β' :=
  fun h' hc h1 hh => (hE h' hc h1 hh).trans_le (psi_mono (InR_Om_succ 1) (add_le_add hle le_rfl)).1

theorem kcE_mono {l X₀ h h₁ β : Ordinal.{0}} (hle : h₁ ≤ h) (hE : KcE S l X₀ h β) : KcE S l X₀ h₁ β :=
  fun h' hc h1 hh => hE h' hc h1 (hh.trans hle)

theorem kcE_shift {l X₀ X₁ h β : Ordinal.{0}} (hle : X₀ ≤ X₁) (hE : KcE S l X₀ h β) : KcE S l X₁ h β :=
  fun h' hc h1 hh => (hE h' hc h1 hh).trans_le (psi_mono (InR_Om_succ 1) (add_le_add le_rfl
    (leWe_mono (add_le_add hle le_rfl)))).1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The shift `X₀ + W^h·ζ` with a threshold below `ψ₂(β + W^{X₀ + W^h·ζ})` on every base with `ZyQ`: `zySh` for
`ζ > 0`, the shift `X₀` itself for `ζ = 0`. -/
theorem kcSh {X₀ K₀ q₀ h H : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀) (hx : ZxEx S l h H h) {Q₀ : Ordinal.{0} → Prop}
    (hQq : ∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) {ζ : Ordinal.{0}}
    (hζc : GxCl (upsilon l) (ldAtR S l) ζ) (hζθ : ζ < ConjT.th S) :
    ∃ q', ZdShQ S l (X₀ + leWe h * ζ) (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ) q' ∧
      ∀ β, ZyQ S l X₀ h h Q₀ ζ β → q' < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) := by
  rcases eq_or_ne ζ 0 with rfl | hne
  · refine ⟨q₀, ?_, fun β hQ => ?_⟩
    · rw [gxTh_zero, mul_zero, mul_zero, add_zero, add_zero]; exact hs0
    · rw [mul_zero, add_zero]; exact hQq β hQ.1
  · exact ⟨_, zySh hl hX hs0 hx hζc hζθ, fun β hQ => zyThr hQq hQ hζc (zyQh hQ (pos_iff_ne_zero.2 hne))⟩

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE CHAIN OF `W^h` FOR EVERY CODE `1 ≤ h < θ`** over every shift `X₀` with the law at every `X₀ + e`. -/
theorem kcChain : ∀ h, GxCl (upsilon l) (ldAtR S l) h → 1 ≤ h → h < ConjT.th S →
    ∀ {X₀ K₀ q₀ : Ordinal.{0}}, ZdShQ S l X₀ K₀ q₀ →
    ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') → (∀ β, Q₀ β → KcE S l X₀ h β) →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe h * ζ) e β →
        ZyQ S l X₀ h h Q₀ ζ β → ZdLaw S l A (X₀ + leWe h * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hΘpos : ∀ c, 0 < c → 0 < gxTh (upsilon l) (ldAtR S l) c := fun c hc => by
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
      intro X₀ K₀ q₀ hs0 Q₀ hQq hQup _ H0 ζ hζc hζθ e hec he2 β hβD hB hQ
      rw [zero_add] at hB hQ ⊢
      exact zyChain1 hl hX hA hρ hs0 Q₀ hQq hQup H0 ζ hζc hζθ e hec he2 β hβD hB
        ⟨hQ.1, (SC_psi hκ2 _).1, hQ.2.2⟩
    · -- a successor `h' + 1`, `h' ≥ 1`: the jump at `h'`
      have hh'1 : 1 ≤ h' := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)
      intro X₀ K₀ q₀ hs0 Q₀ hQq hQup hQE H0
      have hxs := zxEx_code hl hX hc hθ
      refine zyChain hl hX hA hρ hs0 hxs (hΘpos _ (lt_of_le_of_lt zero_le (lt_add_one h'))) Q₀ hQq hQup H0
        fun ζ hζc hζθ β hβD hB hQ IHc => ?_
      obtain ⟨q', hs', hq'⟩ := kcSh hl hX hs0 hxs hQq hζc hζθ
      have hQζ : ZyQ S l X₀ (h' + 1) (h' + 1) Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
      have hXle : X₀ ≤ X₀ + leWe (h' + 1) * ζ := le_self_add
      have hE' : ∀ β', ZyQ S l X₀ (h' + 1) (h' + 1) Q₀ ζ β' → KcE S l (X₀ + leWe (h' + 1) * ζ) h' β' :=
        fun β' hQ' => kcE_shift hXle (kcE_mono (lt_add_one h').le (hQE β' hQ'.1))
      have hh'X : h' < S.psi (β + leWe (X₀ + leWe (h' + 1) * ζ + leWe h')) (Om (1 + 1)) :=
        hE' β hQζ h' hh'c hh'1 le_rfl
      refine kbLawJ hl hX hA hρ hs' (zxEx_code hl hX hh'c hh'θ) hβD hB (hq' β hQζ) hh'X
        fun u hu huθ hown hBu => ?_
      exact IH h' (lt_add_one h') hh'c hh'1 hh'θ hs' (ZyQ S l X₀ (h' + 1) (h' + 1) Q₀ ζ) hq'
        (fun _ _ hle hQ' => zyQ_up hQup hle hQ') hE' IHc u hu huθ 0 h0c ldOm2_SC.1 β hβD hBu
        ⟨hQζ, hh'X, hown⟩
  · -- a limit code `h`: `T` is continuous at `h`
    intro X₀ K₀ q₀ hs0 Q₀ hQq hQup hQE H0
    have hxs := zxEx_code hl hX hc hθ
    have hh0 : (0 : Ordinal.{0}) < h := pos_iff_ne_zero.2 hlim.ne_bot
    refine zyChain hl hX hA hρ hs0 hxs (hΘpos _ hh0) Q₀ hQq hQup H0 fun ζ hζc hζθ β hβD hB hQ IHc => ?_
    obtain ⟨q', hs', hq'⟩ := kcSh hl hX hs0 hxs hQq hζc hζθ
    have hQζ : ZyQ S l X₀ h h Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
    have hXle : X₀ ≤ X₀ + leWe h * ζ := le_self_add
    refine zzLimW hl hX hA hρ hs' hxs (hΘpos _ hh0) hβD fun y hy => ?_
    obtain ⟨c, hcc, hch, hcy⟩ := gxTh_onto (xmTh_lim hl hX h2 hlim y hy)
    have hc0 : 0 < c := by
      rcases eq_or_ne c 0 with h0 | h0
      · exfalso; rw [h0, gxTh_zero] at hcy; exact absurd hcy.symm (lt_of_le_of_lt zero_le (lt_add_one y)).ne'
      · exact pos_iff_ne_zero.2 h0
    have hc1 : 1 ≤ c := Order.one_le_iff_pos.2 hc0
    have hcθ : c < ConjT.th S := hch.trans hθ
    have hcx := zxEx_code hl hX hcc hcθ
    refine ⟨c, hcx.D, hch.le, by rw [hcx.T, hcy]; exact lt_add_one y, ?_⟩
    have hle : X₀ + leWe h * ζ + leWe c * 1 ≤ X₀ + leWe h * ζ + leWe h := by
      rw [mul_one]; exact add_le_add le_rfl (leWe_mono hch.le)
    have hE' : ∀ β', ZyQ S l X₀ h h Q₀ ζ β' → KcE S l (X₀ + leWe h * ζ) c β' :=
      fun β' hQ' => kcE_shift hXle (kcE_mono hch.le (hQE β' hQ'.1))
    have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
    have hlw := IH c hch hcc hc1 hcθ hs' (ZyQ S l X₀ h h Q₀ ζ) hq'
      (fun _ _ hle hQ' => zyQ_up hQup hle hQ') hE' IHc 1 h1c h1θ 0 h0c ldOm2_SC.1 β hβD
      (zzBase0_mono hle hB) ⟨hQζ, hE' β hQζ c hcc hc1 le_rfl, fun u' _ hu' =>
        hu'.trans_lt ((gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1)⟩
    rwa [mul_one] at hlw

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^h·ζ + e`**, `h` a code with `1 ≤ h < θ` (`ζ < θ`, `e < Ω₂` codes,
on the bases with `ZyQ` and `KcE`). -/
theorem kcTop (k : ℕ) (h : Ordinal.{0}) (hc : GxCl (upsilon l) (ldAtR S l) h) (h1 : 1 ≤ h)
    (hθ : h < ConjT.th S) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β →
        Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ) e β →
        ZyQ S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) h h (KcE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) h) ζ β →
          ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ) e β :=
  kcChain hl hX hA hρ h hc h1 hθ ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1)
    (KcE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) h) (fun _ _ => (SC_psi (InR_Om_succ 1) _).1)
    (fun _ _ hle hE => kcE_up hle hE) (fun _ hE => hE)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kc

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kc.kcChain
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kc.kcTop
