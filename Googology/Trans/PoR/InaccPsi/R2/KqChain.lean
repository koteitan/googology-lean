import Googology.Trans.PoR.InaccPsi.R2.KpCls

/-!
# Kq: THE CHAIN OF `W^g` FOR EVERY `W`-TERM `g ≥ 1` OVER THE CODES, over any shift

`Θ`, `T`, `A`, `W^x = leWe x`, `Zd.ZdShQ`, `Zd.ZdLaw`, `Zx.ZxEx`, `Zy.ZyQ`, `Ko.KoThr` as before.  The base condition
is `Zy.ZyQ λ X₀ g q_g Q₀ ζ β` alone: its second component `q_g < ψ₂(β + W^{X₀ + W^g})` (the threshold of `g` at its
first use) passes to every piece met on the way down by `Ko.koGOL_top` (the predecessor) and `Kp.kpClass` (the
members of a continuity family, the values of a context).

* `kqSh` (the shift `X₀ + W^h·ζ` with a threshold below `ψ₂(β + W^{X₀ + W^h·ζ})` on the bases with `ZyQ`),
  `kqBase1` (`Ro.RoBaseE (X + W⁰) 0 β ⇒ Ro.RoBaseE X 1 β`);
* `kqChain` (**THE CHAIN OF `W^g` FOR EVERY `W`-TERM `g ≥ 1`**: over every shift `X₀` with the law at every `X₀ + e`
  on the bases with `Q₀`, the law at every `X₀ + W^g·ζ + e` on the bases with `ZyQ`; strong induction on `g`:
  `Zy.zyChain1` at `g = 1`, `Zy.zyChain` with `Kb.kbLawJ` at a successor, with `Zz.zzLimW` at a point of continuity
  of `T`, with `Ke.keLaw` at the top of a context),
* `kqTop` (**THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^g·ζ + e`**, `g ≥ 1` a `W`-term over the codes).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz
  Googology.Trans.PoR.InaccPsi.R2.Kb Googology.Trans.PoR.InaccPsi.R2.Ke Googology.Trans.PoR.InaccPsi.R2.Ko
  Googology.Trans.PoR.InaccPsi.R2.Kp

variable {S : InaccSeq.{0}}

/-- `Ro.RoBaseE (X + W⁰) 0 β ⇒ Ro.RoBaseE X 1 β`. -/
theorem kqBase1 {l X β : Ordinal.{0}} (hB : Ro.RoBaseE S l (X + leWe 0) 0 β) : Ro.RoBaseE S l X 1 β := by
  unfold Ro.RoBaseE at hB ⊢
  rw [leWe_zero, add_zero] at hB
  obtain ⟨h1, h2, h3, h4, -⟩ := hB
  exact ⟨h1, h2, h3, h4, fun e' _ he' =>
    he'.trans_lt ((gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1)⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The shift `X₀ + W^h·ζ` with a threshold below `ψ₂(β + W^{X₀ + W^h·ζ})` on every base with `ZyQ`. -/
theorem kqSh {X₀ K₀ q₀ h H qh : Ordinal.{0}} (hs0 : ZdShQ S l X₀ K₀ q₀) (hx : ZxEx S l h H qh)
    {Q₀ : Ordinal.{0} → Prop} (hQq : ∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) {ζ : Ordinal.{0}}
    (hζc : GxCl (upsilon l) (ldAtR S l) ζ) (hζθ : ζ < ConjT.th S) :
    ∃ q', ZdShQ S l (X₀ + leWe h * ζ) (K₀ + leOe H * gxTh (upsilon l) (ldAtR S l) ζ) q' ∧
      ∀ β, ZyQ S l X₀ h qh Q₀ ζ β → q' < S.psi (β + leWe (X₀ + leWe h * ζ)) (Om (1 + 1)) := by
  rcases eq_or_ne ζ 0 with rfl | hne
  · refine ⟨q₀, ?_, fun β hQ => ?_⟩
    · rw [gxTh_zero, mul_zero, mul_zero, add_zero, add_zero]; exact hs0
    · rw [mul_zero, add_zero]; exact hQq β hQ.1
  · exact ⟨_, zySh hl hX hs0 hx hζc hζθ, fun β hQ => zyThr hQq hQ hζc (zyQh hQ (pos_iff_ne_zero.2 hne))⟩

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE CHAIN OF `W^g` FOR EVERY `W`-TERM `g ≥ 1`** over every shift `X₀` with the law at every `X₀ + e`. -/
theorem kqChain : ∀ g qg, KoThr S l g qg → 1 ≤ g →
    ∀ {X₀ K₀ q₀ : Ordinal.{0}}, ZdShQ S l X₀ K₀ q₀ →
    ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + leWe g * ζ) e β →
        ZyQ S l X₀ g qg Q₀ ζ β → ZdLaw S l A (X₀ + leWe g * ζ) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
  have h1Ω : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h1P : ∀ x, (1 : Ordinal.{0}) < S.psi x (Om (1 + 1)) := fun x =>
    (gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) x 1).1
  have hT0 : vbT S l 0 = 0 := Vh.vhT_zero hl hX
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro qg hk h1 X₀ K₀ q₀ hs0 Q₀ hQq hQup H0
  have hxs := koEx hl hX hk
  have hg0 : 0 < g := zero_lt_one.trans_le h1
  have hH0 : 0 < vbT S l g := by
    have h := vbT_mono hl hX (Xi.xiD_zero l) hxs.D hg0
    rwa [hT0] at h
  rcases zero_or_succ_or_isSuccLimit g with h0 | ⟨g', hg'⟩ | hlim
  · exact absurd h0 hg0.ne'
  · rw [succ_eq_add_one] at hg'
    subst hg'
    rcases eq_or_ne g' 0 with rfl | hne
    · -- `g = 1`
      intro ζ hζc hζθ e hec he2 β hβD hB hQ
      rw [zero_add] at hB hQ ⊢
      exact zyChain1 hl hX hA hρ hs0 Q₀ hQq hQup H0 ζ hζc hζθ e hec he2 β hβD hB
        ⟨hQ.1, (SC_psi hκ2 _).1, hQ.2.2⟩
    · -- a successor `g' + 1`, `g' ≥ 1`: the jump at `g'`
      have hg'1 : 1 ≤ g' := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)
      obtain ⟨qg', hqg'le, hkg'⟩ := kpPred hl hX hk g' rfl
      refine zyChain hl hX hA hρ hs0 hxs hH0 Q₀ hQq hQup H0 fun ζ hζc hζθ β hβD hB hQ IHc => ?_
      obtain ⟨q', hs', hq'⟩ := kqSh hl hX hs0 hxs hQq hζc hζθ
      have hQζ : ZyQ S l X₀ (g' + 1) qg Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
      have hXle : X₀ ≤ X₀ + leWe (g' + 1) * ζ := le_self_add
      have hqh : qg' < S.psi (β + leWe (X₀ + leWe (g' + 1) * ζ + leWe g')) (Om (1 + 1)) := by
        refine koGOL_top hl hX hkg' ?_
        exact (hqg'le.trans_lt hQ.2.1).trans_le
          (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add hXle le_rfl)))).1
      exact kbLawJ hl hX hA hρ hs' (koEx hl hX hkg') hβD hB (hq' β hQζ) hqh fun u hu huθ hown hBu =>
        IH g' (lt_add_one g') qg' hkg' hg'1 hs' (ZyQ S l X₀ (g' + 1) qg Q₀ ζ) hq'
          (fun _ _ hle hQ' => zyQ_up hQup hle hQ') IHc u hu huθ 0 h0c ldOm2_SC.1 β hβD hBu ⟨hQζ, hqh, hown⟩
  · -- a limit `W`-term: continuity of `T`, or the top of a context
    refine zyChain hl hX hA hρ hs0 hxs hH0 Q₀ hQq hQup H0 fun ζ hζc hζθ β hβD hB hQ IHc => ?_
    obtain ⟨q', hs', hq'⟩ := kqSh hl hX hs0 hxs hQq hζc hζθ
    have hQζ : ZyQ S l X₀ g qg Q₀ ζ β := zyQ_mono (lt_add_one ζ).le hQ
    set X := X₀ + leWe g * ζ with hXdef
    have hXle : X₀ ≤ X := le_self_add
    have hqgX : qg < S.psi (β + leWe (X + leWe g)) (Om (1 + 1)) :=
      hQ.2.1.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add hXle le_rfl)))).1
    -- the law at an owned `W`-term `g' < g` over the shift `X`
    have hIH1 : ∀ g' q'', KoThr S l g' q'' → 1 ≤ g' → g' < g →
        q'' < S.psi (β + leWe (X + leWe g')) (Om (1 + 1)) → Ro.RoBaseE S l (X + leWe g') 0 β →
          ZdLaw S l A (X + leWe g') 0 β := by
      intro g' q'' hk' hg'1 hg'lt hq'' hB'
      have h := IH g' hg'lt q'' hk' hg'1 hs' (ZyQ S l X₀ g qg Q₀ ζ) hq' (fun _ _ hle hQ' => zyQ_up hQup hle hQ')
        IHc 1 h1c h1θ 0 h0c ldOm2_SC.1 β hβD (by rwa [mul_one])
        ⟨hQζ, hq'', fun ζ' _ hζ' => hζ'.trans_lt (h1P _)⟩
      rwa [mul_one] at h
    rcases kpClass hl hX (β := β) hk hlim (F := fun v => X + leWe v)
        (fun _ _ hle => add_le_add le_rfl (leWe_mono hle)) (koTw_top X) (SC_psi hκ2 _).1 hqgX with
      hcont | ⟨C, R, t, qC, hC, -, hqC, hCv⟩
    · -- continuity of `T` at `g`
      refine zzLimW hl hX hA hρ hs' hxs hH0 hβD fun y hy => ?_
      obtain ⟨g', q'', hk', hg'1, hg'lt, hyg', hq''⟩ := hcont y hy
      exact ⟨g', (koEx hl hX hk').D, hg'lt.le, hyg', hIH1 g' q'' hk' hg'1 hg'lt hq''
        (zzBase0_mono (add_le_add le_rfl (leWe_mono hg'lt.le)) hB)⟩
    · -- the top of a context
      refine keLaw hl hX hA hρ (keCtx_nest hl hX (ZdShQ.toEx hs') hC) hβD hB ?_ fun v hv hvθ hown hBv => ?_
      · exact max_lt ((hq' β hQζ).trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1) hqC
      · obtain ⟨hClt, hCown⟩ := hCv v hv hvθ
        show ZdLaw S l A (X + leWe (C v)) 0 β
        rcases eq_or_ne (C v) 0 with hC0 | hC0
        · -- `C v = 0`: the law at `X + 1`
          have hBv' : Ro.RoBaseE S l (X + leWe 0) 0 β := by
            have h := hBv
            simp only [hC0] at h
            exact h
          have h := IHc 1 h1c h1Ω β hβD (kqBase1 hBv') hQζ
          unfold ZdLaw at h ⊢
          rw [hC0, leWe_zero, add_zero]
          exact h
        · obtain ⟨q'', hk'', hq''⟩ := hCown (hown v hv le_rfl)
          exact hIH1 (C v) q'' hk'' (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hC0)) hClt hq'' hBv

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^g·ζ + e`**, `g ≥ 1` a `W`-term over the codes (`ζ < θ`, `e < Ω₂`
codes, on the bases with `ZyQ`). -/
theorem kqTop (k : ℕ) (g qg : Ordinal.{0}) (hk : KoThr S l g qg) (h1 : 1 ≤ g) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ConjT.th S → ∀ e, GxCl (upsilon l) (ldAtR S l) e →
      e < Om (1 + 1) → ∀ β, VbD S l β →
        Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe g * ζ) e β →
        ZyQ S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) g qg (fun _ => True) ζ β →
          ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe g * ζ) e β :=
  kqChain hl hX hA hρ g qg hk h1 ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1) (fun _ => True)
    (fun _ _ => (SC_psi (InR_Om_succ 1) _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kq

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kq.kqChain
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kq.kqTop
