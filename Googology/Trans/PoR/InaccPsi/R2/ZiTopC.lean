import Googology.Trans.PoR.InaccPsi.R2.ZiCoef

/-!
# THE TOPS OF THE CODE CHAIN `P + Ω₂·ξ` (ξ a code) OVER A FIXED PREFIX `P`, AT ONE RESTART

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^x = leWe x`, `(P, P̂)` a fixed relative shift `Zd.ZdRS S P P̂` (the prefix; `(Y₃, Y₂)`
is one, `Zd.zdRS_Y3`), `X_ξ = Zi.ziXp P ξ = P + Ω₂·ξ`, `X̂_y = Zi.ziXhp P̂ y = P̂ + Ω₁·y`,
`T(b) = Zi.ziTC S P b = ψ₂(b + W^{P+Ω₂·Ω₂})`; "rst" = `IsRestartIdx λ`, `ρ_λ < P(η)`, `A` own, `ψ₁(A) = ρ_λ`.

For a CODE `ξ` of `λ` (not a constant: `B_n` moves it, `Θ` reads it as `Θ ξ`), the shift is `(P + Ω₂·ξ, P̂ + Ω₁·Θξ)`
relative to a base `b ≥ Ω₃`, and it is own over `b` exactly when `ξ < T(b)` (`Zi.ziOwnC_iff`).

* `ziVqShC` (**the `Vq.VqSh` fields of `(P + Ω₂·ξ, P̂ + Ω₁·Θξ)` at the base `b`** for every code `ξ < T(b)`),
* `ziTopC` (**THE TOPS**: `Rv.RvTop λ b (P + Ω₂·ξ) (P̂ + Ω₁·Θξ) e` for every code `ξ < T(b)` and every code `e`;
  induction on `ξ`: the tops of `P` at `0`, `Vq.vqTopW` at successors, `Vq.vqTopLimSh` at limits with
  `Θ` onto (`Mx.gxTh_onto`), then `Vq.vqTopE`).

These generalize `Zd.zdVqSh_chain`, `Zd.zdTop_chainR` (constants `ξ < ε₀`, base `Ω₃`) to every code `ξ < T(b)`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

section Rst

variable {P Pt : Ordinal.{0}} (hP : ZdRS S P Pt) {l ηx A b : Ordinal.{0}} (hl : IsRestartIdx l)
  (hX : upsilon l < Pv S ηx) (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
  (hb3 : Om (1 + 1 + 1) ≤ b)

include hP hl hX hA hρ hb3

/-- **The `Vq.VqSh` fields of the code shift `(P + Ω₂·ξ, P̂ + Ω₁·Θξ)`** at the base `b`, `ξ < T(b)` a code. -/
theorem ziVqShC {ξ : Ordinal.{0}} (hξc : GxCl (upsilon l) (ldAtR S l) ξ) (hξT : ξ < ziTC S P b) :
    Vq.VqSh S l A b (ziXp P ξ) (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ξ)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hAo : Om ω ≤ A := Vn.vnA_ge hl hX hA hρ
  have hξ2 : ξ < Om (1 + 1) := hξT.trans (ziTC_lt_Om2 P b)
  have hξH : ξ ∈ cdHull S l := (ldHull_iff hl hX hξ2).2 hξc
  have hown : ξ < S.psi (b + leWe (ziXp P ξ)) (Om (1 + 1)) := (ziOwnC_iff P b ξ).2 hξT ξ le_rfl
  have hΘ : gxTh (upsilon l) (ldAtR S l) ξ <
      gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (ziXp P ξ)) (Om (1 + 1))) := gxTh_lt hξc hown
  have hsP := hP.sh l _ _ hl hX hA hρ
  have hx2 : Om (1 + 1 + 1) + leWe P ≤ b + leWe (ziXp P ξ) := add_le_add hb3 (leWe_mono le_self_add)
  refine ⟨?_, dvd_add hsP.dvd (dvd_mul_right _ _), ?_, ?_, ?_, fun Q hQ hQb => ?_, fun Q hQ hQb => ?_⟩
  · unfold ziXp; exact ((pos_iff_ne_zero.2 hP.ne).trans_le le_self_add).ne'
  · exact CSet.add_mem (hP.mem _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)))
      (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH)
  · exact CSet.add_mem (hP.mem _ _ (hb3.trans_lt (lt_add_of_pos_right _ (leWe_pos _))))
      (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hown))
  · unfold ziXhp
    exact CSet.add_mem (Vq.vqMemh hsP ((add_le_add_iff_left A).2 (leOe_mono le_self_add)) hx2 le_rfl)
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt hΘ))
  · unfold ziXp
    have h := ziVkA_opowMul hQ.1 (VkA.big (k := 1 + 1) (Q := Q) le_rfl ldOm2_SC) ξ (hown.trans_le hQb)
    rw [gg_SC_eps ldOm2_SC] at h
    exact VkA.add (Vq.vqCl hsP hQ hx2 hQb) h
  · unfold ziXhp
    have h := ziVkA_opowMul hQ.1 (VkA.big (k := 1) (Q := Q) le_rfl Ph.ph_SC_Om1) _ (hΘ.trans_le hQb)
    rw [gg_SC_eps Ph.ph_SC_Om1] at h
    exact VkA.add (Vq.vqClh hsP hQ hx2 hQb) h

/-- **THE TOPS OF THE CODE CHAIN**: `Rv.RvTop λ b (P + Ω₂·ξ) (P̂ + Ω₁·Θξ) e` for every code `ξ < T(b)` and every
code `e`. -/
theorem ziTopC : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → ξ < ziTC S P b →
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Rv.RvTop S l b (ziXp P ξ) (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ξ)) e := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξc hξT
  have hξ2 : ξ < Om (1 + 1) := hξT.trans (ziTC_lt_Om2 P b)
  have hs := ziVqShC hP hl hX hA hρ hb3 hξc hξT
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ζ, hζ⟩ | hlim
  · subst h0
    rw [ziXp_zero, gxTh_zero, ziXhp_zero]
    exact fun e hec he2 => Rv.rvTop_mono hb3 (hP.top l _ _ hl hX hA hρ e hec he2)
  · rw [succ_eq_add_one] at hζ
    subst hζ
    have hζ2 : ζ < Om (1 + 1) := (lt_add_one ζ).trans hξ2
    have hζc : GxCl (upsilon l) (ldAtR S l) ζ :=
      (ldHull_iff hl hX hζ2).1 (mem_of_add_one_mem ((ldHull_iff hl hX hξ2).2 hξc))
    have hζT : ζ < ziTC S P b := (lt_add_one ζ).trans hξT
    have hsζ := ziVqShC hP hl hX hA hρ hb3 hζc hζT
    have h0 := Vq.vqTopW hsζ hl hX hA hρ (IHξ ζ (lt_add_one ζ) hζc hζT)
    have hΘs : gxTh (upsilon l) (ldAtR S l) (ζ + 1) = gxTh (upsilon l) (ldAtR S l) ζ + 1 := by
      rw [gxTh_add hρSC hAt hζc 1, hΘ1]
    rw [← ziXp_succ, ← ziXhp_succ, ← hΘs] at h0
    exact Vq.vqTopE hs hl hX hA hρ h0
  · have hξ0 : (0 : Ordinal.{0}) < ξ := pos_iff_ne_zero.2 hlim.ne_bot
    have hs0 := ziVqShC hP hl hX hA hρ hb3 h0c ((zero_le).trans_lt hξT)
    have hT0 := IHξ 0 hξ0 h0c ((zero_le).trans_lt hξT) 0 h0c ldOm2_SC.1
    rw [ziXp_zero, gxTh_zero, ziXhp_zero] at hs0 hT0
    have hΘ0 : (0 : Ordinal.{0}) < gxTh (upsilon l) (ldAtR S l) ξ := by
      have h := gxTh_lt h0c hξ0; rwa [gxTh_zero] at h
    -- the shift `ζ + 1` for a code `ζ < ξ`
    have hstep : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < ξ →
        ζ + 1 < ξ ∧ GxCl (upsilon l) (ldAtR S l) (ζ + 1) ∧
        Vq.VqSh S l A b (ziXp P (ζ + 1)) (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ζ + 1)) ∧
        Rv.RvTop S l b (ziXp P (ζ + 1)) (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ζ + 1)) 0 ∧
        ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ζ + 1) < ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ξ) := by
      intro ζ hζc hζξ
      have hζ1 : ζ + 1 < ξ := hlim.add_one_lt hζξ
      have hζ12 : ζ + 1 < Om (1 + 1) := hζ1.trans hξ2
      have hζ1c : GxCl (upsilon l) (ldAtR S l) (ζ + 1) :=
        (ldHull_iff hl hX hζ12).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one ζ).trans hζ12)).2 hζc))
      have hΘs : gxTh (upsilon l) (ldAtR S l) (ζ + 1) = gxTh (upsilon l) (ldAtR S l) ζ + 1 := by
        rw [gxTh_add hρSC hAt hζc 1, hΘ1]
      have hT1 : ζ + 1 < ziTC S P b := hζ1.trans hξT
      have hsh := ziVqShC hP hl hX hA hρ hb3 hζ1c hT1
      have htop := IHξ (ζ + 1) hζ1 hζ1c hT1 0 h0c ldOm2_SC.1
      rw [hΘs] at hsh htop
      refine ⟨hζ1, hζ1c, hsh, htop, ziXhp_lt Pt ?_⟩
      rw [← hΘs]; exact gxTh_lt hζ1c hζ1
    refine Vq.vqTopE hs hl hX hA hρ (Vq.vqTopLimSh hl hX hA hρ hs (fun x hxH hx => ?_) (fun z hz => ?_))
    · rcases lt_or_ge x P with hxY | hxY
      · exact ⟨P, Pt, (le_self_add : P ≤ P + Om (1 + 1) * ξ), hxY,
          (lt_add_of_pos_right _ (mul_pos (Om_pos one_ne_zero) hΘ0) :
            Pt < Pt + Om 1 * gxTh (upsilon l) (ldAtR S l) ξ),
          hs0, hT0⟩
      · have hxs : x - P < Om (1 + 1) * ξ := by
          have h := Ry.rySub_lt hxY (show x < P + Om (1 + 1) * ξ from hx); exact h
        set q := (x - P) / Om (1 + 1) with hq
        have hqξ : q < ξ := (Ordinal.div_lt hW0).2 hxs
        have hqH : q ∈ cdHull S l := by
          have h := (Vh.vhC_div _ (Ta.taSub_mem x hxH P) (Om (1 + 1))).2.2 (mxOm2_mem _ _)
          rwa [gg_SC_eps ldOm2_SC] at h
        have hqc : GxCl (upsilon l) (ldAtR S l) q := (ldHull_iff hl hX (hqξ.trans hξ2)).1 hqH
        obtain ⟨hq1, -, hsh, htop, hlt⟩ := hstep q hqc hqξ
        refine ⟨_, _, ziXp_mono P hq1.le, ?_, hlt, hsh, htop⟩
        have e1 : x = P + (x - P) := (Ordinal.add_sub_cancel_of_le hxY).symm
        have h2 : x - P < Om (1 + 1) * (q + 1) := by
          have := Ordinal.lt_mul_succ_div (x - P) hW0; rwa [Order.succ_eq_add_one] at this
        unfold ziXp; rw [e1]; exact (add_lt_add_iff_left _).2 h2
    · rcases lt_or_ge z Pt with hzY | hzY
      · exact ⟨P, Pt, (lt_add_of_pos_right _ (mul_pos ldOm2_SC.1 hξ0) : P < P + Om (1 + 1) * ξ), hzY, hs0, hT0⟩
      · have hzs : z - Pt < Om 1 * gxTh (upsilon l) (ldAtR S l) ξ :=
          Ry.rySub_lt hzY hz
        set w := (z - Pt) / Om 1 with hw
        have hwξ : w < gxTh (upsilon l) (ldAtR S l) ξ := (Ordinal.div_lt hΩ0).2 hzs
        obtain ⟨c, hc, hcξ, hcw⟩ := gxTh_onto hwξ
        obtain ⟨hc1, -, hsh, htop, -⟩ := hstep c hc hcξ
        refine ⟨_, _, ziXp_lt P hc1, ?_, hsh, htop⟩
        have e1 : z = Pt + (z - Pt) :=
          (Ordinal.add_sub_cancel_of_le hzY).symm
        have h2 : z - Pt < Om 1 * (w + 1) := by
          have := Ordinal.lt_mul_succ_div (z - Pt) hΩ0
          rwa [Order.succ_eq_add_one] at this
        unfold ziXhp; rw [hcw, e1]; exact (add_lt_add_iff_left _).2 h2

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Zi
