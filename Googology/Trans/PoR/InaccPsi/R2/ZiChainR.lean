import Googology.Trans.PoR.InaccPsi.R2.ZiCst

/-!
# THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·ψ₁(Ω₃+1)}`: the relative shifts `Y₃ + Ω₂·ξ` for every countable constant `ξ`

`Y₃ = ugY S`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `W^x = leWe x`, `X'_ξ = Zd.zdXr ξ = Y₃ + Ω₂·ξ`, `X̂'_ξ = Zd.zdXhr ξ = Y₂ + Ω₁·ξ`,
`K₃ = ziK3 S = ψ_{Ω₁}(Ω₃ + 1)`, `B_n`, "window", `A'`, `Yj.YjBase`, "IH(s)", `Zd.ZdBot` as in `Zd.zdBot_chain`.

`Zd.zdRS_chain` asks `ξ < ε₀` only to place `ξ` in every closure `Cl(c, b)` (`c > Ω₃`) and to have `B_n ξ = ξ`,
`Θ_λ ξ = ξ`.  Every `ξ < K₃` has these properties (`Zi.ziK3_mem`, `Zi.ziK3_lt_C`, `Zi.ziCst_le_rho`), and `ε₀ < K₃`.

* `ziShB_cst`, `ziVqSh_cst`, `ziTop_cstR` (the shift data and the tops `Rv.RvTop λ Ω₃ X'_ξ X̂'_ξ e`, `ξ < K₃`),
* `ziRS_cst` (**every `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`, `ξ < K₃`, IS A RELATIVE SHIFT** `Zd.ZdRS`),
* `ziBot_cst` (**`Zd.ZdBot` at every `Y₃ + Ω₂·ξ`, `ξ ≤ K₃`**),
* `ziPsi3OffK` (**every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·K₃})` moves** for `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`).

These generalize `Zd.zdShB_chain`, `Zd.zdVqSh_chain`, `Zd.zdTop_chainR`, `Zd.zdRS_chain`, `Zd.zdBot_chain`,
`Zd.zdPsi3OffE0` from the bound `ε₀` to the bound `K₃` (the proofs are those, with the constants lemmas of `ZiCst`).

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
  Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

theorem ziOm1_lt_psi2 (x : Ordinal.{0}) : Om 1 < S.psi x (Om (1 + 1)) :=
  lt_psi_of_mem (InR_Om_succ 1) (CSet.Om_mem (CSet.one_mem _ _)) (Om_lt_Om.2 (lt_add_one 1))

/-- `B_n` fixes `Ω₂·(Y₃ + Ω₂·ξ)` and `Ω₁·(Y₂ + Ω₁·ξ)` for every `ξ < K₃`. -/
theorem ziShB_cst {ξ : Ordinal.{0}} (hξ : ξ < ziK3 S) : Ro.RoShB S (zdXr S ξ) (zdXhr S ξ) := by
  refine ⟨?_, fun n => ?_⟩
  · unfold zdXhr; exact (Vq.vqY2_SC.1.trans_le le_self_add).ne'
  obtain ⟨hDY, hBY⟩ := Yy.yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := Yy.yyY2_D (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDp, hBp⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBp
  obtain ⟨hDq, hBq⟩ := mvB_add (k := n) hD1 hD1
  rw [hB1] at hBq
  have hξC : ξ < Bc.bcC S n := hξ.trans (ziK3_lt_C n)
  obtain ⟨hDP, hBP⟩ := ziB_opowMul (n := n) hDp hBp ξ hξC
  obtain ⟨hDQ, hBQ⟩ := ziB_opowMul (n := n) hDq hBq ξ hξC
  have e1 : Om (1 + 1) * zdXr S ξ = ugY S + ω ^ (Om (1 + 1) + Om (1 + 1)) * ξ := by
    unfold zdXr; rw [mul_add, zdOm2_mulY, opow_add, gg_SC_eps ldOm2_SC, mul_assoc]
  have e2 : Om 1 * zdXhr S ξ = S.psi (Om (1 + 1)) (Om (1 + 1)) + ω ^ (Om 1 + Om 1) * ξ := by
    unfold zdXhr; rw [mul_add, zdOm1_mulY2, opow_add, gg_SC_eps Ph.ph_SC_Om1, mul_assoc]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDP
  rw [hBY, hBP] at hBs
  obtain ⟨hDt, hBt⟩ := mvB_add (k := n) hDY2 hDQ
  rw [hBY2, hBQ] at hBt
  rw [e1, e2]
  exact ⟨hDs, hBs, hDt, hBt⟩

/-- **The `Vq.VqSh` fields of `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`** at the base `Ω₃`, `ξ < K₃`, at every restart. -/
theorem ziVqSh_cst {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) {ξ : Ordinal.{0}} (hξ : ξ < ziK3 S) :
    Vq.VqSh S l A (Om (1 + 1 + 1)) (zdXr S ξ) (zdXhr S ξ) := by
  have hA3 : Om (1 + 1 + 1) < A := Ry.ryOm3_lt.trans_le (Vn.vnA_ge hl hX hA hρ)
  have hξm : ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → ξ ∈ S.CSet c b := ziK3_mem hξ
  have hmem : ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → zdXr S ξ ∈ S.CSet c b := fun c b h =>
    CSet.add_mem (Vq.vqY3_mem h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hξm _ _ h))
  have hAo : Om ω ≤ A := Vn.vnA_ge hl hX hA hρ
  have hξρ : ξ ≤ upsilon l := hξ.le.trans (ziCst_le_rho (Order.add_one_le_of_lt Ry.ryOm3_lt) hl hX)
  refine ⟨?_, dvd_add Yy.yyOm2_dvd_Y (dvd_mul_right _ _), hmem _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)),
    hmem _ _ (lt_add_of_pos_right _ (leWe_pos _)), ?_, fun Q hQ hQb => ?_, fun Q hQ hQb => ?_⟩
  · unfold zdXr; exact (uqY_SC.1.trans_le le_self_add).ne'
  · unfold zdXhr
    exact CSet.add_mem (Vq.vqY2_mem ((ldOm2_lt_OmW.trans_le hAo).trans_le le_self_add))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξm _ _ (hA3.trans_le le_self_add)))
  · unfold zdXr
    have hξQ : ξ < Q := (hξ.trans ziK3_lt_Om1).trans ((ziOm1_lt_psi2 _).trans_le hQb)
    have h := ziVkA_opowMul hQ.1 (VkA.big (k := 1 + 1) (Q := Q) le_rfl ldOm2_SC) ξ hξQ
    rw [gg_SC_eps ldOm2_SC] at h
    exact VkA.add (VkA.big uqW_lt_Y.le uqY_SC) h
  · unfold zdXhr
    have hρΘ : upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ξ)) (Om (1 + 1))) := by
      calc upsilon l = gxTh (upsilon l) (ldAtR S l) (upsilon l) := (gxTh_small le_rfl).symm
        _ ≤ _ := gxTh_mono ((leRho hl hX).2.le.trans (ziOm1_lt_psi2 _).le)
    have hξQ : ξ < Q :=
      (hξ.trans_le (ziCst_le_rho (Order.add_one_le_of_lt Ry.ryOm3_lt) hl hX)).trans_le (hρΘ.trans hQb)
    have h := ziVkA_opowMul hQ.1 (VkA.big (k := 1) (Q := Q) le_rfl Ph.ph_SC_Om1) ξ hξQ
    rw [gg_SC_eps Ph.ph_SC_Om1] at h
    exact VkA.add (VkA.big (psiS_bounds (S := S) _ 1).1.le Vq.vqY2_SC) h

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE TOPS OF THE CHAIN**: `Rv.RvTop λ Ω₃ (Y₃ + Ω₂·ξ) (Y₂ + Ω₁·ξ) e` for every `ξ < K₃` and every code `e`. -/
theorem ziTop_cstR : ∀ ξ, ξ < ziK3 S → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    Rv.RvTop S l (Om (1 + 1 + 1)) (zdXr S ξ) (zdXhr S ξ) e := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    rw [zdXr_zero, zdXhr_zero]
    exact Vq.vqTopY3E hl hX hA hρ (le_refl _)
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'0 : ξ' < ziK3 S := (lt_add_one ξ').trans hξ
    have h0 := Vq.vqTopW (ziVqSh_cst hl hX hA hρ hξ'0) hl hX hA hρ (IHξ ξ' (lt_add_one ξ') hξ'0)
    rw [← zdXr_succ, ← zdXhr_succ] at h0
    exact Vq.vqTopE (ziVqSh_cst hl hX hA hρ hξ) hl hX hA hρ h0
  · have hs := ziVqSh_cst hl hX hA hρ hξ
    refine Vq.vqTopE hs hl hX hA hρ (Vq.vqTopLimSh hl hX hA hρ hs (fun x _ hx => ?_) (fun z hz => ?_))
    · obtain ⟨ξ', hξ', hx'⟩ := zdXr_cof hlim hx
      exact ⟨_, _, zdXr_mono hξ'.le, hx', zdXhr_lt hξ', ziVqSh_cst hl hX hA hρ (hξ'.trans hξ),
        IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1⟩
    · obtain ⟨ξ', hξ', hz'⟩ := zdXhr_cof hlim hz
      exact ⟨_, _, zdXr_lt hξ', hz', ziVqSh_cst hl hX hA hρ (hξ'.trans hξ),
        IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1⟩

end Rst

/-- **Every `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`, `ξ < K₃ = ψ_{Ω₁}(Ω₃ + 1)`, IS A RELATIVE SHIFT** (`Zd.zdRS_chain` is `ξ < ε₀`). -/
theorem ziRS_cst {ξ : Ordinal.{0}} (hξ : ξ < ziK3 S) : ZdRS S (zdXr S ξ) (zdXhr S ξ) := by
  refine ⟨?_, (zdXr_lt_Om3 (hξ.trans ziK3_lt_Om2)).trans Ry.ryOm3_lt, fun c b h => ?_, ziShB_cst hξ,
    fun _ _ _ hl hX hA hρ => ziVqSh_cst hl hX hA hρ hξ, fun _ _ _ hl hX hA hρ => ziTop_cstR hl hX hA hρ ξ hξ⟩
  · unfold zdXr; exact (uqY_SC.1.trans_le le_self_add).ne'
  · exact CSet.add_mem (Vq.vqY3_mem h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (ziK3_mem hξ c b h))

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE MOVES BELOW EVERY SHIFT `Y₃ + Ω₂·ξ`, `ξ ≤ K₃`** (`Zd.zdBot_chain` is `ξ ≤ ε₀`). -/
theorem ziBot_cst : ∀ ξ, ξ ≤ ziK3 S → ZdBot S n l l' A' (zdXr S ξ) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    rw [zdXr_zero, Vq.vqWeY3] at hdv hdv' hsT
    exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hb hdv hdv' hs hsa hsT IH
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'0 : ξ' < ziK3 S := (lt_add_one ξ').trans_le hξ
    intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    rw [zdXr_succ] at hdv hdv' hsT
    exact zdXUp hR h1 hr hl' hB hA' hρ' (ziRS_cst hξ'0) (IHξ ξ' (lt_add_one ξ') hξ'0.le) (Om (1 + 1)) hD2 le_rfl
      a D hb hdv (by rw [hB2]; exact hdv') ha3 s hs hsa hsT IH
  · intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    have hXW : zdXr S ξ < Om ω := (zdXr_lt_Om3 (hξ.trans_lt ziK3_lt_Om2)).trans Ry.ryOm3_lt
    have haW : a + leWe (zdXr S ξ) < Om ω :=
      vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hXW).1
    have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
    obtain ⟨d, -, hds, hdn⟩ := vbReach hl hX hs hsθ
    subst hds
    have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
      psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
    have had : a ≤ d := by
      by_contra hc; push Not at hc
      exact absurd (hdnx a hc) (not_lt.2 hsa)
    have hdae : d < a + leWe (zdXr S ξ) := by
      by_contra hc; push Not at hc
      exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
    have hδ : d - a < leWe (zdXr S ξ) := Ry.rySub_lt had hdae
    obtain ⟨ξ', hξ', hδ'⟩ := zdW_cof hlim hδ
    have hle : leWe (zdXr S ξ') ∣ leWe (zdXr S ξ) := leWe_dvd (zdXr_mono hξ'.le)
    refine IHξ ξ' hξ' (hξ'.le.trans hξ) a D hb (hle.trans hdv) (hle.trans hdv') ha3 _ hs hsa ?_ IH
    refine hdnx _ ?_
    have e1 : d = a + (d - a) := (Ordinal.add_sub_cancel_of_le had).symm
    rw [e1]; exact (add_lt_add_iff_left a).2 hδ'

/-- **THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·K₃}`**, `K₃ = ψ_{Ω₁}(Ω₃ + 1)`: above a base `a ≥ Ω₃` with a law at both ends,
`Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·K₃})` moves under IH(s). -/
theorem ziPsi3OffK {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + leWe (zdXr S (ziK3 S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have h3 : leWe (zdXr S (ziK3 S)) ∣ Om (1 + 1 + 1) := by
    have h := leWe_dvd (zdXr_lt_Om3 (S := S) (ziK3_lt_Om2 (S := S))).le
    rwa [Vn.vnWe_Om3] at h
  exact ziBot_cst hR h1 hr hl' hB hA' hρ' (ziK3 S) le_rfl a D hb (h3.trans hd3) (h3.trans hd3') ha3 s hs hsa
    hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zi
