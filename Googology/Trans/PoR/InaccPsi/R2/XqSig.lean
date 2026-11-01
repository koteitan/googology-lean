import Googology.Trans.PoR.InaccPsi.R2.XqMove

/-!
# `B_n` through `σ(a) = ψ₁(A + 1 + ψ₂(T a))`, and the atom move at every atom where the law holds at both ends

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `A'` the same at
`λ'`, `B_n = Bc.bcB S n`, `c_n = Bc.bcC S n`.

* `xqTnorm` (**`T a` is normal at `Ω₂`**: `T a ∈ Cl(T a, ψ₂(T a))` for every normal `a ∈ D`);
* `xqSigMove` (**`B_n(σ_λ(a)) = ψ₁(A' + 1 + ψ₂(B_n(T a)))`** at every window `c_n ≤ ρ_λ`, `B_n ρ_λ = ρ_{λ'}`, with
  `σ_λ(a) < c_{n+1}`; `Ld.ldB_psi_add`, `Ug.ugB_psiS`, `Mx.mxPsi_inj`);
* `xqLawMove` (**THE ATOM MOVE FROM THE LAW AT BOTH ENDS**: under the moves of the codes below `ψ₂ a`, if
  `Θ(ψ₂ a) = σ_λ(a)` and `Θ'(ψ₂(B_n a)) = σ_{λ'}(B_n a)`, then `B_n(ψ₂ a) = ψ₂(B_n a)` and
  `Θ'(B_n(ψ₂ a)) = B_n(Θ(ψ₂ a))`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **`T a` is normal at `Ω₂`** for every normal `a ∈ D`. -/
theorem xqTnorm {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {a : Ordinal.{0}}
    (ha : VbD S l a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    vbT S l a ∈ S.CSet (vbT S l a) (S.psi (vbT S l a) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine Xd.xdT_cl hl hX (psi_lt hκ2 a).le (fun e he hea => vbT_mono hl hX he ha hea)
    (fun c hc hc2 _ => ?_) a ha han
  rw [vbT_code hl hX hc2 hc.1]
  exact CSet.of_lt (((gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) hc2).trans_le (vbZ2_le hl hX)).trans
    (psiS_bounds (S := S) _ 1).1)

section Move

variable {n : ℕ} {l l' ηx ηx' A A' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hl hX hA hρ hA' hρ'

/-- **`B_n` through `σ_λ(a)`**: `B_n(ψ₁(A + 1 + ψ₂(T a))) = ψ₁(A' + 1 + ψ₂(B_n(T a)))`. -/
theorem xqSigMove (hlo : Bc.bcC S n ≤ upsilon l) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {a : Ordinal.{0}} (ha : VbD S l a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hDT : MvD S (vbT S l a))
    (hhi : S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1)) :
    MvD S (S.psi (vbT S l a) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (vbT S l a) (Om (1 + 1))) = S.psi (Bc.bcB S n (vbT S l a)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) =
        S.psi (A' + 1 + S.psi (Bc.bcB S n (vbT S l a)) (Om (1 + 1))) (Om 1) := by
  have hown := xqOwn hl hX hA hρ ha han
  obtain ⟨-, eA⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hD1 : MvD S 1 := mvD_of_lt h1L
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDψ, hBψ, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero hD1 hDT (xqTnorm hl hX ha han)
  rw [hB1] at hBψ
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1 hDψ
  rw [hB1, hBψ] at hBd
  subst eA
  rw [add_assoc] at hown hhi
  obtain ⟨A'', hA'', hBρ, hBσ⟩ := ldB_psi_add hg (by rw [hpv]; exact hlo) hDd hown hhi
  have e : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBρ, hpv, hB, hρ'])
  refine ⟨hDψ, hBψ, ?_⟩
  rw [add_assoc, hBσ, e, hBd, add_assoc]

include hl' hX'

/-- **THE ATOM MOVE FROM THE LAW AT BOTH ENDS.** -/
theorem xqLawMove (hlo : Bc.bcC S n ≤ upsilon l) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {a : Ordinal.{0}} (ha : VbD S l a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1))
    (hhi : S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1))
    (hlaw' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n a) (Om (1 + 1))) =
      S.psi (A' + 1 + S.psi (vbT S l' (Bc.bcB S n a)) (Om (1 + 1))) (Om 1)) :
    MvD S (S.psi a (Om (1 + 1))) ∧ Bc.bcB S n (S.psi a (Om (1 + 1))) = S.psi (Bc.bcB S n a) (Om (1 + 1)) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi a (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) := by
  obtain ⟨hDa, hDT, hTmv⟩ := xqTMove hl hX hl' hX' hA hρ IH a ha han
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDa han
  rw [hB1] at hBs
  obtain ⟨-, -, hσ⟩ := xqSigMove hl hX hA hρ hA' hρ' hlo hB ha han hDT hhi
  refine ⟨hDs, hBs, ?_⟩
  rw [hBs, hlaw', hTmv, hlaw, hσ]

end Move

end Googology.Trans.PoR.InaccPsi.R2.Xq

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTnorm
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqSigMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqLawMove
