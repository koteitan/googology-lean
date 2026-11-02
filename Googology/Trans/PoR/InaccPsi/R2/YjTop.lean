import Googology.Trans.PoR.InaccPsi.R2.YjBlk

/-!
# Every top atom is a base with a law at both ends; the blocks `ψ₂(t + Ω₂·m + c)` above it move

`X = Ω_{k+3}`, `t = β + W^{X+e}` a top base of `λ` (`β ∈ D`, `Ro.RoBaseE λ X e β`), `T = Vb.vbT`, `A = A_{η_λ}`,
`D_t = 1 + ψ₂(T t)` (so `Θ(ψ₂ t) = ψ₁(A + D_t)`, `Xm.xmTopUp`), "window" and "IH" as in `Yj.yjBaseFacts`.

* `yjTopBase` (**THE TOP ATOM IS A BASE WITH A LAW AT BOTH ENDS**: at a window, under IH below `ψ₂ t`,
  `Yj.YjBase λ λ' A' t D_t`, with `B_n t = B_n β + W^{X+B_n e}`; the `λ'` side from the two base facts
  `Yj.yjBaseFacts`, `Yd.ydBaseMoveB`, the top law at `λ'` (`Xm.xmTopUp`), the `T`-move `Xq.xqTMove` and
  `Xq.xqSigMove`);
* `yjTopBlk` (**EVERY ATOM `ψ₂(t + Ω₂·m + c)` MOVES**, `m < ω`, `c < F^{t+Ω₂·m}` a code of `λ`, at a window under the
  moves of the codes below it; this covers every atom of `H_λ` in `[ψ₂ t, ψ₂(t + Ω₂·ω))`, the non-top atoms of the
  first `ω` blocks above every top atom).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE TOP ATOM IS A BASE WITH A LAW AT BOTH ENDS.** -/
theorem yjTopBase (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))
        (1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) ∧
      Bc.bcB S n (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
        Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set t := β + leWe (X + e) with htdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he2 : e < Om (1 + 1) := (Yd.ydBaseE_lt k hβD hb).trans (psi_lt hκ2 _)
  -- the `λ` side
  obtain ⟨htD, htd, htown⟩ := Xq.xqTopD hl hX k hec he2 hβD hb
  have htn : t ∈ S.CSet t (S.psi t (Om (1 + 1))) := by have h := htown 0 zero_le; rwa [add_zero] at h
  obtain ⟨hDt, hDT, hTmv⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH t htD htn
  have hlaw := Xm.xmTopUp S k l _ _ hl hX hown hρA e β hec he2 hβD hb
  unfold leTe at hlaw
  have hhi : S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l t) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hlaw]; exact yjTh_hi hR h1 hr hl' hB (yjPsi2_leW htD.2.2)
  obtain ⟨hDψ, hBψ, -⟩ := Xq.xqSigMove hl hX hown hρA hA' hρ' h1.le hB htD htn hDT hhi
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) (mvD_of_lt h1L) hDψ
  rw [hB1, hBψ] at hBD
  have hat := Xq.xqOwn hl hX hown hρA htD htn
  -- the `λ'` side
  obtain ⟨hdv', hD'⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hb IH
  obtain ⟨-, -, hBec, hBe2, hb', hBt⟩ := Yd.ydBaseMoveB hR h1 hr hl' hB k hec hβD hb IH hdv' hD'
  obtain ⟨htD', htd', htown'⟩ := Xq.xqTopD hl' hX' k hBec hBe2 hD' hb'
  have htn' : Bc.bcB S n β + leWe (X + Bc.bcB S n e) ∈ S.CSet (Bc.bcB S n β + leWe (X + Bc.bcB S n e))
      (S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e)) (Om (1 + 1))) := by
    have h := htown' 0 zero_le; rwa [add_zero] at h
  have hlaw' := Xm.xmTopUp S k l' _ _ hl' hX' hA' hρ' (Bc.bcB S n e) (Bc.bcB S n β) hBec hBe2 hD' hb'
  unfold leTe at hlaw'
  have hat' := Xq.xqOwn hl' hX' hA' hρ' htD' htn'
  rw [← hBt, hTmv] at hlaw' hat'
  refine ⟨⟨htD, htd, htown, hDt, hDD, by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw,
    hBt ▸ htD', hBt ▸ htd', hBt ▸ htown', by rw [hBD, ← add_assoc]; exact hat',
    by rw [hBD, ← add_assoc]; exact hlaw'⟩, hBt⟩

/-- **EVERY ATOM `ψ₂(t + Ω₂·m + c)` MOVES** above every top atom `t` (`m < ω`, `c < F^{t+Ω₂·m}` a code). -/
theorem yjTopBlk (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) (m : ℕ) {c : Ordinal.{0}}
    (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcF : c < ldTop S (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0})))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
        (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
        (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
        (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
            (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
            (Om (1 + 1)))) := by
  set t := β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) with htdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hle : S.psi t (Om (1 + 1)) ≤ S.psi (t + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1)) :=
    (psi_mono hκ2 (le_self_add.trans le_self_add)).1
  obtain ⟨hbt, -⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hb fun x hx hxs => IH x hx (hxs.trans_le hle)
  have hW : t + Om (1 + 1) * ω < Om ω :=
    vkOmW.1.isPrincipal hbt.D_a.2.2 ldW2_lt_OmW
  exact yjBlkFin hR h1 hr hl' hB hA' hρ' hbt hW m hc hcF IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yj

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjTopBase
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjTopBlk
