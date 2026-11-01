import Googology.Trans.PoR.InaccPsi.R2.XqSig

/-!
# Every top atom moves once its base data move

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `X = Ω_{k+3}`, `t = β + W^{X+e}` a top base
(`e < Ω₂` a code, `β ∈ D` a base of exponent `e`, `Ro.RoBaseE`), `B_n = Bc.bcB S n`.

* `xqTopD` (**the data of a top base**: `t ∈ D`, `Ω₂ ∣ t`, `t ∈ Cl(t + d, ψ₂(t + d))` for `d ≤ Ω₂`);
* `xqTopMove` (**THE TOP-ATOM MOVE**: under the moves of the codes below `ψ₂ t`, if `B_n t = β' + W^{X+e'}` is a top
  base of `λ'` (BASE-DATA MOVE) and `Θ(ψ₂ t) < c_{n+1}`, then `B_n(ψ₂ t) = ψ₂(B_n t)` and
  `Θ'(B_n(ψ₂ t)) = B_n(Θ(ψ₂ t))`; the law at both ends is `Xm.xmTopUp`);
* `xqTopTest` (non-vacuity of the `λ`-side hypotheses: at the restart of `m* = L(0)` the top base `(e, β) = (0, 0)`
  of every level `k` meets them, and the block law `xqTopBlk` holds there).

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

/-- **The data of a top base** `t = β + W^{Ω_{k+3}+e}`. -/
theorem xqTopD {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ)
    {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1))
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) :
    VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) ∧
      Om (1 + 1) ∣ β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∧
      ∀ d, d ≤ Om (1 + 1) → β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∈
        S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + d)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + d) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  obtain ⟨hβd, hβH, -, hβown, hexpA⟩ := hB
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have hβW : β < Om ω := hβD.2.2
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (he2.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  have hD : VbD S l (β + leWe (X + e)) :=
    ⟨CSet.add_mem hβH (leWe_mem (CSet.add_mem (hXmem _ _) ((ldHull_iff hl hX he2).2 hec))),
      CSet.add_mem hβD.2.1 (leWe_mem (CSet.add_mem (hXmem _ _) (CSet.of_lt heθ))),
      vkOmW.1.isPrincipal hβW hwW⟩
  have h1g : (1 : Ordinal.{0}) ≤ X + e :=
    (Order.one_le_iff_pos.2 (Om_pos (add_pos_of_right zero_lt_one _).ne')).trans le_self_add
  have hW2 : Om (1 + 1) ∣ leWe (X + e) := by
    have h := leWe_dvd h1g; rwa [leWe_one] at h
  refine ⟨hD, dvd_add (hW2.trans hβd) hW2, fun d _ => ?_⟩
  have hle : β + leWe (X + e) ≤ β + leWe (X + e) + d := le_self_add
  have hβm := (psi_mono (S := S) hκ2 hle).2 (hβown _ le_rfl)
  have hem : e ∈ S.CSet (β + leWe (X + e) + d) (S.psi (β + leWe (X + e) + d) (Om (1 + 1))) :=
    CSet.of_lt (hexp.trans_le (psi_mono hκ2 hle).1)
  exact CSet.add_mem hβm (leWe_mem (CSet.add_mem (hXmem _ _) hem))

section Move

variable {n : ℕ} {l l' ηx ηx' A A' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hl hX hl' hX' hA hρ hA' hρ'

/-- **THE TOP-ATOM MOVE** from the BASE-DATA MOVE (`B_n t` a top base of `λ'`). -/
theorem xqTopMove (hlo : Bc.bcC S n ≤ upsilon l) (hB : Bc.bcB S n (upsilon l) = upsilon l') (k : ℕ)
    {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1))
    (hβD : VbD S l β) (hBE : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    {e' β' : Ordinal.{0}} (hec' : GxCl (upsilon l') (ldAtR S l') e') (he2' : e' < Om (1 + 1))
    (hβD' : VbD S l' β') (hBE' : Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e' β')
    (hmv : Bc.bcB S n (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
      β' + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e'))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    (hhi : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) <
      Bc.bcC S (n + 1)) :
    MvD S (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) =
        S.psi (β' + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e')) (Om (1 + 1)) ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) := by
  obtain ⟨hD, -, hown⟩ := xqTopD hl hX k hec he2 hβD hBE
  have han := hown 0 zero_le
  rw [add_zero] at han
  have hlaw := Xm.xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hBE
  have hlaw' := Xm.xmTopUp S k l' ηx' A' hl' hX' hA' hρ' e' β' hec' he2' hβD' hBE'
  unfold leTe at hlaw hlaw'
  rw [← hmv] at hlaw'
  have hhi' := hhi
  rw [hlaw] at hhi'
  obtain ⟨hDs, hBs, hmove⟩ := xqLawMove hl hX hl' hX' hA hρ hA' hρ' hlo hB hD han IH hlaw hhi' hlaw'
  exact ⟨hDs, by rw [hBs, hmv], hmove⟩

end Move

/-- **UNCONDITIONAL (non-vacuity)**: at the restart of `m* = L(0)` with its own `A`, the top base `(e, β) = (0, 0)` of
every level `k` meets the `λ`-side hypotheses of `xqTopBlk` / `xqTopMove`, so the block law holds above `ψ₂(Ω_{k+3})`. -/
theorem xqTopTest (S : InaccSeq.{0}) (k : ℕ) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ GxCl (upsilon l) (ldAtR S l) 0 ∧ (0 : Ordinal.{0}) < Om (1 + 1) ∧
      VbD S l 0 ∧ Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 0 ∧
      ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0)) →
        gxTh (upsilon l) (ldAtR S l) (S.psi (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) + c) (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
            gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have h02 : (0 : Ordinal.{0}) < Om (1 + 1) := Om_pos (add_pos_of_right zero_lt_one _).ne'
  have hB := Xi.xiBase_zero (S := S) k l
  refine ⟨l, _, _, hl, hX, hA, hρ, h0c, h02, Xi.xiD_zero l, hB, ?_⟩
  exact (xqTopBlk hl hX hA hρ k h0c h02 (Xi.xiD_zero l) hB).1

end Googology.Trans.PoR.InaccPsi.R2.Xq

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTopD
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTopMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTopTest
