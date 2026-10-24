import Googology.Trans.PoR.InaccPsi.R2.SgCnf

/-!
# The local supremum: a code own at its own level lies below some `SQ_j`

`W^E = Ω₂^E`, `SQ_0 = Ω₁`, `SQ_{j+1} = ψ_{Ω₂}(β + W^{X₀ + G(SQ_j)})` (`Sc.scSq`).

`Sc.scSq_sup` gives `T_{X₀ + G*}(β) = sup_j SQ_j` at a base `β` divisible by `W^{X₀ + G*}` (the top).  Here the base
is divisible only by `W^{X₀ + G η}` (the level of the code `η` itself), and own only up to it:

* `sgSq_lt_succ_le` (`SQ_j < SQ_{j+1}` if every `SQ_i ≤ η`);
* `sgSq_supAt` (**`η < ψ_{Ω₂}(β + W^{X₀ + G η})` ⇒ `η < SQ_j` for some `j`**, for a strictly monotone `G` with the
  closure law of its top above `ψ_{Ω₂}(β + W^{X₀ + G(Ω₁)})`, `W^{X₀ + G η} ∣ β`, `β` own for `d ≤ W^{X₀ + G η}`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

variable {S : InaccSeq.{0}}

section Loc

variable {G : Ordinal.{0} → Ordinal.{0}} {X0 β η Gs : Ordinal.{0}} (hGst : StrictMono G)
  (hβown : ∀ d, d ≤ leWe (X0 + G η) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hGm : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c)

include hGst hβown hX0m hGm

/-- `SQ_j < SQ_{j+1}` if every `SQ_i ≤ η`. -/
theorem sgSq_lt_succ_le (hall : ∀ i, scSq S G X0 β i ≤ η) :
    ∀ j, scSq S G X0 β j < scSq S G X0 β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have hle1 : scSq S G X0 β (j + 1) ≤ η := hall (j + 1)
    have IH := sgSq_lt_succ_le hall j
    have hle : scSq S G X0 β (j + 1) ≤ scSq S G X0 β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (hGst IH)))) ?_
    set c := scSq S G X0 β (j + 2) with hc
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + G (scSq S G X0 β (j + 1)))) c :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    have hbot : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (hGst.monotone (scSq_Om1_le (j + 1))))))).1
    have hGj : G (scSq S G X0 β j) ∈ S.CSet 0 c := hGm _ c (CSet.of_lt (IH.trans_le hle)) hbot
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone hle1))))
      (leWe_mem (CSet.add_mem hX0 (CSet_mono zero_le le_rfl hGj)))

/-- **The local supremum: `η < ψ_{Ω₂}(β + W^{X₀ + G η})` ⇒ `η < SQ_j` for some `j`.** -/
theorem sgSq_supAt (hGs : ∀ x, x < Om (1 + 1) → G x ≤ Gs)
    (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q)
    (hβd : leWe (X0 + G η) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + G η < S.psi 0 (Om (1 + 1 + 1)))
    (hη : η < S.psi (β + leWe (X0 + G η)) (Om (1 + 1))) : ∃ j, η < scSq S G X0 β j := by
  by_contra hno
  push Not at hno
  have hsucc : ∀ j, scSq S G X0 β j < scSq S G X0 β (j + 1) :=
    fun j => sgSq_lt_succ_le hGst hβown hX0m hGm hno j
  have hmono : ∀ {i j : ℕ}, i ≤ j → scSq S G X0 β i ≤ scSq S G X0 β j :=
    fun h => (strictMono_nat_of_lt_succ hsucc).monotone h
  have hbdd : BddAbove (Set.range (scSq S G X0 β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, scSq S G X0 β j ↔ ∃ j, y < scSq S G X0 β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, scSq S G X0 β j < ⨆ j, scSq S G X0 β j := fun j => (hlt _).2 ⟨j + 1, hsucc j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, scSq S G X0 β j := hKQ 0
  have hQSC : SC (⨆ j, scSq S G X0 β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (hmono (le_max_left i j))
    have hj' := hj.trans_le (hmono (le_max_right i j))
    exact ((scSq_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, scSq S G X0 β j with hQ
  have hηQ : Q ≤ η := Ordinal.iSup_le hno
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hbot1 : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) = scSq S G X0 β 1 := rfl
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hβ1 : S.psi β (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1.trans hX1
  have hFQ : S.psi (β + leWe (X0 + G η)) (Om (1 + 1)) ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans hβ1).trans_lt (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + G η) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact hβ1.trans_lt (hKQ 1)
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + G η)) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + G η)) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + G η) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + Om (1 + 1) * G η := by
      rw [← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans hX1).trans_lt
        (hKQ 1)
    have hXC : LeCl (Om (1 + 1)) Q (Om (1 + 1) * X0) :=
      LeCl.mulK hQSC ldOm2_SC X0 (hX0cl Q hQSC (hX1.trans_lt (hKQ 1)).le)
    have hu := (leClDec hQSC ldOm2_SC (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X0 < Om (1 + 1) * Gs := by
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + Om (1 + 1) * G η := by
        rw [hdec]; exact hla
      exact ((add_lt_add_iff_left _).1 this).trans_le
        (mul_le_mul_right (hGs η (hη.trans (psi_lt (InR_Om_succ 1) _))) _)
    obtain ⟨ζ, hζQ, hζ⟩ := hcl Q hQSC (by rw [hbot1]; exact (hKQ 1).le) _ hu hu2
    obtain ⟨j, hj⟩ := (hlt _).1 hζQ
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + G (scSq S G X0 β j)) := by
      rw [mul_add, ← hdec, add_assoc]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt (hζ.trans_le
        (mul_le_mul_right (hGst.monotone hj.le) _)))
    have hxW : x' < leWe (X0 + G (scSq S G X0 β j)) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact absurd (hη.trans_le (hFQ.trans hηQ)) (lt_irrefl _)

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Sg
