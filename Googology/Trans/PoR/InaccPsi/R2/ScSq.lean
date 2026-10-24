import Googology.Trans.PoR.InaccPsi.R2.ScSucc

/-!
# The own parameters of a shape: `T_{X₀ + G*}(β) = sup_j SQ_j` for every shape `G`

`W^E = Ω₂^E` (`Le.leWe`), `T_E(β) = ψ_{Ω₂}(β + W^E)` (`Le.leTe`).  A **shape** is a map `G` from the code
parameters `ζ < Ω₂` to exponents, strictly monotone, below its top `G*` (`G ζ < G*`), with
`SQ_0 = Ω₁`, `SQ_{j+1} = ψ_{Ω₂}(β + W^{X₀ + G(SQ_j)})` (`scSq S G X₀ β j`).  Instances: `G ζ = W^ζ`
(`Rw.rwEX`, top `W^{Ω₂}`), `G ζ = W^E·ζ` (`Rv.rvEE`, top `W^{E+1}`), and every shape built from them (`Sc.ScShp`).
The parameters `ζ < SQ_j` are own: `ζ < ψ_{Ω₂}(β + W^{X₀ + G ζ})` (`scSq_gt`), and below the top
`T_{X₀+G*}(β)` every code is below some `SQ_j` (`scSq_sup`), under
* `G` keeps the closure above its bottom `Bot = ψ_{Ω₂}(β + W^{X₀ + G(Ω₁)})` (`hGm`);
* the **closure law** of the shape (`ScShCl G G* Q`): every `w` of `Le.LeCl(Ω₂, Q)` below `Ω₂·G*` is below
  `Ω₂·G ζ` for some `ζ < Q` (at every strongly critical `Q ≥ Bot`).

* `scSq_lt_Om2`, `scSq_SC`, `scSq_gt`, `scSq_le_top`, `scSq_mono_base`, `scSq_lt_succ`, `scSq_mono`,
  `scSq_sup` (**`T_{X₀ + G*}(β) = sup_j SQ_j`**), `scSq_ge`, `scSq_gtT`.

No new axiom.  New definitions: `scSq`, `ScShCl`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

/-- `SQ_0 = Ω₁`, `SQ_{j+1} = ψ_{Ω₂}(β + W^{X₀ + G(SQ_j)})`. -/
noncomputable def scSq (S : InaccSeq.{0}) (G : Ordinal.{0} → Ordinal.{0}) (X0 β : Ordinal.{0}) :
    ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (X0 + G (scSq S G X0 β j))) (Om (1 + 1))

/-- **The closure law of a shape `G` with top `G*` at `Q`.** -/
def ScShCl (G : Ordinal.{0} → Ordinal.{0}) (Gs Q : Ordinal.{0}) : Prop :=
  ∀ w, LeCl (Om (1 + 1)) Q w → w < Om (1 + 1) * Gs → ∃ ζ, ζ < Q ∧ w < Om (1 + 1) * G ζ

section Seq

variable {G : Ordinal.{0} → Ordinal.{0}} {X0 β : Ordinal.{0}}

theorem scSq_lt_Om2 : ∀ j, scSq S G X0 β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem scSq_SC : ∀ j, SC (scSq S G X0 β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem scSq_Om1_le : ∀ j, Om (1 : Ordinal.{0}) ≤ scSq S G X0 β j
  | 0 => le_rfl
  | _ + 1 => (psiS_bounds (S := S) _ 1).1.le

variable (hGmo : Monotone G)

include hGmo in
theorem scSq_gt : ∀ j x, x < scSq S G X0 β j → x < S.psi (β + leWe (X0 + G x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (scSq S G X0 β j) with h' | h'
    · exact scSq_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (hGmo h'))))).1

theorem scSq_le_top {Gs : Ordinal.{0}} (hGs : ∀ x, x < Om (1 + 1) → G x ≤ Gs) :
    ∀ j, scSq S G X0 β j ≤ leTe S (X0 + Gs) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGs _ (scSq_lt_Om2 j)))))).1

include hGmo in
theorem scSq_mono_base {β' : Ordinal.{0}} (hββ : β ≤ β') : ∀ j, scSq S G X0 β j ≤ scSq S G X0 β' j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (add_le_add hββ (leWe_mono ((add_le_add_iff_left X0).2
      (hGmo (scSq_mono_base hββ j)))))).1

variable {Gs : Ordinal.{0}} (hGst : StrictMono G) (hGs : ∀ x, x < Om (1 + 1) → G x ≤ Gs)
  (hβown : ∀ d, d ≤ leWe (X0 + Gs) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hGm : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c)

include hGst hGs hβown hX0m hGm

theorem scSq_lt_succ : ∀ j, scSq S G X0 β j < scSq S G X0 β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := scSq_lt_succ j
    have hle : scSq S G X0 β (j + 1) ≤ scSq S G X0 β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (hGst IH)))) ?_
    set c := scSq S G X0 β (j + 2) with hc
    have hc' : c = S.psi (β + leWe (X0 + G (scSq S G X0 β (j + 1)))) (Om (1 + 1)) := rfl
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + G (scSq S G X0 β (j + 1)))) c :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    have hbot : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (hGst.monotone (scSq_Om1_le (j + 1))))))).1
    have hGj : G (scSq S G X0 β j) ∈ S.CSet 0 c := hGm _ c (CSet.of_lt (IH.trans_le hle)) hbot
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (hGs _ (scSq_lt_Om2 _)))))
      (leWe_mem (CSet.add_mem hX0 (CSet_mono zero_le le_rfl hGj)))

theorem scSq_mono {j j' : ℕ} (h : j ≤ j') : scSq S G X0 β j ≤ scSq S G X0 β j' :=
  (strictMono_nat_of_lt_succ (fun i => scSq_lt_succ hGst hGs hβown hX0m hGm i)).monotone h

/-- **`T_{X₀ + G*}(β) = sup_j SQ_j`** for a shape `G` with its closure law. -/
theorem scSq_sup (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + Gs < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + Gs) β) : ∃ j, x < scSq S G X0 β j := by
  have hbdd : BddAbove (Set.range (scSq S G X0 β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, scSq S G X0 β j ↔ ∃ j, y < scSq S G X0 β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, scSq S G X0 β j < ⨆ j, scSq S G X0 β j :=
    fun j => (hlt _).2 ⟨j + 1, scSq_lt_succ hGst hGs hβown hX0m hGm j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, scSq S G X0 β j := hKQ 0
  have hQSC : SC (⨆ j, scSq S G X0 β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (scSq_mono hGst hGs hβown hX0m hGm (le_max_left i j))
    have hj' := hj.trans_le (scSq_mono hGst hGs hβown hX0m hGm (le_max_right i j))
    exact ((scSq_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, scSq S G X0 β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hbot1 : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) = scSq S G X0 β 1 := rfl
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hβ1 : S.psi β (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1.trans hX1
  have hFQ : leTe S (X0 + Gs) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans hβ1).trans_lt (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + Gs) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact hβ1.trans_lt (hKQ 1)
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + Gs)) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + Gs)) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + Gs) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + Om (1 + 1) * Gs := by
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
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + Om (1 + 1) * Gs := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨ζ, hζQ, hζ⟩ := hcl Q hQSC (by rw [hbot1]; exact (hKQ 1).le) _ hu hu2
    obtain ⟨j, hj⟩ := (hlt _).1 hζQ
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + G (scSq S G X0 β j)) := by
      rw [mul_add, ← hdec, add_assoc]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt (hζ.trans_le
        (mul_le_mul_right (hGst.monotone hj.le) _)))
    have hxW : x' < leWe (X0 + G (scSq S G X0 β j)) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X₀ + G x}) ≥ T_{X₀ + G*}(β)` for `x ≥ T_{X₀ + G*}(β)`. -/
theorem scSq_ge (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + Gs < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : leTe S (X0 + Gs) β ≤ x) :
    leTe S (X0 + Gs) β ≤ S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := scSq_sup hGst hGs hβown hX0m hGm hcl hβd hX0cl hX0G3 h
  have h1 : scSq S G X0 β (j + 1) ≤ S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone ((scSq_le_top hGs j).trans hx)))))).1
  exact absurd (hj.trans_le ((scSq_lt_succ hGst hGs hβown hX0m hGm j).le.trans h1)) (lt_irrefl _)

/-- **Every code below the top is an own parameter of the shape.** -/
theorem scSq_gtT (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + Gs < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + Gs) β) :
    x < S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := scSq_sup hGst hGs hβown hX0m hGm hcl hβd hX0cl hX0G3 hx
  exact scSq_gt hGst.monotone j x hj

end Seq

end Googology.Trans.PoR.InaccPsi.R2.Sc
