import Googology.Trans.PoR.InaccPsi.R2.YdMoveB

/-!
# THE PLATEAU OVER A BASE FOR A SHIFT IN THE CLOSURES ABOVE THE BASE

`W^x = leWe x`, `e^β_m = Yd.ydEB S X β m` (`e_0 = 0`, `e_{m+1} = ψ₂(β + W^{X+e_m})`).  `Yd.ydKeyB`, `Yd.ydTopB_eq`,
`Yd.ydOwnB_iff` ask `X ∈ Cl(a, b)` for EVERY `a, b`; that is false for `X = Y₃ = ψ_{Ω₃}(Ω₃)` (it lies in `Cl(a, b)`
only for `a > Ω₃`).  Here the hypothesis is only `X ∈ Cl(a, b)` for every `a > β`:

* `zdR3c` (as `Yd.ydR3c`, no membership hypothesis), `zdEBr_lt_succ`, `zdEBr_mono`, `zdStageBr_mono`, `zdR3Br`,
  `zdKeyBr`, `zdTopBr_eq` (**THE PLATEAU `ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`**), `zdLtTopBr`, `zdOwnBr_iff`
  (**`(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < ψ₂(β + W^{X+Ω₂})`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

/-- **A member of `Cl(a, ψ₂ a)` below `W^{X+Ω₂}` is below `W^{X+ψ₂ a}`** (any `a`, any `X`). -/
theorem zdR3c (X a : Ordinal.{0}) {y : Ordinal.{0}} (hy : y ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hlt : y < leWe (X + Om (1 + 1))) : y < leWe (X + S.psi a (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hεΩ : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  set E := S.psi a (Om (1 + 1)) with hEdef
  rcases eq_or_ne y 0 with rfl | hy0
  · exact opow_pos _ omega0_pos
  set L := log ω y with hLdef
  have hLmem : L ∈ S.CSet a E := leLog_mem hy
  have hlt' : y < ω ^ (Om (1 + 1) * (X + Om (1 + 1))) := hlt
  have hLlt : L < Om (1 + 1) * X + Om (1 + 1) * Om (1 + 1) := by
    have := (lt_opow_iff_log_lt one_lt_omega0 hy0).1 hlt'
    rwa [mul_add] at this
  unfold leWe
  refine (lt_opow_iff_log_lt one_lt_omega0 hy0).2 ?_
  rw [mul_add]
  rcases lt_or_ge L (Om (1 + 1) * X) with h1 | h1
  · exact h1.trans_le le_self_add
  · have hsub : L - Om (1 + 1) * X < Om (1 + 1) * Om (1 + 1) := Ry.rySub_lt h1 hLlt
    set q := (L - Om (1 + 1) * X) / Om (1 + 1) with hq
    have hsm : L - Om (1 + 1) * X ∈ S.CSet a E := Ta.taSub_mem L hLmem _
    have hqC : q ∈ S.CSet a E := by
      have h := (Vh.vhC_div _ hsm (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [hεΩ] at h
    have hq2 : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hsub
    have hqE : q < E := lt_psi_of_mem hκ2 hqC hq2
    have hq1 : q + 1 ≤ E := Order.add_one_le_of_lt hqE
    have hlm : L - Om (1 + 1) * X < Om (1 + 1) * (q + 1) := by
      have := Ordinal.lt_mul_succ_div (L - Om (1 + 1) * X) hΩ0
      rwa [Order.succ_eq_add_one] at this
    have e1 : L = Om (1 + 1) * X + (L - Om (1 + 1) * X) := (Ordinal.add_sub_cancel_of_le h1).symm
    show L < _
    rw [e1]
    exact (add_lt_add_iff_left _).2 (hlm.trans_le (mul_le_mul_right hq1 _))

section Gen

variable {X β : Ordinal.{0}} (hXr : ∀ a b : Ordinal.{0}, β < a → X ∈ S.CSet a b)
  (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
include hXr hβ

/-- The iterates over `β` increase strictly. -/
theorem zdEBr_lt_succ : ∀ m, ydEB S X β m < ydEB S X β (m + 1)
  | 0 => by rw [ydEB_zero]; exact (ydEB_SC X β 0).1
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    have ih := zdEBr_lt_succ m
    rw [ydEB_succ X β (m + 1)]
    conv_lhs => rw [ydEB_succ]
    refine psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 ih))) ?_
    refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβ)
      (leWe_mem (CSet.add_mem (hXr _ _ (lt_add_of_pos_right β (leWe_pos _))) (CSet.of_lt ?_)))
    calc ydEB S X β m < ydEB S X β (m + 1) := ih
      _ = S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) := ydEB_succ X β m
      _ ≤ S.psi (β + leWe (X + ydEB S X β (m + 1))) (Om (1 + 1)) :=
        (psi_mono hκ2 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 ih.le)) β)).1

theorem zdEBr_mono : Monotone (ydEB S X β) :=
  monotone_nat_of_le_succ fun m => (zdEBr_lt_succ hXr hβ m).le

theorem zdStageBr_mono {i j : ℕ} (h : i ≤ j) :
    S.CSet (β + leWe (X + ydEB S X β i)) (ydEB S X β (i + 1)) ⊆
      S.CSet (β + leWe (X + ydEB S X β j)) (ydEB S X β (j + 1)) := by
  rw [ydEB_succ, ydEB_succ]
  exact (psi_mono (InR_Om_succ 1)
    (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (zdEBr_mono hXr hβ h))) β)).2

omit hXr hβ in
/-- **A member of the stage below `β + W^{X+Ω₂}` is below `β + W^{X+e^β_{k+1}}`.** -/
theorem zdR3Br (k : ℕ) {y : Ordinal.{0}} (hy : y ∈ S.CSet (β + leWe (X + ydEB S X β k)) (ydEB S X β (k + 1)))
    (hlt : y < β + leWe (X + Om (1 + 1))) : y < β + leWe (X + ydEB S X β (k + 1)) := by
  rcases lt_or_ge y β with h1 | h1
  · exact h1.trans_le le_self_add
  · rw [ydEB_succ] at hy ⊢
    have hz : y - β ∈ S.CSet (β + leWe (X + ydEB S X β k))
        (S.psi (β + leWe (X + ydEB S X β k)) (Om (1 + 1))) := Ta.taSub_mem y hy β
    have hzl : y - β < leWe (X + Om (1 + 1)) := Ry.rySub_lt h1 hlt
    have h := zdR3c X _ hz hzl
    have e1 : y = β + (y - β) := (Ordinal.add_sub_cancel_of_le h1).symm
    rw [e1]
    exact (add_lt_add_iff_left β).2 h

/-- **Every member of `Cl(β + W^{X+Ω₂}, sup_m e^β_m)` lies in a stage.** -/
theorem zdKeyBr : ∀ y ∈ S.CSet (β + leWe (X + Om (1 + 1))) (⨆ m : ℕ, ydEB S X β m),
    ∃ k, y ∈ S.CSet (β + leWe (X + ydEB S X β k)) (ydEB S X β (k + 1)) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ydEB_bdd X β)).1 h
    exact ⟨n, CSet.of_lt (hn.trans (zdEBr_lt_succ hXr hβ n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (zdStageBr_mono hXr hβ (le_max_left i j) hi)
      (zdStageBr_mono hXr hβ (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (zdStageBr_mono hXr hβ (le_max_left i j) hi)
      (zdStageBr_mono hXr hβ (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < β + leWe (X + ydEB S X β (k + 1)) := zdR3Br k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < β + leWe (X + ydEB S X β N) :=
      hlt.trans_le (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2
        (zdEBr_mono hXr hβ (le_max_left (k + 1) i)))) β)
    have heN := zdStageBr_mono hXr hβ ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := zdStageBr_mono hXr hβ (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU OVER `β`**: `ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`. -/
theorem zdTopBr_eq : S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) = ⨆ m : ℕ, ydEB S X β m := by
  refine le_antisymm (psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_) (ciSup_le (ydEB_le_top X β))
  obtain ⟨n, hn⟩ := zdKeyBr hXr hβ y hy
  rw [ydEB_succ] at hn
  have h := lt_psi_of_mem (InR_Om_succ 1) hn hy2
  rw [← ydEB_succ] at h
  exact h.trans_le (le_ciSup (ydEB_bdd X β) (n + 1))

theorem zdLtTopBr {e : Ordinal.{0}} (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    ∃ m, e < ydEB S X β m := by
  rw [zdTopBr_eq hXr hβ] at he
  exact (lt_ciSup_iff (ydEB_bdd X β)).1 he

/-- **`(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < ψ₂(β + W^{X+Ω₂})`.** -/
theorem zdOwnBr_iff (e : Ordinal.{0}) :
    (∀ e', e' ≤ e → e' < S.psi (β + leWe (X + e')) (Om (1 + 1))) ↔
      e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd ((h _ hc).trans_le (ydTopFailB X β)) (lt_irrefl _)
  · intro he e' he'
    obtain ⟨m, hm⟩ := zdLtTopBr hXr hβ (he'.trans_lt he)
    exact ydOwnB X β m e' hm

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Zd
