import Googology.Trans.PoR.InaccPsi.R2.ZiPlat3

/-!
# THE PLATEAU OVER A BASE FOR A SHIFT WITH RELATIVE MEMBERSHIP

`W^x = leWe x`, `e^β_m = Yd.ydEB S X β m` (`e_0 = 0`, `e_{m+1} = ψ₂(β + W^{X+e_m})`).  `Zd.zdTopBr_eq`,
`Zd.zdOwnBr_iff` ask `X ∈ Cl(a, b)` for every `a > β` and EVERY `b`; that is false for a shift `X = P + Ω₂·ξ` with a
code coefficient `ξ` (it is in `Cl(a, b)` only for `b > ξ`).  Here the hypothesis is `ZiMemR S β X`: `X ∈ Cl(a, b)` for
every `a > β` and every `b ≥ ψ₂(β + W^X)` (the closures the plateau argument meets):

* `ziEBr_lt_succ`, `ziEBr_mono`, `ziStageBr_mono`, `ziKeyBr`, `ziTopBr_eq` (**`ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`**),
  `ziLtTopBr`, `ziOwnBr_iff` (**`(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < ψ₂(β + W^{X+Ω₂})`**), `ziTopE_ge`.

These generalize `Zd.zdEBr_lt_succ` … `Zd.zdOwnBr_iff`, `Zd.zdTopE_ge` (same proofs; the one use of the membership
is at `b = ψ₂(β + W^{X+e_m}) ≥ ψ₂(β + W^X)`).

No new axiom.  New definition: `ZiMemR` (the relative membership hypothesis).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Yd Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

/-- **Relative membership of a shift `X` over the base `β`**: `X ∈ Cl(a, b)` for every `a > β`, `b ≥ ψ₂(β + W^X)`. -/
def ZiMemR (S : InaccSeq.{0}) (β X : Ordinal.{0}) : Prop :=
  ∀ a b : Ordinal.{0}, β < a → S.psi (β + leWe X) (Om (1 + 1)) ≤ b → X ∈ S.CSet a b

/-- Membership in every closure above `β` gives the relative membership. -/
theorem ziMemR_of {β X : Ordinal.{0}} (h : ∀ a b : Ordinal.{0}, β < a → X ∈ S.CSet a b) : ZiMemR S β X :=
  fun a b ha _ => h a b ha

/-- The relative membership at `β` gives it at every `β' ≥ β`. -/
theorem ziMemR_mono {β β' X : Ordinal.{0}} (h : ZiMemR S β X) (hβ : β ≤ β') : ZiMemR S β' X :=
  fun a b ha hb => h a b (hβ.trans_lt ha)
    (((psi_mono (InR_Om_succ 1) (add_le_add_left hβ _)).1).trans hb)

section Gen

variable {X β : Ordinal.{0}} (hXr : ZiMemR S β X)
  (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
include hXr hβ

/-- The iterates over `β` increase strictly. -/
theorem ziEBr_lt_succ : ∀ m, ydEB S X β m < ydEB S X β (m + 1)
  | 0 => by rw [ydEB_zero]; exact (ydEB_SC X β 0).1
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    have ih := ziEBr_lt_succ m
    rw [ydEB_succ X β (m + 1)]
    conv_lhs => rw [ydEB_succ]
    refine psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 ih))) ?_
    refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβ)
      (leWe_mem (CSet.add_mem (hXr _ _ (lt_add_of_pos_right β (leWe_pos _))
        (psi_mono hκ2 (add_le_add_right (leWe_mono le_self_add) β)).1) (CSet.of_lt ?_)))
    calc ydEB S X β m < ydEB S X β (m + 1) := ih
      _ = S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) := ydEB_succ X β m
      _ ≤ S.psi (β + leWe (X + ydEB S X β (m + 1))) (Om (1 + 1)) :=
        (psi_mono hκ2 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 ih.le)) β)).1

theorem ziEBr_mono : Monotone (ydEB S X β) :=
  monotone_nat_of_le_succ fun m => (ziEBr_lt_succ hXr hβ m).le

theorem ziStageBr_mono {i j : ℕ} (h : i ≤ j) :
    S.CSet (β + leWe (X + ydEB S X β i)) (ydEB S X β (i + 1)) ⊆
      S.CSet (β + leWe (X + ydEB S X β j)) (ydEB S X β (j + 1)) := by
  rw [ydEB_succ, ydEB_succ]
  exact (psi_mono (InR_Om_succ 1)
    (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ziEBr_mono hXr hβ h))) β)).2

/-- **Every member of `Cl(β + W^{X+Ω₂}, sup_m e^β_m)` lies in a stage.** -/
theorem ziKeyBr : ∀ y ∈ S.CSet (β + leWe (X + Om (1 + 1))) (⨆ m : ℕ, ydEB S X β m),
    ∃ k, y ∈ S.CSet (β + leWe (X + ydEB S X β k)) (ydEB S X β (k + 1)) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ydEB_bdd X β)).1 h
    exact ⟨n, CSet.of_lt (hn.trans (ziEBr_lt_succ hXr hβ n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ziStageBr_mono hXr hβ (le_max_left i j) hi)
      (ziStageBr_mono hXr hβ (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ziStageBr_mono hXr hβ (le_max_left i j) hi)
      (ziStageBr_mono hXr hβ (le_max_right i j) hj)⟩
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
        (ziEBr_mono hXr hβ (le_max_left (k + 1) i)))) β)
    have heN := ziStageBr_mono hXr hβ ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ziStageBr_mono hXr hβ (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU OVER `β`**: `ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`. -/
theorem ziTopBr_eq : S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) = ⨆ m : ℕ, ydEB S X β m := by
  refine le_antisymm (psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_) (ciSup_le (ydEB_le_top X β))
  obtain ⟨n, hn⟩ := ziKeyBr hXr hβ y hy
  rw [ydEB_succ] at hn
  have h := lt_psi_of_mem (InR_Om_succ 1) hn hy2
  rw [← ydEB_succ] at h
  exact h.trans_le (le_ciSup (ydEB_bdd X β) (n + 1))

theorem ziLtTopBr {e : Ordinal.{0}} (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    ∃ m, e < ydEB S X β m := by
  rw [ziTopBr_eq hXr hβ] at he
  exact (lt_ciSup_iff (ydEB_bdd X β)).1 he

/-- **`(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < ψ₂(β + W^{X+Ω₂})`.** -/
theorem ziOwnBr_iff (e : Ordinal.{0}) :
    (∀ e', e' ≤ e → e' < S.psi (β + leWe (X + e')) (Om (1 + 1))) ↔
      e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd ((h _ hc).trans_le (ydTopFailB X β)) (lt_irrefl _)
  · intro he e' he'
    obtain ⟨m, hm⟩ := ziLtTopBr hXr hβ (he'.trans_lt he)
    exact ydOwnB X β m e' hm

end Gen

/-- `ψ₂(a + W^{X+x}) ≥ ψ₂(a + W^{X+Ω₂})` for every `x ≥ ψ₂(a + W^{X+Ω₂})` (`X` in the closures above `a`). -/
theorem ziTopE_ge {X a x : Ordinal.{0}} (hXr : ZiMemR S a X)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hx : S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1)) ≤ x) :
    S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1)) ≤ S.psi (a + leWe (X + x)) (Om (1 + 1)) := by
  rw [ziTopBr_eq hXr han]
  refine ciSup_le fun m => ?_
  cases m with
  | zero => rw [ydEB_zero]; exact zero_le
  | succ m =>
    rw [ydEB_succ]
    refine (psi_mono (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono ((add_le_add_iff_left X).2 ?_)))).1
    exact ((ziEBr_lt_succ hXr han m).trans_le (ydEB_le_top X a (m + 1))).le.trans hx

end Googology.Trans.PoR.InaccPsi.R2.Zi
