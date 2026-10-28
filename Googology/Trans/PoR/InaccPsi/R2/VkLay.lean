import Googology.Trans.PoR.InaccPsi.R2.VkOwn

/-!
# The layers of a block at an exponent `E` that is a code above the level 2, with no bound on `E`

`W = Ω₂`, `W^E = Le.leWe E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(β + W^E·K_j)`
(`Le.leKe S E β`), `VkA 2 Q` the codes over `Q` above the level 2 (module `Vk.VkCode`).  `Uj.ujKe_sup`,
`Uj.ujTe_ge`, `Uj.ujTe_gt` ask `E + 1 < Y₃` and `E` a level-2 code `Ug.UgC S 2 Q`; here **no bound on `E`** and `E`
a code above the level 2 for every strongly critical `Q > K_1`, through `Vk.vkPsi2_le` and `Vk.vkA_boundY`.

* `vkKe_sup` (**`T_{E+1}(β) = sup_j K_j`** for `W^{E+1} ∣ β`), `vkTe_ge`, `vkTe_gt`
  (**`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

section Layers

variable {E β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (E + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hEC : E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1))))

include hβown hEC

/-- **`T_{E+1}(β) = sup_j K_j`** (for `W^{E+1} ∣ β` and `E` a code above the level 2 over every `Q > K_1`; no bound
on `E`). -/
theorem vkKe_sup (hβd : leWe (E + 1) ∣ β)
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E) {x : Ordinal.{0}}
    (hx : x < leTe S (E + 1) β) : ∃ j, x < leKe S E β j := by
  have hμ0 : leWe E ≠ 0 := (leWe_pos _).ne'
  have hbdd : BddAbove (Set.range (leKe S E β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, leKe S E β j ↔ ∃ j, y < leKe S E β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, leKe S E β j < ⨆ j, leKe S E β j :=
    fun j => (hlt _).2 ⟨j + 1, roKe_lt_succ hβown hEC j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, leKe S E β j := hKQ 0
  have hQSC : SC (⨆ j, leKe S E β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (roKe_mono hβown hEC (le_max_left i j))
    have hj' := hj.trans_le (roKe_mono hβown hEC (le_max_right i j))
    exact ((leKe_SC E β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, leKe S E β j with hQ
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hFQ : leTe S (E + 1) β ≤ Q := by
    refine vkPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases lt_or_ge x β with hxβ | hxβ
    · have h1 : S.psi x (Om (1 + 1)) ≤ leKe S E β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (hxβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le hxβ
      have hd : d < leWe (E + 1) := (add_lt_add_iff_left β).1 hx
      have hc2 := vkA_mod hQSC (Om (1 + 1) * (E + 1)) hc
      change VkA (1 + 1) Q ((β + d) % leWe (E + 1)) at hc2
      have hdm : (β + d) % leWe (E + 1) = d := by
        obtain ⟨q, rfl⟩ := hβd
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rw [hdm] at hc2
      have hd' : d < ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by
        have : leWe (E + 1) = ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this]; exact hd
      have hb := vkA_boundY hQSC h2 (hEL Q hQSC (hKQ 1)) d hc2 hd'
      change d < leWe E * Q at hb
      have hdq : d / leWe E < Q := (Ordinal.lt_mul_iff_div_lt hμ0).1 hb
      obtain ⟨j, hj⟩ := (hlt _).1 hdq
      have hd2 : d < leWe E * leKe S E β j := by
        calc d < leWe E * (d / leWe E) + leWe E := Ordinal.lt_mul_div_add d hμ0
          _ = leWe E * (d / leWe E + 1) := (mul_add_one _ _).symm
          _ ≤ leWe E * leKe S E β j := leMulWe_mono (Order.add_one_le_of_lt hj)
      have := hKQ (j + 1)
      rw [leKe_succ] at this
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hd2.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^E·γ) ≥ T_{E+1}(β)` for `γ ≥ T_{E+1}(β)`. -/
theorem vkTe_ge (hβd : leWe (E + 1) ∣ β)
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E) {γ : Ordinal.{0}}
    (hγ : leTe S (E + 1) β ≤ γ) : leTe S (E + 1) β ≤ S.psi (β + leWe E * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := vkKe_sup hβown hEC hβd hEL h
  have h1 : leKe S E β (j + 1) ≤ S.psi (β + leWe E * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulWe_mono ((leKe_le_top E β j).trans hγ)))).1
  exact absurd (hj.trans_le ((roKe_lt_succ hβown hEC j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`** (`E` a code above the level 2; no bound on `E`). -/
theorem vkTe_gt (hβd : leWe (E + 1) ∣ β)
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E) {γ : Ordinal.{0}}
    (hγ : γ < leTe S (E + 1) β) : γ < S.psi (β + leWe E * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := vkKe_sup hβown hEC hβd hEL hγ
  exact leKe_gt E β j γ hj

end Layers

end Googology.Trans.PoR.InaccPsi.R2.Vk
