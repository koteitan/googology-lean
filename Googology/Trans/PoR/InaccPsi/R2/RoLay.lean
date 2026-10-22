import Googology.Trans.PoR.InaccPsi.R2.RnT1

/-!
# The layers of a block at an arbitrary exponent `E` (not only a code)

`W = Ω₂`, `W^E = Le.leWe E`, `T_E(β) = Le.leTe S E β = ψ_{Ω₂}(β + W^E)`, `K_0 = Ω₁`,
`K_{j+1} = ψ_{Ω₂}(β + W^E·K_j)` (`Le.leKe S E β`).  The lemmas of `Le.LeELay` that ask the exponent to be a code
`e < ψ_{Ω₂}(β + W^e)` are restated for an exponent `E` that is only **own in the closure sense**
(`E ∈ Cl(β + W^E, ψ_{Ω₂}(β + W^E))`) and **a code over `Q` with the generator `Ω₂`** (`Le.LeCl`) for every
strongly critical `Q > K_1`; this covers the shifted exponents `E = X + e` (`X = Ω₂·k`, `e` a code).

* `roEC_mono` (the closure ownness is inherited upwards), `roKe_E_mem`, `roKe_lt_succ`, `roKe_mono`;
* `roKe_sup` (**`T_{E+1}(β) = sup_j K_j`** for `W^{E+1} ∣ β`), `roTe_ge`, `roTe_gt`
  (**`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- The closure ownness of an exponent is inherited upwards. -/
theorem roEC_mono {E β x : Ordinal.{0}}
    (hEC : E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1)))) (hx : leWe E ≤ x) :
    E ∈ S.CSet (β + x) (S.psi (β + x) (Om (1 + 1))) :=
  CSet_mono ((add_le_add_iff_left β).2 hx)
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hx)).1 hEC

theorem roOne_le_Ke (E β : Ordinal.{0}) (j : ℕ) : 1 ≤ leKe S E β j := by
  rcases j with _ | j
  · exact (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le
  · exact (one_lt_omega0.trans (Lw.lw_omega_lt_SC (leKe_SC E β (j + 1)))).le

section Layers

variable {E β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (E + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hEC : E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1))))

include hEC in
theorem roKe_E_mem (j : ℕ) :
    E ∈ S.CSet (β + leWe E * leKe S E β j) (S.psi (β + leWe E * leKe S E β j) (Om (1 + 1))) := by
  refine roEC_mono hEC ?_
  calc leWe E = leWe E * 1 := (mul_one _).symm
    _ ≤ leWe E * leKe S E β j := leMulWe_mono (roOne_le_Ke E β j)

include hβown hEC

theorem roKe_lt_succ : ∀ j, leKe S E β j < leKe S E β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := roKe_lt_succ j
    have hle : leKe S E β (j + 1) ≤ leKe S E β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulWe_mono IH.le))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulWe_lt IH)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (roKe_E_mem hEC (j + 1)) (CSet.of_lt (IH.trans_le hle)))
    rw [leWe_succ]; exact leMulWe_mono (leKe_lt_Om2 E β (j + 1)).le

theorem roKe_mono {j j' : ℕ} (h : j ≤ j') : leKe S E β j ≤ leKe S E β j' :=
  (strictMono_nat_of_lt_succ (fun i => roKe_lt_succ hβown hEC i)).monotone h

/-- **`T_{E+1}(β) = sup_j K_j`** (for `W^{E+1} ∣ β`, `E + 1 < ψ_{Ω₃}(0)`, `E` a code over every `Q > K_1`). -/
theorem roKe_sup (hβd : leWe (E + 1) ∣ β) (hEG : E + 1 < S.psi 0 (Om (1 + 1 + 1)))
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → LeCl (Om (1 + 1)) Q E) {x : Ordinal.{0}}
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
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hFQ : leTe S (E + 1) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases lt_or_ge x β with hxβ | hxβ
    · have h1 : S.psi x (Om (1 + 1)) ≤ leKe S E β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (hxβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le hxβ
      have hd : d < leWe (E + 1) := (add_lt_add_iff_left β).1 hx
      have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (E + 1)) hc
      change LeCl (Om (1 + 1)) Q ((β + d) % S.psi 0 (Om (1 + 1 + 1)) % leWe (E + 1)) at hc2
      rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hEG).2] at hc2
      have hdm : (β + d) % leWe (E + 1) = d := by
        obtain ⟨q, rfl⟩ := hβd
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rw [hdm] at hc2
      have hd' : d < ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by
        have : leWe (E + 1) = ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this]; exact hd
      have hb := leCl_boundY hQSC ldOm2_SC (hEL Q hQSC (hKQ 1)) d hc2 hd'
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
theorem roTe_ge (hβd : leWe (E + 1) ∣ β) (hEG : E + 1 < S.psi 0 (Om (1 + 1 + 1)))
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → LeCl (Om (1 + 1)) Q E) {γ : Ordinal.{0}}
    (hγ : leTe S (E + 1) β ≤ γ) : leTe S (E + 1) β ≤ S.psi (β + leWe E * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := roKe_sup hβown hEC hβd hEG hEL h
  have h1 : leKe S E β (j + 1) ≤ S.psi (β + leWe E * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulWe_mono ((leKe_le_top E β j).trans hγ)))).1
  exact absurd (hj.trans_le ((roKe_lt_succ hβown hEC j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`.** -/
theorem roTe_gt (hβd : leWe (E + 1) ∣ β) (hEG : E + 1 < S.psi 0 (Om (1 + 1 + 1)))
    (hEL : ∀ Q, SC Q → leKe S E β 1 < Q → LeCl (Om (1 + 1)) Q E) {γ : Ordinal.{0}}
    (hγ : γ < leTe S (E + 1) β) : γ < S.psi (β + leWe E * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := roKe_sup hβown hEC hβd hEG hEL hγ
  exact leKe_gt E β j γ hj

end Layers

end Googology.Trans.PoR.InaccPsi.R2.Ro
