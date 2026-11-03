import Googology.Trans.PoR.InaccPsi.R2.YtUx

/-!
# The sub-bases `β + W^{X+e}·γ` (`X = Ω_{k+3}`): layers and the base data

`W^E = Le.leWe E`, `T_E(β) = Le.leTe S E β = ψ₂(β + W^E)`, `K^{E,β}_0 = Ω₁`, `K^{E,β}_{j+1} = ψ₂(β + W^E·K^{E,β}_j)`
(`Le.leKe`, defined for every exponent).  `Le.leKe_sup` / `Le.leTe_gt` / `Le.leBaseE_sub` need `E < Ω₂` (they bound
`ψ₂` through the codes modulo `ψ_{Ω₃}(0)`); `Ro.roBaseE_sub` needs a small shift (`X + e < ψ_{Ω₃}(0)`).  At the
exponents `E = Ω_{k+3} + e` the layer bound goes through the codes above the level `2` (`Vk.vkPsi2_le`) and the digit
at the position `E` (`Vk.vkA_mod`, `Vk.vkA_boundY`).

* `ytKe_lt_succ`, `ytKe_sup` (**`T_{E+1}(β) = sup_j K^{E,β}_j`** for `W^{E+1} ∣ β`, `β` own, `E` own over `β` and a code
  above the level `2` over every `Q > K_1`), `ytTe_gt` (**`γ < ψ₂(β + W^E·γ)` for every `γ < T_{E+1}(β)`**);
* `ytBaseSub` (**`Ro.RoBaseE λ X e (β + W^{X+e}·γ)`** from `Ro.RoBaseE λ X (e+1) β`, `e` a code, `γ ∈ H_λ`,
  `γ < T_{X+e+1}(β)`, `X = Ω_{k+3}`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

section KLay

variable {E β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (E + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hEm : ∀ x, 1 ≤ x → E ∈ S.CSet (β + leWe E * x) (S.psi (β + leWe E * x) (Om (1 + 1))))

include hβown hEm

theorem ytKe_lt_succ : ∀ j, leKe S E β j < leKe S E β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := ytKe_lt_succ j
    have hle : leKe S E β (j + 1) ≤ leKe S E β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulWe_mono IH.le))).1
    have h1 : (1 : Ordinal.{0}) ≤ leKe S E β (j + 1) :=
      (one_lt_omega0.trans (Lw.lw_omega_lt_SC (leKe_SC E β (j + 1)))).le
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulWe_lt IH)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (hEm _ h1) (CSet.of_lt (IH.trans_le hle)))
    rw [leWe_succ]; exact leMulWe_mono (leKe_lt_Om2 E β (j + 1)).le

theorem ytKe_mono {j j' : ℕ} (h : j ≤ j') : leKe S E β j ≤ leKe S E β j' :=
  (strictMono_nat_of_lt_succ (fun i => ytKe_lt_succ hβown hEm i)).monotone h

/-- **`T_{E+1}(β) = sup_j K^{E,β}_j`** (for `W^{E+1} ∣ β` and `E` a code above the level `2` over every `Q > K_1`). -/
theorem ytKe_sup (hβd : leWe (E + 1) ∣ β) (hEQ : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E)
    {x : Ordinal.{0}} (hx : x < leTe S (E + 1) β) : ∃ j, x < leKe S E β j := by
  have hμ0 : leWe E ≠ 0 := (leWe_pos _).ne'
  have hbdd : BddAbove (Set.range (leKe S E β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, leKe S E β j ↔ ∃ j, y < leKe S E β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, leKe S E β j < ⨆ j, leKe S E β j := fun j => (hlt _).2 ⟨j + 1, ytKe_lt_succ hβown hEm j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, leKe S E β j := hKQ 0
  have hQSC : SC (⨆ j, leKe S E β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (ytKe_mono hβown hEm (le_max_left i j))
    have hj' := hj.trans_le (ytKe_mono hβown hEm (le_max_right i j))
    exact ((leKe_SC E β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, leKe S E β j with hQ
  have hEQ' : VkA (1 + 1) Q E := hEQ Q hQSC (hKQ 1)
  have hFQ : leTe S (E + 1) β ≤ Q := by
    refine vkPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases lt_or_ge x β with hxβ | hxβ
    · have h1 : S.psi x (Om (1 + 1)) ≤ leKe S E β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (hxβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le hxβ
      have hd : d < leWe (E + 1) := (add_lt_add_iff_left β).1 hx
      have hc2 := vkA_mod hQSC (Om (1 + 1) * (E + 1)) hc
      have hdm : (β + d) % ω ^ (Om (1 + 1) * (E + 1)) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (E + 1) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rw [hdm] at hc2
      have hd' : d < ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by
        have : leWe (E + 1) = ω ^ (Om (1 + 1) * E + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this]; exact hd
      have hb := vkA_boundY hQSC (k := 1 + 1) (by rw [one_add_one_eq_two]; exact two_ne_zero) hEQ' d hc2 hd'
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

/-- **`γ < ψ₂(β + W^E·γ)` for every `γ < T_{E+1}(β)`.** -/
theorem ytTe_gt (hβd : leWe (E + 1) ∣ β) (hEQ : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E)
    {γ : Ordinal.{0}} (hγ : γ < leTe S (E + 1) β) : γ < S.psi (β + leWe E * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := ytKe_sup hβown hEm hβd hEQ hγ
  exact leKe_gt E β j γ hj

end KLay

/-- `Ω₂ ≤ Ω_{k+3}` as a `VkA` code: `Ω_{k+3} + e` is a code above the level `2` over every `Q > e`. -/
theorem ytXe_vkA (k : ℕ) {e Q : Ordinal.{0}} (hQ : 0 < Q) (he : e < Q) :
    VkA (1 + 1) Q (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) :=
  VkA.add (VkA.om hQ (add_le_add_left (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1) 1))
    (VkA.small he)

/-- **The sub-bases of a base of exponent `e + 1`** at `X = Ω_{k+3}`: `Ro.RoBaseE λ X e (β + W^{X+e}·γ)`. -/
theorem ytBaseSub {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ)
    {e β γ : Ordinal.{0}} (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hγH : γ ∈ cdHull S l)
    (hγ : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) :
    Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  rw [← add_assoc] at hβd hβA hβown
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hγW : γ < Om (1 + 1) := hγ.trans (leTe_lt_Om2 _ _)
  have hγ1W : γ + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hγW
  have hXeC : ∀ x, 1 ≤ x → X + e ∈ S.CSet (β + leWe (X + e) * x) (S.psi (β + leWe (X + e) * x) (Om (1 + 1))) := by
    intro x hx
    refine CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt (hexp.trans_le ?_))
    refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * x := leMulWe_mono hx
  have hEQ : ∀ Q, SC Q → leKe S (X + e) β 1 < Q → VkA (1 + 1) Q (X + e) := by
    intro Q hQ h1
    refine ytXe_vkA k hQ.1 ((hexp.trans_le ?_).trans h1)
    refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
    show leWe (X + e) ≤ leWe (X + e) * Om 1
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * Om 1 := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le
  have hγs := ytTe_gt hβown hXeC hβd hEQ hγ
  refine ⟨?_, CSet.add_mem hβH (leMulWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) heH) hγH), ?_,
    fun d hd => ?_, fun e' he' h' => ?_⟩
  · obtain ⟨q, rfl⟩ := hβd
    rw [leWe_succ, mul_assoc, ← mul_add]
    exact dvd_mul_right _ _
  · rw [add_assoc, ← mul_add_one]
    refine lt_of_le_of_lt ?_ hβA
    rw [leWe_succ]
    exact (add_le_add_iff_left β).2 (leMulWe_mono hγ1W.le)
  · have hd' : leWe (X + e) * γ + d ≤ leWe (X + e + 1) := by
      rw [leWe_succ]
      calc leWe (X + e) * γ + d ≤ leWe (X + e) * γ + leWe (X + e) := (add_le_add_iff_left _).2 hd
        _ = leWe (X + e) * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (X + e) * Om (1 + 1) := leMulWe_mono hγ1W.le
    rw [add_assoc]
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [mul_zero, zero_add, add_zero]
      rw [mul_zero, zero_add] at hd'
      exact hβown d hd'
    refine CSet.add_mem (hβown _ hd') (leMulWe_mem ?_ (CSet.of_lt ?_))
    · have h := hXeC γ (Order.one_le_iff_ne_zero.2 hγ0)
      exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 le_self_add)).2 h
    · exact hγs.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 le_self_add)).1
  · refine (hexpA e' he' (h'.trans (lt_add_one e).le)).trans_le ?_
    refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
    rw [add_assoc]; exact (add_le_add_iff_left β).2 le_add_self

end Googology.Trans.PoR.InaccPsi.R2.Yt
