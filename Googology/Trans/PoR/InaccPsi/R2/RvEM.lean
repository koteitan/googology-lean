import Googology.Trans.PoR.InaccPsi.R2.RvW2

/-!
# The level-`k` sequence `EM^k_j(X₀, β)` and the members `X₀ + W^k·ζ` of a level-`k` family

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `W_k = Ω₂^k` (`Le.leW k`), `O_k = Ω₁^k` (`Le.leO k`),
`T_E(β) = ψ_{Ω₂}(β + W^E)`.

* `rvW_mul` (`Ω₂·W_k = W_{k+1}`), `rvO_mul` (`Ω₁·O_k = O_{k+1}`), `rvClW`, `rvClO` (`LeCl` is closed under `W_k·`,
  `O_k·`);
* `rvEM S X₀ β k` (**`EM_0 = Ω₁`, `EM_{j+1} = T_{X₀ + W_k·EM_j}(β)`**), `rvEM_gt`, `rvEM_le_top`, `rvEM_lt_succ`,
  `rvEM_mono`, `rvEM_sup` (**`T_{X₀ + W_{k+1}}(β) = sup_j EM_j`**), `rvEM_ge`, `rvEM_gtT` (**every
  `ζ < T_{X₀ + W_{k+1}}(β)` is own at the shift `X₀ + W_k·ζ` relative to `β`**);
* `RvOff` (**an offset: `X₀ = X̂₀ = 0`, or a relative shift with the top law**), `rvOff_mono`, `rvSh_m` (**the
  members `(X₀ + W_k·ζ, X̂₀ + O_k·Θ ζ)` are shifts own relative to `β`**).

No new axiom.  New definitions: `rvEM`, `RvOff`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

theorem rvW_mul : ∀ k : ℕ, Om (1 + 1 : Ordinal.{0}) * leW k = leW (k + 1)
  | 0 => by rw [leW_zero, mul_one, leW_one]
  | k + 1 => by rw [leW_succ, ← mul_assoc, rvW_mul k, ← leW_succ]

theorem rvO_mul : ∀ k : ℕ, Om (1 : Ordinal.{0}) * leO k = leO (k + 1)
  | 0 => by rw [leO_zero, mul_one, leO_one]
  | k + 1 => by rw [leO_succ, ← mul_assoc, rvO_mul k, ← leO_succ]

theorem rvClW {Q : Ordinal.{0}} (hQ : SC Q) : ∀ (k : ℕ) {y : Ordinal.{0}}, LeCl (Om (1 + 1)) Q y →
    LeCl (Om (1 + 1)) Q (leW k * y)
  | 0, y, hy => by rw [leW_zero, one_mul]; exact hy
  | k + 1, y, hy => by
    rw [leW_succ, mul_assoc]; exact rvClW hQ k (LeCl.mulK hQ ldOm2_SC y hy)

theorem rvClO {Q : Ordinal.{0}} (hQ : SC Q) : ∀ (k : ℕ) {y : Ordinal.{0}}, LeCl (Om 1) Q y →
    LeCl (Om 1) Q (leO k * y)
  | 0, y, hy => by rw [leO_zero, one_mul]; exact hy
  | k + 1, y, hy => by
    rw [leO_succ, mul_assoc]; exact rvClO hQ k (LeCl.mulK hQ Ph.ph_SC_Om1 y hy)

theorem rvW_lt_succ {k : ℕ} {x : Ordinal.{0}} (hx : x < Om (1 + 1)) : leW k * x < leW (k + 1) := by
  rw [leW_succ]; exact leMulW_lt hx

theorem rvO_lt_succ {k : ℕ} {x : Ordinal.{0}} (hx : x < Om 1) : leO k * x < leO (k + 1) := by
  rw [leO_succ]; exact (mul_lt_mul_iff_right₀ (leO_pos k)).2 hx

/-- `EM_0 = Ω₁`, `EM_{j+1} = ψ_{Ω₂}(β + W^{X₀ + W_k·EM_j})`. -/
noncomputable def rvEM (S : InaccSeq.{0}) (X0 β : Ordinal.{0}) (k : ℕ) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (X0 + leW k * rvEM S X0 β k j)) (Om (1 + 1))

section Seq

variable {X0 β : Ordinal.{0}} {k : ℕ}

theorem rvEM_lt_Om2 : ∀ j, rvEM S X0 β k j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rvEM_SC : ∀ j, SC (rvEM S X0 β k j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem rvEM_gt : ∀ j x, x < rvEM S X0 β k j → x < S.psi (β + leWe (X0 + leW k * x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rvEM S X0 β k j) with h' | h'
    · exact rvEM_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (leMulW_mono h'))))).1

theorem rvEM_le_top : ∀ j, rvEM S X0 β k j ≤ leTe S (X0 + leW (k + 1)) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (rvW_lt_succ (rvEM_lt_Om2 j)).le)))).1

variable (hβown : ∀ d, d ≤ leWe (X0 + leW (k + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))

include hβown hX0m

theorem rvEM_lt_succ : ∀ j, rvEM S X0 β k j < rvEM S X0 β k (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rvEM_lt_succ j
    have hle : rvEM S X0 β k (j + 1) ≤ rvEM S X0 β k (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leMulW_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leMulW_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leW k * rvEM S X0 β k (j + 1)))
        (S.psi (β + leWe (X0 + leW k * rvEM S X0 β k (j + 1))) (Om (1 + 1))) :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvW_lt_succ (rvEM_lt_Om2 _)).le)))
      (leWe_mem (CSet.add_mem hX0 (leMulW_mem k (CSet.of_lt (IH.trans_le hle)))))

theorem rvEM_mono {j j' : ℕ} (h : j ≤ j') : rvEM S X0 β k j ≤ rvEM S X0 β k j' :=
  (strictMono_nat_of_lt_succ (fun i => rvEM_lt_succ hβown hX0m i)).monotone h

/-- **`T_{X₀ + W_{k+1}}(β) = sup_j EM_j`.** -/
theorem rvEM_sup (hβd : leWe (X0 + leW (k + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leW (k + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leW (k + 1)) β) : ∃ j, x < rvEM S X0 β k j := by
  have hbdd : BddAbove (Set.range (rvEM S X0 β k)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rvEM S X0 β k j ↔ ∃ j, y < rvEM S X0 β k j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rvEM S X0 β k j < ⨆ j, rvEM S X0 β k j :=
    fun j => (hlt _).2 ⟨j + 1, rvEM_lt_succ hβown hX0m j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rvEM S X0 β k j := hKQ 0
  have hQSC : SC (⨆ j, rvEM S X0 β k j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rvEM_mono hβown hX0m (le_max_left i j))
    have hj' := hj.trans_le (rvEM_mono hβown hX0m (le_max_right i j))
    exact ((rvEM_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rvEM S X0 β k j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rvEM S X0 β k 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (mul_pos (leW_pos k) (Om_pos one_ne_zero))))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvW_lt_succ gg_Om1_lt_Om2).le)))
      (leWe_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rvEM S X0 β k 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hFQ : leTe S (X0 + leW (k + 1)) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leW (k + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + leW (k + 1))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + leW (k + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leW (k + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + leW (k + 1 + 1) := by
      rw [← rvW_mul (k + 1), ← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans_lt hX1).trans
        (hKQ 1)
    have hXC : LeCl (Om (1 + 1)) Q (Om (1 + 1) * X0) :=
      LeCl.mulK hQSC ldOm2_SC X0 (hX0cl Q hQSC (hX1.trans (hKQ 1)).le)
    have hu := (leClDec hQSC ldOm2_SC (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X0 < ω ^ (Om (1 + 1) * ((k + 1 + 1 : ℕ) : Ordinal.{0})) := by
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + leW (k + 1 + 1) := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have hb := leCl_bound hQSC ldOm2_SC (k + 1) _ hu hu2
    change _ < leW (k + 1) * Q at hb
    have hK0 : leW (k + 1) ≠ 0 := (leW_pos _).ne'
    have hq : (log ω x' - Om (1 + 1) * X0) / leW (k + 1) < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + leW k * rvEM S X0 β k j) := by
      rw [mul_add, ← mul_assoc, rvW_mul k, ← hdec, add_assoc]
      refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
      calc log ω x' - Om (1 + 1) * X0
          < leW (k + 1) * ((log ω x' - Om (1 + 1) * X0) / leW (k + 1)) + leW (k + 1) :=
            Ordinal.lt_mul_div_add _ hK0
        _ = leW (k + 1) * ((log ω x' - Om (1 + 1) * X0) / leW (k + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ leW (k + 1) * rvEM S X0 β k j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (X0 + leW k * rvEM S X0 β k j) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X₀ + W_k·x}) ≥ T_{X₀ + W_{k+1}}(β)` for `x ≥ T_{X₀ + W_{k+1}}(β)`. -/
theorem rvEM_ge (hβd : leWe (X0 + leW (k + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leW (k + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : leTe S (X0 + leW (k + 1)) β ≤ x) :
    leTe S (X0 + leW (k + 1)) β ≤ S.psi (β + leWe (X0 + leW k * x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rvEM_sup hβown hX0m hβd hX0cl hX0G3 h
  have h1 : rvEM S X0 β k (j + 1) ≤ S.psi (β + leWe (X0 + leW k * x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leMulW_mono ((rvEM_le_top j).trans hx)))))).1
  exact absurd (hj.trans_le ((rvEM_lt_succ hβown hX0m j).le.trans h1)) (lt_irrefl _)

/-- **Every `ζ < T_{X₀ + W_{k+1}}(β)` is own at the shift `X₀ + W_k·ζ` relative to `β`.** -/
theorem rvEM_gtT (hβd : leWe (X0 + leW (k + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leW (k + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leW (k + 1)) β) :
    x < S.psi (β + leWe (X0 + leW k * x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rvEM_sup hβown hX0m hβd hX0cl hX0G3 hx
  exact rvEM_gt j x hj

end Seq

/-- **An offset at `λ` over `b`**: `X₀ = X̂₀ = 0`, or a shift own relative to `b` with the top law at the bases
`≥ b`. -/
def RvOff (S : InaccSeq.{0}) (l b X0 Xh0 : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ (RvSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0)

theorem rvOff_mono {l b b' X0 Xh0 : Ordinal.{0}} (hbb : b ≤ b') (h : RvOff S l b X0 Xh0) :
    RvOff S l b' X0 Xh0 := by
  rcases h with h | ⟨hs, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨rvSh_mono hbb hs, rvTop_mono hbb ht⟩

/-- The membership and the codes of an offset. -/
theorem rvOff_data {l b X0 Xh0 : Ordinal.{0}} (h : RvOff S l b X0 Xh0) :
    Om (1 + 1) ∣ X0 ∧ X0 ∈ cdHull S l ∧ X0 ∈ S.CSet 0 (S.psi (b + leWe X0) (Om (1 + 1))) ∧
      Xh0 ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X0) (Om (1 + 1)))) ∧
      (∀ Q, SC Q → S.psi (b + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0) ∧
      (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X0) (Om (1 + 1))) ≤ Q →
        LeCl (Om 1) Q Xh0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hs, -⟩
  · refine ⟨dvd_zero _, CSet.zero_mem _ _, CSet.zero_mem _ _, CSet.zero_mem _ _,
      fun Q hQ _ => LeCl.zero hQ.1, fun Q hQ _ => LeCl.zero hQ.1⟩
  · exact ⟨hs.dvd, hs.hull, hs.mem, hs.memh, hs.cl, hs.clh⟩

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The members `(X₀ + W_k·ζ, X̂₀ + O_k·Θ ζ)` of the level-`k` family are shifts own relative to `β`.** -/
theorem rvSh_m {k : ℕ} (hk : 1 ≤ k) {β X0 Xh0 ζ : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζW : ζ < Om (1 + 1))
    (hown : ζ < S.psi (β + leWe (X0 + leW k * ζ)) (Om (1 + 1)))
    (hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1) (hne : X0 + leW k * ζ ≠ 0)
    (hG3 : X0 + leW (k + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leO (k + 1) + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l β (X0 + leW k * ζ) (Xh0 + leO k * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have hle : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leW k * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ hown
  have hWk : Om (1 + 1) ∣ leW k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, ← rvW_mul j]; exact dvd_mul_right _ _
  have hlt1 : leW k * ζ < leW (k + 1) := rvW_lt_succ hζW
  have hlt2 : leO k * gxTh (upsilon l) (ldAtR S l) ζ < leO (k + 1) := rvO_lt_succ hΘ1
  refine ⟨hne, dvd_add hd (hWk.trans (dvd_mul_right _ _)),
    CSet.add_mem hH (leMulW_mem k ((ldHull_iff hl hX hζW).2 hζ)),
    CSet.add_mem (CSet_mono le_rfl hle hm) (leMulW_mem k (CSet.of_lt hown)),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh) (leMulO_mem k (CSet.of_lt hΘown)), ?_, ?_,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (rvClW hQ k (LeCl.small (hown.trans_le hb))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (rvClO hQ k (LeCl.small (hΘown.trans_le hb)))⟩
  · refine lt_of_le_of_lt ?_ hG3
    exact add_le_add_left ((add_le_add_iff_left X0).2 hlt1.le) _
  · refine lt_of_le_of_lt ?_ hG
    exact add_le_add_left ((add_le_add_iff_left Xh0).2 hlt2.le) _

end Mem

end Googology.Trans.PoR.InaccPsi.R2.Rv
