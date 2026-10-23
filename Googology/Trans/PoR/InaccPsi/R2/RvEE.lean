import Googology.Trans.PoR.InaccPsi.R2.RvCor

/-!
# Ordinal levels: the sequence `EE_j(X₀, β, e)` and the members `X₀ + W^e·ζ`, for `1 ≤ e < ρ_λ`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), `T_E(β) = ψ_{Ω₂}(β + W^E)`.
As `Rv.RvEM` with the natural level `k` replaced by an ordinal `e < Ω₁` (`Ω₂·W^e = W^{1+e}`).

* `rvE_mem`, `rvCl_mulOp` (`LeCl` is closed under `ω^c·`), `rvWe_mul` (`Ω₂·W^e = W^{1+e}`), `rvOe_mul`,
  `rvWe_lt_succ`, `rvOe_lt_succ`;
* `rvEE S X₀ β e` (**`EE_0 = Ω₁`, `EE_{j+1} = T_{X₀ + W^e·EE_j}(β)`**), `rvEE_gt`, `rvEE_le_top`, `rvEE_lt_succ`,
  `rvEE_mono`, `rvEE_sup` (**`T_{X₀ + W^{e+1}}(β) = sup_j EE_j`**), `rvEE_ge`, `rvEE_gtT`;
* `rvSh_me` (**the members `(X₀ + W^e·ζ, X̂₀ + Ω^e·Θ ζ)` are shifts own relative to `β`**, `1 ≤ e < ρ_λ`).

No new axiom.  New definition: `rvEE`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

theorem rvE_mem {e a x : Ordinal.{0}} (he : e < Om 1) : e ∈ S.CSet a (S.psi x (Om (1 + 1))) :=
  CSet.of_lt (he.trans (psiS_bounds (S := S) x 1).1)

/-- `LeCl` is closed under `ω^c·` for a code `c`. -/
theorem rvCl_mulOp {κ Q c : Ordinal.{0}} (hQ : SC Q) (hc : LeCl κ Q c) (hκ : SC κ) :
    ∀ y, LeCl κ Q y → LeCl κ Q (ω ^ c * y) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact LeCl.zero hQ.1
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ y hy
  have hlead : ω ^ log ω y ≤ y := opow_log_le_self ω hy0
  have hdec : ω ^ log ω y + (y - ω ^ log ω y) = y := Ordinal.add_sub_cancel_of_le hlead
  have e : ω ^ c * y = ω ^ (c + log ω y) + ω ^ c * (y - ω ^ log ω y) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add]
  rw [e]
  exact LeCl.add (LeCl.opow hQ.1 (LeCl.add hc hlog))
    (IH _ (leRest_lt hy0) (hsub _ (LeCl.opow hQ.1 hlog) hlead))

theorem rvWe_mul (e : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) * leWe e = leWe (1 + e) := by
  unfold leWe; rw [mul_add, mul_one, opow_add, gg_SC_eps ldOm2_SC]

theorem rvOe_mul (e : Ordinal.{0}) : Om (1 : Ordinal.{0}) * leOe e = leOe (1 + e) := by
  unfold leOe; rw [mul_add, mul_one, opow_add, gg_SC_eps Ph.ph_SC_Om1]

theorem rvWe_lt_succ {e x : Ordinal.{0}} (hx : x < Om (1 + 1)) : leWe e * x < leWe (e + 1) := by
  rw [leWe_succ]; exact leMulWe_lt hx

theorem rvOe_lt_succ {e x : Ordinal.{0}} (hx : x < Om 1) : leOe e * x < leOe (e + 1) := by
  rw [leOe_succ]; exact (mul_lt_mul_iff_right₀ (leOe_pos e)).2 hx

/-- `EE_0 = Ω₁`, `EE_{j+1} = ψ_{Ω₂}(β + W^{X₀ + W^e·EE_j})`. -/
noncomputable def rvEE (S : InaccSeq.{0}) (X0 β e : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (X0 + leWe e * rvEE S X0 β e j)) (Om (1 + 1))

section Seq

variable {X0 β e : Ordinal.{0}}

theorem rvEE_lt_Om2 : ∀ j, rvEE S X0 β e j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rvEE_SC : ∀ j, SC (rvEE S X0 β e j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem rvEE_gt : ∀ j x, x < rvEE S X0 β e j → x < S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rvEE S X0 β e j) with h' | h'
    · exact rvEE_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono h'))))).1

theorem rvEE_le_top : ∀ j, rvEE S X0 β e j ≤ leTe S (X0 + leWe (e + 1)) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ (rvEE_lt_Om2 j)).le)))).1

variable (hβown : ∀ d, d ≤ leWe (X0 + leWe (e + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) (he1 : e < Om 1)

include hβown hX0m he1

theorem rvEE_lt_succ : ∀ j, rvEE S X0 β e j < rvEE S X0 β e (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rvEE_lt_succ j
    have hle : rvEE S X0 β e (j + 1) ≤ rvEE S X0 β e (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leMulWe_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1)))
        (S.psi (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1))) (Om (1 + 1))) :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ (rvEE_lt_Om2 _)).le)))
      (leWe_mem (CSet.add_mem hX0 (leMulWe_mem (rvE_mem he1) (CSet.of_lt (IH.trans_le hle)))))

theorem rvEE_mono {j j' : ℕ} (h : j ≤ j') : rvEE S X0 β e j ≤ rvEE S X0 β e j' :=
  (strictMono_nat_of_lt_succ (fun i => rvEE_lt_succ hβown hX0m he1 i)).monotone h

/-- **`T_{X₀ + W^{e+1}}(β) = sup_j EE_j`.** -/
theorem rvEE_sup (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) : ∃ j, x < rvEE S X0 β e j := by
  have hbdd : BddAbove (Set.range (rvEE S X0 β e)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rvEE S X0 β e j ↔ ∃ j, y < rvEE S X0 β e j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rvEE S X0 β e j < ⨆ j, rvEE S X0 β e j :=
    fun j => (hlt _).2 ⟨j + 1, rvEE_lt_succ hβown hX0m he1 j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rvEE S X0 β e j := hKQ 0
  have hQSC : SC (⨆ j, rvEE S X0 β e j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rvEE_mono hβown hX0m he1 (le_max_left i j))
    have hj' := hj.trans_le (rvEE_mono hβown hX0m he1 (le_max_right i j))
    exact ((rvEE_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rvEE S X0 β e j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rvEE S X0 β e 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (mul_pos (leWe_pos e) (Om_pos one_ne_zero))))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ gg_Om1_lt_Om2).le)))
      (leWe_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rvEE S X0 β e 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hFQ : leTe S (X0 + leWe (e + 1)) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe (e + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + leWe (e + 1))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + leWe (e + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe (e + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
      rw [show (1 : Ordinal.{0}) + e + 1 = 1 + (e + 1) from add_assoc _ _ _, ← rvWe_mul (e + 1), ← mul_add]
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
    have hu2 : log ω x' - Om (1 + 1) * X0 < ω ^ (Om (1 + 1) * (1 + e) + Om (1 + 1)) := by
      rw [← mul_add_one]; change _ < leWe (1 + e + 1)
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have h1e : LeCl (Om (1 + 1)) Q (1 + e) := LeCl.small ((Ph.ph_SC_Om1.isPrincipal
      (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)) he1).trans hΩQ)
    have hb := leCl_boundY hQSC ldOm2_SC h1e _ hu hu2
    change _ < leWe (1 + e) * Q at hb
    have hK0 : leWe (1 + e) ≠ 0 := (leWe_pos _).ne'
    have hq : (log ω x' - Om (1 + 1) * X0) / leWe (1 + e) < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + leWe e * rvEE S X0 β e j) := by
      rw [mul_add, ← mul_assoc, rvWe_mul e, ← hdec, add_assoc]
      refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
      calc log ω x' - Om (1 + 1) * X0
          < leWe (1 + e) * ((log ω x' - Om (1 + 1) * X0) / leWe (1 + e)) + leWe (1 + e) :=
            Ordinal.lt_mul_div_add _ hK0
        _ = leWe (1 + e) * ((log ω x' - Om (1 + 1) * X0) / leWe (1 + e) + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (1 + e) * rvEE S X0 β e j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (X0 + leWe e * rvEE S X0 β e j) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X₀ + W^e·x}) ≥ T_{X₀ + W^{e+1}}(β)` for `x ≥ T_{X₀ + W^{e+1}}(β)`. -/
theorem rvEE_ge (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : leTe S (X0 + leWe (e + 1)) β ≤ x) :
    leTe S (X0 + leWe (e + 1)) β ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rvEE_sup hβown hX0m he1 hβd hX0cl hX0G3 h
  have h1 : rvEE S X0 β e (j + 1) ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono ((rvEE_le_top j).trans hx)))))).1
  exact absurd (hj.trans_le ((rvEE_lt_succ hβown hX0m he1 j).le.trans h1)) (lt_irrefl _)

/-- **Every `ζ < T_{X₀ + W^{e+1}}(β)` is own at the shift `X₀ + W^e·ζ` relative to `β`.** -/
theorem rvEE_gtT (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) :
    x < S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rvEE_sup hβown hX0m he1 hβd hX0cl hX0G3 hx
  exact rvEE_gt j x hj

end Seq

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The members `(X₀ + W^e·ζ, X̂₀ + Ω^e·Θ ζ)` of the level-`e` family are shifts own relative to `β`**
(`1 ≤ e < ρ_λ`). -/
theorem rvSh_me {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) {β X0 Xh0 ζ : Ordinal.{0}}
    (hoff : RvOff S l β X0 Xh0)
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζW : ζ < Om (1 + 1))
    (hown : ζ < S.psi (β + leWe (X0 + leWe e * ζ)) (Om (1 + 1)))
    (hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1) (hne : X0 + leWe e * ζ ≠ 0)
    (hG3 : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (e + 1) + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l β (X0 + leWe e * ζ) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have hle : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe e * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ hown
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hWk : Om (1 + 1) ∣ leWe e := by
    have h := leWe_dvd he1; rwa [leWe_one] at h
  have heΩ : e < Om 1 := heρ.trans hρ1
  have hρT : upsilon l < gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X0 + leWe e * ζ)) (Om (1 + 1))) := by
    have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om
      (psiS_bounds (S := S) (β + leWe (X0 + leWe e * ζ)) 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at h
  have hlt1 : leWe e * ζ < leWe (e + 1) := rvWe_lt_succ hζW
  have hlt2 : leOe e * gxTh (upsilon l) (ldAtR S l) ζ < leOe (e + 1) := rvOe_lt_succ hΘ1
  refine ⟨hne, dvd_add hd (hWk.trans (dvd_mul_right _ _)),
    CSet.add_mem hH (leMulWe_mem ((ldHull_iff hl hX (heΩ.trans gg_Om1_lt_Om2)).2 (GxCl.small heρ))
      ((ldHull_iff hl hX hζW).2 hζ)),
    CSet.add_mem (CSet_mono le_rfl hle hm) (leMulWe_mem (rvE_mem heΩ) (CSet.of_lt hown)),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh)
      (leMulOe_mem (CSet.of_lt (heρ.trans hρT)) (CSet.of_lt hΘown)), ?_, ?_,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC e
      (LeCl.small ((heΩ.trans (psiS_bounds (S := S) _ 1).1).trans_le hb))) ldOm2_SC _ (LeCl.small (hown.trans_le hb))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 e
      (LeCl.small ((heρ.trans hρT).trans_le hb))) Ph.ph_SC_Om1 _ (LeCl.small (hΘown.trans_le hb)))⟩
  · refine lt_of_le_of_lt ?_ hG3
    exact add_le_add_left ((add_le_add_iff_left X0).2 hlt1.le) _
  · refine lt_of_le_of_lt ?_ hG
    exact add_le_add_left ((add_le_add_iff_left Xh0).2 hlt2.le) _

end Mem

end Googology.Trans.PoR.InaccPsi.R2.Rv
