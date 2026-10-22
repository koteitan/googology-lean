import Googology.Trans.PoR.InaccPsi.R2.RqAt

/-!
# `sup_j EM_j = ψ_{Ω₂}(Ω₂^{Ω₂²})`, at every base: the own codes of the shifts `Ω₂·ξ`, and the road with the atoms
in `[ψ_{Ω₂}(Ω₂^{Ω₂²}), θ]`

`W^E = Ω₂^E = ω^{Ω₂·E}` (`Le.leWe`), `T_E(β) = ψ_{Ω₂}(β + W^E)` (`Le.leTe`), so `T_{Ω₂·Ω₂}(β) = ψ_{Ω₂}(β + Ω₂^{Ω₂²})`.
`EMb_0(β) = Ω₁`, `EMb_{j+1}(β) = ψ_{Ω₂}(β + W^{Ω₂·EMb_j(β)})` (`rqEMb`); `EMb(0) = EM` (`Rq.rqEM`).

* `rqEMb_gt` (`ξ < EMb_j(β) ⇒ ξ < ψ_{Ω₂}(β + W^{Ω₂·ξ})`), `rqEMb_le_top`, `rqEMb_lt_succ`, `rqEMb_mono`;
* `rqEMb_sup` (**`T_{Ω₂·Ω₂}(β) = sup_j EMb_j(β)`** for a base `β` with `W^{Ω₂·Ω₂} ∣ β`, own for
  `d ≤ W^{Ω₂·Ω₂}`: by `Le.lePsi2_le` and `Le.leCl_bound` at `m = 2` (the leading exponent `w < Ω₂³` of a code
  below `W^{Ω₂·Ω₂}` is `< Ω₂²·Q`)), `rqW2_gt` (**every `ξ < T_{Ω₂·Ω₂}(β)` is own at the shift `Ω₂·ξ` relative
  to `β`: `ξ < ψ_{Ω₂}(β + W^{Ω₂·ξ})`**), `rqW2_ge`;
* `rqEM_eq` (`EMb(0) = EM`), `rqEM_sup0` (**every `x < ψ_{Ω₂}(Ω₂^{Ω₂²})` is below some `EM_j`**), `rqEM_lt_FW`;
* `RqAtMove6 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `ψ_{Ω₂}(Ω₂^{Ω₂²}) ≤ s ≤ θ`;
  `rqAtMove5_of6`, `rqAtMove6_of5` (**`RqAtMove6 ⇔ RqAtMove5`**), `rqAtMove4_of6` (**`RqAtMove6` gives
  `Ro.RoAtMove4`**), `rqRoadH` (**the road**), `rqRoadH_hyps`.

No new axiom.  New definitions: `rqEMb`, the hypothesis name `RqAtMove6`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

/-- `EMb_0(β) = Ω₁`, `EMb_{j+1}(β) = ψ_{Ω₂}(β + W^{Ω₂·EMb_j(β)})`. -/
noncomputable def rqEMb (S : InaccSeq.{0}) (β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (Om (1 + 1) * rqEMb S β j)) (Om (1 + 1))

theorem rqEMb_lt_Om2 (β : Ordinal.{0}) : ∀ j, rqEMb S β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rqEMb_SC (β : Ordinal.{0}) : ∀ j, SC (rqEMb S β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem rqEMb_gt (β : Ordinal.{0}) :
    ∀ j x, x < rqEMb S β j → x < S.psi (β + leWe (Om (1 + 1) * x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rqEMb S β j) with h' | h'
    · exact rqEMb_gt β j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono (mul_le_mul_right h' _)))).1

theorem rqEMb_le_top (β : Ordinal.{0}) : ∀ j, rqEMb S β j ≤ leTe S (Om (1 + 1) * Om (1 + 1)) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono (mul_le_mul_right (rqEMb_lt_Om2 β j).le _)))).1

theorem rqW2_eq (y : Ordinal.{0}) :
    Om (1 + 1 : Ordinal.{0}) * (Om (1 + 1) * y) = ω ^ (Om (1 + 1) * ((2 : ℕ) : Ordinal.{0})) * y := by
  rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one, opow_add, gg_SC_eps ldOm2_SC,
    mul_assoc]

theorem rqW3_eq : Om (1 + 1 : Ordinal.{0}) * (Om (1 + 1) * Om (1 + 1)) =
    ω ^ (Om (1 + 1) * ((2 + 1 : ℕ) : Ordinal.{0})) := by
  rw [show ((2 + 1 : ℕ) : Ordinal.{0}) = 1 + 1 + 1 by norm_num, mul_add, mul_add, mul_one, opow_add, opow_add,
    gg_SC_eps ldOm2_SC, mul_assoc]

section Base

variable {β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (Om (1 + 1) * Om (1 + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))

include hβown

theorem rqEMb_lt_succ : ∀ j, rqEMb S β j < rqEMb S β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rqEMb_lt_succ j
    have hle : rqEMb S β (j + 1) ≤ rqEMb S β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono (mul_le_mul_right IH.le _)))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 IH))) ?_
    refine CSet.add_mem (hβown _ (leWe_mono (mul_le_mul_right (rqEMb_lt_Om2 β (j + 1)).le _)))
      (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (IH.trans_le hle))))

theorem rqEMb_mono {j j' : ℕ} (h : j ≤ j') : rqEMb S β j ≤ rqEMb S β j' :=
  (strictMono_nat_of_lt_succ (fun i => rqEMb_lt_succ hβown i)).monotone h

/-- **`T_{Ω₂·Ω₂}(β) = sup_j EMb_j(β)`.** -/
theorem rqEMb_sup (hβd : leWe (Om (1 + 1) * Om (1 + 1)) ∣ β) {x : Ordinal.{0}}
    (hx : x < leTe S (Om (1 + 1) * Om (1 + 1)) β) : ∃ j, x < rqEMb S β j := by
  have hbdd : BddAbove (Set.range (rqEMb S β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rqEMb S β j ↔ ∃ j, y < rqEMb S β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rqEMb S β j < ⨆ j, rqEMb S β j :=
    fun j => (hlt _).2 ⟨j + 1, rqEMb_lt_succ hβown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rqEMb S β j := hKQ 0
  have hQSC : SC (⨆ j, rqEMb S β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rqEMb_mono hβown (le_max_left i j))
    have hj' := hj.trans_le (rqEMb_mono hβown (le_max_right i j))
    exact ((rqEMb_SC β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rqEMb S β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hWWG3 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) := ldMul_lt_SC hG3 hWG3 hWG3
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hβ1 : S.psi β (Om (1 + 1)) < rqEMb S β 1 :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _))
      (hβown _ (leWe_mono (mul_le_mul_right gg_Om1_lt_Om2.le _)))
  have hFQ : leTe S (Om (1 + 1) * Om (1 + 1)) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (Om (1 + 1) * Om (1 + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (Om (1 + 1) * Om (1 + 1))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (Om (1 + 1) * Om (1 + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hWWG3).2] at hc2
    have hm : (β + x') % leWe (Om (1 + 1) * Om (1 + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < ω ^ (Om (1 + 1) * ((2 + 1 : ℕ) : Ordinal.{0})) := by
      rw [← rqW3_eq]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hb := leCl_bound hQSC ldOm2_SC 2 _ hlog hla
    set K := ω ^ (Om (1 + 1) * ((2 : ℕ) : Ordinal.{0})) with hK
    have hK0 : K ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hq : log ω x' / K < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (Om (1 + 1) * rqEMb S β j) := by
      rw [rqW2_eq]
      refine Order.add_one_le_of_lt ?_
      calc log ω x' < K * (log ω x' / K) + K := Ordinal.lt_mul_div_add _ hK0
        _ = K * (log ω x' / K + 1) := (mul_add_one _ _).symm
        _ ≤ K * rqEMb S β j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    have hxW : x' < leWe (Om (1 + 1) * rqEMb S β j) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{Ω₂·x}) ≥ T_{Ω₂·Ω₂}(β)` for `x ≥ T_{Ω₂·Ω₂}(β)`. -/
theorem rqW2_ge (hβd : leWe (Om (1 + 1) * Om (1 + 1)) ∣ β) {x : Ordinal.{0}}
    (hx : leTe S (Om (1 + 1) * Om (1 + 1)) β ≤ x) :
    leTe S (Om (1 + 1) * Om (1 + 1)) β ≤ S.psi (β + leWe (Om (1 + 1) * x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rqEMb_sup hβown hβd h
  have h1 : rqEMb S β (j + 1) ≤ S.psi (β + leWe (Om (1 + 1) * x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono (mul_le_mul_right ((rqEMb_le_top β j).trans hx) _)))).1
  exact absurd (hj.trans_le ((rqEMb_lt_succ hβown j).le.trans h1)) (lt_irrefl _)

/-- **Every `ξ < T_{Ω₂·Ω₂}(β)` is own at the shift `Ω₂·ξ` relative to `β`.** -/
theorem rqW2_gt (hβd : leWe (Om (1 + 1) * Om (1 + 1)) ∣ β) {x : Ordinal.{0}}
    (hx : x < leTe S (Om (1 + 1) * Om (1 + 1)) β) : x < S.psi (β + leWe (Om (1 + 1) * x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rqEMb_sup hβown hβd hx
  exact rqEMb_gt β j x hj

end Base

theorem rqEM_eq : ∀ j, rqEMb S 0 j = rqEM S j
  | 0 => rfl
  | j + 1 => by
    change S.psi (0 + leWe (Om (1 + 1) * rqEMb S 0 j)) (Om (1 + 1)) =
      S.psi (leWe (Om (1 + 1) * rqEM S j)) (Om (1 + 1))
    rw [zero_add, rqEM_eq j]

/-- **Every `x < ψ_{Ω₂}(Ω₂^{Ω₂²})` is below some `EM_j`.** -/
theorem rqEM_sup0 {x : Ordinal.{0}} (hx : x < S.psi (leWe (Om (1 + 1) * Om (1 + 1))) (Om (1 + 1))) :
    ∃ j, x < rqEM S j := by
  have hx' : x < leTe S (Om (1 + 1) * Om (1 + 1)) 0 := by unfold leTe; rwa [zero_add]
  obtain ⟨j, hj⟩ := rqEMb_sup (S := S) (β := 0) (fun _ _ => CSet.zero_mem _ _) (dvd_zero _) hx'
  exact ⟨j, by rwa [rqEM_eq] at hj⟩

theorem rqEM_lt_FW (j : ℕ) : rqEM S j < S.psi (leWe (Om (1 + 1) * Om (1 + 1))) (Om (1 + 1)) := by
  have h1 := rqEMb_lt_succ (S := S) (β := 0) (fun _ _ => CSet.zero_mem _ _) j
  have h2 := rqEMb_le_top (S := S) 0 (j + 1)
  rw [rqEM_eq] at h1
  have h3 := h1.trans_le h2
  unfold leTe at h3; rwa [zero_add] at h3

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(Ω₂^{Ω₂²}) ≤ s ≤ θ`.** -/
def RqAtMove6 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (Om (1 + 1) * Om (1 + 1))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RqAtMove6` gives `RqAtMove5`.** -/
theorem rqAtMove5_of6 (h : RqAtMove6 S) : RqAtMove5 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsj hsθ IH
  refine h n l l' hR h1 hr hl' hB hm hF hK s hs ?_ hsθ IH
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := rqEM_sup0 hlt
  exact absurd (hsj j) (not_lt.2 hj.le)

/-- **`RqAtMove5` gives `RqAtMove6`.** -/
theorem rqAtMove6_of5 (h : RqAtMove5 S) : RqAtMove6 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsW hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (fun j => (rqEM_lt_FW j).trans_le hsW) hsθ IH

/-- **`RqAtMove6` gives `RoAtMove4`** (hence `Rn.RnAtMove2`). -/
theorem rqAtMove4_of6 (h : RqAtMove6 S) : RoAtMove4 S := rqAtMove4_of5 (rqAtMove5_of6 h)

/-- **The road with `RqAtMove6`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rqRoadH (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RqAtMove6 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rqRoadG hU hO hL hV hN hlh (fun hν => rqAtMove5_of6 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `rqRoadH` follows from that of `Rn.rnRoadD`. -/
theorem rqRoadH_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RqAtMove6 S :=
  fun hν => rqAtMove6_of5 (rqAtMove5_of (roAtMove4_of (hat hν)))

end Googology.Trans.PoR.InaccPsi.R2.Rq
