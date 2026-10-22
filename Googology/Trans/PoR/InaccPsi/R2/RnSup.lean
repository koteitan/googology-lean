import Googology.Trans.PoR.InaccPsi.R2.LjRoad

/-!
# The own exponents at a base `β`: every `e < T_W(β) = ψ_{Ω₂}(β + Ω₂^{Ω₂})` is own

`W = Ω₂`, `W^e = Le.leWe e`, `T_W(β) = ψ_{Ω₂}(β + W^W)` (`rnTW`; `rnTW 0 = ψ_{Ω₂}(Ω₂^{Ω₂})`).  A **base** at `λ`
(`RnBase S λ β`): `W^W ∣ β`, `β ∈ H_λ`, `β + W^W < A_{η_λ}`, `β ∈ Cl(β + d, ψ_{Ω₂}(β + d))` for `d ≤ W^W`.

* `rnEL` (`EL^β_0 = Ω₁`, `EL^β_{j+1} = ψ_{Ω₂}(β + W^{EL^β_j})`), `rnEL_lt_succ`, `rnEL_gt`, `rnEL_sup`
  (**`T_W(β) = sup_j EL^β_j`**, from `Le.lePsi2_le`: the tail of a code over `β` is a code), `rnTW_gt` (**every
  `e < T_W(β)` is an own exponent at `β`**), `rnTW_ge`;
* `rnBaseE` (**a base is a base of exponent `e`** (`Le.LeBaseE`) **for every `e < T_W(β)`**), `rnTW_atom`,
  `rnBase_atom`, `rnBase_lt`.

So past `ψ_{Ω₂}(Ω₂^{Ω₂})` the condition of `Le.LeBaseE` holds at every base `β` for the exponents below `T_W(β)`
only; `Le.LeBaseE S λ e 0` fails at `e = ψ_{Ω₂}(Ω₂^{Ω₂})`.

No new axiom.  New definitions: `rnTW`, `rnEL`, `RnBase`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `T_W(β) = ψ_{Ω₂}(β + Ω₂^{Ω₂})`. -/
noncomputable def rnTW (S : InaccSeq.{0}) (β : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (β + leWe (Om (1 + 1))) (Om (1 + 1))

/-- `EL^β_0 = Ω₁`, `EL^β_{j+1} = ψ_{Ω₂}(β + W^{EL^β_j})`. -/
noncomputable def rnEL (S : InaccSeq.{0}) (β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (rnEL S β j)) (Om (1 + 1))

theorem rnTW_zero : rnTW S 0 = leFWW S := by unfold rnTW leFWW; rw [zero_add]

theorem rnTW_SC (β : Ordinal.{0}) : SC (rnTW S β) := SC_psi (InR_Om_succ 1) _
theorem rnTW_lt_Om2 (β : Ordinal.{0}) : rnTW S β < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem rnOm1_lt_TW (β : Ordinal.{0}) : Om (1 : Ordinal.{0}) < rnTW S β := (psiS_bounds (S := S) _ 1).1

theorem rnEL_lt_Om2 (β : Ordinal.{0}) : ∀ j, rnEL S β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rnEL_SC (β : Ordinal.{0}) : ∀ j, SC (rnEL S β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

section Base

variable {β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (Om (1 + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))

include hβown

theorem rnEL_lt_succ : ∀ j, rnEL S β j < rnEL S β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rnEL_lt_succ j
    have hle : rnEL S β (j + 1) ≤ rnEL S β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono IH.le))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt IH)) ?_
    exact CSet.add_mem (hβown _ (leWe_mono (rnEL_lt_Om2 β (j + 1)).le))
      (leWe_mem (CSet.of_lt (IH.trans_le hle)))

theorem rnEL_mono {j j' : ℕ} (h : j ≤ j') : rnEL S β j ≤ rnEL S β j' :=
  (strictMono_nat_of_lt_succ (fun i => rnEL_lt_succ hβown i)).monotone h

omit hβown in
theorem rnEL_gt : ∀ j x, x < rnEL S β j → x < S.psi (β + leWe x) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rnEL S β j) with h' | h'
    · exact rnEL_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono h'))).1

omit hβown in
theorem rnEL_le_top : ∀ j, rnEL S β j ≤ rnTW S β
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 (leWe_mono (rnEL_lt_Om2 β j).le))).1

/-- **`T_W(β) = sup_j EL^β_j`.** -/
theorem rnEL_sup (hβd : leWe (Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : x < rnTW S β) :
    ∃ j, x < rnEL S β j := by
  have hbdd : BddAbove (Set.range (rnEL S β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rnEL S β j ↔ ∃ j, y < rnEL S β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rnEL S β j < ⨆ j, rnEL S β j :=
    fun j => (hlt _).2 ⟨j + 1, rnEL_lt_succ hβown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rnEL S β j := hKQ 0
  have hQSC : SC (⨆ j, rnEL S β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rnEL_mono hβown (le_max_left i j))
    have hj' := hj.trans_le (rnEL_mono hβown (le_max_right i j))
    exact ((rnEL_SC β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rnEL S β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hβ1 : S.psi β (Om (1 + 1)) < rnEL S β 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) ?_
    exact hβown _ (leWe_mono gg_Om1_lt_Om2.le)
  have hFQ : rnTW S β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (Om (1 + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * Om (1 + 1)) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (Om (1 + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hWG3).2] at hc2
    have hm : (β + x') % leWe (Om (1 + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * Om (1 + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hb := leCl_boundK hQSC ldOm2_SC _ hlog hla
    have hq : log ω x' / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt hW0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h1 : log ω x' + 1 ≤ Om (1 + 1) * rnEL S β j := by
      refine Order.add_one_le_of_lt ?_
      calc log ω x' < Om (1 + 1) * (log ω x' / Om (1 + 1)) + Om (1 + 1) :=
            Ordinal.lt_mul_div_add _ hW0
        _ = Om (1 + 1) * (log ω x' / Om (1 + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * rnEL S β j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (rnEL S β j) := by
      unfold leWe
      calc x' < ω ^ (log ω x' + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x'
        _ ≤ ω ^ (Om (1 + 1) * rnEL S β j) := opow_le_opow_right omega0_pos h1
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^x) ≥ T_W(β)` for `x ≥ T_W(β)`. -/
theorem rnTW_ge (hβd : leWe (Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : rnTW S β ≤ x) :
    rnTW S β ≤ S.psi (β + leWe x) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rnEL_sup hβown hβd h
  have h1 : rnEL S β (j + 1) ≤ S.psi (β + leWe x) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((rnEL_le_top j).trans hx)))).1
  exact absurd (hj.trans_le ((rnEL_lt_succ hβown j).le.trans h1)) (lt_irrefl _)

/-- **Every `x < T_W(β)` is an own exponent at `β`.** -/
theorem rnTW_gt (hβd : leWe (Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : x < rnTW S β) :
    x < S.psi (β + leWe x) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rnEL_sup hβown hβd hx
  exact rnEL_gt j x hj

end Base

/-! ## Bases -/

/-- **A base** at `λ`: `W^W ∣ β`, `β ∈ H_λ`, `β + W^W < A_{η_λ}`, and `β` is own for every `d ≤ W^W`. -/
def RnBase (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  leWe (Om (1 + 1)) ∣ β ∧ β ∈ cdHull S l ∧ β + leWe (Om (1 + 1)) < ConjT.Aη S (cdEta S l) ∧
    ∀ d, d ≤ leWe (Om (1 + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))

/-- **A base is a base of exponent `e` for every `e < T_W(β)`.** -/
theorem rnBaseE {l β e : Ordinal.{0}} (hb : RnBase S l β) (he : e < rnTW S β) : LeBaseE S l e β := by
  obtain ⟨hβd, hβH, hβA, hβown⟩ := hb
  have heW : e ≤ Om (1 + 1) := (he.trans (rnTW_lt_Om2 β)).le
  refine ⟨(leWe_dvd heW).trans hβd, hβH,
    lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono heW)) hβA,
    fun d hd => hβown d (hd.trans (leWe_mono heW)), fun e' _ h' => ?_⟩
  exact rnTW_gt hβown hβd (h'.trans_lt he)

theorem rnTW_atom {l β : Ordinal.{0}} (hb : RnBase S l β) : rnTW S β ∈ ldAtR S l := by
  obtain ⟨-, hβH, hβA, -⟩ := hb
  exact ⟨β + leWe (Om (1 + 1)), CSet.add_mem hβH (leWe_mem (mxOm2_mem _ _)), hβA, rfl⟩

theorem rnBase_atom {l β : Ordinal.{0}} (hb : RnBase S l β) : S.psi β (Om (1 + 1)) ∈ ldAtR S l := by
  obtain ⟨-, hβH, hβA, -⟩ := hb
  exact ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩

theorem rnBase_lt {l β : Ordinal.{0}} (hb : RnBase S l β) : S.psi β (Om (1 + 1)) < rnTW S β := by
  obtain ⟨-, -, -, hβown⟩ := hb
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)

theorem rnBase_own {l β : Ordinal.{0}} (hb : RnBase S l β) : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
  obtain ⟨-, -, -, hβown⟩ := hb
  have := hβown 0 zero_le; rwa [add_zero] at this

end Googology.Trans.PoR.InaccPsi.R2.Rn
