import Googology.Trans.PoR.InaccPsi.R2.UuSys

/-!
# The own code exponents past `Γ₂`: `T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j` for offsets with level-2 codes

`W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EX_0 = Ω₁`, `EX_{j+1} = T_{X₀ + W^{EX_j}}(β)` (`Rw.rwEX`),
`Y₃ = ψ_{Ω₃}(Ω₃)`, `C₂(Q) = Ug.UgC S 2 Q` (level-2 codes with `ψ_{Ω₃}`-atoms).

`Rw.rwEX_sup` with the offset past `Γ₂`: the membership of `X₀` is relative (`X₀ ∈ Cl(X₀, T_{X₀}(β))`), the
offset codes are `C₂` codes and the bound is `X₀ + W^{Ω₂} < Y₃` (the proof of `Uj.ujEE_sup` with
`Uj.ujPsi2_le`, `Ug.ugC_mod`, `Ug.ugCDec`, `Uj.ujC_boundY`).

* `uxEX_lt_succ`, `uxEX_mono`, `uxEX_sup` (**`T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j` past `Γ₂`**), `uxEX_own` (**a
  code `x < Ω₂` with `x < T_{X₀ + W^x}(β)` lies below some `EX_j`**: the own predicate of the code levels);
* `uxLogW` (`x ∈ C₂(Q) ⇒ log_ω x / Ω₂ ∈ C₂(Q)`), `uxExtrRem` (**the digit part of a normal-form argument is a
  `C₂` code**: `Sn.snExtrRem` below `Y₃`), `uxCode_lt` (a `C₂` code below `Ω₂` is below `Q`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ux

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Um Googology.Trans.PoR.InaccPsi.R2.Uq

variable {S : InaccSeq.{0}}

theorem uxTwo_ne : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero

/-- **`log_ω x / Ω₂` is a level-2 code** for every level-2 code `x`. -/
theorem uxLogW {Q x : Ordinal.{0}} (hQ : SC Q) (h : UgC S (1 + 1) Q x) :
    UgC S (1 + 1) Q (log ω x / Om (1 + 1)) :=
  ugC_div hQ uxTwo_ne _ (ugCDec hQ uxTwo_ne x h).2

/-- A level-2 code below `Ω₂` is below `Q`. -/
theorem uxCode_lt {Q x : Ordinal.{0}} (hQ : SC Q) (h : UgC S (1 + 1) Q x) (hx : x < Om (1 + 1)) : x < Q :=
  ugC_lt_om hQ h hx

/-- **The digit part of a normal-form argument is a level-2 code** past `Γ₂`: `β + d'` in normal form,
`W^K ∣ β`, `d' < W^K`, `K < Y₃` give `d' ∈ C₂(Q)` for every strongly critical `Q ≥ ψ_{Ω₂}(β + d')`. -/
theorem uxExtrRem {β d' K Q : Ordinal.{0}}
    (hnf : β + d' ∈ S.CSet (β + d') (S.psi (β + d') (Om (1 + 1))))
    (hKd : leWe K ∣ β) (hd' : d' < leWe K) (hKY : K < ugY S)
    (hQ : SC Q) (htQ : S.psi (β + d') (Om (1 + 1)) ≤ Q) : UgC S (1 + 1) Q d' := by
  have hY : SC (ugY S) := uqY_SC
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := uqW_lt_Y
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) _ 1).1.trans_le htQ
  have h0 := umKeyC (S := S) (s := 1) hQ hΩQ (fun a b => CSet.one_mem a b) leOm3_lt_I (snColl htQ) _
    (CSet_mono le_rfl htQ hnf)
  rw [ujY_one] at h0
  have hc2 := ugC_mod hQ uxTwo_ne (Om (1 + 1) * K) h0
  change UgC S (1 + 1) Q ((β + d') % ugY S % leWe K) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hY hWY hKY).2] at hc2
  have hm : (β + d') % leWe K = d' := by
    obtain ⟨q, hq⟩ := hKd
    rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
  rwa [hm] at hc2

section Seq

variable {X0 β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (X0 + leWe (Om (1 + 1))) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet X0 (S.psi (β + leWe X0) (Om (1 + 1))))

include hβown hX0m

theorem uxEX_lt_succ : ∀ j, rwEX S X0 β j < rwEX S X0 β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := uxEX_lt_succ j
    have hle : rwEX S X0 β (j + 1) ≤ rwEX S X0 β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leWe_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leWe (rwEX S X0 β (j + 1))))
        (S.psi (β + leWe (X0 + leWe (rwEX S X0 β (j + 1)))) (Om (1 + 1))) :=
      CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (rwEX_lt_Om2 _).le))))
      (leWe_mem (CSet.add_mem hX0 (leWe_mem (CSet.of_lt (IH.trans_le hle)))))

theorem uxEX_mono {j j' : ℕ} (h : j ≤ j') : rwEX S X0 β j ≤ rwEX S X0 β j' :=
  (strictMono_nat_of_lt_succ (fun i => uxEX_lt_succ hβown hX0m i)).monotone h

/-- **`T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j` past `Γ₂`** (offset codes `C₂`, bound `Y₃`). -/
theorem uxEX_sup (hβd : leWe (X0 + leWe (Om (1 + 1))) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
    (hX0G3 : X0 + leWe (Om (1 + 1)) < ugY S)
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (Om (1 + 1))) β) : ∃ j, x < rwEX S X0 β j := by
  have hbdd : BddAbove (Set.range (rwEX S X0 β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rwEX S X0 β j ↔ ∃ j, y < rwEX S X0 β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rwEX S X0 β j < ⨆ j, rwEX S X0 β j :=
    fun j => (hlt _).2 ⟨j + 1, uxEX_lt_succ hβown hX0m j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rwEX S X0 β j := hKQ 0
  have hQSC : SC (⨆ j, rwEX S X0 β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (uxEX_mono hβown hX0m (le_max_left i j))
    have hj' := hj.trans_le (uxEX_mono hβown hX0m (le_max_right i j))
    exact ((rwEX_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rwEX S X0 β j with hQ
  have hG3 : SC (ugY S) := uqY_SC
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < ugY S := uqW_lt_Y
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := uxTwo_ne
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rwEX S X0 β 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (leWe_pos _)))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono gg_Om1_lt_Om2.le))))
      (leWe_mem (CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rwEX S X0 β 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hFQ : leTe S (X0 + leWe (Om (1 + 1))) β ≤ Q := by
    refine ujPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe (Om (1 + 1))) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := ugC_mod hQSC h2 (Om (1 + 1) * (X0 + leWe (Om (1 + 1)))) hc
    change UgC S (1 + 1) Q ((β + x') % ugY S % leWe (X0 + leWe (Om (1 + 1)))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe (Om (1 + 1))) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := ugCDec hQSC h2 x' hc2
    have eWW : Om (1 + 1 : Ordinal.{0}) * leWe (Om (1 + 1)) = leWe (Om (1 + 1)) := by
      rw [rvWe_mul, Ordinal.one_add_of_omega0_le (Lw.lw_omega_lt_SC ldOm2_SC).le]
    have hla : log ω x' < Om (1 + 1) * X0 + leWe (Om (1 + 1)) := by
      rw [← eWW, ← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans_lt hX1).trans
        (hKQ 1)
    have hXC : UgC S (1 + 1) Q (Om (1 + 1) * X0) :=
      ugC_mulK hQSC h2 X0 (hX0cl Q hQSC (hX1.trans (hKQ 1)).le)
    have hu := (ugCDec hQSC h2 (log ω x') hlog).1 _ hXC h1
    set u := log ω x' - Om (1 + 1) * X0 with hu_def
    have hdec : Om (1 + 1) * X0 + u = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : u < leWe (Om (1 + 1)) := by
      have : Om (1 + 1) * X0 + u < Om (1 + 1) * X0 + leWe (Om (1 + 1)) := by rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have hju : ∃ j, u < leWe (rwEX S X0 β j) := by
      rcases eq_or_ne u 0 with h0 | hu0
      · exact ⟨0, h0 ▸ leWe_pos _⟩
      obtain ⟨-, hlu⟩ := ugCDec hQSC h2 u hu
      have hlu2 : log ω u < ω ^ (Om (1 + 1) * 1 + Om (1 + 1)) := by
        have e : ω ^ (Om (1 + 1 : Ordinal.{0}) * 1 + Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
          rw [mul_one, opow_add, gg_SC_eps ldOm2_SC]
        rw [e]
        exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hu0).trans_lt hu2)
      have hb := ujC_boundY hQSC h2 (UgC.small ((one_lt_omega0.trans
        (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans hΩQ)) _ hlu hlu2
      rw [mul_one, gg_SC_eps ldOm2_SC] at hb
      have hq : log ω u / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt hW0).1 hb
      obtain ⟨j, hj⟩ := (hlt _).1 hq
      have hult := lt_opow_succ_log_self one_lt_omega0 u
      rw [Order.succ_eq_add_one] at hult
      refine ⟨j, hult.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_))⟩
      calc log ω u < Om (1 + 1) * (log ω u / Om (1 + 1)) + Om (1 + 1) := Ordinal.lt_mul_div_add _ hW0
        _ = Om (1 + 1) * (log ω u / Om (1 + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * rwEX S X0 β j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    obtain ⟨j, hj⟩ := hju
    have hWj : Om (1 + 1 : Ordinal.{0}) * leWe (rwEX S X0 β j) = leWe (rwEX S X0 β j) := by
      rw [rvWe_mul, Ordinal.one_add_of_omega0_le (Lw.lw_omega_lt_SC (rwEX_SC j)).le]
    have h2' : log ω x' + 1 ≤ Om (1 + 1) * (X0 + leWe (rwEX S X0 β j)) := by
      rw [mul_add, hWj, ← hdec, add_assoc]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hj)
    have hxW : x' < leWe (X0 + leWe (rwEX S X0 β j)) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2')
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- **A code exponent `x < Ω₂` own over `X₀` at `β` lies below some `EX_j`** (past `Γ₂`). -/
theorem uxEX_own (hβd : leWe (X0 + leWe (Om (1 + 1))) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
    (hX0G3 : X0 + leWe (Om (1 + 1)) < ugY S)
    {x : Ordinal.{0}} (hxW : x < Om (1 + 1)) (hx : x < S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1))) :
    ∃ j, x < rwEX S X0 β j := by
  refine uxEX_sup hβown hX0m hβd hX0cl hX0G3 (hx.trans_le ?_)
  exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
    (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hxW.le))))).1

end Seq

end Googology.Trans.PoR.InaccPsi.R2.Ux
