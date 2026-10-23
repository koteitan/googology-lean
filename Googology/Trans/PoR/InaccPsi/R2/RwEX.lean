import Googology.Trans.PoR.InaccPsi.R2.RwW1

/-!
# The own code exponents one level up: `T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j`

`W^E = Ω₂^E` (`Le.leWe`), `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EX_0 = Ω₁`, `EX_{j+1} = ψ_{Ω₂}(β + W^{X₀ + W^{EX_j}})`
(`rwEX S X₀ β j`).  A code `E < EX_j` is an own exponent of the level `W^E` over the offset `X₀` at `β`:
`E < ψ_{Ω₂}(β + W^{X₀ + W^E})` (`rwEX_gt`, no hypothesis); below the top every code is below some `EX_j`
(`rwEX_sup`, for a base `β` with `W^{X₀ + W^{Ω₂}} ∣ β`, own for `d ≤ W^{X₀ + W^{Ω₂}}`).

* `rwEX_lt_Om2`, `rwEX_SC`, `rwEX_gt`, `rwEX_le_top`, `rwEX_mono_base`, `rwEX_mono_off`;
* `rwEX_lt_succ`, `rwEX_mono`, `rwEX_sup` (**`T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j`**, by `Le.lePsi2_le` and
  `Le.leCl_boundY`), `rwEX_ge`, `rwEX_gtT`.

No new axiom.  New definition: `rwEX`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- `EX_0 = Ω₁`, `EX_{j+1} = ψ_{Ω₂}(β + W^{X₀ + W^{EX_j}})`. -/
noncomputable def rwEX (S : InaccSeq.{0}) (X0 β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe (X0 + leWe (rwEX S X0 β j))) (Om (1 + 1))

section Seq

variable {X0 β : Ordinal.{0}}

theorem rwEX_lt_Om2 : ∀ j, rwEX S X0 β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rwEX_SC : ∀ j, SC (rwEX S X0 β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem rwEX_gt : ∀ j x, x < rwEX S X0 β j → x < S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rwEX S X0 β j) with h' | h'
    · exact rwEX_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono h'))))).1

theorem rwEX_le_top : ∀ j, rwEX S X0 β j ≤ leTe S (X0 + leWe (Om (1 + 1))) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (rwEX_lt_Om2 j).le))))).1

theorem rwEX_mono_base {β' : Ordinal.{0}} (hββ : β ≤ β') : ∀ j, rwEX S X0 β j ≤ rwEX S X0 β' j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (add_le_add hββ (leWe_mono ((add_le_add_iff_left X0).2
      (leWe_mono (rwEX_mono_base hββ j)))))).1

theorem rwEX_mono_off {X0' : Ordinal.{0}} (hXX : X0 ≤ X0') : ∀ j, rwEX S X0 β j ≤ rwEX S X0' β j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono (add_le_add hXX
      (leWe_mono (rwEX_mono_off hXX j)))))).1

variable (hβown : ∀ d, d ≤ leWe (X0 + leWe (Om (1 + 1))) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))

include hβown hX0m

theorem rwEX_lt_succ : ∀ j, rwEX S X0 β j < rwEX S X0 β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rwEX_lt_succ j
    have hle : rwEX S X0 β (j + 1) ≤ rwEX S X0 β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leWe_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leWe (rwEX S X0 β (j + 1))))
        (S.psi (β + leWe (X0 + leWe (rwEX S X0 β (j + 1)))) (Om (1 + 1))) :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (rwEX_lt_Om2 _).le))))
      (leWe_mem (CSet.add_mem hX0 (leWe_mem (CSet.of_lt (IH.trans_le hle)))))

theorem rwEX_mono {j j' : ℕ} (h : j ≤ j') : rwEX S X0 β j ≤ rwEX S X0 β j' :=
  (strictMono_nat_of_lt_succ (fun i => rwEX_lt_succ hβown hX0m i)).monotone h

/-- **`T_{X₀ + W^{Ω₂}}(β) = sup_j EX_j`.** -/
theorem rwEX_sup (hβd : leWe (X0 + leWe (Om (1 + 1))) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (Om (1 + 1))) β) : ∃ j, x < rwEX S X0 β j := by
  have hbdd : BddAbove (Set.range (rwEX S X0 β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rwEX S X0 β j ↔ ∃ j, y < rwEX S X0 β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rwEX S X0 β j < ⨆ j, rwEX S X0 β j :=
    fun j => (hlt _).2 ⟨j + 1, rwEX_lt_succ hβown hX0m j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rwEX S X0 β j := hKQ 0
  have hQSC : SC (⨆ j, rwEX S X0 β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rwEX_mono hβown hX0m (le_max_left i j))
    have hj' := hj.trans_le (rwEX_mono hβown hX0m (le_max_right i j))
    exact ((rwEX_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rwEX S X0 β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rwEX S X0 β 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (leWe_pos _)))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono gg_Om1_lt_Om2.le))))
      (leWe_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rwEX S X0 β 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hFQ : leTe S (X0 + leWe (Om (1 + 1))) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe (Om (1 + 1))) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + leWe (Om (1 + 1)))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + leWe (Om (1 + 1)))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe (Om (1 + 1))) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    -- `Ω₂·(X₀ + W^{Ω₂}) = Ω₂·X₀ + W^{Ω₂}`
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
    have hXC : LeCl (Om (1 + 1)) Q (Om (1 + 1) * X0) :=
      LeCl.mulK hQSC ldOm2_SC X0 (hX0cl Q hQSC (hX1.trans (hKQ 1)).le)
    have hu := (leClDec hQSC ldOm2_SC (log ω x') hlog).1 _ hXC h1
    set u := log ω x' - Om (1 + 1) * X0 with hu_def
    have hdec : Om (1 + 1) * X0 + u = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : u < leWe (Om (1 + 1)) := by
      have : Om (1 + 1) * X0 + u < Om (1 + 1) * X0 + leWe (Om (1 + 1)) := by rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    -- the leading exponent of `u` is below `Ω₂·Q`
    have hju : ∃ j, u < leWe (rwEX S X0 β j) := by
      rcases eq_or_ne u 0 with h0 | hu0
      · exact ⟨0, h0 ▸ leWe_pos _⟩
      obtain ⟨-, hlu⟩ := leClDec hQSC ldOm2_SC u hu
      have hlu2 : log ω u < ω ^ (Om (1 + 1) * 1 + Om (1 + 1)) := by
        have e : ω ^ (Om (1 + 1 : Ordinal.{0}) * 1 + Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
          rw [mul_one, opow_add, gg_SC_eps ldOm2_SC]
        rw [e]
        exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hu0).trans_lt hu2)
      have hb := leCl_boundY hQSC ldOm2_SC (LeCl.small ((one_lt_omega0.trans
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
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + leWe (rwEX S X0 β j)) := by
      rw [mul_add, hWj, ← hdec, add_assoc]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hj)
    have hxW : x' < leWe (X0 + leWe (rwEX S X0 β j)) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X₀ + W^x}) ≥ T_{X₀ + W^{Ω₂}}(β)` for `x ≥ T_{X₀ + W^{Ω₂}}(β)`. -/
theorem rwEX_ge (hβd : leWe (X0 + leWe (Om (1 + 1))) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : leTe S (X0 + leWe (Om (1 + 1))) β ≤ x) :
    leTe S (X0 + leWe (Om (1 + 1))) β ≤ S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rwEX_sup hβown hX0m hβd hX0cl hX0G3 h
  have h1 : rwEX S X0 β (j + 1) ≤ S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono ((rwEX_le_top j).trans hx)))))).1
  exact absurd (hj.trans_le ((rwEX_lt_succ hβown hX0m j).le.trans h1)) (lt_irrefl _)

/-- **Every code `x < T_{X₀ + W^{Ω₂}}(β)` is an own exponent of the level `W^x` over `X₀` at `β`.** -/
theorem rwEX_gtT (hβd : leWe (X0 + leWe (Om (1 + 1))) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (Om (1 + 1))) β) :
    x < S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rwEX_sup hβown hX0m hβd hX0cl hX0G3 hx
  exact rwEX_gt j x hj

end Seq

end Googology.Trans.PoR.InaccPsi.R2.Rw
