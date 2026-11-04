import Googology.Trans.PoR.InaccPsi.R2.YzPlus
import Googology.Trans.PoR.InaccPsi.R2.RcLow
import Googology.Trans.PoR.InaccPsi.R2.FpB0
import Googology.Trans.PoR.InaccPsi.R2.RlNoGo

/-!
# The gap restarts with short codes: `Ye.YeGapRng` reduced to the codes above `θ·ω`

Notation as in `R2.YeGap`, `R2.RcLow`: `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `r(λ) = k_λ(Θ_λ(m_λ))`, `θ = ConjT.th S`,
`P' = Nc.ncPp S`, `L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n`.

* `yz_A_lt_Lam` (`A_{Ω_ω + P'·(ω+1)} < Λ`), `yzOwnA_W1` (**`A_{η_λ}` is own at every restart `ρ_λ < L(ω+1)`**: the
  extension of `Rc.rcOwn` / `Ld.ldOwnA` above `L(ω)`);
* `yzR_lowCode` (**`m_λ ≤ θ·ω` gives `r(λ) < υ_{λ+ω+2}` at every restart `ρ_λ < L(ω+1)`** with `υ_{λ+ω+1} < ν_C`;
  `Rc.rcR_lowCode` asked `ρ_λ < L(ω)`);
* `yzGapRng_low` (**under `L(ω+1) ≤ ν_C` and ENUM-REACH, a gap restart `υ_{l₀}` with `m_{l₀} ≤ θ·ω` at a restart
  `p = υ_κ` has its reach below `B_n p`**: `B_n p = υ_{κ'}`, `κ'` a restart index (`Sf.sfShiftAll`), `l₀ < κ'` gives
  `υ_{l₀+ω+2} < υ_{κ'}`);
* `YzGapRngHi` (the leaf left: `Ye.YeGapRng` only at gap restarts with `m_{l₀} > θ·ω`), `yzGapRng_of_hi`
  (**`YzGapRngHi ⇒ Ye.YeGapRng`** under hν and ENUM-REACH), `yzGapRngHi_of` (the converse, trivial; NON-VACUITY with
  `Ye.yeGap_of_target`).

No new axiom.  New definition: the statement name `YzGapRngHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## The own argument above `L(ω)` -/

/-- `A_{Ω_ω + P'·(ω+1)} < Λ`. -/
theorem yz_A_lt_Lam : ConjT.Aη S (Om ω + Nc.ncPp S * (ω + 1)) < S.Lam := by
  set W := Om (ω + 1 : Ordinal.{0}) with hW
  have hW0 : (ω + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_nonneg_of_pos zero_le one_pos).ne'
  have hWe : W = ω_ (ω + 1) := Om_of_ne_zero hW0
  have hA : ∀ {a b : Ordinal.{0}}, a < W → b < W → a + b < W := fun ha hb => by
    rw [hWe] at ha hb ⊢; exact Ordinal.isPrincipal_add_omega _ ha hb
  have hM : ∀ {a b : Ordinal.{0}}, a < W → b < W → a * b < W := fun ha hb => by
    rw [hWe] at ha hb ⊢; exact Ordinal.isPrincipal_mul_omega _ ha hb
  have h2W : Om (1 + 1 : Ordinal.{0}) ≤ W := Om_le_Om.2 (by
    rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le.trans le_self_add)
  have hωW : Om ω < W := Om_lt_Om.2 (lt_add_one ω)
  have hθ : ConjT.th S < W := Vd.vd_th_lt_W.trans_le h2W
  have hP : Nc.ncPp S < W := (Cd.cdPp_lt_Om2 S).trans_le h2W
  have h11 : (ω + 1 : Ordinal.{0}) < W := by
    have h1 : (ω + 1 : Ordinal.{0}) < Om 1 := by
      rw [← Rj.rj_Om1]; exact Rj.rj_Om1_inE.add_lt (omega0_lt_inE Rj.rj_Om1_inE)
        ((one_lt_omega0).trans (omega0_lt_inE Rj.rj_Om1_inE))
    exact h1.trans_le (Om_le_Om.2 (Ordinal.one_le_iff_ne_zero.2 hW0))
  have hAW : ConjT.Aη S (Om ω + Nc.ncPp S * (ω + 1)) < W := by
    unfold ConjT.Aη
    exact hA hωW (hM hθ (hA hωW (hM hP h11)))
  have hωL : (ω : Ordinal.{0}) < S.Lam := by
    have := Om_lt_Lam (S := S) one_lt_Lam
    exact (omega0_lt_inE (by rw [← Rj.rj_Om1]; exact Rj.rj_Om1_inE)).trans this
  exact hAW.trans (Om_lt_Lam (add_one_lt_Lam hωL))

/-- **`A_{η_λ}` is own at every restart `ρ_λ < L(ω+1)`.** -/
theorem yzOwnA_W1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hω1 : upsilon l < Nc.ncL S (ω + 1)) :
    upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) ∧
      ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq S]; exact hω1
  obtain ⟨hg, -, hlt, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  exact ⟨hX, Sf.sfOwn hg ((ConjT.A_mono S hlt.le).trans_lt yz_A_lt_Lam)⟩

/-- **`m_λ ≤ θ·ω` gives `r(λ) < υ_{λ+ω+2}`** at every restart `ρ_λ < L(ω+1)` with `υ_{λ+ω+1} < ν_C`. -/
theorem yzR_lowCode {l : Ordinal.{0}} (hl : IsRestartIdx l) (hω1 : upsilon l < Nc.ncL S (ω + 1))
    (hC : upsilon (l + ω + 1) < nuC) (hm : cdCode S l ≤ ConjT.th S * ω) :
    cdR S l < upsilon (l + (ω + 2)) := by
  obtain ⟨hX, hown⟩ := yzOwnA_W1 hl hω1
  have hθ : cdTheta S l (cdCode S l) < cdDelta l := Ld.ldTheta_lt_delta hl hX hown hm
  rw [Ra.raR_low hl hC hθ]
  have hE : InE (upsilon (l + (ω + 2))) := upsPt_inE (upsPt_upsilon
    (omega0_pos.trans_le (le_self_add.trans le_add_self)))
  have hδ : cdDelta l < upsilon (l + (ω + 2)) := by
    unfold cdDelta
    refine upsilon_normal.strictMono ?_
    rw [add_assoc]
    exact (add_lt_add_iff_left l).2 ((add_lt_add_iff_left ω).2 one_lt_two)
  exact hE.add_lt hδ (hθ.trans hδ)

/-! ## Gap restarts with short codes -/

/-- Two restart indices `l < κ` give `l + (ω + 2) < κ`. -/
theorem yz_ri_add_lt {l κ : Ordinal.{0}} (hl : IsRestartIdx l) (hκ : IsRestartIdx κ) (h : l < κ) :
    l + (ω + 2) < κ := by
  obtain ⟨a, ha⟩ := (ri_iff.1 hl).2
  obtain ⟨b, hb⟩ := (ri_iff.1 hκ).2
  have hab : a < b := by
    rw [ha, hb] at h; exact (mul_lt_mul_iff_right₀ (mul_pos omega0_pos omega0_pos)).1 h
  have h1 : l + ω * ω ≤ κ := by
    rw [ha, hb, ← mul_add_one]; exact mul_le_mul_left' (Order.add_one_le_of_lt hab) _
  have h2 : ω + 2 < ω * ω := by
    have h3 : ω + 2 < ω + ω := (add_lt_add_iff_left ω).2 (natCast_lt_omega0 2)
    have h4 : (ω : Ordinal.{0}) + ω < ω * ω := by
      rw [← Xw.xw_mul2]; exact (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 2)
    exact h3.trans h4
  exact ((add_lt_add_iff_left l).2 h2).trans_le h1

/-- **Under `L(ω+1) ≤ ν_C` and ENUM-REACH: a gap restart `υ_{l₀}` with `m_{l₀} ≤ θ·ω` at a restart `p = υ_κ` has its
reach below `B_n p`.** -/
theorem yzGapRng_low (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {l l' p l₀ κ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p (upsilon l₀)) (hl₀ : IsRestartIdx l₀)
    (hκ : IsRestartIdx κ) (hpκ : p = upsilon κ) (hm : cdCode S l₀ ≤ ConjT.th S * ω) :
    ∃ r, IsReach R2C (upsilon l₀) r ∧ r < Bc.bcB S n p := by
  obtain ⟨-, hXL, -⟩ := Ye.yeGapPt_facts hν hP
  obtain ⟨hW, hfar, hp, -, -, -, ha, hgap⟩ := hP
  obtain ⟨hpC, -, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have hcp : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  obtain ⟨κ', hκ', hBκ⟩ := Tp.tpRstMove_of_shift Sf.sfShiftAll n κ hκ (hpκ ▸ hcp.le) (hpκ ▸ hpC)
  rw [← hpκ] at hBκ
  have hl₀κ : l₀ < κ' := Tp.tpUps_lt_iff.1 (hBκ ▸ ha)
  have hlt := yz_ri_add_lt hl₀ hκ' hl₀κ
  have hup : upsilon (l₀ + (ω + 2)) < Bc.bcB S n p := hBκ ▸ upsilon_normal.strictMono hlt
  have hC : upsilon (l₀ + ω + 1) < nuC := by
    have h1 : l₀ + ω + 1 < l₀ + (ω + 2) := by
      rw [add_assoc]; exact (add_lt_add_iff_left l₀).2 ((add_lt_add_iff_left ω).2 one_lt_two)
    exact ((upsilon_normal.strictMono h1).trans hup).trans (hXL.trans_le hν)
  have hω1 : upsilon l₀ < Nc.ncL S (ω + 1) := ha.trans hXL
  -- `l₀` is a range restart
  have hB0 : cdB0 ≤ l₀ := by
    have hL0 : Nc.ncL S 0 < Bc.bcC S n :=
      Rl.rlM_lt_L1.trans_le ((le_of_eq (by unfold Bc.bcC; simp)).trans (Bc.bcC_mono S (Nat.zero_le n)))
    have hB : Bc.bcB S n (Bc.bcC S n) ≤ upsilon l₀ := hgap _ hcp
    rw [show Bc.bcC S n = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) from rfl, Bc.bcB_base] at hB
    have h0 : upsilon cdB0 < upsilon l₀ :=
      Fp.fpB0_lt_M.trans (hL0.trans ((Bc.bcC_lt S n).trans_le hB))
    exact (Tp.tpUps_lt_iff.1 h0).le
  have hPp : cdCode S l₀ < Nc.ncPp S := by
    have hPE : InE (Nc.ncPp S) := Gg.gg_SC_eps (Nc.ncPp_SC S)
    exact hm.trans_lt (hPE.mul_lt (Nc.ncTh_lt_Pp S) (omega0_lt_inE hPE))
  have hR : CdRange S l₀ := ⟨hl₀, hB0, hω1, hPp⟩
  exact ⟨_, cdEnum_exact hU hL hR, (yzR_lowCode hl₀ hω1 hC hm).trans hup⟩

/-! ## The leaf left -/

/-- **Leaf (gap restarts with long codes)**: `Ye.YeGapRng` only at the gap restarts `υ_{l₀}` with `m_{l₀} > θ·ω`. -/
def YzGapRngHi (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p l₀ κ : Ordinal.{0}), Ye.YeGapPt S n l l' p (upsilon l₀) → IsRestartIdx l₀ →
    IsRestartIdx κ → p = upsilon κ → ConjT.th S * ω < cdCode S l₀ →
    ∃ r, IsReach R2C (upsilon l₀) r ∧ r < Bc.bcB S n p

/-- **`YzGapRngHi ⇒ Ye.YeGapRng`** (under `L(ω+1) ≤ ν_C` and ENUM-REACH). -/
theorem yzGapRng_of_hi (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (h : YzGapRngHi S) : Ye.YeGapRng S := by
  intro n l l' p l₀ κ hP hl₀ hκ hpκ
  rcases le_or_gt (cdCode S l₀) (ConjT.th S * ω) with hm | hm
  · exact yzGapRng_low hν hU hL hP hl₀ hκ hpκ hm
  · exact h n l l' p l₀ κ hP hl₀ hκ hpκ hm

/-- `Ye.YeGapRng ⇒ YzGapRngHi` (the leaf is a special case; with `Ye.yeGap_of_target` it follows from the target). -/
theorem yzGapRngHi_of (h : Ye.YeGapRng S) : YzGapRngHi S :=
  fun n l l' p l₀ κ hP hl₀ hκ hpκ _ => h n l l' p l₀ κ hP hl₀ hκ hpκ

/-- **NON-VACUITY**: the target gives `YzGapRngHi`. -/
theorem yzGapRngHi_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : YzGapRngHi S :=
  yzGapRngHi_of (Ye.yeGap_of_target hν hU hL hEQ hK).2.1

end Googology.Trans.PoR.InaccPsi.R2.Yz
