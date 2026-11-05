import Googology.Trans.PoR.InaccPsi.R2.ZmLm

/-!
# ZmRef: REFUTE FIRST AT THE OFFSET `B_Γ²·2 + 1` AND AT THE CODE `ε_{B_Γ+1}`

* `zmRef1`: the offset `B_Γ²·2 + 1` (index `B_Γ + 1 + B_Γ²·2 + 1`) reads `D(x)²·2 + 1` with gate `2`; the index is
  no fixed point of `Γ` (`zmRef1_nonfix`); Lemma EXACT holds there (field `ex` of `zmCh 1`).
* `zmRef2`: the code `ε_{B_Γ+1}` (the base of `zmCh 2`) reads `ε_{D(x)+1} = ϑˣ(Ω₁ + D(x))`; the index is no fixed
  point of `Γ` (`zmRef2_nonfix`).
Both readings agree with the generic step; no counterexample: NO EVIDENCE.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl

theorem zm_nat_lt_BG (n : ℕ) : (n : Ordinal.{0}) < tfBG :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE (Low.opow_eq_self_of_SC tfBG_SC))

theorem zmRef1_lt : tfBG ^ (2 : Ordinal.{0}) * 2 + 1 < eN tfBG := by
  have hE := eN_E tfBG
  have hB := lt_eN tfBG
  have h2 : (2 : Ordinal.{0}) < eN tfBG := by exact_mod_cast (zm_nat_lt_BG 2).trans hB
  have h1 : (1 : Ordinal.{0}) < eN tfBG := by exact_mod_cast (zm_nat_lt_BG 1).trans hB
  exact (inE_indec hE).add_lt (mul_lt_inE hE (zm_opow_lt hE hB h2) h2) h1

/-- **REFUTE FIRST at the offset `B_Γ²·2 + 1`**: the reading is `D(x)²·2 + 1`, the gate `2`. -/
theorem zmRef1 (x : Ordinal.{0}) :
    (zmCh 1).R (tfBG ^ (2 : Ordinal.{0}) * 2 + 1) x = ywV 1 0 x ^ (2 : Ordinal.{0}) * 2 + 1 ∧
      (zmCh 1).G (tfBG ^ (2 : Ordinal.{0}) * 2 + 1) = 2 := by
  have h2B : (2 : Ordinal.{0}) < tfBG := by exact_mod_cast zm_nat_lt_BG 2
  have h1B : (1 : Ordinal.{0}) < tfBG := by exact_mod_cast zm_nat_lt_BG 1
  have hr : (1 : Ordinal.{0}) < tfBG ^ (2 : Ordinal.{0}) :=
    h1B.trans_le (by have := opow_le_opow_right tfBG_SC.1 (one_le_two : (1 : Ordinal.{0}) ≤ 2); rwa [opow_one] at this)
  have hR2 : yrR (2 : Ordinal.{0}) x = 2 := by have := yrR_nat 2 x; exact_mod_cast this
  have hG2 : yrG (2 : Ordinal.{0}) = 2 := by
    have := yrG_low (Yh.yh_nat_lt_G 2); rw [glG_nat] at this; exact_mod_cast this
  have hG1 : yrG (1 : Ordinal.{0}) = 1 := by
    have := yrG_low (Yh.yh_nat_lt_G 1); rw [glG_nat] at this; exact_mod_cast this
  have eE : zmYr.E = tfBG := rfl
  have e1 := zmYr.sR_eq (k := 2) (d := 2) (r := 1) two_pos two_ne_zero h2B hr zmRef1_lt x
  have e2 := zmYr.sG_eq (k := 2) (d := 2) (r := 1) two_pos two_ne_zero h2B hr zmRef1_lt
  rw [eE] at e1 e2
  show zmYr.sR _ x = _ ∧ zmYr.sG _ = _
  refine ⟨?_, ?_⟩
  · rw [e1, zmYr.sR_lt h2B, zmYr.sR_lt h1B]
    show ywV 1 0 x ^ yrR 2 x * yrR 2 x + yrR 1 x = _
    rw [hR2, yrR_one]
  · rw [e2, zmYr.sG_lt h2B, zmYr.sG_lt h1B]
    show max (yrG 2) (max (yrG 2) (yrG 1)) = 2
    rw [hG2, hG1]; norm_num

/-- The index `B_Γ + 1 + (B_Γ²·2 + 1)` is no fixed point of `Γ`. -/
theorem zmRef1_nonfix :
    Om1 + 1 + (tfBG + 1 + (tfBG ^ (2 : Ordinal.{0}) * 2 + 1)) <
      gamma (Om1 + 1 + (tfBG + 1 + (tfBG ^ (2 : Ordinal.{0}) * 2 + 1))) := by
  have h : tfBG < (zmCh 1).E := by rw [zmCh_E]; exact zm_BG_lt_veb 0
  have ho : tfBG ^ (2 : Ordinal.{0}) * 2 + 1 < (zmCh 1).E := zmRef1_lt
  exact (zmCh 1).nonfix h ho

/-- **REFUTE FIRST at the code `ε_{B_Γ+1}`**: it reads `ε_{D(x)+1} = ϑˣ(Ω₁ + D(x))`. -/
theorem zmRef2 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (zmCh 2).R (eN tfBG) x = eN (ywV 1 0 x) ∧ (zmCh 2).R (eN tfBG) x = glA 1 (ywV 1 0 x) x ∧
      (zmCh 2).G (eN tfBG) ≤ 1 := by
  have h := (zmCh 1).sR_tw x 0
  have e : (zmCh 2).R (eN tfBG) x = eN (ywV 1 0 x) := h.1
  have hg : (zmCh 2).G (eN tfBG) ≤ max (zmCh 1).Eg 1 := h.2
  rw [zmCh_Eg, max_eq_right zero_le_one] at hg
  exact ⟨e, e.trans (zmD_eN hx hx1), hg⟩

/-- The index `B_Γ + 1 + ε_{B_Γ+1}` is no fixed point of `Γ`. -/
theorem zmRef2_nonfix : Om1 + 1 + (tfBG + 1 + eN tfBG) < gamma (Om1 + 1 + (tfBG + 1 + eN tfBG)) := by
  have h : tfBG < (zmCh 2).E := by rw [zmCh_E]; exact zm_BG_lt_veb 1
  have ho : eN tfBG < (zmCh 2).E := lt_eN (zmCh 1).E
  exact (zmCh 2).nonfix h ho

end Googology.Trans.PoR.InaccPsi.R2.Zm
