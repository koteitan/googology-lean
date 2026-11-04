import Googology.Trans.PoR.InaccPsi.R2.ZgBw

/-!
# ZgRef: REFUTE FIRST AT THE OFFSETS `1`, `ω` (READING `D(x) + yrR o x`) AND `B_Γ·2` (THE ATOM `B_Γ` IN THE OFFSET)

The readings of `Zg.zgB2` at the indices `B_Γ + 2` and `B_Γ + 1 + ω` are `D(x) + 1` and `D(x) + ω`, the readings of
`Zb.zbE0` (`zgRef1`, `zgRefW`); at the index `B_Γ·2` (offset `B_Γ`) the reading of `Zg.zgBw` is `D(x)·2`
(`zgRef2`), the index is not a fixed point of `Γ` (`zgRef2_nonfix`), and Lemma EXACT holds there (a field of the
reading system `Zg.zgBw`).  No contradiction: NO EVIDENCE for the negation.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Gc

theorem zgRef1 (x : Ordinal.{0}) : zgR2 (tfBG + 1 + 1) x = ywV 1 0 x + 1 ∧ zgR2 (tfBG + 1 + 1) x = zbR0 (tfBG + 1 + 1) x := by
  unfold zgR2 zbR0; rw [zbO_add, yrR_one]; exact ⟨rfl, rfl⟩

theorem zgRefW (x : Ordinal.{0}) : zgR2 (tfBG + 1 + ω) x = ywV 1 0 x + ω ∧ zgR2 (tfBG + 1 + ω) x = zbR0 (tfBG + 1 + ω) x := by
  have hωO : (ω : Ordinal.{0}) < Om1 := omega0_lt_inE Rj.rj_Om1_inE
  have hω : yrR ω x = ω := by
    rw [yrR_low ((hωO.trans Gf.Om1_lt_eW).trans Gl.gfE_lt_G0), Gl.glR_low (hωO.trans Gf.Om1_lt_eW),
      (Gf.rdc_const hωO x).1]
  unfold zgR2 zbR0; rw [zbO_add, hω]; exact ⟨rfl, rfl⟩

theorem zgRef2_idx : tfBG + 1 + (tfBG * ((1 : ℕ) : Ordinal.{0}) + 0) = tfBG + tfBG := by
  rw [Nat.cast_one, mul_one, add_zero, add_assoc,
    one_add_of_omega0_le (omega0_le_of_isSuccLimit zgBG_lim)]

theorem zgRef2 (x : Ordinal.{0}) : zgRw (tfBG + tfBG) x = ywV 1 0 x * 2 := by
  rw [← zgRef2_idx, zgRw_eq 1 tfBG_SC.1, yrR_zero, add_zero]; norm_num

theorem zgRef2_nonfix : Om1 + 1 + (tfBG + tfBG) < gamma (Om1 + 1 + (tfBG + tfBG)) := by
  have h := zg_nonfixW (o := tfBG) zgBG_lt_W
  rwa [add_assoc tfBG 1 tfBG, one_add_of_omega0_le (omega0_le_of_isSuccLimit zgBG_lim)] at h

end Googology.Trans.PoR.InaccPsi.R2.Zg
