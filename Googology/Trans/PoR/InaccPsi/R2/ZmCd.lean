import Googology.Trans.PoR.InaccPsi.R2.ZmCu

/-!
# ZmCd: `ZbDirect S ζ_{B_Γ+1}` FROM THE CHAIN OVER CODE INDICES

`ζ_{B_Γ+1} = φ(2, B_Γ+1)` is the least fixed point of `φ(1, ·)` above `B_Γ + 1` (`zm_Z_nfp`); the tower
`B_Γ, φ(1, B_Γ + B_Γ), …` (`zmIt`) of code indices with gate `≤ 1` is cofinal in it, and the step of the digit
system at each tower index has a base gate below `K`.

* `zm_Z_nfp`, `zmIt`, `zmIt_lt`, `zmIt_cof`, `zmHG_base`, `zmIt_gate`;
* `zmDirectZ` (**`ZbDirect S ζ_{B_Γ+1}`, UNCONDITIONAL**), `zmUVZ` (**UPPER ∧ LOWER ∧ CapV at every range restart
  below `ι(Γ(B)·ω)`, every `B < ζ_{B_Γ+1}`, UNCONDITIONAL**).

No new axiom.  New definition: `zmIt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **`ζ_{B_Γ+1}` is the least fixed point of `φ(1, ·)` above `B_Γ + 1`.** -/
theorem zm_Z_nfp : zmZ = nfp (veblen 1) (tfBG + 1) := by
  have h2 : veblen 2 = deriv (veblen 1) := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, veblen_add_one]
  unfold zmZ
  rw [h2, deriv_add_one, ← h2, zm_BG_fix2]

/-- **The tower of code indices** `B_Γ, φ(1, B_Γ + B_Γ), φ(1, B_Γ + φ(1, B_Γ + B_Γ)), …`. -/
noncomputable def zmIt : ℕ → Ordinal.{0}
  | 0 => tfBG
  | m + 1 => veblen 1 (tfBG + zmIt m)

theorem zmIt_lt : ∀ m, zmIt m < zmZ
  | 0 => zm_BG_lt_Z
  | m + 1 => zm_veb_lt_Z (zmIt_lt m)

theorem zmIt_iter : ∀ m : ℕ, (veblen 1)^[m] (tfBG + 1) ≤ tfBG + zmIt m
  | 0 => by
    show tfBG + 1 ≤ tfBG + tfBG
    exact add_le_add_right (gg_one_lt_of_SC tfBG_SC).le _
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    exact ((isNormal_veblen 1).strictMono.monotone (zmIt_iter m)).trans le_add_self

/-- **The tower is cofinal in `ζ_{B_Γ+1}`.** -/
theorem zmIt_cof {B : Ordinal.{0}} (hB : B < zmZ) : ∃ m, B < zmIt m := by
  rw [zm_Z_nfp] at hB
  obtain ⟨m, hm⟩ := lt_nfp_iff.1 hB
  exact ⟨m + 1, hm.trans_le ((zmIt_iter m).trans (right_le_veblen _ _))⟩

/-- **The gate of a base `φ(1, B_Γ + n)` is `max (G n) (G 1)`.** -/
theorem zmHG_base {n : Ordinal.{0}} (hn : n < zmZ) :
    zmHG (veblen 1 (tfBG + n)) = max (zmHG n) (zmHG 1) := by
  set E := veblen 1 (tfBG + n) with hEdef
  have hEE : InE E := zm_veb_E _
  have hB : tfBG ≤ E := le_self_add.trans (right_le_veblen _ _)
  have hZ : E < zmZ := zm_veb_lt_Z hn
  have h2 : E < veblen 1 (tfBG + (n + 1)) :=
    (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one n))
  have hN : zmN E = n := zmN_eq le_rfl h2
  have hBE : zmBE E = E := zmBE_eq le_rfl h2
  have h1E : (1 : Ordinal.{0}) < E := lu_one_lt_E hEE
  have hr : (0 : Ordinal.{0}) < E ^ (1 : Ordinal.{0}) := by rw [opow_one]; exact hEE.pos
  obtain ⟨u1, u2, u3⟩ := zm_dec_uniq hEE one_ne_zero h1E hr
  rw [opow_one, mul_one, add_zero] at u1 u2 u3
  rw [zmHG_cnf hB hZ, hN, hBE, u1, opow_one, Ordinal.div_self hEE.pos.ne', Ordinal.mod_self, zmHG_zero,
    max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ zmHG 1), max_self]

theorem zmHG_one : zmHG 1 ≤ 1 := by
  rw [zmHG_lt (gg_one_lt_of_SC tfBG_SC)]
  have h1 : yrG ((1 : ℕ) : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) := by
    rw [yrG_low (Yh.yh_nat_lt_G 1), glG_nat]
  simpa using h1.le

theorem zmIt_gate : ∀ m, zmHG (zmIt m) ≤ 1
  | 0 => by
    show zmHG tfBG ≤ 1
    have h := zmHG_base (n := 0) (lt_of_le_of_lt zero_le zm_BG_lt_Z)
    rw [add_zero, zm_BG_fix, zmHG_zero, max_eq_right zero_le] at h
    rw [h]; exact zmHG_one
  | m + 1 => by
    show zmHG (veblen 1 (tfBG + zmIt m)) ≤ 1
    rw [zmHG_base (zmIt_lt m)]
    exact max_le (zmIt_gate m) zmHG_one

/-- **`ZbDirect S ζ_{B_Γ+1}`, UNCONDITIONAL.** -/
theorem zmDirectZ (S : InaccSeq.{0}) : ZbDirect S zmZ := by
  intro B hB1 hB2
  obtain ⟨m, hm⟩ := zmIt_cof hB2
  obtain ⟨M, hE, hEg, -, -, -, -⟩ := zmGood2_all (zmIt m) (zmIt_lt m)
  have hBM : B < M.step.E := by
    show B < eN M.E
    rw [hE]
    have h1 : zmIt m ≤ veblen 1 (tfBG + zmIt m) := (le_add_self : zmIt m ≤ tfBG + zmIt m).trans (right_le_veblen _ _)
    exact (hm.trans_le h1).trans (lt_eN _)
  have hGM : tfBG < M.step.E := by
    show tfBG < eN M.E
    rw [hE]
    have h1 : tfBG ≤ veblen 1 (tfBG + zmIt m) := (le_self_add : tfBG ≤ tfBG + zmIt m).trans (right_le_veblen _ _)
    exact h1.trans_lt (lt_eN _)
  have hK : M.step.Eg < Td.tdK S := by
    show M.Eg < _
    rw [hEg]; exact (zmIt_gate m).trans_lt (gg_one_lt_of_SC Td.tdK_SC)
  exact M.step.direct S hGM hK M.step_gc0 B hB1 hBM

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < ζ_{B_Γ+1}`
(UNCONDITIONAL).** -/
theorem zmUVZ (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < zmZ) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zmDirectZ S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zm
