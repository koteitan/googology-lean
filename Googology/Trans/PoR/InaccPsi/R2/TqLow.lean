import Googology.Trans.PoR.InaccPsi.R2.LgPBc
import Googology.Trans.PoR.InaccPsi.R2.TpUps
import Googology.Trans.PoR.InaccPsi.R2.CxLow
import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# (TC) and (EMB₂) below the frontier `Λ⁺(lgPB)`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n` (the base change on `[0, L(n+2))`, the identity
on `[0, L(n+1))`), `U = υ_{Λ⁺(lgPB)} = P(ω^{ω^{Γ_{Ω₁+1}+Ω₁·Ω₁}}·ω)` (`lgPB_loc`), and `U < L(0) = m*`
(`lgPB_fr_order`).

* `tqUps_lt_nuC`: for every block specification `OffSpecGen O B` (every system below its first limit of frontiers),
  `υ_B < ν_C` (the first non-standard `<₂`-pair lies above `υ_B`, `left_ge_of_spec`);
* `tqReach_below` (**every point below `υ_B` has an `R₂^C`-reach below `υ_B`**): a point off `υ` (`Lh.lhSk_all`,
  reach below the next `υ`-point), a restart `ρ_λ` (reach `δ_λ + O(λ) < υ_{λ+ω+2}`, BLK^O), a `υ`-point of a block
  (reach the top of the block, `Tp.tpBlock_reach`);
* `tqPB_low`: so every `x < U` has a reach `< L(0)`;
* `tqTCrest_of`, `tqTC_of`, `tqEMB2_of`: if every `x < U` has a reach `< L(0)` (`TqLow S U`), then TCrest, (TC) and
  (EMB₂) follow from their parts with left end `x ≥ U` (`TqTCrestUp`, `TqTCUp`, `TqEMB2Up`; for (EMB₂) only the pairs
  `U ≤ x ≤ y` are asked: `x > y` is false on both sides, `B_n` being strictly increasing);
* `tqRoadPB` (**the road with TCrest and (EMB₂) asked only above `U`**) and `tqRoadPB_CL` (**the same with (TC)
  above `U` in place of TCrest, and (CL) derived**: (CL) and (C1) follow from (TC) and (EMB₂), `Cx.cxCL`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tp Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **`υ_B < ν_C`** for every block specification `OffSpecGen O B`. -/
theorem tqUps_lt_nuC {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (Sp : OffSpecGen O B) :
    upsilon B < nuC := by
  obtain ⟨L, ξ, hL, -, hLξ, he, h2, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  exact (upsilon_normal.strictMono.monotone (left_ge_of_spec Sp hL hLν h2)).trans_lt hLν

theorem tq_idx_lt {l B : Ordinal.{0}} (hB : IsRestartIdx B) (hl : IsRestartIdx l) (hlB : l < B) :
    l + ω + 1 + 1 < B := by
  have h3 : (ω : Ordinal.{0}) + 1 + 1 < ω * ω := by
    have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
    calc (ω : Ordinal.{0}) + 1 + 1 = ω + (1 + 1) := add_assoc _ _ _
      _ < ω + ω := (add_lt_add_iff_left _).2 h2ω
      _ = ω * 2 := (Ordinal.mul_two _).symm
      _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos
  have e : l + ω + 1 + 1 = l + (ω + 1 + 1) := by simp only [add_assoc]
  rw [e]
  exact tpAdd_lt hB (mult_of (Or.inr hl)) h3 hlB

/-- **Every point below `υ_B` has an `R₂^C`-reach below `υ_B`**, for every block specification `OffSpecGen O B`. -/
theorem tqReach_below {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (Sp : OffSpecGen O B) :
    ∀ x < upsilon B, ∃ r < upsilon B, IsReach R2C x r := by
  intro x hx
  have hBν := tqUps_lt_nuC Sp
  have hxν : x < nuC := hx.trans hBν
  by_cases hU : UpsPt x
  swap
  · obtain ⟨ξ, r, h1, -, hr, -, hr2, -⟩ := Lh.lhSk_all hxν hU
    have hξ : ξ < B := tpUps_lt_iff.1 (h1.trans_lt hx)
    exact ⟨r, hr2.trans_le (tpUps_le_iff.2 (Order.add_one_le_of_lt hξ)), hr⟩
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hx
    exact absurd hx (not_lt_of_ge zero_le)
  have hBr : IsRestartIdx B := ri_iff.2 ⟨hB0, Sp.mult⟩
  rcases classify hU.1 with ⟨l, hl, rfl⟩ | ⟨μ, j, hμ, h1, h2⟩
  · have hlB : l < B := tpUps_lt_iff.1 hx
    have hreach := ((blk_genGen Sp).2.1 l hl hlB).2.2
    refine ⟨_, ?_, hreach⟩
    have hlt : upsilon (l + ω + 1) + O l < upsilon (l + ω + 1 + 1) := Rz.rz_delta_add_lt (Sp.le l hl hlB)
    exact hlt.trans (upsilon_normal.strictMono (tq_idx_lt hBr hl hlB))
  · have hb : botI μ j < B := tpUps_lt_iff.1 (h1.trans hx)
    have hμB : μ < B := lt_of_le_of_lt (le_self_add.trans (botI_ge μ j)) hb
    have htop : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon B :=
      tpUps_lt_iff.2 (by rw [add_assoc]; exact tpAdd_lt hBr (mult_of hμ) (tpStdIdx_lt j) hμB)
    exact ⟨_, htop, tpBlock_reach hU hμ h1 h2 (htop.trans hBν)⟩

/-! ## Below a point `U ≤ L(0)` where every point has a reach below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- Every point below `U` has an `R₂^C`-reach below `L(0) = m*`. -/
def TqLow (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ x < U, ∃ r < Nc.ncL S 0, IsReach R2C x r

/-- **TCrest at the points `x ≥ U`** (the three alternatives of `CdTCrest`). -/
def TqTCrestUp (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x →
    (∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)) ∨
      (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ CdTCAt S n x

/-- **(TC) at the points `x ≥ U`**. -/
def TqTCUp (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → CdTCAt S n x

/-- **(TC) at the points `x ≥ U` with no reach below `L(n+1)`**. -/
def TqTCRest (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) → CdTCAt S n x

/-- **(EMB₂) at the pairs `U ≤ x ≤ y < L(n+2)`**. -/
def TqEMB2Up (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), ∀ y < Bc.bcC S (n + 1), U ≤ x → x ≤ y →
    (le2 x y ↔ le2 (Bc.bcB S n x) (Bc.bcB S n y))

theorem tqL0_le (n : ℕ) : Nc.ncL S 0 ≤ Bc.bcC S n := (Ph.phL_chain (S := S) n).1

/-- **Every point below `υ_B` has a reach below `L(0)`** when `υ_B ≤ L(0)`. -/
theorem tqLow_spec {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (Sp : OffSpecGen O B)
    (hB : upsilon B ≤ Nc.ncL S 0) : TqLow S (upsilon B) := fun x hx => by
  obtain ⟨r, hr, hR⟩ := tqReach_below Sp x hx
  exact ⟨r, hr.trans_le hB, hR⟩

/-- **Every point below `U = υ_{Λ⁺(lgPB)}` has a reach below `L(0)`.** -/
theorem tqPB_low : TqLow S (upsilon (xtB1 lgPB.sys)) :=
  tqLow_spec (xtSpec1 lgPB.topPkg) (lgPB_fr_order (S := S) 0).2.1.le

/-- **TCrest from its part above `U`.** -/
theorem tqTCrest_of {U : Ordinal.{0}} (hlow : TqLow S U) (hup : TqTCrestUp S U) : CdTCrest S := by
  intro n x hx
  by_cases hxU : U ≤ x
  · exact hup n x hx hxU
  · obtain ⟨r, hr, hR⟩ := hlow x (not_le.1 hxU)
    exact Or.inr (Or.inl ⟨r, hr.trans_le (tqL0_le n), hR⟩)

/-- **(TC) from its part above `U` at the points with no reach below `L(n+1)`.** -/
theorem tqTC_of {U : Ordinal.{0}} (hlow : TqLow S U) (hup : TqTCRest S U) : CdTC S := by
  intro n x hx
  by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C x r
  · obtain ⟨r, hrC, hR⟩ := hr
    exact cdTCAt_low hR hrC
  by_cases hxU : U ≤ x
  · exact hup n x hx hxU hr
  · obtain ⟨r, hr', hR⟩ := hlow x (not_le.1 hxU)
    exact absurd ⟨r, hr'.trans_le (tqL0_le n), hR⟩ hr

theorem tqTCRest_of {U : Ordinal.{0}} (h : TqTCUp S U) : TqTCRest S U :=
  fun n x hx hxU _ => h n x hx hxU

/-- TCrest above `U` from (TC) above `U` at the points with no reach below `L(n+1)`. -/
theorem tqTCrestUp_of {U : Ordinal.{0}} (h : TqTCRest S U) : TqTCrestUp S U := by
  intro n x hx hxU
  by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C x r
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr (h n x hx hxU hr))

/-- **(EMB₂) at a left end with a reach below `L(n+1)`**: if `lh(x) = r < L(n+1)`, then `x ≤₂ y ↔ B_n x ≤₂ B_n y`
for every `y < L(n+2)` (for `y < L(n+1)` both sides are the same, `B_n` being the identity there; for
`y ≥ L(n+1)` both are false: `y > r` and `B_n y ≥ B_n(L(n+1)) = L(ω) > r`). -/
theorem tqEMB2_low {n : ℕ} {x r : Ordinal.{0}} (hR : IsReach R2C x r) (hrC : r < Bc.bcC S n)
    {y : Ordinal.{0}} (hy : y < Bc.bcC S (n + 1)) :
    (le2 x y ↔ le2 (Bc.bcB S n x) (Bc.bcB S n y)) := by
  have hBx : Bc.bcB S n x = x := Bc.bcB_fix' S n x ((le1_le hR.1).trans_lt hrC)
  rcases lt_or_ge y (Bc.bcC S n) with hyc | hyc
  · rw [hBx, Bc.bcB_fix' S n y hyc]
  rw [hBx]
  have hbase : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base (S := S) n
  have hBy : Nc.ncL S ω ≤ Bc.bcB S n y := by
    rcases hyc.lt_or_eq with h | h
    · rw [← hbase]; exact (Bc.bcB_mono' S n (hyc.trans_lt hy) hy h).le
    · rw [← h, hbase]
  have hω : r < Nc.ncL S ω := hrC.trans (Bc.bcC_lt S n)
  exact iff_of_false (fun h => absurd (hR.2 y (le2_le1 h)) (not_le.2 (hrC.trans_le hyc)))
    (fun h => absurd (hR.2 _ (le2_le1 h)) (not_le.2 (hω.trans_le hBy)))

/-- **(EMB₂) at the pairs `U ≤ x ≤ y < L(n+2)` whose left end has no reach below `L(n+1)`**. -/
def TqEMB2Rest (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), ∀ y < Bc.bcC S (n + 1), U ≤ x → x ≤ y →
    (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) → (le2 x y ↔ le2 (Bc.bcB S n x) (Bc.bcB S n y))

theorem tqEMB2Rest_of {U : Ordinal.{0}} (h : TqEMB2Up S U) : TqEMB2Rest S U :=
  fun n x hx y hy hxU hxy _ => h n x hx y hy hxU hxy

/-- **(EMB₂) from its part on the pairs `U ≤ x ≤ y` whose left end has no reach below `L(n+1)`.** -/
theorem tqEMB2_of {U : Ordinal.{0}} (hlow : TqLow S U) (hup : TqEMB2Rest S U) : CdEMB2 S := by
  intro n x hx y hy
  rcases lt_or_ge y x with hyx | hxy
  · have hB : Bc.bcB S n y < Bc.bcB S n x := Bc.bcB_mono' S n hy hx hyx
    exact iff_of_false (fun h => absurd (le2_le h) (not_le.2 hyx))
      (fun h => absurd (le2_le h) (not_le.2 hB))
  by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C x r
  · obtain ⟨r, hrC, hR⟩ := hr
    exact tqEMB2_low hR hrC hy
  by_cases hxU : U ≤ x
  · exact hup n x hx y hy hxU hxy hr
  obtain ⟨r, hr', hR⟩ := hlow x (not_le.1 hxU)
  exact absurd ⟨r, hr'.trans_le (tqL0_le n), hR⟩ hr

/-! ## The roads -/

/-- **The road with TCrest and (EMB₂) asked only above `U = υ_{Λ⁺(lgPB)}`** (`lgPBRoadPh` with `CdTCrest`, `CdEMB2`
replaced by their parts above `U`). -/
theorem tqRoadPB (hU : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lgPB.sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (upsilon (xtB1 lgPB.sys)))
    (hB2 : TqEMB2Rest S (upsilon (xtB1 lgPB.sys))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lgPBRoadPh hU hL hV hC hEQ (tqTCrest_of tqPB_low hrest) (tqEMB2_of tqPB_low hB2)

/-- **The road with (TC) and (EMB₂) asked only above `U = υ_{Λ⁺(lgPB)}`, (CL) derived**: (TC) and (EMB₂) hold
everywhere, hence (CL) and (C1) (`Cx.cxCL`, `Cx.cxC1`), and the conclusion of `lgPBRoadPh`. -/
theorem tqRoadPB_CL (hU : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lgPB.sys) l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (upsilon (xtB1 lgPB.sys)))
    (hB2 : TqEMB2Rest S (upsilon (xtB1 lgPB.sys))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of tqPB_low htc
  have hE : CdEMB2 S := tqEMB2_of tqPB_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1,
    tqRoadPB hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

end Googology.Trans.PoR.InaccPsi.R2.Tq
