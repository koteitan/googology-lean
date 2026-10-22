import Googology.Trans.PoR.InaccPsi.R2.TqLow
import Googology.Trans.PoR.InaccPsi.R2.LqBN

/-!
# (TC) and (EMB₂) below the frontier `sup_n Λ⁺(lqBN n)`, and only at restart points below `L(n+1)`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `U' = υ(sup_n Λ⁺(lqBN n)) = P(ω^{ω^{Γ_{Ω₁+1} +
phB·ω}})` (`lqFamB_loc`), `U' < L(0)` (`lqFamB_fr_order`).

* `rbFam_low` (**every point below `υ_Λ` has a reach below `L(0)`**, for every family `F : XtFam` with `υ_Λ ≤ L(0)`,
  `Λ = F.famSup`: a point below `υ_Λ` lies below some `υ_{Λ_k}`, `Tq.tqReach_below`); `rbB_low`: at `U'`,
  unconditionally;
* `rbRoadB`, `rbRoadB_CL` (**the road `lqFamBRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U'`**, and the
  same with (TC) in place of TCrest and (CL) derived);
* `rbReach_nonRst` (**below `L(n+1)`, given `L(ω) ≤ ν_C`, every point that is not a restart point has a reach below
  `L(n+1)`**: a point off `υ` (`Lh.lhSk_all`), a `υ`-point of a block (`Tp.tpBlock_reach`, the block ends below the
  restart `L(n+1)`));
* `RbTCRst S U`, `RbEMB2Rst S U` (hypothesis names): (TC) and (EMB₂) at the left ends `x ∈ [U, L(n+2))` with no reach
  below `L(n+1)` that are **restart points or lie in `[L(n+1), L(n+2))`** (for (EMB₂) only `y ≥ L(n+1)`);
  `rbTCRest_of`, `rbEMB2Rest_of`: with `L(ω) ≤ ν_C` they give `Tq.TqTCRest`, `Tq.TqEMB2Rest`;
* `rbRoadB_rst` (**the road with (TC) and (EMB₂) asked only at those left ends above `U'`**; `L(ω) ≤ ν_C` comes from
  UPPER and the cap of the values, `cdLow_enum`; (CL) derived);
* `RbTCrestRst S U` (TCrest at those left ends that are not restarts `ρ_λ` of the range with `r(λ) < L(n+2)`),
  `rbTCrestUp_of`, `rbRoadB_rst2` (**the road with TCrest and (EMB₂) asked only there**; (TC) by `cdTC_of_enum`, (CL)
  derived).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Tq

variable {S : InaccSeq.{0}}

/-! ## Below the frontier -/

/-- **Every point below `υ_Λ` (`Λ = F.famSup`) has a reach below `L(0)`**, when `υ_Λ ≤ L(0)`. -/
theorem rbFam_low (F : XtFam) (hU : upsilon F.famSup ≤ Nc.ncL S 0) : TqLow S (upsilon F.famSup) := by
  intro x hx
  obtain ⟨k, hk⟩ := F.famUps_lt hx
  obtain ⟨r, hr, hR⟩ := tqReach_below (F.spec k) x hk
  exact ⟨r, (hr.trans (upsilon_normal.strictMono (F.famBd_lt k))).trans_le hU, hR⟩

/-- **Every point below `U' = υ(sup_n Λ⁺(lqBN n))` has a reach below `L(0)`.** -/
theorem rbB_low : TqLow S (upsilon lqFamB.famSup) :=
  rbFam_low lqFamB (lqFamB_fr_order (S := S) 0 0).2.1.le

/-- **The road `lqFamBRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U'`.** -/
theorem rbRoadB (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (upsilon lqFamB.famSup))
    (hB2 : TqEMB2Rest S (upsilon lqFamB.famSup)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lqFamBRoad hU hL hV hC hEQ (tqTCrest_of rbB_low hrest) (tqEMB2_of rbB_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U'` with no reach below `L(n+1)`, (CL) derived.** -/
theorem rbRoadB_CL (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (upsilon lqFamB.famSup))
    (hB2 : TqEMB2Rest S (upsilon lqFamB.famSup)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rbB_low htc
  have hE : CdEMB2 S := tqEMB2_of rbB_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rbRoadB hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-! ## Below `L(n+1)` only the restart points are left -/

/-- **Below `L(n+1)`, given `L(ω) ≤ ν_C`, a point that is not a restart point has a reach below `L(n+1)`.** -/
theorem rbReach_nonRst (hν : Nc.ncL S ω ≤ nuC) {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S n)
    (hnr : ∀ l, IsRestartIdx l → x ≠ upsilon l) : ∃ r < Bc.bcC S n, IsReach R2C x r := by
  have hxν : x < nuC := (hx.trans (Bc.bcC_lt S n)).trans_le hν
  by_cases hU : UpsPt x
  · obtain ⟨μ, j, hμ, h1, h2⟩ := tpBlock hU hnr
    obtain ⟨lam, hlam, hL⟩ := tpIdx S n
    have hT : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω * ω := tpStdIdx_lt j
    have hbl : botI μ j < lam := by
      rw [hL] at hx; exact tpUps_lt_iff.1 (h1.trans hx)
    have hμl : μ < lam := lt_of_le_of_lt (le_self_add.trans (botI_ge μ j)) hbl
    have htop : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < Bc.bcC S n := by
      rw [hL, add_assoc]; exact tpUps_lt_iff.2 (tpAdd_lt hlam (mult_of hμ) hT hμl)
    exact ⟨_, htop, tpBlock_reach hU hμ h1 h2 (htop.trans ((Bc.bcC_lt S n).trans_le hν))⟩
  · obtain ⟨ξ, r, h1, -, hr, -, hr2, -⟩ := Lh.lhSk_all hxν hU
    exact ⟨r, hr2.trans_le (Cx.cxUps_succ_le h1 hx), hr⟩

/-- **(TC) at the left ends `x ∈ [U, L(n+2))` with no reach below `L(n+1)` that are restart points or lie in
`[L(n+1), L(n+2))`.** -/
def RbTCRst (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) →
    (Bc.bcC S n ≤ x ∨ ∃ l, IsRestartIdx l ∧ x = upsilon l) → CdTCAt S n x

/-- **(EMB₂) at the pairs `U ≤ x ≤ y < L(n+2)`, `y ≥ L(n+1)`, whose left end has no reach below `L(n+1)` and is a
restart point or lies in `[L(n+1), L(n+2))`.** -/
def RbEMB2Rst (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), ∀ y < Bc.bcC S (n + 1), U ≤ x → x ≤ y → Bc.bcC S n ≤ y →
    (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) → (Bc.bcC S n ≤ x ∨ ∃ l, IsRestartIdx l ∧ x = upsilon l) →
    (le2 x y ↔ le2 (Bc.bcB S n x) (Bc.bcB S n y))

/-- The left ends without a reach below `L(n+1)` are restart points or lie in `[L(n+1), L(n+2))`. -/
theorem rb_left_cases (hν : Nc.ncL S ω ≤ nuC) {n : ℕ} {x : Ordinal.{0}}
    (hr : ¬ ∃ r < Bc.bcC S n, IsReach R2C x r) :
    Bc.bcC S n ≤ x ∨ ∃ l, IsRestartIdx l ∧ x = upsilon l := by
  rcases le_or_gt (Bc.bcC S n) x with h | h
  · exact Or.inl h
  · by_contra hc
    push Not at hc
    exact hr (rbReach_nonRst hν h fun l hl he => hc.2 l hl he)

/-- **`RbTCRst` gives `Tq.TqTCRest`**, given `L(ω) ≤ ν_C`. -/
theorem rbTCRest_of (hν : Nc.ncL S ω ≤ nuC) {U : Ordinal.{0}} (h : RbTCRst S U) : TqTCRest S U :=
  fun n x hx hxU hr => h n x hx hxU hr (rb_left_cases hν hr)

/-- **`RbEMB2Rst` gives `Tq.TqEMB2Rest`**, given `L(ω) ≤ ν_C` (for `y < L(n+1)` both sides agree: `B_n` is the identity
on `[0, L(n+1))`). -/
theorem rbEMB2Rest_of (hν : Nc.ncL S ω ≤ nuC) {U : Ordinal.{0}} (h : RbEMB2Rst S U) : TqEMB2Rest S U := by
  intro n x hx y hy hxU hxy hr
  rcases lt_or_ge y (Bc.bcC S n) with hyc | hyc
  · rw [Bc.bcB_fix' S n x (hxy.trans_lt hyc), Bc.bcB_fix' S n y hyc]
  · exact h n x hx y hy hxU hxy hyc hr (rb_left_cases hν hr)

/-- **`L(ω) ≤ ν_C` from UPPER at `λ ≥ U'` and the cap of the values outside `sup_n Λ⁺(lqBN n)`.** -/
theorem rbB_nu (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (lqFamB.famUPPER3 hU fun n _ hr hln hfix => lqBNT_fix n hr hln hfix) (lqFamB.famCapVAll hV)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U'` with no reach below `L(n+1)` that are restart
points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rbRoadB_rst (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (upsilon lqFamB.famSup))
    (hB2 : RbEMB2Rst S (upsilon lqFamB.famSup)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rbB_nu hU hV
  rbRoadB_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **TCrest at the left ends `x ∈ [U, L(n+2))` with no reach below `L(n+1)` that are restart points or lie in `[L(n+1),
L(n+2))`, and are not restarts `ρ_λ` of the range with `r(λ) < L(n+2)`.** -/
def RbTCrestRst (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) →
    (Bc.bcC S n ≤ x ∨ ∃ l, IsRestartIdx l ∧ x = upsilon l) →
    (¬ ∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)) → CdTCAt S n x

/-- **`RbTCrestRst` gives `Tq.TqTCrestUp`**, given `L(ω) ≤ ν_C`. -/
theorem rbTCrestUp_of (hν : Nc.ncL S ω ≤ nuC) {U : Ordinal.{0}} (h : RbTCrestRst S U) : TqTCrestUp S U := by
  intro n x hx hxU
  by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C x r
  · exact Or.inr (Or.inl hr)
  by_cases hR : ∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)
  · exact Or.inl hR
  exact Or.inr (Or.inr (h n x hx hxU hr (rb_left_cases hν hr) hR))

/-- **The road with TCrest and (EMB₂) asked only at left ends `x ≥ U'` with no reach below `L(n+1)` that are restart
points or lie in `[L(n+1), L(n+2))` (TCrest also not at the restarts of the range with `r(λ) < L(n+2)`)**; (TC) from
ENUM-REACH and EQ (`cdTC_of_enum`), (CL) derived. -/
theorem rbRoadB_rst2 (hU : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lqFamB.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lqFamB.famSup l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (upsilon lqFamB.famSup))
    (hB2 : RbEMB2Rst S (upsilon lqFamB.famSup)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rbB_nu hU hV
  have hT : lqFamB.famTHfix S := fun n _ hr hln hfix => lqBNT_fix n hr hln hfix
  have hTCr : CdTCrest S := tqTCrest_of rbB_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rbB_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (lqFamB.famUPPER3 hU hT) (lqFamB.famLOWER3 hL hT) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, lqFamBRoad hU hL hV hC hEQ hTCr hE⟩

end Googology.Trans.PoR.InaccPsi.R2.Rb
