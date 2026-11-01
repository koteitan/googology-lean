import Googology.Trans.PoR.InaccPsi.R2.XwGap

/-!
# The jump leaf `Xr.XrJump` split by the kind of the jump point

Notation as in `R2.XrTop`.  An *instance* of `XrJump` is `(n, R, R', s)` with the part's hypotheses (`hν`,
ENUM-REACH, `WdThLow`, `SkThFar`, `XgKCof`), `R < c_{n+1}`, EQ below `R`, `c_n < s`, the chain points of `(R, R')`
cofinal below `s` and none at or above `s`, `lh(s) = R`, and a jump of `B_n` at `s`.  `s* = sup_{q<s} B_n q`, so
`lh(s*) = R'` (`Xr.xrGap_reach`).

* `xwJump_off_iff`: at an instance where `s` is NOT a range restart (then `lh(B_n s) = B_n R`, `Xr.xrRM_off`):
  `B_n R = R' ⇔ B_n s ≤₁ R'` (the image of the jump point is `≤₁` the reach of the gap bottom).
* `xwJump_noRng_of`: `XrJump` excludes every instance where `s` IS a range restart `ρ_μ` (`Xr.xrClass` gives EQ at
  `μ`, which with `B_n R = R'` makes `s` a chain point).
* So `XrJump ⇔ XwJumpOff ∧ XwJumpNoRng` (`xwJump_iff`):
  - `XwJumpOff`: at every instance with `s` not a range restart, `B_n s ≤₁ R'`;
  - `XwJumpNoRng`: there is no instance with `s` a range restart.
* Non-vacuity: both follow from the target `Cx.CxEQtop` (`xwJump_of_EQtop`).

New definitions: the statement names `XwJumpOff`, `XwJumpNoRng`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **At a non-range jump point: `B_n R = R' ⇔ B_n s ≤₁ R'`.** -/
theorem xwJump_off_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hnr : ∀ μ, CdRange S μ → s ≠ upsilon μ) :
    Bc.bcB S n R = R' ↔ le1 (Bc.bcB S n s) R' := by
  have hsRle : s ≤ R := hsR.2 s (le1_refl s)
  have hsL : s < Nc.ncL S ω := (hsRle.trans_lt hRc).trans (Bc.bcC_lt S (n + 1))
  have hm : IsReach R2C (Bc.bcB S n s) (Bc.bcB S n R) := Xr.xrRM_off hν h1s hRc hsR hnr
  have hg := Xr.xrGap_reach hν hU hL hRc h1s hcof hsRle
  constructor
  · intro e; rw [← e]; exact hm.1
  · intro h
    have hR'le : R' ≤ Bc.bcB S n R := hm.2 R' h
    have hs0 : (0 : Ordinal.{0}) < s := lt_of_le_of_lt zero_le h1s
    have hsle : sSup (Bc.bcB S n '' Iio s) ≤ Bc.bcB S n s := by
      refine csSup_le ⟨_, 0, hs0, rfl⟩ ?_
      rintro _ ⟨q, hq, rfl⟩
      exact Xg.xgB_le ((show q < s from hq).trans hsL) hsL (show q < s from hq).le
    have h1 : le1 (sSup (Bc.bcB S n '' Iio s)) (Bc.bcB S n s) :=
      le1_of_le_of_le1 hsle (le1_le h) hg.1
    exact le_antisymm (hg.2 _ (le1_trans h1 hm.1)) hR'le

/-- **Leaf part 1 (non-range jump points)**: at every instance of `XrJump` whose jump point `s` is not a range
restart, `B_n s ≤₁ R' = lh(s*)`. -/
def XwJumpOff (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → Xr.XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) → (∀ y, Xr.XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    (∀ μ, CdRange S μ → s ≠ upsilon μ) → le1 (Bc.bcB S n s) R'

/-- **Leaf part 2 (range jump points)**: no instance of `XrJump` has a range restart as its jump point. -/
def XwJumpNoRng (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → Xr.XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) → (∀ y, Xr.XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    (∃ μ, CdRange S μ ∧ s = upsilon μ) → False

/-- `XrJump ⇒ XwJumpOff`. -/
theorem xwJump_off_of (hJ : Xr.XrJump S) : XwJumpOff S := by
  intro n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hnr
  exact (xwJump_off_iff hν hU hL hRc h1s hcof hsR hnr).1
    (hJ n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump)

/-- **`XrJump ⇒ XwJumpNoRng`**: at a range jump point `s = ρ_μ`, `Xr.xrClass` gives EQ at `μ`; with the conclusion
`B_n R = R'` of `XrJump`, `s` would be a chain point, but no chain point is `≥ s`. -/
theorem xwJump_noRng_of (hJ : Xr.XrJump S) : XwJumpNoRng S := by
  intro n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hr
  obtain ⟨μ, hμ, hsμ⟩ := hr
  have hconc := hJ n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump
  have hsRle : s ≤ R := hsR.2 s (le1_refl s)
  have hsc : s < Bc.bcC S (n + 1) := hsRle.trans_lt hRc
  have h1μ : Bc.bcC S n < upsilon μ := hsμ ▸ h1s
  obtain ⟨μ', hμ', e⟩ := Sf.sfRstMove (S := S) n μ hμ.1 h1μ.le (hsμ ▸ hsc)
  have hRμ : cdR S μ = R := Xr.xrReach_unique (cdEnum_exact hU hL hμ) (hsμ ▸ hsR)
  have hEQ : Bc.bcB S n (cdR S μ) = cdR S μ' :=
    Xr.xrClass hν hU hL hTL hTF hC hJ hRc IH μ hμ h1μ hRμ μ' hμ' e
  have hR' : cdR S μ' = R' := by rw [← hEQ, hRμ, hconc]
  exact lt_irrefl s (hup s ⟨μ, μ', hμ, h1μ, hsμ.symm, hRμ, hμ', e, hR'⟩)

/-- **`XwJumpOff ∧ XwJumpNoRng ⇒ XrJump`.** -/
theorem xwJump_of (hO : XwJumpOff S) (hN : XwJumpNoRng S) : Xr.XrJump S := by
  intro n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump
  by_cases hr : ∃ μ, CdRange S μ ∧ s = upsilon μ
  · exact (hN n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hr).elim
  · push Not at hr
    exact (xwJump_off_iff hν hU hL hRc h1s hcof hsR hr).2
      (hO n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hr)

/-- **`XrJump ⇔ XwJumpOff ∧ XwJumpNoRng`** (unconditional). -/
theorem xwJump_iff : Xr.XrJump S ↔ XwJumpOff S ∧ XwJumpNoRng S :=
  ⟨fun h => ⟨xwJump_off_of h, xwJump_noRng_of h⟩, fun h => xwJump_of h.1 h.2⟩

/-- **NON-VACUITY**: the target `Cx.CxEQtop` gives both parts. -/
theorem xwJump_of_EQtop (h : Cx.CxEQtop S) : XwJumpOff S ∧ XwJumpNoRng S :=
  xwJump_iff.1 (Xr.xrJump_of_EQtop h)

/-- **NON-VACUITY**: the old leaves `Xn.XnTop` and `Xn.XnChainWF` give both parts. -/
theorem xwJump_of_top (h : Xn.XnTop S) : XwJumpOff S ∧ XwJumpNoRng S :=
  xwJump_iff.1 (Xr.xrJump_of_top h)

theorem xwJump_of_wf (h : Xn.XnChainWF S) : XwJumpOff S ∧ XwJumpNoRng S :=
  xwJump_iff.1 (Xr.xrJump_of_wf h)

end Googology.Trans.PoR.InaccPsi.R2.Xw
