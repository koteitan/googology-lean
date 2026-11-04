import Googology.Trans.PoR.InaccPsi.R2.YzRng
import Googology.Trans.PoR.InaccPsi.R2.YkJump

/-!
# The jump instances with a short-code gap bottom

Notation as in `R2.YkJump`: an instance `(n, R, R', s)` of `Xr.XrJump` (chain points of `(R, R')` cofinal below
`s`, `lh(s) = R`, `B_n` jumps at `s`), `s* = sup_{q<s} B_n q = υ_κ` its gap bottom (`Yk.ykGapBot`).

* `yzJump_shortBot`: **at an instance whose jump point `s` is a range restart and whose gap bottom `κ` has a code
  `m_κ ≤ θ·ω`, `r(κ) < B_n s`** (`Yz.yzR_lowCode`: `r(κ) < υ_{κ+ω+2}`; `B_n s = υ_{μ'}`, `μ'` a restart index above
  `κ`).
* `yzJump_short_ne`: **so the leaf `Yk.YkJumpGap` (`r(κ) = B_n R`) fails at every such instance**
  (`Yk.ykGapTop_ge`); `yzJump_short_noEQ`: such an instance refutes the target `Cx.CxEQtop`.  Hence
  `Xw.XwJumpNoRng` holds at the short-code bottoms only by the absence of instances; the leaf is split into
  `YzJumpShort` (no instance with a short-code bottom) and `YzJumpLong` (the long-code bottoms), `yzJumpNoRng_iff`.

No new axiom.  New definitions: the statement names `YzJumpShort`, `YzJumpLong`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **At an instance with a range jump point `s` and a short-code gap bottom `κ`: `r(κ) < B_n s`.** -/
theorem yzJump_shortBot (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) (hs : ∃ μ, CdRange S μ ∧ s = upsilon μ)
    (hκ : CdRange S κ) (he : sSup (Bc.bcB S n '' Iio s) = upsilon κ) (hm : cdCode S κ ≤ ConjT.th S * ω) :
    cdR S κ < Bc.bcB S n s := by
  obtain ⟨κ₀, -, e₀, -, -, hκs, -, -⟩ := Yk.ykGapBot hν hU hL hRc h1s hcof hsR hjump
  have hκκ : κ₀ = κ := Tp.tpUps_inj (e₀.symm.trans he)
  subst hκκ
  obtain ⟨μ, hμ, rfl⟩ := hs
  have hsRle : upsilon μ ≤ R := hsR.2 _ (le1_refl _)
  have hsc : upsilon μ < Bc.bcC S (n + 1) := hsRle.trans_lt hRc
  obtain ⟨μ', hμ', hB⟩ := Tp.tpRstMove_of_shift Sf.sfShiftAll n μ hμ.1 h1s.le hsc
  rw [hB] at hκs ⊢
  have hlt := yz_ri_add_lt hκ.1 hμ' (Tp.tpUps_lt_iff.1 hκs)
  have hup : upsilon (κ₀ + (ω + 2)) < upsilon μ' := upsilon_normal.strictMono hlt
  have hXL : upsilon μ' < Nc.ncL S (ω + 1) := hB ▸ Bc.bcB_bound' S n _ hsc
  have hC : upsilon (κ₀ + ω + 1) < nuC := by
    have h1 : κ₀ + ω + 1 < κ₀ + (ω + 2) := by
      rw [add_assoc]; exact (add_lt_add_iff_left κ₀).2 ((add_lt_add_iff_left ω).2 one_lt_two)
    exact ((upsilon_normal.strictMono h1).trans hup).trans (hXL.trans_le hν)
  exact (yzR_lowCode hκ.1 hκ.2.2.1 hC hm).trans hup

/-- **The leaf `Yk.YkJumpGap` fails at every instance with a range jump point and a short-code gap bottom.** -/
theorem yzJump_short_ne (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) (hs : ∃ μ, CdRange S μ ∧ s = upsilon μ)
    (hκ : CdRange S κ) (he : sSup (Bc.bcB S n '' Iio s) = upsilon κ) (hm : cdCode S κ ≤ ConjT.th S * ω) :
    cdR S κ ≠ Bc.bcB S n R := fun hEq =>
  absurd (yzJump_shortBot hν hU hL hRc h1s hcof hsR hjump hs hκ he hm)
    (not_lt.2 (Yk.ykGapTop_ge hRc hsR hEq))

/-- **Such an instance refutes the target `Cx.CxEQtop`** (through `Yk.ykJumpGap_of_EQtop`). -/
theorem yzJump_short_noEQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (hTL : Wd.WdThLow S) (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) {n : ℕ}
    {R R' s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (IH : Xr.XrIH S n R) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hup : ∀ y, Xr.XrPt S n R R' y → y < s)
    (hsR : IsReach R2C s R) (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q)
    (hs : ∃ μ, CdRange S μ ∧ s = upsilon μ) (hκ : CdRange S κ) (he : sSup (Bc.bcB S n '' Iio s) = upsilon κ)
    (hm : cdCode S κ ≤ ConjT.th S * ω) : ¬ Cx.CxEQtop S := fun hEQ =>
  yzJump_short_ne hν hU hL hRc h1s hcof hsR hjump hs hκ he hm
    (Yk.ykJumpGap_of_EQtop hEQ n R R' s κ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hκ he)

/-- **Leaf part (short-code gap bottoms)**: no instance of `Xw.XwJumpNoRng` has a gap bottom with `m_κ ≤ θ·ω`. -/
def YzJumpShort (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s κ : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → Xr.XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) → (∀ y, Xr.XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    (∃ μ, CdRange S μ ∧ s = upsilon μ) → CdRange S κ → sSup (Bc.bcB S n '' Iio s) = upsilon κ →
    cdCode S κ ≤ ConjT.th S * ω → False

/-- **Leaf part (long-code gap bottoms)**: no instance of `Xw.XwJumpNoRng` has a gap bottom with `m_κ > θ·ω`. -/
def YzJumpLong (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s κ : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → Xr.XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) → (∀ y, Xr.XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    (∃ μ, CdRange S μ ∧ s = upsilon μ) → CdRange S κ → sSup (Bc.bcB S n '' Iio s) = upsilon κ →
    ConjT.th S * ω < cdCode S κ → False

/-- **`Xw.XwJumpNoRng ⇔ YzJumpShort ∧ YzJumpLong`** (the gap bottom exists by `Yk.ykGapBot`). -/
theorem yzJumpNoRng_iff : Xw.XwJumpNoRng S ↔ YzJumpShort S ∧ YzJumpLong S := by
  constructor
  · intro h
    exact ⟨fun n R R' s _ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs _ _ _ =>
        h n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs,
      fun n R R' s _ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs _ _ _ =>
        h n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs⟩
  · rintro ⟨hS, hLg⟩ n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs
    obtain ⟨κ, hκ, e, -⟩ := Yk.ykGapBot hν hU hL hRc h1s hcof hsR hjump
    rcases le_or_gt (cdCode S κ) (ConjT.th S * ω) with hm | hm
    · exact hS n R R' s κ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs hκ e hm
    · exact hLg n R R' s κ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hs hκ e hm

/-- **NON-VACUITY**: the target `Cx.CxEQtop` gives both parts (through `Yk.ykJumpGap_of_EQtop`). -/
theorem yzJump_of_EQtop (h : Cx.CxEQtop S) : YzJumpShort S ∧ YzJumpLong S :=
  yzJumpNoRng_iff.1 (Yk.ykNoRng_iff_gap.2 (Yk.ykJumpGap_of_EQtop h))

end Googology.Trans.PoR.InaccPsi.R2.Yz
