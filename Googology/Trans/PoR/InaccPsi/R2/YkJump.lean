import Googology.Trans.PoR.InaccPsi.R2.YeJump

/-!
# The jump leaf at the bottom of the jump gap

Notation as in `R2.XrTop`: `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`.  An *instance* of `Xr.XrJump` is
`(n, R, R', s)` with the part's hypotheses, `R < c_{n+1}`, EQ below `R`, the chain points of `(R, R')` cofinal below
`s ∈ (c_n, c_{n+1})` and none at or above `s`, `lh(s) = R`, and a jump of `B_n` at `s`.
`s* = sup_{q<s} B_n q` is the bottom of the jump gap.

* `ykChain_le1`: every chain point `y` of an instance has `y ≤₁ s` (`y ≤₁ R`, `y < s ≤ R`).
* `ykGapBot` (**the gap bottom is a range restart that is no `B_n`-image**): at an instance, `s* = υ_κ` with
  `κ` a range restart, `L(ω) < υ_κ < B_n s`, `B_n q < υ_κ` for every `q < s`, `B_n y ≠ υ_κ` for every
  `y < c_{n+1}`, and (under ENUM-REACH) `r(κ) = R'` (`Xr.xrGap_reach`).
* `YkJumpGap` (the leaf in gap-restart form): at an instance, the gap-bottom restart `κ` has `r(κ) = B_n R`.
  `ykJump_iff_gap`: **`Xr.XrJump ⇔ YkJumpGap`** (unconditional), so with `Ye.yeJump_iff`,
  `Xw.XwJumpNoRng ⇔ YkJumpGap`.  This is an equivalent form, not a proof: the gap-bottom restart `κ` must
  reach past the gap (`r(κ) = B_n R ≥ B_n s > υ_κ`, `ykGapTop_ge`), the opposite of the gap leaves
  `Ye.YeGapRng` at far indices (there the gap restarts stay below `B_n p`).  So the leaf says exactly: no
  instance has `lh(s*) < B_n s`, and at the others `lh(s*) = B_n R`.
* `ykJumpGap_of_EQtop` (NON-VACUITY): the target `Cx.CxEQtop` gives `YkJumpGap`.

New definitions: the statement name `YkJumpGap`.  No axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Every chain point of an instance is `≤₁ s`.** -/
theorem ykChain_le1 (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s y : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (hsR : IsReach R2C s R)
    (hy : Xr.XrPt S n R R' y) (hys : y < s) : le1 y s :=
  le1_of_le_of_le1 hys.le (hsR.2 s (le1_refl s)) (Xr.xrPt_facts hν hU hL hRc hy).2.2.1.1

/-- **The bottom of the jump gap is a range restart, no `B_n`-image, with the reach `R'`.** -/
theorem ykGapBot (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) :
    ∃ κ, CdRange S κ ∧ sSup (Bc.bcB S n '' Iio s) = upsilon κ ∧ cdR S κ = R' ∧
      Nc.ncL S ω < upsilon κ ∧ upsilon κ < Bc.bcB S n s ∧ (∀ q < s, Bc.bcB S n q < upsilon κ) ∧
      ∀ y < Bc.bcC S (n + 1), Bc.bcB S n y ≠ upsilon κ := by
  have hsRle : s ≤ R := hsR.2 s (le1_refl s)
  have hsc : s < Bc.bcC S (n + 1) := hsRle.trans_lt hRc
  have hsL : s < Nc.ncL S ω := hsc.trans (Bc.bcC_lt S (n + 1))
  have hBlt : ∀ {a b : Ordinal.{0}}, a < Bc.bcC S (n + 1) → b < Bc.bcC S (n + 1) → a < b →
      Bc.bcB S n a < Bc.bcB S n b := fun ha hb hab =>
    (Bc.bcB_lt_iff (ha.trans (Bc.bcC_lt S (n + 1))) (hb.trans (Bc.bcC_lt S (n + 1)))).2 hab
  set T : Set Ordinal.{0} := Bc.bcB S n '' Iio s with hT
  have hbdd : BddAbove T := ⟨Bc.bcB S n s, by
    rintro _ ⟨q, hq, rfl⟩; exact (hBlt ((show q < s from hq).trans hsc) hsc hq).le⟩
  obtain ⟨y0, -, hy0s, hy0⟩ := hcof _ h1s
  have hTne : T.Nonempty := ⟨_, y0, hy0s, rfl⟩
  set s' := sSup T with hs'
  have hmem : ∀ y, y < s → Bc.bcB S n y ≤ s' := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
  -- every image below `s` is strictly below `s'`
  have hbelow : ∀ q < s, Bc.bcB S n q < s' := by
    intro q hq
    obtain ⟨y, hqy, hys, -⟩ := hcof q hq
    exact (hBlt (hq.trans hsc) (hys.trans hsc) hqy).trans_le (hmem y hys)
  obtain ⟨Q, hQ, hQq⟩ := hjump
  have hs'top : s' < Bc.bcB S n s :=
    (csSup_le hTne (by rintro _ ⟨q, hq, rfl⟩; exact hQq q hq)).trans_lt hQ
  have hnimg : ∀ y < Bc.bcC S (n + 1), Bc.bcB S n y ≠ s' := by
    intro y hy e
    rcases lt_or_ge y s with h | h
    · exact (hbelow y h).ne e
    · rcases h.lt_or_eq with h' | h'
      · exact (hs'top.trans (hBlt hsc hy h')).ne' e
      · subst h'; exact hs'top.ne' e
  -- the images of chain points are `υ`-points of range restarts, cofinal below `s'`
  have hW : ∀ y, Xr.XrPt S n R R' y → y < s → ∃ μ', CdRange S μ' ∧ Bc.bcB S n y = upsilon μ' := by
    rintro y ⟨μ, μ', hμ, h1, rfl, -, hμ', hB, -⟩ hys
    exact ⟨μ', Xn.xnRange_img hμ h1 (hys.trans hsc) hμ' hB, hB⟩
  have hcofT : ∀ X < s', ∃ y, y < s ∧ Xr.XrPt S n R R' y ∧ X < Bc.bcB S n y := by
    intro X hX
    obtain ⟨_, ⟨q, hq, rfl⟩, hXq⟩ := (lt_csSup_iff hbdd hTne).1 hX
    obtain ⟨y, hqy, hys, hy⟩ := hcof q hq
    exact ⟨y, hys, hy, hXq.trans (hBlt (hq.trans hsc) (hys.trans hsc) hqy)⟩
  set W : Set Ordinal.{0} := {z | ∃ y, y < s ∧ Xr.XrPt S n R R' y ∧ z = Bc.bcB S n y} with hWdef
  have hWU : W ⊆ UpsSet := by
    rintro _ ⟨y, hys, hy, rfl⟩
    obtain ⟨μ', -, e⟩ := hW y hy hys
    rw [e]; exact upsilon_mem μ'
  have hWne : W.Nonempty := ⟨_, y0, hy0s, hy0, rfl⟩
  have hWb : BddAbove W := ⟨s', by rintro _ ⟨y, hys, -, rfl⟩; exact hmem y hys⟩
  have hsupW : sSup W = s' := by
    refine le_antisymm (csSup_le hWne (by rintro _ ⟨y, hys, -, rfl⟩; exact hmem y hys)) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hys, hy, hXy⟩ := hcofT _ hlt
    exact absurd (le_csSup hWb ⟨y, hys, hy, rfl⟩) (not_le.2 hXy)
  have hs'U : s' ∈ UpsSet := hsupW ▸ upsSet_closed W hWU hWne hWb
  have hy0lt : Bc.bcB S n y0 < s' := hbelow y0 hy0s
  have hs'0 : 0 < s' := lt_of_le_of_lt zero_le hy0lt
  have hs'P : UpsPt s' := by
    rcases hs'U with h | h
    · exact absurd h hs'0.ne'
    · exact h
  obtain ⟨κ, hκ0, hκ⟩ := upsPt_iff_upsilon.1 hs'P
  -- `κ` is a restart index
  have hdvd : ω ^ 2 ∣ κ := by
    refine Ye.ye_dvd_of_cof fun ι hι => ?_
    have h1 : upsilon ι < s' := hκ ▸ upsilon_normal.strictMono hι
    obtain ⟨y, hys, hy, hXy⟩ := hcofT _ h1
    obtain ⟨μ', hμ', e⟩ := hW y hy hys
    refine ⟨μ', upsilon_normal.strictMono.lt_iff_lt.1 (e ▸ hXy), ?_, hμ'.1.2⟩
    have h2 : upsilon μ' < upsilon κ := by rw [← e, ← hκ]; exact hbelow y hys
    exact upsilon_normal.strictMono.lt_iff_lt.1 h2
  have hκr : IsRestartIdx κ := ⟨hκ0.ne', hdvd⟩
  -- the window facts
  obtain ⟨μ0', hμ0', e0⟩ := hW y0 hy0 hy0s
  have hL0 : Nc.ncL S ω < s' := by
    have hc0 : Bc.bcC S n < y0 := (Xr.xrPt_facts hν hU hL hRc hy0).1
    have hw := Cx.cxB_window (S := S) hc0.le (hy0s.trans hsc)
    have : Nc.ncL S ω < Bc.bcB S n y0 := by
      rw [← Cx.cxB_base (S := S) n]
      exact hBlt (Cx.cxC_lt n) (hy0s.trans hsc) hc0
    exact this.trans hy0lt
  have hs'L1 : s' < Nc.ncL S (ω + 1) := hs'top.trans (Bc.bcB_bound' S n s hsc)
  have hB0κ : cdB0 ≤ κ := by
    refine hμ0'.2.1.trans (upsilon_normal.strictMono.lt_iff_lt.1 ?_).le
    rw [← e0, ← hκ]; exact hy0lt
  have hκR : CdRange S κ :=
    ⟨hκr, hB0κ, hκ ▸ hs'L1, Tp.tpCode_top hκr (hκ ▸ hL0) (hκ ▸ hs'L1)⟩
  have hreach := Xr.xrGap_reach hν hU hL hRc h1s hcof hsRle
  refine ⟨κ, hκR, hκ, ?_, hκ ▸ hL0, hκ ▸ hs'top, fun q hq => hκ ▸ hbelow q hq,
    fun y hy => hκ ▸ hnimg y hy⟩
  exact Xr.xrReach_unique (cdEnum_exact hU hL hκR) (hκ ▸ hreach)

/-- **The leaf `Xr.XrJump` in gap-restart form**: at every instance, the restart `κ` at the bottom of the jump gap
(`s* = υ_κ`) has the reach `r(κ) = B_n R`. -/
def YkJumpGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s κ : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → Xr.XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) → (∀ y, Xr.XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    CdRange S κ → sSup (Bc.bcB S n '' Iio s) = upsilon κ → cdR S κ = Bc.bcB S n R

/-- **`YkJumpGap ⇒ Xr.XrJump`.** -/
theorem ykJump_of_gap (h : YkJumpGap S) : Xr.XrJump S := by
  intro n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump
  obtain ⟨κ, hκ, e, hR', -⟩ := ykGapBot hν hU hL hRc h1s hcof hsR hjump
  rw [← hR']
  exact (h n R R' s κ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hκ e).symm

/-- **`Xr.XrJump ⇒ YkJumpGap`.** -/
theorem ykGap_of_jump (h : Xr.XrJump S) : YkJumpGap S := by
  intro n R R' s κ hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump hκ e
  obtain ⟨κ0, -, e0, hR', -⟩ := ykGapBot hν hU hL hRc h1s hcof hsR hjump
  have hk : κ0 = κ := upsilon_normal.strictMono.injective (e0.symm.trans e)
  subst hk
  rw [hR', h n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump]

/-- **`Xr.XrJump ⇔ YkJumpGap`** (unconditional). -/
theorem ykJump_iff_gap : Xr.XrJump S ↔ YkJumpGap S := ⟨ykGap_of_jump, ykJump_of_gap⟩

/-- **`Xw.XwJumpNoRng ⇔ YkJumpGap`** (unconditional; with `Ye.yeJump_iff`). -/
theorem ykNoRng_iff_gap : Xw.XwJumpNoRng S ↔ YkJumpGap S :=
  Ye.yeJump_iff.symm.trans ykJump_iff_gap

/-- At an instance where the leaf holds, the gap-bottom restart reaches past the gap: `B_n s ≤ r(κ)`. -/
theorem ykGapTop_ge {n : ℕ} {R s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (hsR : IsReach R2C s R)
    (hEq : cdR S κ = Bc.bcB S n R) : Bc.bcB S n s ≤ cdR S κ := by
  have hsRle : s ≤ R := hsR.2 s (le1_refl s)
  have hsc : s < Bc.bcC S (n + 1) := hsRle.trans_lt hRc
  rw [hEq]
  rcases hsRle.lt_or_eq with h | h
  · exact ((Bc.bcB_lt_iff (hsc.trans (Bc.bcC_lt S (n + 1)))
      (hRc.trans (Bc.bcC_lt S (n + 1)))).2 h).le
  · rw [h]

/-- **So an instance whose gap bottom stays in the gap (`lh(s*) < B_n s`) refutes the leaf there**: the leaf
`YkJumpGap` (equivalently `Xw.XwJumpNoRng`) asks that such instances do not exist. -/
theorem ykGap_short_ne (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) (hshort : R' < Bc.bcB S n s) :
    Bc.bcB S n R ≠ R' := by
  intro e
  obtain ⟨κ, -, -, hR', -⟩ := ykGapBot hν hU hL hRc h1s hcof hsR hjump
  have := ykGapTop_ge hRc hsR (κ := κ) (hR'.trans e.symm)
  rw [hR'] at this
  exact absurd hshort (not_lt.2 this)

/-- **NON-VACUITY**: the target `Cx.CxEQtop` gives `YkJumpGap`. -/
theorem ykJumpGap_of_EQtop (h : Cx.CxEQtop S) : YkJumpGap S :=
  ykGap_of_jump (Xr.xrJump_of_EQtop h)

end Googology.Trans.PoR.InaccPsi.R2.Yk
