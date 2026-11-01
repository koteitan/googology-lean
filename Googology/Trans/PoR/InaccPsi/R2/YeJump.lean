import Googology.Trans.PoR.InaccPsi.R2.XwJump

/-!
# Every jump point of `Xr.XrJump` is a range restart: `Xw.XwJumpOff` holds

Notation as in `R2.XrTop`: `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`.  An instance of `Xr.XrJump` has a point
`s ∈ (c_n, c_{n+1})` below which the chain points of a class `(R, R')` (`Xr.XrPt`: points `ρ_μ` of range restarts
`μ`) are cofinal.

* `ye_dvd_of_cof`: an ordinal `l` below which multiples of `ω²` are cofinal is a multiple of `ω²`;
* `yeJump_rst` (**the jump point is a range restart**): such an `s` is `υ_l` with `l = sup` of the chain indices,
  `ω² ∣ l` (`ye_dvd_of_cof`), so `l` is a restart index, and a restart strictly inside `(c_n, c_{n+1})` is a range
  restart (`Se.seRange_mid`);
* `yeJumpOff`: **`Xw.XwJumpOff S` is a theorem** (its hypotheses contain "`s` is no range restart", which
  `yeJump_rst` refutes: the leaf is vacuous);
* `yeJump_iff`: so `Xr.XrJump S ⇔ Xw.XwJumpNoRng S` (unconditional).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ye

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- An ordinal below which multiples of `d ≠ 0` are cofinal is a multiple of `d`. -/
theorem ye_dvd_of_cof' {d l : Ordinal.{0}} (hd0 : d ≠ 0) (h : ∀ ι < l, ∃ μ, ι < μ ∧ μ < l ∧ d ∣ μ) : d ∣ l := by
  rw [Ordinal.dvd_iff_mod_eq_zero]
  by_contra hr
  have hl : d * (l / d) + l % d = l := Ordinal.div_add_mod l d
  have hlt : d * (l / d) < l := by
    conv_rhs => rw [← hl]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
  obtain ⟨μ, h1, h2, ⟨c, rfl⟩⟩ := h _ hlt
  have hc : l / d < c := (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 hd0)).1 h1
  have hc' : l / d + 1 ≤ c := Order.add_one_le_iff.2 hc
  have h3 : d * (l / d) + d ≤ d * c := by
    rw [← mul_add_one]; exact mul_le_mul_right hc' d
  have h4 : l < d * (l / d) + d := by
    conv_lhs => rw [← hl]
    exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt l hd0)
  exact absurd (h4.trans_le h3) (not_lt.2 h2.le)

/-- **An ordinal below which multiples of `ω²` are cofinal is a multiple of `ω²`.** -/
theorem ye_dvd_of_cof {l : Ordinal.{0}} (h : ∀ ι < l, ∃ μ, ι < μ ∧ μ < l ∧ ω ^ 2 ∣ μ) : ω ^ 2 ∣ l :=
  ye_dvd_of_cof' (pow_pos omega0_pos 2).ne' h

/-- **The jump point is a range restart**: if the chain points of a class are cofinal below `s ∈ (c_n, c_{n+1})`,
then `s = ρ_l` for a range restart `l`. -/
theorem yeJump_rst {n : ℕ} {R R' s : Ordinal.{0}} (h1s : Bc.bcC S n < s) (hs2 : s < Bc.bcC S (n + 1))
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) :
    ∃ l, CdRange S l ∧ s = upsilon l := by
  -- `s` is a `υ`-point: the supremum of the chain points below it
  set T : Set Ordinal.{0} := {y | y < s ∧ Xr.XrPt S n R R' y} with hT
  have hTU : T ⊆ UpsSet := by
    rintro y ⟨-, μ, -, hμ, -, e, -⟩
    rw [← e]; exact upsilon_mem μ
  obtain ⟨y0, -, hy0s, hy0⟩ := hcof _ h1s
  have hTne : T.Nonempty := ⟨y0, hy0s, hy0⟩
  have hTb : BddAbove T := ⟨s, fun y hy => hy.1.le⟩
  have hsup : sSup T = s := by
    refine le_antisymm (csSup_le hTne fun y hy => hy.1.le) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy1, hy2, hy⟩ := hcof _ hlt
    exact absurd (le_csSup hTb ⟨hy2, hy⟩) (not_le.2 hy1)
  have hsU : s ∈ UpsSet := hsup ▸ upsSet_closed T hTU hTne hTb
  have hs0 : 0 < s := lt_of_le_of_lt zero_le h1s
  have hsP : UpsPt s := by
    rcases hsU with h | h
    · exact absurd h hs0.ne'
    · exact h
  obtain ⟨l, hl0, rfl⟩ := upsPt_iff_upsilon.1 hsP
  -- the index is a multiple of `ω²`
  have hdvd : ω ^ 2 ∣ l := by
    refine ye_dvd_of_cof fun ι hι => ?_
    obtain ⟨y, hy1, hy2, μ, μ', hμ, -, e, -⟩ := hcof (upsilon ι) (upsilon_normal.strictMono hι)
    rw [← e] at hy1 hy2
    exact ⟨μ, upsilon_normal.strictMono.lt_iff_lt.1 hy1, upsilon_normal.strictMono.lt_iff_lt.1 hy2,
      hμ.1.2⟩
  have hr : IsRestartIdx l := ⟨hl0.ne', hdvd⟩
  exact ⟨l, Se.seRange_mid hr h1s hs2, rfl⟩

/-- **`Xw.XwJumpOff` holds**: its hypotheses say that `s` is no range restart, which `yeJump_rst` refutes. -/
theorem yeJumpOff : Xw.XwJumpOff S := by
  intro n R R' s _ _ _ _ _ _ hRc _ h1s hcof _ hsR _ hnr
  have hs2 : s < Bc.bcC S (n + 1) := (hsR.2 s (le1_refl s)).trans_lt hRc
  obtain ⟨l, hl, e⟩ := yeJump_rst h1s hs2 hcof
  exact absurd e (hnr l hl)

/-- **`Xr.XrJump ⇔ Xw.XwJumpNoRng`** (unconditional). -/
theorem yeJump_iff : Xr.XrJump S ↔ Xw.XwJumpNoRng S :=
  ⟨fun h => (Xw.xwJump_iff.1 h).2, fun h => Xw.xwJump_of yeJumpOff h⟩

end Googology.Trans.PoR.InaccPsi.R2.Ye
