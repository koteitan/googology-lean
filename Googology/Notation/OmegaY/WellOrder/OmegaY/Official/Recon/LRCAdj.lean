/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCAdj.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCM

set_option backward.do.legacy false

/-!
# The adjacent case in the source mountain

In the adjacent case (`Adj`), the origin `a` of `θ` is the node of `x` just above the origin
`a_λ` of `λ`, and the two rows differ first at the exponent `e`. The canonical mountain gives the
parent `p` of the node `(x, a)` in its leg column `l`: the highest row of `l` below `a`, with
`a = bump a_λ (jump a_λ p)`; so `jump a_λ p = e`, `p` lies in the region of `J`, below `a_λ`
in the coefficient `e - 1` (`adj_M`).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

theorem lt_of_agree {a b : Row} {e : Nat} (hag : ∀ q, e < q → a.coeff q = b.coeff q)
    (hlt : b.coeff e < a.coeff e) : b < a :=
  Row.lt_iff.mpr ⟨e, fun q hq => (hag q hq).symm, hlt⟩

/-- **The adjacent case.** -/
theorem adj_M {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {x l : Nat}
    {u : Ref × Cell} (hu : u ∈ realNodes M x) (hleg : leftColumn u.2 = .ok l) {τ : Row}
    {e : Nat} {J : Item} (hadj : Adj M x τ e J (official u.2.row))
    (haτ : official u.2.row < τ) :
    ∃ p, p ∈ rowsOf M l ∧ inRegion (e + 1) J.source p = true ∧
      (∀ q, e < q → p.coeff q = (official u.2.row).coeff q) ∧
      (∀ r ∈ rowsOf M l, r < official u.2.row → r ≤ p) ∧
      ∃ aL, aL ∈ rowsOf M x ∧ inRegion (e + 1) J.source aL = true ∧
        (∀ r ∈ rowsOf M x, inRegion (e + 1) J.source r = true → r ≤ aL) ∧
        (∀ r, inRegion (e + 1) J.source r = true → r < official u.2.row) ∧
        (∀ d, e = d + 1 → p.coeff d < aL.coeff d) ∧ (e = 0 → p = aL) := by
  obtain ⟨aL, ⟨qL, hqL, hqLr⟩, haLJ, hag, hlt, _, _, hcons⟩ := hadj
  set a := official u.2.row with ha
  have haL : aL < a := lt_of_agree hag hlt
  have hJlt : ∀ r, inRegion (e + 1) J.source r = true → r < a := by
    intro r hr
    apply lt_of_agree (e := e)
    · intro q hq
      rw [hag q hq, inRegion_iff'.mp hr q (by omega), inRegion_iff'.mp haLJ q (by omega)]
    · rw [inRegion_iff'.mp hr e (by omega), ← inRegion_iff'.mp haLJ e (by omega)]
      exact hlt
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at haL
    exact absurd haL (not_lt.mpr (Row.zero_le _))
  obtain ⟨σ, l', ps, hσm, hσlt, hσmax, hleg', _, hHB, hpsσ, hrow⟩ := source_edge hb hu ha0
  rw [hleg] at hleg'
  obtain rfl := Except.ok.inj hleg'
  have haLm : aL ∈ rowsOf M x := List.mem_map.mpr ⟨qL, hqL, hqLr⟩
  -- the row below `a` is `a_λ`
  have hσ : σ = aL := by
    have h1 := hσmax aL haLm haL
    rcases eq_or_lt_of_le h1 with h | h
    · exact h.symm
    · exfalso
      obtain ⟨qσ, hqσ, hqσr⟩ := List.mem_map.mp hσm
      refine hcons qσ hqσ ?_ ⟨by rw [hqσr]; exact h, by rw [hqσr]; exact hσlt⟩
      rw [hqσr]; exact lt_trans hσlt haτ
  subst hσ
  -- the exponent of the step is `e`
  have hje : Row.jump σ ps = e := by
    rcases Nat.lt_trichotomy (Row.jump σ ps) e with h | h | h
    · exfalso
      have h1 : a.coeff e = (Row.bump σ (Row.jump σ ps)).coeff e := by rw [← hrow]
      rw [bump_coeff_high h] at h1
      omega
    · exact h
    · exfalso
      have h1 : a.coeff (Row.jump σ ps) = (Row.bump σ (Row.jump σ ps)).coeff (Row.jump σ ps) := by
        rw [← hrow]
      rw [bump_coeff_at] at h1
      have h2 := hag (Row.jump σ ps) h
      omega
  have hagp : ∀ q, e ≤ q → ps.coeff q = σ.coeff q := by
    intro q hq
    exact (Row.coeff_eq_of_jump_le (le_of_eq hje) hq).symm
  have hpJ : inRegion (e + 1) J.source ps = true := by
    rw [inRegion_iff'] at haLJ ⊢
    intro q hq
    rw [hagp q (by omega), haLJ q hq]
  refine ⟨ps, hHB.1, hpJ, ?_, hHB.2.2, σ, haLm, haLJ, ?_, hJlt, ?_, ?_⟩
  · intro q hq
    rw [hagp q hq.le, hag q hq]
  · intro r hr hrJ
    by_contra hn
    obtain ⟨qr, hqr, hqrr⟩ := List.mem_map.mp hr
    refine hcons qr hqr ?_ ⟨by rw [hqrr]; exact lt_of_not_ge hn, by rw [hqrr]; exact hJlt r hrJ⟩
    rw [hqrr]; exact lt_trans (hJlt r hrJ) haτ
  · intro d hd
    subst hd
    -- `ps` and `σ` differ at `d`
    have hne : ps.coeff d ≠ σ.coeff d := by
      intro heq
      have : Row.jump σ ps ≤ d := by
        rw [Row.jump_le_iff]
        intro q hq
        rcases Nat.eq_or_lt_of_le hq with h | h
        · subst h; exact heq.symm
        · exact (hagp q (by omega)).symm
      omega
    by_contra hge
    have : σ < ps := by
      refine Row.lt_iff.mpr ⟨d, fun q hq => (hagp q (by omega)).symm, by omega⟩
    exact absurd hpsσ (not_le.mpr this)
  · intro he
    subst he
    exact (Row.jump_eq_zero.mp hje).symm

end OmegaY.Official.Recon.LRC
