import Googology.Trans.PoR.InaccPsi.R2.QqName

/-!
# The `≤₁` clause of EMB from reach commutation (TC)

* `qqLe1_of_reach`: let `B` be strictly increasing on `[0, d)`, and for every `x < d` let either
  (i) `x` have a reach `r < d` with `lh(B x) = B r` (TC), or (ii) `x ≤₁ z` and `B x ≤₁ B z` for every
  `z ∈ [x, d)`.  Then `B` keeps and reflects `≤₁` on `[0, d)`.  (The `≤₁`-successors of `x` are the
  interval `[x, lh(x)]`: `le1_of_le_of_le1`.)
* `qqPair_L_tc` (**PAIR from (C1), TC, the rest of EMB, ONTO-FIN**): `qqPair_L` with the `≤₁` clause
  of EMB replaced by TC on `[0, L(n+1))`.

No axiom beyond those of `qqPair_L`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Qq

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nc
  Googology.Notation.InaccPsi

/-- **TC gives the `≤₁` clause of EMB.** -/
theorem qqLe1_of_reach {d : Ordinal.{0}} {B : Ordinal.{0} → Ordinal.{0}}
    (hm : StrictMonoOn B (Set.Iio d))
    (hr : ∀ x < d, (∃ r < d, IsReach R2C x r ∧ IsReach R2C (B x) (B r)) ∨
      (∀ z, x ≤ z → z < d → le1 x z ∧ le1 (B x) (B z))) :
    ∀ x < d, ∀ y < d, (le1 x y ↔ le1 (B x) (B y)) := by
  intro x hx y hy
  rcases hr x hx with ⟨r, hrd, hxr, hBr⟩ | hall
  · constructor
    · intro h
      exact le1_of_le_of_le1 (hm.monotoneOn hx hy (le1_le h))
        (hm.monotoneOn hy hrd (hxr.2 y h)) hBr.1
    · intro h
      have hxy : x ≤ y := (hm.le_iff_le hx hy).1 (le1_le h)
      have hyr : y ≤ r := (hm.le_iff_le hy hrd).1 (hBr.2 _ h)
      exact le1_of_le_of_le1 hxy hyr hxr.1
  · constructor
    · intro h
      exact (hall y (le1_le h) hy).2
    · intro h
      exact (hall y ((hm.le_iff_le hx hy).1 (le1_le h)) hy).1

/-- **PAIR** `L(ω) <₂ L(ω+1)` from (C1), TC on `[0, L(n+1))`, the other clauses of EMB, and
ONTO-FIN. -/
theorem qqPair_L_tc (S : InaccSeq.{0}) {B : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hc1 : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω))
    (hBm : ∀ n : ℕ, StrictMonoOn (B n) (Set.Iio (ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hBb : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}), B n x < ncL S (ω + 1))
    (hBadd : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
      ∀ y < ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∀ z < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
      (x + y = z ↔ B n x + B n y = B n z))
    (hTC : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
      (∃ r < ncL S ((n + 1 : ℕ) : Ordinal.{0}), IsReach R2C x r ∧ IsReach R2C (B n x) (B n r)) ∨
      (∀ z, x ≤ z → z < ncL S ((n + 1 : ℕ) : Ordinal.{0}) → le1 x z ∧ le1 (B n x) (B n z)))
    (hB2 : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
      ∀ y < ncL S ((n + 1 : ℕ) : Ordinal.{0}), (le2 x y ↔ le2 (B n x) (B n y)))
    (hBcl : ∀ n : ℕ, Closed (B n '' Set.Iio (ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hfix : ∀ n : ℕ, ∀ x < ncL S (n : Ordinal.{0}), B n x = x)
    (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, ncL S ω ≤ y ∧ y < ncL S (ω + 1)) → ∀ N, ∃ n,
      N ≤ n ∧ ∀ y ∈ Y, ∃ y' < ncL S ((n + 1 : ℕ) : Ordinal.{0}), B n y' = y) :
    ncL S ω < ncL S (ω + 1) ∧ le2 (ncL S ω) (ncL S (ω + 1)) :=
  qqPair_L S hc1 hBm hBb hBadd (fun n => qqLe1_of_reach (hBm n) (hTC n)) hB2 hBcl hfix honto

end Googology.Trans.PoR.InaccPsi.R2.Qq
