import Googology.Trans.PoR.InaccPsi.R2.LhSk
import Googology.Trans.PoR.InaccPsi.R2.QqName

/-!
# The named `υ`-points in `R₂^C` under NU-NAME

At the named points `L(n)`, `L(ω)`, `L(ω+1)` (all `υ`-points) the `R₁⁺`-reach is `∞` (`lhL_inf`), so `R₁⁺`
decides none of the `≤₁`-relations of `R₂^C` there.  Here they are derived from the explicit hypothesis
NU-NAME: the first non-standard pair of `R₂^C` is `L(ω) <₂ ν_C` and `ν_C = L(ω+1)` (`hρ`, `hν`; not proved in
Lean: Lean's lower bound for `ν_C` is near `Φ_Γ`, far below `L(0)`).  Under NU-NAME, by LIFT-0 at `k = 2`
(`U2_shape`, `nuC_reach`, `pred1_cof`):

* `lhNu_L`: `L(ω) ≤₁ L(ω+1)`, `L(ω) <₂ L(ω+1)` (PAIR), `lh(L(ω)) = L(ω+1)` in `R₂^C` (so not
  `L(ω) ≤₁ L(ω+1) + 1`, (Q)), and (P) at `(L(ω), L(ω+1))`;
* `lhNu_pred` (**the three relations at `L(n)` reduce to one**): for `u < L(ω)`, `u ≤₁ L(ω) ⇔ u ≤₁ L(ω+1)`,
  and then `u ≤₁ g` for every `g ∈ [u, L(ω+1)]`; so `L(n+1) ≤₁ L(ω)` (the hypothesis (C1) of SHIFT) gives
  `L(n+1) ≤₁ L(n+2)` and `L(n+1) ≤₁ L(ω+1)`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

section NuName

variable (S : InaccSeq.{0}) (hρ : le2 (ncL S ω) nuC) (hν : nuC = ncL S (ω + 1))
include hρ hν

/-- **Under NU-NAME, at `L(ω)`**: `L(ω) ≤₁ L(ω+1)`, `L(ω) <₂ L(ω+1)`, `lh(L(ω)) = L(ω+1)`, not
`L(ω) ≤₁ L(ω+1) + 1`, and (P) at `(L(ω), L(ω+1))`. -/
theorem lhNu_L :
    le1 (ncL S ω) (ncL S (ω + 1)) ∧ le2 (ncL S ω) (ncL S (ω + 1)) ∧
      IsReach R2C (ncL S ω) (ncL S (ω + 1)) ∧ ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1) ∧
      NcCofPred (ncL S ω) (ncL S (ω + 1)) := by
  have hlt : ncL S ω < ncL S (ω + 1) := (Qq.qqL_lt_succ S)
  obtain ⟨l, -, hle⟩ := Pp.ppL_omega_restart (S := S)
  have hR : IsReach R2C (ncL S ω) nuC := by
    rw [hle]
    exact nuC_reach (by rw [← hle, hν]; exact hlt) (by rw [← hle]; exact hρ)
  rw [hν] at hρ hR
  refine ⟨le2_le1 hρ, hρ, hR, fun h => absurd (hR.2 _ h) (not_le.2 (lt_add_one _)), ?_⟩
  intro γ hγ
  obtain ⟨y, h1, h2, h3⟩ := pred1_cof hρ hlt γ hγ
  exact ⟨y, h1, h2, le1_trans h3 (le2_le1 hρ)⟩

/-- **Under NU-NAME, the relations at a point below `L(ω)` reduce to one**: `u ≤₁ L(ω) ⇔ u ≤₁ L(ω+1)`, and
`u ≤₁ L(ω)` gives `u ≤₁ g` for every `g ∈ [u, L(ω+1)]`. -/
theorem lhNu_pred {u : Ordinal.{0}} (hu : u < ncL S ω) :
    (le1 u (ncL S ω) ↔ le1 u (ncL S (ω + 1))) ∧
      (le1 u (ncL S ω) → ∀ g, u ≤ g → g ≤ ncL S (ω + 1) → le1 u g) := by
  have hlt : ncL S ω < ncL S (ω + 1) := (Qq.qqL_lt_succ S)
  obtain ⟨l, hl, hle⟩ := Pp.ppL_omega_restart (S := S)
  have hlν : upsilon l < nuC := by rw [← hle, hν]; exact hlt
  have h2 : le2 (upsilon l) nuC := by rw [← hle]; exact hρ
  have hsh := U2_shape hl hlν h2 u
  rw [← hle] at hsh
  have hiff : le1 u (ncL S ω) ↔ le1 u (ncL S (ω + 1)) := by
    constructor
    · intro h
      exact le1_trans h (by rw [← hν]; exact le2_le1 hρ)
    · intro h
      have hu' : u ≤ nuC := by rw [hν]; exact (hu.trans hlt).le
      rcases hsh.1 ⟨hu', by rw [hν]; exact h⟩ with ⟨-, h'⟩ | e | e
      · exact h'
      · exact absurd e (ne_of_lt hu)
      · exact absurd (e ▸ hν ▸ hu.trans hlt) (lt_irrefl _)
  refine ⟨hiff, fun h g hg1 hg2 => ?_⟩
  exact le1_of_le_of_le1 hg1 hg2 (hiff.1 h)

/-- **Under NU-NAME, (C1) at `L(n+1)` gives the other two relations**: `L(n+1) ≤₁ L(ω)` implies
`L(n+1) ≤₁ L(n+2)` and `L(n+1) ≤₁ L(ω+1)`. -/
theorem lhNu_C1 (n : ℕ) (hC1 : le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω)) :
    le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})) ∧
      le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S (ω + 1)) := by
  have hu := Pp.ppL_lt_omega (S := S) n
  have hP := lhNu_pred S hρ hν hu
  refine ⟨hP.2 hC1 _ (Pp.ppL_lt_succ n).le ?_, hP.1.1 hC1⟩
  exact ((Pp.ppL_lt_omega (n + 1)).trans (Qq.qqL_lt_succ S)).le

end NuName

end Googology.Trans.PoR.InaccPsi.R2.Lh
