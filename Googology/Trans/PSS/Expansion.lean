import Googology.Trans.PSS.Rank

/-!
# Pair sequences → extended Buchholz's ψ: one step does not go to one step

The translation `pairOrdTerm` sends a pair sequence `M` to the standard form
of its ordinal: `0` for `[]`, and `1 + toTerm (Trans M)` otherwise, where
`Trans` is the map of [koteitan/pss-proof](https://github.com/koteitan/pss-proof).
This file shows that it does **not** send one expansion step of the pair
sequences to one step `fs X (idx X k)` of extended Buchholz's ψ.

The counterexample is the generator `(0,0)(1,1)`:

```
(0,0)(1,1)      ↦  ψ_0(Ω_1)   (= ε₀)
(0,0)(1,1)[1] = (0,0)  ↦  1
```

and every fundamental-sequence member `ψ_0(Ω_1)[Y]` of p進大好きbot's system
has the form `ψ_0(Z)` with `Z ≠ 0` (`fs_psiOmega1`), so it is never `1`,
whatever the index `Y` is.  The step of `pairL` at bracket `0` is
`PSS.oper M 1`: pss-proof's `M[1]` drops the last column.  Its image `1`
lies many fundamental-sequence steps below `ε₀`.

This is not a corner case of the bracket `0`.  A numerical search over the
standard pair sequences of length at most `6` reached from `(0,0)(1,1)(2,2)`
finds many states `M` and brackets `n ∈ {1,2,3}` where `pairOrdTerm (M[n])` is
none of `fs X (idx X m)` for `m < 12`, for example
`(0,0)(1,1)(1,1)[2] ↦ ψ_0(Ω+ψ_0(Ω))`, while every `ψ_0(Ω+Ω)[m]` ends in
`ψ_0(Ω+1)`.  pss-proof itself relates `Trans (M[n])` to Buchholz's own
fundamental sequences only under the conditions (I)–(VI) of its §8, and under
condition (VI) `Trans (M[1])` can be `Trans M [0]` iterated `k ≥ 2` times.

Results:

* `fs_psiOmega1`: `fs (ψ_0(Ω_1)) Y = ψ_0(Z)` with `Z ≠ 0`, for every `Y`.
* `pairOrdTerm_gen1`, `pairOrdTerm_gen1_step0`: the two images above.
* `pairOrdTerm_step_ne_fs`: the image of `(0,0)(1,1)[1]` is no
  `fs (image of (0,0)(1,1)) Y`.

`pairOrdTerm_step_ne_fs` refutes the columns "preserves expansion" and
"commutes with expansion" of `pairToExbGoals` in `Googology/Goals.lean`: the
record's map `pairToExb` is `pairOrdTerm` on the first component, and the step
of its target `exbPair` is `fs X (idx X k)` on the first component.
-/

namespace Googology.Trans.PSS

open Googology.Trans.BMS (pairL PairState pairStd expand2L)
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- `Ω_1` as a term. -/
abbrev tOmega1 : Term := psi t1 nil

/-- `ψ_0(Ω_1)`, the term of `ε₀`. -/
abbrev tEps0 : Term := psi nil tOmega1

private theorem dom_t1 : dom t1 = t1 := by decide

/-- `Ω_1[Y] = Y`. -/
theorem fs_tOmega1 (Y : Term) : fs tOmega1 Y = Y := by
  rw [fs]
  simp only [dom_nil, if_true, dom_t1]
  exact if_neg (by decide)

/-- **Every member of the fundamental sequence of `ψ_0(Ω_1)` is `ψ_0(Z)` with
`Z ≠ 0`**, whatever the index. -/
theorem fs_psiOmega1 (Y : Term) : ∃ Z, Z ≠ nil ∧ fs tEps0 Y = psi nil Z := by
  rw [fs]
  have h1 : ¬ dom tOmega1 = nil := by decide
  have h2 : ¬ dom tOmega1 = t1 := by decide
  have h3 : ¬ dom tOmega1 = tw := by decide
  have h4 : ¬ dom tOmega1 < cons nil tOmega1 nil := by decide
  simp only [h1, h2, h3, h4, if_false, fs_tOmega1]
  split
  · split
    · split
      · exact ⟨_, fun h => Term.noConfusion h, rfl⟩
      · exact ⟨_, fun h => Term.noConfusion h, rfl⟩
    · exact ⟨_, fun h => Term.noConfusion h, rfl⟩
  · exact ⟨_, fun h => Term.noConfusion h, rfl⟩

/-- A member of the fundamental sequence of `ψ_0(Ω_1)` is never `1`. -/
theorem fs_psiOmega1_ne_t1 (Y : Term) : fs tEps0 Y ≠ t1 := by
  obtain ⟨Z, hZ, h⟩ := fs_psiOmega1 Y
  rw [h]
  intro h'
  injection h' with _ h''
  exact hZ h''

/-- The generator `(0,0)(1,1)`. -/
theorem pairStd_gen1 : (pairStd.gen 1).1 = [(0, 0), (1, 1)] := rfl

/-- `(0,0)(1,1)` goes to `ψ_0(Ω_1)`. -/
theorem pairOrdTerm_gen1 : pairOrdTerm [(0, 0), (1, 1)] = tEps0 := by decide

/-- The step of `pairL` at bracket `0` sends `(0,0)(1,1)` to `(0,0)`. -/
theorem expand2L_gen1 : expand2L 0 [(0, 0), (1, 1)] = [(0, 0)] := by decide +kernel

/-- `(0,0)` goes to `1`. -/
theorem pairOrdTerm_single : pairOrdTerm [(0, 0)] = t1 := by decide

/-- `(0,0)(1,1)[1]` goes to `1`. -/
theorem pairOrdTerm_gen1_step0 :
    pairOrdTerm (pairL.step (pairStd.gen 1) 0).1 = t1 := by
  show pairOrdTerm (expand2L 0 (pairStd.gen 1).1) = t1
  rw [pairStd_gen1, expand2L_gen1, pairOrdTerm_single]

/-- The generator `(0,0)(1,1)` is not halted. -/
theorem not_halted_gen1 : ¬ pairL.halted (pairStd.gen 1) := by
  show ¬ (pairStd.gen 1).1 = []
  rw [pairStd_gen1]
  exact List.cons_ne_nil _ _

/-- **One step of the pair sequences does not go to one step of extended
Buchholz's ψ.**  The step `(0,0)(1,1) → (0,0)` goes to `ψ_0(Ω_1) → 1`, and `1`
is `fs (ψ_0(Ω_1)) Y` for no index `Y`. -/
theorem pairOrdTerm_step_ne_fs (Y : Term) :
    pairOrdTerm (pairL.step (pairStd.gen 1) 0).1 ≠ fs (pairOrdTerm (pairStd.gen 1).1) Y := by
  rw [pairOrdTerm_gen1_step0, pairStd_gen1, pairOrdTerm_gen1]
  exact fun h => fs_psiOmega1_ne_t1 Y h.symm

end Googology.Trans.PSS
