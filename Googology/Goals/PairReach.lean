import Googology.Goals
import Googology.Trans.PSS.Steps

/-!
# Pair sequences → extended Buchholz's ψ: reachability

`Goals.lean` refutes that `pairToExb` preserves one expansion step
(`pairToExb_not_preserves`).  This file proves the weaker statement that holds:
one step goes to one or more steps of `exbPair`, and more precisely `pairToExb`
preserves and reflects the transitive closure of the step relation.

* `exbPair_transGen_iff`: `B` is reached from `A` in `exbPair` iff `B < A`.
* `pairToExb_transGen_iff`: `pairToExb b` is reached from `pairToExb a` iff `b`
  is reached from `a`.
* `pairToExb_preserves_transGen`: `pairL.Rel b a → TransGen exbPair.Rel
  (pairToExb b) (pairToExb a)`.

The term-level results are in `Trans/PSS/Steps.lean`.
-/

namespace Googology.Goals
open Googology.Trans.BMS Googology.Trans.PSS Googology.Notation.ExBuchholz Googology.Notation.ExBuchholz.Term
open Relation

/-- One step of `exbPair` is one step of `exbOT` on the underlying term. -/
theorem exbPair_rel_map {A B : exbPair.State} (h : exbPair.Rel B A) :
    exbOT.Rel (exbPairHom.map B) (exbPairHom.map A) := by
  obtain ⟨hne, n, rfl⟩ := h
  exact ⟨hne, n, rfl⟩

/-- Below a state of `exbPair`, everything standard is reached from it. -/
theorem exbPair_transGen_of_lt : ∀ A B : exbPair.State, B.1 < A.1 → TransGen exbPair.Rel B A := by
  intro A
  induction A using WellFounded.induction exbPair_wf with
  | _ A ih =>
    intro B hBA
    have hne : A.1 ≠ nil := fun h => not_lt_nil _ (h ▸ hBA)
    obtain ⟨n, hn⟩ :=
      exists_le_fs_idx A.2.1 (lt_tW_of_lt_psiOmegaOmega A.2.2) hne B.2.1 hBA
    have hrel : exbPair.Rel (exbPair.step A n) A := ⟨hne, n, rfl⟩
    rcases le_iff_lt_or_eq.mp hn with h | h
    · exact TransGen.tail (ih _ hrel B h) hrel
    · rw [show B = exbPair.step A n from Subtype.ext h]
      exact TransGen.single hrel

/-- In `exbPair`, `B` is reached from `A` by one or more steps exactly when `B < A`. -/
theorem exbPair_transGen_iff (A B : exbPair.State) :
    TransGen exbPair.Rel B A ↔ B.1 < A.1 :=
  ⟨fun h => (exbOT_transGen_iff _ _).mp (TransGen.lift exbPairHom.map (fun _ _ => exbPair_rel_map) h),
   exbPair_transGen_of_lt A B⟩

/-- **Pair sequences → extended Buchholz's ψ preserves and reflects reachability**:
`pairToExb b` is reached from `pairToExb a` by one or more steps exactly when `b`
is reached from `a` by one or more expansions. -/
theorem pairToExb_transGen_iff (a b : PairState) :
    TransGen exbPair.Rel (pairToExb b) (pairToExb a) ↔ TransGen pairL.Rel b a := by
  rw [exbPair_transGen_iff, pairL_transGen_iff]
  exact pairToExbOT_lt_iff a b

/-- **One step of the pair sequences goes to finitely many (≥ 1) steps of `exbPair`.** -/
theorem pairToExb_preserves_transGen {a b : PairState} (h : pairL.Rel b a) :
    TransGen exbPair.Rel (pairToExb b) (pairToExb a) :=
  (pairToExb_transGen_iff a b).mpr (TransGen.single h)

end Googology.Goals
