import Googology.Goals.PairReach
import Googology.Trans.PSS.StepBound

/-!
# Pair sequences → extended Buchholz's ψ: the number of steps has no bound

`PairReach.lean` proves that one expansion step of the pair sequences goes to
one or more steps of `exbPair` (`pairToExb_preserves_transGen`).  This file
proves that the number of those steps is not bounded.

"`B` is reached from `A` in exactly `m` steps" is
`Trans.PSS.StepBound.Steps exbPair.Rel m A B`, defined by recursion on `m`
(`Steps r 0 a b ↔ a = b`, `Steps r (m+1) a b ↔ ∃ c, r c a ∧ Steps r m c b`).
It is the `m`-th power of the one-step relation,
`(Relation.Comp (flip exbPair.Rel))^[m] Eq` (`steps_iff_iterate`); the second
statement below uses that form.

* `pairToExb_steps_ge`: from `famA p n = (0,0)(1,1)⋯(p,p)(p+1,p)⋯` to
  `famB p n` (its last column dropped, one step), every chain of `exbPair`
  steps has at least `p + 1` steps.
* `pairToExb_min_steps`: at `n = 0` the least number is exactly `p + 1`.
* `pairToExb_steps_unbounded`, `pairToExb_steps_unbounded_iterate`:
  `¬ ∃ K, ∀ a b, pairL.Rel b a → ∃ m ≤ K, (m steps from pairToExb a to pairToExb b)`.

The proofs are in `Trans/PSS/StepBound.lean`, on `exbOT`; this file carries
them to `exbPair`, whose steps are those of `exbOT` on the same terms.
-/

namespace Googology.Goals
open Googology.Trans.BMS Googology.Trans.PSS Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.PSS.StepBound (Steps steps_iff_iterate famA famB famB_rel
  famA_famB_steps_ge famA_famB_steps)

/-- A chain of `exbPair` steps is a chain of `exbOT` steps on the same terms. -/
theorem steps_exbPair_map : ∀ (m : ℕ) (A B : exbPair.State),
    Steps exbPair.Rel m A B → Steps exbOT.Rel m (exbPairHom.map A) (exbPairHom.map B)
  | 0, _, _, h => congrArg exbPairHom.map h
  | m + 1, _, _, ⟨C, hC, h⟩ => ⟨_, exbPair_rel_map hC, steps_exbPair_map m C _ h⟩

/-- And back: the states of `exbOT` below `ψ_0(Ω_ω)` are those of `exbPair`. -/
theorem steps_exbOT_lift : ∀ (m : ℕ) (A : exbPair.State) (B : exbPair.State),
    Steps exbOT.Rel m (exbPairHom.map A) (exbPairHom.map B) → Steps exbPair.Rel m A B
  | 0, A, B, h => by
    have h' : exbPairHom.map A = exbPairHom.map B := h
    exact Subtype.ext (show A.1 = B.1 from congrArg (fun x : exbOT.State => x.1) h')
  | m + 1, A, B, ⟨_, ⟨hne, k, rfl⟩, h⟩ =>
    ⟨exbPair.step A k, ⟨hne, k, rfl⟩, steps_exbOT_lift m _ B h⟩

theorem exbPairHom_map_pairToExb (a : PairState) : exbPairHom.map (pairToExb a) = pairToExbOT a :=
  rfl

/-- **Every chain of `exbPair` steps from `pairToExb (famA p n)` to
`pairToExb (famB p n)` has at least `p + 1` steps**, although `famB p n` is one
expansion step from `famA p n`. -/
theorem pairToExb_steps_ge {p : ℕ} (hp : 0 < p) (n m : ℕ)
    (h : Steps exbPair.Rel m (pairToExb (famA p n)) (pairToExb (famB p n))) : p + 1 ≤ m :=
  famA_famB_steps_ge hp n m (steps_exbPair_map m _ _ h)

/-- **The least number is exactly `p + 1`** at `n = 0`:
`(0,0)(1,1)⋯(p,p)(p+1,p) → (0,0)(1,1)⋯(p,p)` goes to
`ψ_0(ψ_p(ψ_p(0))) → ⋯ → ψ_0(ψ_p(0))` in `p + 1` steps and no fewer. -/
theorem pairToExb_min_steps {p : ℕ} (hp : 0 < p) :
    pairL.Rel (famB p 0) (famA p 0) ∧
    Steps exbPair.Rel (p + 1) (pairToExb (famA p 0)) (pairToExb (famB p 0)) ∧
    ∀ m, Steps exbPair.Rel m (pairToExb (famA p 0)) (pairToExb (famB p 0)) → p + 1 ≤ m :=
  ⟨famB_rel hp 0, steps_exbOT_lift _ _ _ (famA_famB_steps hp), pairToExb_steps_ge hp 0⟩

/-- **Pair sequences → extended Buchholz's ψ: the number of ψ steps for one
step has no bound.** -/
theorem pairToExb_steps_unbounded :
    ¬ ∃ K : ℕ, ∀ a b : PairState, pairL.Rel b a →
      ∃ m ≤ K, Steps exbPair.Rel m (pairToExb a) (pairToExb b) := by
  rintro ⟨K, hK⟩
  obtain ⟨m, hmK, hm⟩ := hK _ _ (famB_rel (Nat.succ_pos K) 0)
  have := pairToExb_steps_ge (Nat.succ_pos K) 0 m hm
  omega

/-- The same with the `m`-th power of the step relation written as
`Nat.iterate` of `Relation.Comp`. -/
theorem pairToExb_steps_unbounded_iterate :
    ¬ ∃ K : ℕ, ∀ a b : PairState, pairL.Rel b a →
      ∃ m ≤ K, (Relation.Comp (flip exbPair.Rel))^[m] Eq (pairToExb a) (pairToExb b) := by
  rintro ⟨K, hK⟩
  refine pairToExb_steps_unbounded ⟨K, fun a b h => ?_⟩
  obtain ⟨m, hmK, hm⟩ := hK a b h
  exact ⟨m, hmK, (steps_iff_iterate _ m _ _).mpr hm⟩

end Googology.Goals
