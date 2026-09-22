import Googology.Core
import Googology.Rank
import Pattern.Main

/-!
# Bashicu matrices as an expansion system

`BM4.Arr r` is an array with `r` rows, `BM4.expand` is one bracket expansion,
and `Pat.Std r` says an array is reachable from some
`(0,…,0)(1,…,1)⋯(n,…,n)`.  The termination proof, by labels in `R_r` and
Σ-elementary substructures, is in koteitan/bms-elem-pattern; what this file
does is present it as a `Rewrite` so that `Googology.Core` applies.

The fit is exact: `Pat.StdR` is already `Rewrite.Rel` written out by hand.
-/

namespace Googology.Notation.BMS

open BM4 Pat

/-- Bashicu matrices with `r` rows, as an expansion system.  Standardness is
carried by the state type, so `Rewrite.Std` below has nothing left to say. -/
noncomputable def bms (r : ℕ) : Rewrite where
  State := StdElt r
  step := fun A k => ⟨expand A.1 k, Std.step k A.2⟩
  halted := fun A => A.1.len = 0

@[simp] theorem bms_step_val (r : ℕ) (A : StdElt r) (k : ℕ) :
    ((bms r).step A k).1 = expand A.1 k := rfl

@[simp] theorem bms_halted_iff (r : ℕ) (A : StdElt r) :
    (bms r).halted A ↔ A.1.len = 0 := Iff.rfl

/-- The one-step relation of the expansion system is exactly the relation the
termination proof is about. -/
theorem bms_Rel_iff {r : ℕ} {A B : StdElt r} : (bms r).Rel A B ↔ StdR r A B := by
  constructor
  · rintro ⟨h0, k, hk⟩
    exact ⟨Nat.pos_of_ne_zero h0, k, by rw [hk]; rfl⟩
  · rintro ⟨h0, k, hk⟩
    exact ⟨Nat.pos_iff_ne_zero.mp h0, k, Subtype.ext hk⟩

/-- **One-step expansion is well founded.** -/
theorem bms_wf (r : ℕ) : (bms r).WF :=
  Subrelation.wf (fun {_ _} h => bms_Rel_iff.mp h) (StdR_wf r)

/-- **Bashicu matrices terminate, for every number of rows.**  Supplied by
`Rewrite.terminates_of_wf`; nothing about termination is proved here. -/
theorem bms_terminates (r : ℕ) : (bms r).Terminates :=
  (bms r).terminates_of_wf (bms_wf r)

/-- The generators `(0,…,0)(1,…,1)⋯(n,…,n)`. -/
def bmsStd (r : ℕ) : (bms r).Std where
  Standard := fun _ => True
  gen := fun n => ⟨stair r n, Std.init n⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-- Primitive sequences. -/
theorem primitive_terminates : (bms 1).Terminates := bms_terminates 1
/-- Pair sequences. -/
theorem pair_terminates : (bms 2).Terminates := bms_terminates 2
/-- Trio sequences. -/
theorem trio_terminates : (bms 3).Terminates := bms_terminates 3

/-- Bashicu matrices carry an ordinal measure: the rank of one-step expansion.
It decreases strictly at every step, for every number of rows. -/
noncomputable def bmsEval (r : ℕ) :
    Eval (bms r) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (bms_wf r)

example (r : ℕ) : (bms r).Terminates := (bmsEval r).terminates Ordinal.lt_wf

end Googology.Notation.BMS
