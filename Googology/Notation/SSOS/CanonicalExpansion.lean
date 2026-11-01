import Googology.Notation.SSOS.Expansion

/-! Canonical block boundaries survive the tree expansion, even off standard forms. -/

namespace Googology.Notation.SSOS

theorem canonical_zeros_append (k : ℕ) (P : List U) (hP : Canonical P) :
    Canonical (List.replicate k U.z ++ P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih => simpa [List.replicate_succ] using Canonical.zero ih

theorem canonical_repeatBlock (r P : List U) (hr : Canonical r)
    (hP : Canonical P) (hg : BlockGap P) (k : ℕ) :
    Canonical ((List.replicate k [U.z, U.z, U.b r]).flatten ++ P) ∧
    BlockGap ((List.replicate k [U.z, U.z, U.b r]).flatten ++ P) := by
  induction k with
  | zero => simpa using And.intro hP hg
  | succ k ih =>
    simpa [List.replicate_succ, List.append_assoc, BlockGap] using
      And.intro (Canonical.zero (.zero (.block hr ih.1 ih.2)))
        (show BlockGap (.z :: .z :: .b r ::
          ((List.replicate k [U.z, U.z, U.b r]).flatten ++ P)) from trivial)

theorem canonical_H_append (u P : List U) (hc : Canonical (.b u :: P))
    (k : ℕ) (hk : 1 ≤ k) : Canonical (H u k ++ P) := by
  have hu : Canonical u := by cases hc; assumption
  have hP : Canonical P := by cases hc; assumption
  have hg : BlockGap P := by cases hc; assumption
  match u with
  | [] => simpa [H] using canonical_zeros_append k P hP
  | .z :: r =>
    have hr : Canonical r := by cases hu; assumption
    simpa [H] using (canonical_repeatBlock r P hr hP hg k).1
  | .b w :: r =>
    have hi := canonical_H_append w r hu k hk
    obtain ⟨t, ht⟩ := H_head w k hk
    rw [ht] at hi
    have hit : Canonical (t ++ r) := by cases hi; assumption
    simpa [H, ht] using Canonical.zero (.block hit hP hg)
termination_by sizeOf u
decreasing_by simp_wf; omega

theorem canonical_E (u P : List U) (hc : Canonical (.b u :: P))
    (k : ℕ) (hk : 1 ≤ k) : Canonical (E (.b u :: P) k) :=
  canonical_H_append u P hc k hk

end Googology.Notation.SSOS
