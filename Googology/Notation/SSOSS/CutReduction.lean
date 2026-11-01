import Googology.Notation.SSOSS.BinarySearch
import Googology.Notation.SSOSS.Bridge

/-!
An exact combinatorial replacement for CutCorrect. The right-hand side
contains only a finite search on zeros, run lengths, suffix order, and the
tree cut. No standardness or unproved cut assumption is used.
-/

namespace Googology.Notation.SSOSS

theorem binary_raiseBits (s : List ℕ) : Binary (raiseBits s) := by
  intro n hn
  simp only [raiseBits, List.mem_cons, List.mem_flatMap] at hn
  rcases hn with rfl | ⟨a, _, hn⟩
  · simp
  · unfold raiseBit at hn
    split at hn <;> simp_all

theorem binary_flat (t : List U) : Binary (flat t) := by
  induction t with
  | nil => intro n hn; simp at hn
  | cons x P ih =>
    cases x with
    | z =>
      intro n hn
      simp only [flat_z, List.mem_append, List.mem_singleton] at hn
      rcases hn with hn | rfl
      · exact ih n hn
      · simp
    | b u =>
      intro n hn
      simp only [flat_b, List.mem_append] at hn
      rcases hn with hn | hn
      · exact ih n hn
      · exact binary_raiseBits (flat u) n hn

theorem binaryLimit_encode_block (u P : List U) : BinaryLimit (encode (.b u :: P)) := by
  refine ⟨?_, ⟨flat (.b u :: P), rfl⟩, ?_⟩
  · intro n hn
    simp only [encode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with (rfl | rfl) | hn
    · simp
    · simp
    · exact binary_flat (.b u :: P) n hn
  · rw [encode_parts u P, Seq.entry_append_last]

theorem cutCorrect_iff_shortZero_argmax (u P : List U) :
    CutCorrect u P ↔
      Seq.IsZeroArgmax (encode (.b u :: P)) (Seq.shortZero (encode (.b u :: P)))
        (encode P ++ (parts u).1).length :=
  Seq.cut_eq_iff_shortZero_argmax _ (binaryLimit_encode_block u P) _

end Googology.Notation.SSOSS
