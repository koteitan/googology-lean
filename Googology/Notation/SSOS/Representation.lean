import Googology.Notation.SSOS.Parse
import Googology.Notation.SSOS.Standard

/-! Binary preservation and the precise domain of the representation theorem. -/

namespace Googology.Notation.SSOS

theorem binary_iff_le_one (S : List ℕ) : Binary S ↔ ∀ n ∈ S, n ≤ 1 := by
  constructor <;> intro h n hn <;> specialize h n hn <;> omega

theorem binary_entry (S : List ℕ) (hS : Binary S) (i : ℕ) : Seq.entry S i ≤ 1 := by
  unfold Seq.entry
  cases h : S[i - 1]? with
  | none => simp
  | some n =>
    simp only [Option.getD_some]
    exact (binary_iff_le_one S).1 hS n (List.mem_of_getElem? h)

theorem binary_fs (S : List ℕ) (hS : Binary S) (k : ℕ) : Binary (Seq.fs S k) := by
  rw [binary_iff_le_one] at hS ⊢
  have he := binary_entry S ((binary_iff_le_one S).2 hS) S.length
  intro n hn
  unfold Seq.fs at hn
  split at hn
  · simp at hn
  · split at hn
    · exact hS n (List.mem_of_mem_dropLast hn)
    · simp only [List.mem_append, List.mem_flatten, List.mem_replicate] at hn
      rcases hn with hgood | ⟨B, ⟨_, rfl⟩, hn⟩
      · exact hS n (List.mem_of_mem_take hgood)
      · unfold Seq.bad at hn
        simp only [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact hS n (List.mem_of_mem_dropLast (List.mem_of_mem_drop hn))
        · omega

theorem standard_binary {S : List ℕ} (hs : Standard S) : Binary S := by
  induction hs with
  | tower n =>
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at ha
    rcases ha with (rfl | rfl) | ⟨_, rfl⟩ <;> simp
  | expand _ _ k _ ih => exact binary_fs _ ih k
  | erase _ ih => exact fun n hn => ih n (List.mem_append_left _ hn)

theorem standard_nil : Standard [] :=
  Standard.erase (S := []) (Standard.erase (S := [0]) (Standard.tower 0))

theorem no_encode_nil : ¬∃ t, encode t = [] := by
  rintro ⟨t, ht⟩
  simp [encode] at ht

/-- The unqualified existence goal is false: Standard includes the empty sequence. -/
theorem not_unrestricted_standard_encode :
    ¬(∀ S, Standard S → ∃ t, Canonical t ∧ encode t = S) := by
  intro h
  obtain ⟨t, _, ht⟩ := h [] standard_nil
  exact no_encode_nil ⟨t, ht⟩

/-- Corrected existence goal: the (0,0)-fragment, not the erased short sequences. -/
theorem standard_encode {Y : List ℕ} (hs : Standard ([0,0] ++ Y)) :
    ∃ t, Canonical t ∧ encode t = [0,0] ++ Y := by
  apply binary_encode_exists
  exact fun n hn => standard_binary hs n (List.mem_append_right _ hn)

end Googology.Notation.SSOS
