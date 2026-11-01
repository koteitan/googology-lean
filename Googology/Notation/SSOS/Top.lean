import Googology.Notation.SSOS.Bridge
import Googology.Notation.SSOS.Standard

/-! Unconditional connection of the actual terms of `(0,0,2)` to the towers. -/

namespace Googology.Notation.SSOS

open Ordinal

theorem canonical_tower (n : ℕ) : Canonical (tower n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .block ih .nil trivial

theorem standard_encode_tower (n : ℕ) : Standard (encode (tower n)) := by
  simpa [encode, flat_tower] using Standard.tower n

theorem cut_top : Seq.cut [0,0,2] = 2 := by decide +kernel

theorem fs_top (k : ℕ) : Seq.fs [0,0,2] k = encode (tower k) := by
  have h := Seq.fs_of_cut [0,0] [] 1 k cut_top
  simpa [encode, flat_tower, copies, List.flatten_replicate_singleton] using h

theorem fs_top_lt_epsilon (k : ℕ) :
    ∃ t, Seq.fs [0,0,2] k = encode t ∧ treeOrdinal t < ε₀ := by
  exact ⟨tower k, fs_top k, tower_lt_epsilon k⟩

theorem fs_top_cof_epsilon (β : Ordinal.{0}) (hβ : β < ε₀) :
    ∃ k, 1 ≤ k ∧ ∃ t, Seq.fs [0,0,2] k = encode t ∧ β < treeOrdinal t := by
  obtain ⟨n, hn⟩ := tower_cof_epsilon (max β 2) (max_lt hβ (by
    simpa using Ordinal.natCast_lt_epsilon 2 0))
  have hn' : n ≠ 0 := by
    intro hz
    subst n
    simpa [tower] using (lt_of_le_of_lt (le_max_right β 2) hn)
  exact ⟨n, by omega, tower n, fs_top n, lt_of_le_of_lt (le_max_left β 2) hn⟩

end Googology.Notation.SSOS
