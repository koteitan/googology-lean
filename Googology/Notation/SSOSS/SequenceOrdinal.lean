import Googology.Notation.SSOSS.Representation
import Googology.Notation.SSOSS.Bridge
import Googology.Notation.SSOSS.CanonicalExpansion
import Googology.Notation.SSOSS.Top

/-!
A value for the binary (0,0)-fragment, with uniqueness and the successor
equation unconditional. Limit equations explicitly assume CutCorrect.
The short erased sequences have values 0 and 1. The definition is total,
but no meaning is assigned to its values outside this fragment. In
particular, `o_fs_top_sup` describes (0,0,2) via its binary terms, not o [0,0,2].
-/

namespace Googology.Notation.SSOSS

noncomputable def o (S : List ℕ) : Ordinal.{0} :=
  if S.length < 2 then S.length else treeOrdinal (parse (S.drop 2))

theorem o_encode (t : List U) (hc : Canonical t) : o (encode t) = treeOrdinal t := by
  simp [o, encode, parse_flat t hc]

theorem value_independent {t t' : List U} (hc : Canonical t) (hc' : Canonical t')
    (h : encode t = encode t') : treeOrdinal t = treeOrdinal t' := by
  rw [encode_injective hc hc' h]

theorem o_append_zero (S : List ℕ) : o (S ++ [0]) = o S + 1 := by
  cases S with
  | nil => simp [o]
  | cons a S => cases S with
    | nil =>
      simp [o, treeOrdinal]
      exact_mod_cast (show (2 : ℕ) = 1 + 1 from rfl)
    | cons b S => simp [o, parse_append_zero, treeOrdinal_z]

theorem o_fs_lt_of_cutCorrect (u P : List U) (hc : Canonical (.b u :: P))
    (hcut : CutCorrect u P) (k : ℕ) (hk : 1 ≤ k) :
    o (Seq.fs (encode (.b u :: P)) k) < o (encode (.b u :: P)) := by
  rw [fs_encode u P hcut k hk, o_encode _ (canonical_E u P hc k hk), o_encode _ hc]
  exact treeOrdinal_E_lt u P k hk

theorem o_fs_cof_of_cutCorrect (u P : List U) (hc : Canonical (.b u :: P))
    (hcut : CutCorrect u P) (β : Ordinal.{0}) (hβ : β < o (encode (.b u :: P))) :
    ∃ k, 1 ≤ k ∧ β < o (Seq.fs (encode (.b u :: P)) k) := by
  rw [o_encode _ hc] at hβ
  obtain ⟨k, hk, h⟩ := treeOrdinal_E_cof u P β hβ
  exact ⟨k, hk, by
    rw [fs_encode u P hcut k hk, o_encode _ (canonical_E u P hc k hk)]
    exact h⟩

theorem o_fs_sup_of_cutCorrect (u P : List U) (hc : Canonical (.b u :: P))
    (hcut : CutCorrect u P) :
    o (encode (.b u :: P)) = ⨆ n : ℕ, o (Seq.fs (encode (.b u :: P)) (n + 1)) := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨k, hk, h⟩ := o_fs_cof_of_cutCorrect u P hc hcut _ (lt_of_not_ge hn)
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact (not_lt_of_ge (Ordinal.le_iSup (fun n : ℕ =>
      o (Seq.fs (encode (.b u :: P)) (n + 1))) n)) h
  · exact Ordinal.iSup_le fun n => (o_fs_lt_of_cutCorrect u P hc hcut (n+1) (by omega)).le

open Ordinal in
theorem o_fs_top_sup : (⨆ n : ℕ, o (Seq.fs [0,0,2] (n+1))) = ε₀ := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro n
    rw [fs_top, o_encode _ (canonical_tower _)]
    exact (tower_lt_epsilon _).le
  · by_contra hn
    let β := ⨆ n : ℕ, o (Seq.fs [0,0,2] (n+1))
    obtain ⟨k, hk⟩ := tower_cof_epsilon (max β 2)
      (max_lt (lt_of_not_ge hn) (by simpa using natCast_lt_epsilon 2 0))
    have hk0 : k ≠ 0 := by
      intro h0
      subst k
      simpa [tower] using (lt_of_le_of_lt (le_max_right β 2) hk)
    have hβ' : β < treeOrdinal (tower k) := lt_of_le_of_lt (le_max_left β 2) hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
    have hle := Ordinal.le_iSup (fun n : ℕ => o (Seq.fs [0,0,2] (n+1))) n
    rw [fs_top, o_encode _ (canonical_tower _)] at hle
    exact (not_lt_of_ge hle) hβ'

end Googology.Notation.SSOSS
