import Googology.Notation.SSOSS.Def
import Googology.Notation.SSOSS.Expansion

/-!
The bridge is reduced to a single, k-independent cut equality.
`CutCorrect` is NOT a definition of standard form: proving it for canonical
trees encoding reachable standard forms is the remaining search-theoretic
obligation. Canonicality matters because `flat` is not injective on all trees.
-/

namespace Googology.Notation.SSOSS

namespace Seq

@[simp] theorem entry_append_last (S : Sequence) (a : ℕ) :
    entry (S ++ [a]) (S ++ [a]).length = a := by
  simp [entry]

theorem fs_append_zero (S : Sequence) (k : ℕ) : fs (S ++ [0]) k = S := by
  unfold fs
  rw [entry_append_last]
  simp

theorem fs_of_cut (G B : Sequence) (a k : ℕ)
    (hc : cut (G ++ B ++ [a + 1]) = G.length) :
    fs (G ++ B ++ [a + 1]) k = G ++ copies (B ++ [a]) k := by
  unfold fs
  rw [entry_append_last]
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  unfold good bad
  rw [hc, entry_append_last]
  simp [copies]

end Seq

/-- A concrete search computation to prove for each canonical terminal block. -/
def CutCorrect (u P : List U) : Prop :=
  Seq.cut (encode (.b u :: P)) = (encode P ++ (parts u).1).length

theorem fs_encode (u P : List U) (hc : CutCorrect u P) (k : ℕ) (hk : 1 ≤ k) :
    Seq.fs (encode (.b u :: P)) k = encode (E (.b u :: P) k) := by
  unfold CutCorrect at hc
  rw [encode_E_parts u P k hk]
  have hs := encode_parts u P
  have hcut : Seq.cut ((encode P ++ (parts u).1) ++ (parts u).2 ++ [0 + 1]) =
      (encode P ++ (parts u).1).length := by
    simpa only [← hs] using (hc : Seq.cut (encode (.b u :: P)) = _)
  rw [hs]
  exact Seq.fs_of_cut _ _ 0 k hcut

theorem fs_encode_z (P : List U) (k : ℕ) :
    Seq.fs (encode (.z :: P)) k = encode P := by
  rw [encode_z, Seq.fs_append_zero]

/-- The value of an encoded tree. No inverse parser or uniqueness is assumed. -/
noncomputable def treeOrdinal (t : List U) : Ordinal.{0} := 2 + vs t

theorem treeOrdinal_z (t : List U) : treeOrdinal (.z :: t) = treeOrdinal t + 1 := by
  simp [treeOrdinal, add_assoc]

theorem treeOrdinal_E_lt (u P : List U) (k : ℕ) (hk : 1 ≤ k) :
    treeOrdinal (E (.b u :: P) k) < treeOrdinal (.b u :: P) := by
  exact (add_lt_add_iff_left 2).2 (E_lt u P k hk)

theorem treeOrdinal_E_cof (u P : List U) (β : Ordinal.{0})
    (hβ : β < treeOrdinal (.b u :: P)) :
    ∃ k, 1 ≤ k ∧ β < treeOrdinal (E (.b u :: P) k) := by
  obtain ⟨δ, hδ, hβδ⟩ :=
    (Ordinal.lt_add_iff (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)).1
      (show β < (2 + vs P) + Ordinal.omega0 ^ (1 + vs u) by
        simpa [treeOrdinal, add_assoc] using hβ)
  obtain ⟨k, hk, hδk⟩ := (H_spec u).2 δ hδ
  refine ⟨k, hk, ?_⟩
  simp only [treeOrdinal, E, vs_append]
  exact hβδ.trans_lt (by simpa [add_assoc] using
    (add_lt_add_iff_left (2 + vs P)).2 hδk)

/-- Strict decrease and cofinality for the *actual* fs, given cut correctness. -/
theorem fs_encode_spec (u P : List U) (hc : CutCorrect u P) :
    (∀ k, 1 ≤ k → ∃ t, Seq.fs (encode (.b u :: P)) k = encode t ∧
      treeOrdinal t < treeOrdinal (.b u :: P)) ∧
    (∀ β < treeOrdinal (.b u :: P), ∃ k, 1 ≤ k ∧ ∃ t,
      Seq.fs (encode (.b u :: P)) k = encode t ∧ β < treeOrdinal t) := by
  constructor
  · intro k hk
    exact ⟨E (.b u :: P) k, fs_encode u P hc k hk, treeOrdinal_E_lt u P k hk⟩
  · intro β hβ
    obtain ⟨k, hk, h⟩ := treeOrdinal_E_cof u P β hβ
    exact ⟨k, hk, E (.b u :: P) k, fs_encode u P hc k hk, h⟩

end Googology.Notation.SSOSS
