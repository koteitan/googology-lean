import Googology.Notation.SSOSS.Flat

/-!
The tree's cut, independently of the searches in `Seq`.
`parts u = (g,b)` means that the original block is `g ++ b ++ [1]`
and its expansion is `g ++ (b ++ [0])^k`.
These identities hold for every tree, even noncanonical ones.
-/

namespace Googology.Notation.SSOSS

def copies (s : List ℕ) (k : ℕ) : List ℕ := (List.replicate k s).flatten

theorem liftBits_copies (s : List ℕ) (k : ℕ) :
    liftBits (copies s k) = copies (liftBits s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [copies, List.replicate_succ, List.flatten_cons, liftBits_append] at *
    rw [ih]

def parts : List U → List ℕ × List ℕ
  | [] => ([], [])
  | .z :: rest => ([], raiseBits (flat rest) ++ [0])
  | .b w :: rest =>
    (liftBits (flat rest) ++ liftBits (parts w).1, liftBits (parts w).2 ++ [1])
termination_by u => sizeOf u
decreasing_by simp_wf; omega

theorem parts_original (u : List U) :
    raiseBits (flat u) = (parts u).1 ++ (parts u).2 ++ [1] := by
  match u with
  | [] => simp [parts, raiseBits]
  | .z :: rest =>
    simp [parts, raiseBits_eq, List.append_assoc]
  | .b w :: rest =>
    have ih := parts_original w
    rw [flat_b, raiseBits_eq, liftBits_append, ih]
    simp [parts, List.append_assoc]
termination_by sizeOf u
decreasing_by simp_wf; omega

theorem flat_H_parts (u : List U) (k : ℕ) (hk : 1 ≤ k) :
    flat (H u k) = (parts u).1 ++ copies ((parts u).2 ++ [0]) k := by
  match u with
  | [] =>
    simp [H, parts, flat_replicate_z, copies, List.flatten_replicate_singleton]
  | .z :: rest =>
    simp [H, parts, flat_flatten_replicate, copies, List.append_assoc]
  | .b w :: rest =>
    have ih := flat_H_parts w k hk
    obtain ⟨t, ht⟩ := H_head w k hk
    have hflat : flat t ++ [0] = (parts w).1 ++ copies ((parts w).2 ++ [0]) k := by
      simpa [ht] using ih
    have hlift := congrArg liftBits hflat
    simp only [liftBits_append, liftBits_zero, liftBits_copies] at hlift
    simp only [H, ht, List.tail_cons, flat_z, flat_b, flat_nil, List.nil_append,
      flat_append, raiseBits_eq, liftBits_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hlift ⊢
    rw [hlift]
    simp [parts, List.append_assoc]
termination_by sizeOf u
decreasing_by simp_wf; omega

theorem encode_parts (u P : List U) :
    encode (.b u :: P) = (encode P ++ (parts u).1) ++ (parts u).2 ++ [1] := by
  simp [encode, parts_original, List.append_assoc]

theorem encode_E_parts (u P : List U) (k : ℕ) (hk : 1 ≤ k) :
    encode (E (.b u :: P) k) =
      (encode P ++ (parts u).1) ++ copies ((parts u).2 ++ [0]) k := by
  simp [encode, E, flat_append, flat_H_parts u k hk, List.append_assoc]

end Googology.Notation.SSOSS
