import Googology.Notation.SSOSS.Shape
import Googology.Notation.SSOSS.Expansion

/-! Preservation of the candidate tree shape. No cut correctness is assumed. -/

namespace Googology.Notation.SSOSS

theorem lex_le_append (s t : List ℕ) : s ≤ s ++ t := by
  cases t with
  | nil => simp
  | cons a t =>
    have h : s < s ++ a :: t := by
      simpa using List.Lex.append_left (· < ·)
        (show List.Lex (· < ·) ([] : List ℕ) (a :: t) from .nil) s
    exact h.le

theorem flat_H_lt_block (u : List U) (k : ℕ) (hk : 1 ≤ k) :
    flat (H u k) < raiseBits (flat u) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
  rw [flat_H_parts u (n+1) (by omega), parts_original]
  simp only [copies, List.replicate_succ, List.flatten_cons, List.append_assoc]
  apply List.Lex.append_left
  apply List.Lex.append_left
  exact List.Lex.rel (by decide)

theorem StdShape.child {u P : List U} (h : StdShape (.b u :: P)) : StdShape u := by
  cases h <;> assumption

theorem StdShape.drop_block {u P : List U} (h : StdShape (.b u :: P)) : StdShape P := by
  cases h with
  | single _ => exact .nil
  | next _ hp _ => exact .zero (.zero hp)

theorem StdShape.block_le_flat {t : List U} (h : StdShape t) :
    ∀ u, U.b u ∈ t → raiseBits (flat u) ≤ flat t := by
  induction h with
  | nil => simp
  | @zero t ht ih =>
    intro u hm
    have hm' : U.b u ∈ t := by simpa using hm
    exact (ih u hm').trans (by simpa using lex_le_append (flat t) [0])
  | @single v hv ih =>
    intro u hm
    have hu : u = v := by simpa using hm
    subst u
    simp
  | @next u v P hu hP hcmp ihu ihP =>
    intro w hm
    have hm' : w = u ∨ U.b w ∈ (.b v :: P) := by simpa using hm
    have he : flat (.b u :: .z :: .z :: .b v :: P) =
        flat (.b v :: P) ++ ([0,0] ++ raiseBits (flat u)) := by
      simp [List.append_assoc]
    rw [he]
    rcases hm' with rfl | hm'
    · exact (hcmp.trans (ihP v (by simp))).trans (lex_le_append _ _)
    · exact (ihP w hm').trans (lex_le_append _ _)

/-- Attach a replacement forest whose blocks are bounded by the removed block. -/
theorem StdShape.attach {t : List U} (ht : StdShape t) (u P : List U)
    (hP : StdShape (.b u :: P))
    (hb : ∀ w, U.b w ∈ t → raiseBits (flat w) ≤ raiseBits (flat u)) :
    StdShape (t ++ P) := by
  induction ht generalizing u P with
  | nil => simpa using hP.drop_block
  | @zero t ht ih =>
    exact .zero (ih u P hP (fun w hm => hb w (List.mem_cons_of_mem _ hm)))
  | @single w hw ih =>
    have hwu := hb w (by simp)
    cases hP with
    | single _ => simpa using StdShape.single hw
    | next _ hp hcmp => simpa using StdShape.next hw hp (hwu.trans hcmp)
  | @next w v Q hw hQ hcmp ihw ihQ =>
    have hnew := ihQ u P hP (fun a ha => hb a (by simp [ha]))
    simpa using StdShape.next hw hnew hcmp

theorem StdShape.zeros (k : ℕ) : StdShape (List.replicate k U.z) := by
  induction k with
  | zero => exact .nil
  | succ k ih => simpa [List.replicate_succ] using StdShape.zero ih

theorem StdShape.repeatBlockTail (u : List U) (hu : StdShape u) (k : ℕ) :
    StdShape (.b u :: (List.replicate k [U.z, U.z, U.b u]).flatten) := by
  induction k with
  | zero => simpa using StdShape.single hu
  | succ k ih => simpa [List.replicate_succ] using StdShape.next hu ih le_rfl

theorem StdShape.repeatBlock (u : List U) (hu : StdShape u) (k : ℕ) :
    StdShape (List.replicate k [U.z, U.z, U.b u]).flatten := by
  cases k with
  | zero => exact .nil
  | succ k =>
    simpa [List.replicate_succ] using StdShape.zero
      (StdShape.zero (StdShape.repeatBlockTail u hu k))

theorem StdShape.H_append (u P : List U) (h : StdShape (.b u :: P))
    (k : ℕ) (hk : 1 ≤ k) : StdShape (H u k ++ P) := by
  have hu := h.child
  have hH : StdShape (H u k) := by
    match u with
    | [] => simpa [H] using StdShape.zeros k
    | .z :: r =>
      have hr : StdShape r := hu.erase
      simpa [H] using StdShape.repeatBlock r hr k
    | .b w :: r =>
      have hi := StdShape.H_append w r hu k hk
      obtain ⟨t, ht⟩ := H_head w k hk
      rw [ht] at hi
      have hit : StdShape (t ++ r) := hi.erase
      simpa [H, ht] using StdShape.zero (StdShape.single hit)
  apply hH.attach u P h
  intro w hw
  exact ((hH.block_le_flat w hw).trans_lt (flat_H_lt_block u k hk)).le
termination_by sizeOf u
decreasing_by simp_wf; omega

theorem StdShape.E (u P : List U) (h : StdShape (.b u :: P))
    (k : ℕ) (hk : 1 ≤ k) : StdShape (Googology.Notation.SSOSS.E (.b u :: P) k) :=
  h.H_append u P k hk

end Googology.Notation.SSOSS
