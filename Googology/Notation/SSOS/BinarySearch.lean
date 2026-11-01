import Googology.Notation.SSOS.Search
import Googology.Notation.SSOS.Representation

/-!
The binary search reduction. All results apply off standard forms too.
`BinaryLimit` packages precisely: binary entries, prefix (0,0), last entry 1.
-/

namespace Googology.Notation.SSOS

structure BinaryLimit (S : List ℕ) : Prop where
  binary : Binary S
  zeros : ∃ Y, S = [0,0] ++ Y
  last : Seq.entry S S.length = 1

namespace BinaryLimit

theorem first {S : List ℕ} (h : BinaryLimit S) : Seq.entry S 1 = 0 := by
  obtain ⟨Y, rfl⟩ := h.zeros
  simp [Seq.entry]

theorem second {S : List ℕ} (h : BinaryLimit S) : Seq.entry S 2 = 0 := by
  obtain ⟨Y, rfl⟩ := h.zeros
  simp [Seq.entry]

theorem length_ge_three {S : List ℕ} (h : BinaryLimit S) : 3 ≤ S.length := by
  obtain ⟨Y, he⟩ := h.zeros
  have hl := h.last
  cases Y with
  | nil => simp [he, Seq.entry] at hl
  | cons a Y => simp [he]

end BinaryLimit

namespace Seq

theorem p_one_eq_sp (S : Sequence) : p S 1 = sp S S.length := by simp [p]

theorem p_succ (S : Sequence) (i : ℕ) : p S (i+1) = sp S (p S i) := by
  simp [p, Function.iterate_succ_apply']

theorem suf_last_binary (S : Sequence) (hS : BinaryLimit S) : suf S S.length = [1] := by
  rw [suf_cons S S.length (by have := hS.length_ge_three; omega) le_rfl,
    hS.last, suf_end]

theorem suf_lt_last_iff_zero (S : Sequence) (hS : BinaryLimit S) (i : ℕ)
    (hi : 1 ≤ i) (hiL : i < S.length) : suf S i < suf S S.length ↔ entry S i = 0 := by
  rw [suf_cons S i hi hiL.le, suf_last_binary S hS]
  have hb := binary_entry S hS.binary i
  by_cases hz : entry S i = 0
  · rw [hz]
    exact ⟨fun _ => rfl, fun _ => List.Lex.rel (by decide)⟩
  · have ho : entry S i = 1 := by omega
    rw [ho]
    constructor
    · intro h
      have hn : suf S (i+1) < [] := List.lex_cons_iff.mp h
      exact False.elim (List.not_lt_nil _ hn)
    · omega

def lastZero (S : Sequence) : ℕ :=
  ((List.range S.length).filter fun i => 1 ≤ i ∧ entry S i = 0).foldl max 1

theorem p_one_binary (S : Sequence) (hS : BinaryLimit S) : p S 1 = lastZero S := by
  rw [p_one_eq_sp, sp, lastZero]
  apply congrArg (fun l : List ℕ => l.foldl max 1)
  apply List.filter_congr
  intro i hi
  have hiL : i < S.length := List.mem_range.mp hi
  by_cases h1 : 1 ≤ i
  · simp [h1, suf_lt_last_iff_zero S hS i h1 hiL]
  · simp [h1]

theorem p_one_spec_binary (S : Sequence) (hS : BinaryLimit S) :
    2 ≤ p S 1 ∧ p S 1 < S.length ∧ entry S (p S 1) = 0 ∧
    ∀ i, 1 ≤ i → i < S.length → entry S i = 0 → i ≤ p S 1 := by
  have hL := hS.length_ge_three
  have h2 := le_sp S S.length 2 (by omega) (by omega)
    ((suf_lt_last_iff_zero S hS 2 (by omega) (by omega)).2 hS.second)
  have hlt := sp_lt S S.length (by omega)
  rw [← p_one_eq_sp] at h2 hlt
  refine ⟨h2, hlt, ?_, ?_⟩
  · rcases sp_origin S S.length with he | hs
    · rw [← p_one_eq_sp] at he; omega
    · rw [← p_one_eq_sp] at hs
      exact (suf_lt_last_iff_zero S hS _ (by omega) hlt).1 hs.2.2
  · intro i hi hiL hz
    rw [p_one_eq_sp]
    exact le_sp S S.length i hi hiL ((suf_lt_last_iff_zero S hS i hi hiL).2 hz)

theorem mem_suf_succ (S : Sequence) (i n : ℕ) (hn : n ∈ suf S (i+1)) :
    ∃ j, i < j ∧ j ≤ S.length ∧ entry S j = n := by
  obtain ⟨k, hk, hv⟩ := List.mem_iff_getElem.mp hn
  have hik : i+k < S.length := by simp [suf] at hk; omega
  refine ⟨i+k+1, by omega, by omega, ?_⟩
  simpa [entry, suf, List.getElem?_eq_getElem hik] using hv

theorem suf_after_p_one (S : Sequence) (hS : BinaryLimit S) :
    suf S (p S 1+1) = List.replicate (S.length-p S 1) 1 := by
  have hs := p_one_spec_binary S hS
  have hones : ∀ n ∈ suf S (p S 1+1), n = 1 := by
    intro n hn
    obtain ⟨j, hj, hjL, he⟩ := mem_suf_succ S (p S 1) n hn
    have hval := binary_entry S hS.binary j
    by_contra hn1
    have hz : entry S j = 0 := by omega
    have hjlt : j < S.length := by
      by_contra h
      have hjEq : j = S.length := by omega
      rw [hjEq, hS.last] at hz
      contradiction
    have := hs.2.2.2 j (by omega) hjlt hz
    omega
  simpa [suf_length] using List.eq_replicate_of_mem hones

theorem suf_first_lt_p_one (S : Sequence) (hS : BinaryLimit S) :
    suf S 1 < suf S (p S 1) := by
  have hs := p_one_spec_binary S hS
  have hL := hS.length_ge_three
  rw [suf_cons S 1 (by omega) (by omega), hS.first,
    suf_cons S 2 (by omega) (by omega), hS.second,
    suf_cons S (p S 1) (by omega) hs.2.1.le, hs.2.2.1, suf_after_p_one S hS]
  cases he : S.length-p S 1 with
  | zero => omega
  | succ n =>
    rw [List.replicate_succ]
    exact List.Lex.cons (List.Lex.rel (by decide))

theorem p_two_spec_binary (S : Sequence) (hS : BinaryLimit S) :
    1 ≤ p S 2 ∧ p S 2 < p S 1 ∧ entry S (p S 2) = 0 ∧
    suf S (p S 2) < suf S (p S 1) := by
  have hs := p_one_spec_binary S hS
  have hlo := one_le_sp S (p S 1)
  have hhi := sp_lt S (p S 1) (by omega)
  have heq : p S 2 = sp S (p S 1) := p_succ S 1
  rw [← heq] at hlo hhi
  have hlex : suf S (p S 2) < suf S (p S 1) := by
    rcases sp_origin S (p S 1) with he | h
    · rw [← heq] at he
      rw [he]
      exact suf_first_lt_p_one S hS
    · simpa only [← heq] using h.2.2
  refine ⟨hlo, hhi, ?_, hlex⟩
  rw [suf_cons S (p S 2) hlo (by omega),
    suf_cons S (p S 1) (by omega) hs.2.1.le, hs.2.2.1] at hlex
  have h := List.head_le_of_lt hlex
  omega

/-- Length of the initial run of ones. -/
def oneRun : List ℕ → ℕ
  | [] => 0
  | n :: s => if n = 1 then oneRun s+1 else 0

def onesAfter (S : Sequence) (i : ℕ) : ℕ := oneRun (suf S (i+1))

theorem oneRun_replicate (n : ℕ) : oneRun (List.replicate n 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, oneRun, ih]

theorem binary_suf (S : Sequence) (hb : Binary S) (i : ℕ) : Binary (suf S (i+1)) := by
  intro n hn
  exact hb n (List.mem_of_mem_drop hn)

theorem oneRun_lt_replicate_iff (s : List ℕ) (hb : Binary s) (a : ℕ)
    (ha : a ≤ s.length) : s < List.replicate a 1 ↔ oneRun s < a := by
  induction a generalizing s with
  | zero => simp [List.not_lt_nil]
  | succ a ih =>
    cases s with
    | nil => simp at ha
    | cons n s =>
      have hn := hb n (by simp)
      have ht : Binary s := fun k hk => hb k (List.mem_cons_of_mem _ hk)
      have hlen : a ≤ s.length := by simp only [List.length_cons] at ha; omega
      rcases hn with rfl | rfl
      · constructor
        · intro _; simp [oneRun]
        · intro _; rw [List.replicate_succ]; exact List.Lex.rel (by decide)
      · rw [List.replicate_succ]
        change (1 :: s < 1 :: List.replicate a 1) ↔ oneRun s+1 < a+1
        rw [Nat.add_lt_add_iff_right]
        exact List.lex_cons_iff.trans (ih s ht hlen)

theorem onesAfter_p_one (S : Sequence) (hS : BinaryLimit S) :
    onesAfter S (p S 1) = S.length-p S 1 := by
  rw [onesAfter, suf_after_p_one S hS, oneRun_replicate]

theorem suf_lt_p_one_iff_short_zero (S : Sequence) (hS : BinaryLimit S) (i : ℕ)
    (hi : 1 ≤ i) (hir : i < p S 1) :
    suf S i < suf S (p S 1) ↔
      entry S i = 0 ∧ onesAfter S i < onesAfter S (p S 1) := by
  have hs := p_one_spec_binary S hS
  have hiL : i ≤ S.length := by omega
  have hlen : S.length-p S 1 ≤ (suf S (i+1)).length := by rw [suf_length]; omega
  have hrun := oneRun_lt_replicate_iff (suf S (i+1)) (binary_suf S hS.binary i)
    (S.length-p S 1) hlen
  rw [suf_cons S i hi hiL, suf_cons S (p S 1) (by omega) hs.2.1.le, hs.2.2.1]
  constructor
  · intro hlex
    have hz : entry S i = 0 := by have := List.head_le_of_lt hlex; omega
    refine ⟨hz, ?_⟩
    rw [hz] at hlex
    have htail := List.lex_cons_iff.mp hlex
    rw [suf_after_p_one S hS] at htail
    rw [onesAfter_p_one S hS]
    exact hrun.mp htail
  · rintro ⟨hz, hr⟩
    rw [hz]
    apply List.Lex.cons
    rw [suf_after_p_one S hS]
    apply hrun.mpr
    rw [onesAfter_p_one S hS] at hr
    exact hr

/-- The rightmost earlier zero whose following run is shorter than the final run. -/
def shortZero (S : Sequence) : ℕ :=
  ((List.range (lastZero S)).filter fun i =>
    1 ≤ i ∧ entry S i = 0 ∧ onesAfter S i < onesAfter S (lastZero S)).foldl max 1

theorem p_two_binary (S : Sequence) (hS : BinaryLimit S) : p S 2 = shortZero S := by
  rw [p_succ S 1, sp, shortZero, ← p_one_binary S hS]
  apply congrArg (fun l : List ℕ => l.foldl max 1)
  apply List.filter_congr
  intro i hi
  have hir : i < p S 1 := List.mem_range.mp hi
  by_cases h1 : 1 ≤ i
  · simp [h1, suf_lt_p_one_iff_short_zero S hS i h1 hir]
  · simp [h1]

theorem p_two_short_zero_spec (S : Sequence) (hS : BinaryLimit S) :
    1 ≤ p S 2 ∧ p S 2 < p S 1 ∧ entry S (p S 2) = 0 ∧
    onesAfter S (p S 2) < onesAfter S (p S 1) ∧
    ∀ i, 1 ≤ i → i < p S 1 → entry S i = 0 →
      onesAfter S i < onesAfter S (p S 1) → i ≤ p S 2 := by
  have hs := p_two_spec_binary S hS
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · exact ((suf_lt_p_one_iff_short_zero S hS _ hs.1 hs.2.1).1 hs.2.2.2).2
  · intro i hi hir hz hrun
    rw [p_succ S 1]
    exact le_sp S (p S 1) i hi hir
      ((suf_lt_p_one_iff_short_zero S hS i hi hir).2 ⟨hz, hrun⟩)

theorem mbp_p_two_binary (S : Sequence) (hS : BinaryLimit S) :
    p S 2 < mbp S (p S 2) ∧ mbp S (p S 2) < S.length ∧
    entry S (mbp S (p S 2)) = 0 := by
  have h1 := p_one_spec_binary S hS
  have h2 := p_two_spec_binary S hS
  have hcan : Candidate S (p S 1) := ⟨h1.2.1, by rw [h1.2.2.1, hS.last]; decide⟩
  have hlt := mbp_lt_length_of_candidate S (p S 2) (p S 1) h2.2.1.le hcan
  have hsel := mbp_candidate_of_exists S (p S 2) (p S 1) h2.2.1.le hcan
  have hs := mbp_spec S (p S 2)
  have hlex := h2.2.2.2
  rw [suf_cons S (p S 2) h2.1 (by omega), h2.2.2.1,
    suf_cons S (p S 1) (by omega) h1.2.1.le, h1.2.2.1] at hlex
  have htail : suf S (p S 2+1) < suf S (p S 1+1) := List.lex_cons_iff.mp hlex
  have hbest := (hs.2.2.2 (p S 1) h2.2.1.le hcan).1
  have hne : p S 2 ≠ mbp S (p S 2) := by
    intro he
    rw [← he] at hbest
    exact (not_lt_of_ge hbest) htail
  have hlow := hs.1
  have hval := hsel.2
  rw [hS.last] at hval
  exact ⟨by omega, hlt, by omega⟩

theorem breakAt_two_binary (S : Sequence) (hS : BinaryLimit S) : breakAt S 2 := by
  have h := mbp_p_two_binary S hS
  apply Or.inr
  refine ⟨mbp S (p S 2), ?_, h.1, ?_⟩
  · simp [fbp]
  · rw [h.2.2]
    exact Nat.zero_le _

theorem br_eq_two_of_breakAt (S : Sequence) (hL : 2 ≤ S.length) (hb : breakAt S 2) :
    br S = 2 := by
  have hf : ((List.range (S.length+1)).find? fun i => 1 < i ∧ breakAt S i) = some 2 := by
    apply List.find?_range_eq_some.mpr
    refine ⟨by simpa using And.intro (show 1 < 2 by decide) hb, by simp; omega, ?_⟩
    intro j hj
    have hn : ¬1 < j := by omega
    simp [hn]
  unfold br
  rw [hf]
  rfl

theorem br_binary (S : Sequence) (hS : BinaryLimit S) : br S = 2 :=
  br_eq_two_of_breakAt S (by have := hS.length_ge_three; omega) (breakAt_two_binary S hS)

/-- A specification of the rightmost suffix argmax, with no mbp or br. -/
def IsZeroArgmax (S : Sequence) (x r : ℕ) : Prop :=
  x ≤ r ∧ r < S.length ∧ entry S r = 0 ∧
  ∀ j, x ≤ j → j < S.length → entry S j = 0 →
    suf S (j+1) ≤ suf S (r+1) ∧ (suf S (j+1) = suf S (r+1) → j ≤ r)

theorem cut_eq_mbp_p_two_binary (S : Sequence) (hS : BinaryLimit S) :
    cut S = mbp S (p S 2) := by simp [cut, fbp, br_binary S hS]

theorem cut_binary (S : Sequence) (hS : BinaryLimit S) :
    IsZeroArgmax S (p S 2) (cut S) := by
  rw [cut_eq_mbp_p_two_binary S hS]
  have h := mbp_p_two_binary S hS
  refine ⟨h.1.le, h.2.1, h.2.2, ?_⟩
  intro j hj hjL hz
  exact (mbp_spec S (p S 2)).2.2.2 j hj ⟨hjL, by rw [hz, hS.last]; decide⟩

theorem cut_gt_p_two_binary (S : Sequence) (hS : BinaryLimit S) : p S 2 < cut S := by
  rw [cut_eq_mbp_p_two_binary S hS]
  exact (mbp_p_two_binary S hS).1

theorem cut_entry_zero_binary (S : Sequence) (hS : BinaryLimit S) : entry S (cut S) = 0 :=
  (cut_binary S hS).2.2.1

theorem cut_lt_length_binary (S : Sequence) (hS : BinaryLimit S) : cut S < S.length :=
  (cut_binary S hS).2.1

theorem IsZeroArgmax.unique {S : Sequence} {x r r' : ℕ}
    (h : IsZeroArgmax S x r) (h' : IsZeroArgmax S x r') : r = r' := by
  have ha := h.2.2.2 r' h'.1 h'.2.1 h'.2.2.1
  have hb := h'.2.2.2 r h.1 h.2.1 h.2.2.1
  have he := le_antisymm ha.1 hb.1
  exact Nat.le_antisymm (hb.2 he.symm) (ha.2 he)

theorem cut_eq_iff_zeroArgmax (S : Sequence) (hS : BinaryLimit S) (r : ℕ) :
    cut S = r ↔ IsZeroArgmax S (p S 2) r := by
  constructor
  · intro he; rw [← he]; exact cut_binary S hS
  · intro h; exact (cut_binary S hS).unique h

/-- No sp, p, mbp or br occurs on the right-hand side, including definitions. -/
theorem cut_eq_iff_shortZero_argmax (S : Sequence) (hS : BinaryLimit S) (r : ℕ) :
    cut S = r ↔ IsZeroArgmax S (shortZero S) r := by
  rw [← p_two_binary S hS]
  exact cut_eq_iff_zeroArgmax S hS r

theorem existsUnique_zeroArgmax (S : Sequence) (hS : BinaryLimit S) :
    ∃! r, IsZeroArgmax S (shortZero S) r := by
  refine ⟨cut S, (cut_eq_iff_shortZero_argmax S hS _).1 rfl, ?_⟩
  intro r hr
  exact ((cut_eq_iff_shortZero_argmax S hS r).2 hr).symm

end Seq
end Googology.Notation.SSOS
