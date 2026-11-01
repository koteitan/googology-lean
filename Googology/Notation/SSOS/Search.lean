import Googology.Notation.SSOS.Def

/-!
Search specifications, independent of standardness and of binary entries.
The sentinel L has the empty suffix. Ties in mbp are resolved to the right.
-/

namespace Googology.Notation.SSOS.Seq

theorem suf_succ (S : Sequence) (i : ℕ) : suf S (i+1) = S.drop i := by
  simp [suf]

theorem suf_end (S : Sequence) : suf S (S.length+1) = [] := by
  simp [suf]

theorem suf_cons (S : Sequence) (i : ℕ) (hi : 1 ≤ i) (hiL : i ≤ S.length) :
    suf S i = entry S i :: suf S (i+1) := by
  have hlt : i-1 < S.length := by omega
  simp only [suf, entry, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [List.drop_eq_getElem_cons hlt]
  have he : i-1+1 = i := by omega
  simp only [he, Nat.add_sub_cancel]

theorem suf_length (S : Sequence) (i : ℕ) : (suf S (i+1)).length = S.length-i := by
  simp [suf]

theorem suf_ne_nil (S : Sequence) (i : ℕ) (hi : i < S.length) :
    suf S (i+1) ≠ [] := by
  intro hn
  have h := suf_length S i
  rw [hn] at h
  simp only [List.length_nil] at h
  omega

/-- A strict-entry candidate for the right-to-left scan. -/
def Candidate (S : Sequence) (j : ℕ) : Prop :=
  j < S.length ∧ entry S j < entry S S.length

/-- The scan chooses a candidate or the end sentinel, and maximizes the suffix.
The final implication states the rightmost tie rule. -/
def IsMbp (S : Sequence) (x r : ℕ) : Prop :=
  min x S.length ≤ r ∧ r ≤ S.length ∧
  (r = S.length ∨ Candidate S r) ∧
  ∀ j, x ≤ j → Candidate S j →
    suf S (j+1) ≤ suf S (r+1) ∧
    (suf S (j+1) = suf S (r+1) → j ≤ r)

theorem mbp_spec (S : Sequence) (x : ℕ) : IsMbp S x (mbp S x) := by
  rw [mbp]
  split
  next hx =>
    refine ⟨by omega, le_rfl, Or.inl rfl, ?_⟩
    intro j hj hcan
    have hjL := hcan.1
    omega
  next hx =>
    have ih := mbp_spec S (x+1)
    obtain ⟨hmin, hmax, hsel, hbest⟩ := ih
    have hxm : x+1 ≤ mbp S (x+1) := by omega
    dsimp only
    split
    next htake =>
      refine ⟨by omega, by omega, Or.inr ⟨by omega, htake.1⟩, ?_⟩
      intro j hj hcan
      by_cases heq : j = x
      · subst j; exact ⟨le_rfl, fun _ => le_rfl⟩
      · have h := (hbest j (by omega) hcan).1.trans_lt htake.2
        exact ⟨h.le, fun he => False.elim (h.ne he)⟩
    next hskip =>
      refine ⟨by omega, hmax, hsel, ?_⟩
      intro j hj hcan
      by_cases heq : j = x
      · subst j
        refine ⟨?_, fun _ => by omega⟩
        exact le_of_not_gt fun hlt => hskip ⟨hcan.2, hlt⟩
      · exact hbest j (by omega) hcan
termination_by S.length-x

theorem mbp_lt_length_of_candidate (S : Sequence) (x j : ℕ)
    (hxj : x ≤ j) (hj : Candidate S j) : mbp S x < S.length := by
  have hs := mbp_spec S x
  have hle := (hs.2.2.2 j hxj hj).1
  have hne : mbp S x ≠ S.length := by
    intro he
    rw [he, suf_end] at hle
    have hnil : suf S (j+1) = [] := by
      by_contra h
      have hlt : [] < suf S (j+1) := by
        cases heq : suf S (j+1) with
        | nil => exact False.elim (h heq)
        | cons a t => exact List.Lex.nil
      exact (not_lt_of_ge hle) hlt
    exact suf_ne_nil S j hj.1 hnil
  exact lt_of_le_of_ne hs.2.1 hne

theorem mbp_candidate_of_exists (S : Sequence) (x j : ℕ)
    (hxj : x ≤ j) (hj : Candidate S j) : Candidate S (mbp S x) := by
  have hs := (mbp_spec S x).2.2.1
  rcases hs with he | hcan
  · exact False.elim ((mbp_lt_length_of_candidate S x j hxj hj).ne he)
  · exact hcan

theorem foldl_max_le_iff (l : List ℕ) (a b : ℕ) :
    l.foldl max a ≤ b ↔ a ≤ b ∧ ∀ i ∈ l, i ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [List.foldl_cons, ih, Nat.max_le, and_assoc]

theorem foldl_max_origin (l : List ℕ) (a : ℕ) :
    l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    rcases ih (max a i) with he | hm
    · rw [he]
      by_cases h : a ≤ i
      · exact Or.inr (by simp [max_eq_right h])
      · exact Or.inl (max_eq_left (by omega))
    · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem sp_le_iff (S : Sequence) (x b : ℕ) :
    sp S x ≤ b ↔ 1 ≤ b ∧ ∀ i, 1 ≤ i → i < x → suf S i < suf S x → i ≤ b := by
  rw [sp, foldl_max_le_iff]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h⟩
    exact ⟨h1, fun i hi hix hs => h i ⟨hix, hi, hs⟩⟩
  · rintro ⟨h1, h⟩
    exact ⟨h1, fun i ⟨hix, hi, hs⟩ => h i hi hix hs⟩

theorem one_le_sp (S : Sequence) (x : ℕ) : 1 ≤ sp S x :=
  ((sp_le_iff S x (sp S x)).1 le_rfl).1

theorem le_sp (S : Sequence) (x i : ℕ) (hi : 1 ≤ i) (hix : i < x)
    (hs : suf S i < suf S x) : i ≤ sp S x :=
  ((sp_le_iff S x (sp S x)).1 le_rfl).2 i hi hix hs

theorem sp_lt (S : Sequence) (x : ℕ) (hx : 1 < x) : sp S x < x := by
  have h : sp S x ≤ x-1 := (sp_le_iff S x (x-1)).2
    ⟨by omega, fun i _ hi _ => by omega⟩
  omega

theorem sp_origin (S : Sequence) (x : ℕ) :
    sp S x = 1 ∨ (1 ≤ sp S x ∧ sp S x < x ∧ suf S (sp S x) < suf S x) := by
  rcases foldl_max_origin
      ((List.range x).filter fun i => 1 ≤ i ∧ suf S i < suf S x) 1 with h | h
  · exact Or.inl h
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at h
    exact Or.inr ⟨h.2.1, h.1, h.2.2⟩

end Googology.Notation.SSOS.Seq
