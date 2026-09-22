import Googology.Trans.BMS.OneRow
import Googology.Trans.BMS.Cut

/-!
# From the array to the entries

`BMS/OneRow.lean` says what `BM4.expand` does to a one-row array, in terms of
its columns.  `BMS/Cut.lean` says what `expandL` does to a list, in terms of
concatenation.  This file matches them: `entries` reads an array off as a
list, and `entries_expand` says the two expansions agree,

    entries (expand A N) = expandL N 0 (entries A).

Both sides are written as one map over a range, which is what makes the proof
short: `entries_split` cuts the range into the good part, the bad part and the
last column, and `flatten_replicate_map` writes the repeated bad part the same
way.  No entry is ever indexed by hand.

The hypothesis is that the array's entries form a matrix — `Col 0`.  Every
array reachable from a stair has that property; `BMS/Bms.lean` proves it by
induction over reachability.
-/

namespace Googology.Trans.BMS

open BM4

/-- The entries of a one-row array, as a list. -/
def entries (A : Arr 1) : List Nat := (List.range A.len).map (fun i => A.col i 0)

@[simp] theorem entries_length (A : Arr 1) : (entries A).length = A.len := by
  rw [entries, List.length_map, List.length_range]

/-- Reading the entries of a one-row array off in three pieces. -/
theorem entries_split (A : Arr 1) (p s : Nat) (h : A.len = p + (s + 1)) :
    entries A = (List.range p).map (fun i => A.col i 0)
      ++ ((List.range s).map (fun j => A.col (p + j) 0) ++ [A.col (p + s) 0]) := by
  rw [entries, h, List.range_add, List.map_append, List.map_map, List.range_succ,
    List.map_append]
  rfl

/-- A block repeated `k` times, written as one map over a range. -/
theorem flatten_replicate_map : ∀ (k s : Nat) (h : Nat → Nat),
    (List.replicate k ((List.range s).map h)).flatten
      = (List.range (k * s)).map (fun j => h (j % s)) := by
  intro k
  induction k with
  | zero => intro s h; rw [List.replicate_zero, List.flatten_nil, Nat.zero_mul, List.range_zero,
      List.map_nil]
  | succ m ih =>
    intro s h
    rw [List.replicate_succ, List.flatten_cons, ih s h,
      show (m + 1) * s = s + m * s by ring, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left ?_
      intro j hj
      rw [Nat.mod_eq_of_lt (List.mem_range.mp hj)]
    · refine List.map_congr_left ?_
      intro j _
      simp only [Function.comp_apply, Nat.add_mod_left]

/-- **The array and the list expand the same way.** -/
theorem entries_expand (A : Arr 1) (N : Nat) (h : Col 0 (entries A)) (hne : A.len ≠ 0) :
    entries (expand A N) = expandL N 0 (entries A) := by
  have hl : entries A ≠ [] := by
    intro he
    have hL := entries_length A
    rw [he] at hL
    exact hne hL.symm
  obtain ⟨g, bad, x, heq, hlast, hhead, htail, hiff, hexp⟩ :=
    expandL_split N (entries A) 0 h hl
  have hlen : A.len = g.length + (bad.length + 1) := by
    have hL := congrArg List.length heq
    rw [entries_length] at hL
    simp only [List.length_append, List.length_cons, List.length_nil] at hL
    omega
  have hlen1 : A.len - 1 = g.length + bad.length := by rw [hlen]; omega
  have hsp := entries_split A g.length bad.length hlen
  have heq' : entries A = g ++ (bad ++ [x]) := by rw [heq, List.append_assoc]
  obtain ⟨hg, hrest⟩ := List.append_inj (heq'.symm.trans hsp)
    (by rw [List.length_map, List.length_range])
  obtain ⟨hbad, hxX⟩ := List.append_inj hrest (by rw [List.length_map, List.length_range])
  have hx : x = A.col (g.length + bad.length) 0 := by
    have hh := congrArg List.head? hxX
    simpa using hh
  rw [hexp, hg]
  by_cases hb : bad = []
  · -- nothing below the last entry: the last column goes
    have hs0 : bad.length = 0 := by rw [hb]; rfl
    have hx0 : x = 0 := hiff.mp hb
    have hnp : ∀ j, ¬ parent A 0 j (A.len - 1) := by
      intro j hj
      have h2 := (parent_one.mp hj).2.1
      rw [hlen1, ← hx, hx0] at h2
      omega
    rw [expand_one_drop hne hnp N, hb, flatten_replicate_nil, List.append_nil,
      entries, show (dropLast A).len = g.length by simp [dropLast, hlen1, hs0]]
    rfl
  · -- the bad part is there: keep the good part, repeat the bad one
    have hs1 : 1 ≤ bad.length := by
      cases bad with
      | nil => exact absurd rfl hb
      | cons _ _ => simp
    have hbadhead : bad.head? = some (A.col g.length 0) := by
      conv_lhs => rw [hbad]
      cases hc : bad.length with
      | zero => omega
      | succ m => rw [List.range_succ_eq_map]; simp
    have hpar : parent A 0 g.length (A.len - 1) := by
      refine parent_one.mpr ⟨by rw [hlen1]; omega, ?_, ?_,
        Nat.sub_lt (Nat.pos_of_ne_zero hne) Nat.one_pos⟩
      · rw [hlen1, ← hx]
        exact hhead _ hbadhead
      · intro j' h1 h2
        rw [hlen1] at h2
        rw [hlen1, ← hx]
        refine htail (A.col j' 0) ?_
        rw [show A.col j' 0 = A.col (g.length + (j' - g.length)) 0 from by
          congr 1; omega, hbad]
        cases hc : bad.length with
        | zero => omega
        | succ m =>
          rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.tail_cons]
          refine List.mem_map.mpr ⟨j' - g.length - 1, List.mem_range.mpr (by omega), ?_⟩
          simp only [Function.comp_apply]
          congr 1
          omega
    have hs : A.len - 1 - g.length = bad.length := by rw [hlen1]; omega
    rw [entries, expand_one_len hpar N, hs]
    have hcol : ∀ i, (expand A N).col i 0
        = if i < g.length then A.col i 0
          else A.col (g.length + (i - g.length) % bad.length) 0 := by
      intro i; rw [expand_one_col hpar N i 0, hs]
    rw [List.map_congr_left (fun i _ => hcol i), List.range_add, List.map_append,
      List.map_map]
    conv_rhs => rw [hbad]
    rw [flatten_replicate_map]
    congr 1
    · exact List.map_congr_left (fun i hi => if_pos (List.mem_range.mp hi))
    · refine List.map_congr_left ?_
      intro j _
      simp only [Function.comp_apply]
      rw [if_neg (by omega), show g.length + j - g.length = j by omega]

end Googology.Trans.BMS
