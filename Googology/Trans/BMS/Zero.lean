import Googology.Trans.BMS.AllL
import Googology.Trans.BMS.Entries2

/-!
# A row of zeros underneath

Adding a row of zeros below a one-row matrix changes nothing:
`expand2L_withZero` says the two-row rule on `(a₀,0)(a₁,0)⋯` is the one-row
rule on `(a₀)(a₁)⋯`.

Why it holds is short.  A column has a parent in row `1` only if its row-`1`
entry is strictly above an earlier one, and they are all `0`, so `m₀` is `0`
and `BMS/TwoRow.lean`'s column map is the copy — the same rule row `0` follows
on its own.  The bad root is the row-`0` parent either way, because row `0`'s
candidates are all the earlier columns and nothing else is consulted.

What this does **not** give is a `Sim` from `prim` into `pairL`.  That would
need every standard one-row matrix to stay standard with the zero row added,
and standardness for two rows is reachability from `(0,0)(1,1)⋯(n,n)`, which
this file says nothing about.  The reference implementation agrees on the
cases in `test/TransCheck.lean`, and that is all that is claimed.
-/

namespace Googology.Trans.BMS

open BM4

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) :
    ∀ (l : List α) (i : Nat), i < l.length → (l.map f)[i]! = f (l[i]!) := by
  intro l i h
  rw [getElem!_pos (l.map f) i (by simpa using h), getElem!_pos l i h, List.getElem_map]

/-- Writing a one-row matrix with a row of zeros underneath. -/
abbrev withZero (l : List Nat) : List (Nat × Nat) := l.map (fun a => (a, 0))

@[simp] theorem ofList2_len (l : List Nat) : (ofList2 (withZero l)).len = l.length := by
  show (withZero l).length = l.length
  rw [withZero, List.length_map]

theorem col_zero_row (l : List Nat) {i : Nat} (h : i < l.length) :
    (ofList2 (withZero l)).col i 0 = l[i]!
      ∧ (ofList2 (withZero l)).col i 1 = 0 := by
  have hm : (withZero l)[i]! = (l[i]!, 0) := getElem!_map _ l i h
  constructor
  · show (if (0 : Nat) = 0 then ((withZero l)[i]!).1 else ((withZero l)[i]!).2) = l[i]!
    rw [if_pos rfl, hm]
  · show (if (1 : Nat) = 0 then ((withZero l)[i]!).1 else ((withZero l)[i]!).2) = 0
    rw [if_neg (by decide), hm]

/-- With a row of zeros underneath, no column has a parent in row `1`. -/
theorem no_parent_one (l : List Nat) (j i : Nat) :
    ¬ parent (ofList2 (withZero l)) 1 j i := by
  intro h
  obtain ⟨h1, _, h3, _, h5⟩ := parent_one_iff.mp h
  rw [ofList2_len] at h5
  rw [(col_zero_row l (show j < l.length by omega)).2,
    (col_zero_row l (show i < l.length by omega)).2] at h3
  omega

theorem col_zero_row_all (l : List Nat) (i : Nat) :
    (ofList2 (withZero l)).col i 0 = (ofList l).col i 0
      ∧ (ofList2 (withZero l)).col i 1 = 0 := by
  by_cases h : i < l.length
  · obtain ⟨h0, h1⟩ := col_zero_row l h
    exact ⟨h0, h1⟩
  · have hm : (withZero l)[i]! = default :=
      getElem!_neg _ _ (by rw [withZero, List.length_map]; exact h)
    constructor
    · show (if (0 : Nat) = 0 then ((withZero l)[i]!).1 else ((withZero l)[i]!).2)
        = (ofList l).col i 0
      rw [if_pos rfl, hm, show (ofList l).col i 0 = l[i]! from rfl,
        getElem!_neg l i h]
      rfl
    · show (if (1 : Nat) = 0 then ((withZero l)[i]!).1 else ((withZero l)[i]!).2) = 0
      rw [if_neg (by decide), hm]
      rfl

theorem parent_zero_withZero (l : List Nat) (j i : Nat) :
    parent (ofList2 (withZero l)) 0 j i ↔ parent (ofList l) 0 j i := by
  rw [parent_zero_iff, parent_one]
  simp only [(col_zero_row_all l _).1, ofList2_len, show (ofList l).len = l.length from rfl]

/-- **A row of zeros underneath changes nothing.**  The two-row rule applied
to a one-row matrix with a zero row added is the one-row rule. -/
theorem expand2L_withZero (N : Nat) (l : List Nat) (hc : Col 0 l) :
    expand2L N (withZero l) = withZero (expandL N 0 l) := by
  have hB : entries2 (ofList2 (withZero l)) = withZero l := entries2_ofList2 _
  have hA : entries (ofList l) = l := entries_ofList l
  have hkey : entries2 (expand (ofList2 (withZero l)) N)
      = withZero (entries (expand (ofList l) N)) := by
    by_cases hp : ∃ p, parent (ofList l) 0 p (l.length - 1)
    · obtain ⟨p, hpar⟩ := hp
      have hparB : parent (ofList2 (withZero l)) 0 p ((ofList2 (withZero l)).len - 1) := by
        simp only [ofList2_len]
        exact (parent_zero_withZero l p _).mpr hpar
      have hmB : ¬ HasParent (ofList2 (withZero l)) 1
          ((ofList2 (withZero l)).len - 1) := by
        rintro ⟨j, hj⟩; exact no_parent_one l j _ hj
      have hlenA := expand_one_len hpar N
      have hlenB := expand_two_len_zero hmB hparB N
      simp only [ofList2_len] at hlenB
      have hcB : ∀ i k, (expand (ofList2 (withZero l)) N).col i k
          = if i < p then (ofList2 (withZero l)).col i k
            else (ofList2 (withZero l)).col (p + (i - p) % (l.length - 1 - p)) k := by
        intro i k
        have := expand_two_col_zero hmB hparB N i k
        simpa only [ofList2_len] using this
      have hcA : ∀ i, (expand (ofList l) N).col i 0
          = if i < p then (ofList l).col i 0
            else (ofList l).col (p + (i - p) % (l.length - 1 - p)) 0 :=
        fun i => expand_one_col hpar N i 0
      simp only [entries2, entries, withZero]
      rw [hlenA, hlenB, List.map_map]
      refine List.map_congr_left (fun i _ => ?_)
      show ((expand (ofList2 (withZero l)) N).col i 0,
        (expand (ofList2 (withZero l)) N).col i 1) = ((expand (ofList l) N).col i 0, 0)
      rw [hcB i 0, hcB i 1, hcA i]
      simp only [(col_zero_row_all l _).1, (col_zero_row_all l _).2, ite_self]
    · push Not at hp
      have hnB : ¬ LastHasParent (ofList2 (withZero l)) := by
        rintro ⟨_, k, hk, hpk⟩
        interval_cases k
        · obtain ⟨j, hjp⟩ := hpk
          simp only [ofList2_len] at hjp
          exact hp j ((parent_zero_withZero l j _).mp hjp)
        · obtain ⟨j, hjp⟩ := hpk
          exact no_parent_one l j _ hjp
      by_cases h0 : l = []
      · subst h0
        rw [expand_of_len_zero (show (ofList2 (withZero ([] : List Nat))).len = 0 from rfl) N,
          expand_of_len_zero (show (ofList ([] : List Nat)).len = 0 from rfl) N, hB, hA]
      · have hlen0 : l.length ≠ 0 := by simpa using h0
        have hlen0B : (ofList2 (withZero l)).len ≠ 0 := by
          simp only [ofList2_len]; exact hlen0
        rw [expand_one_drop hlen0 hp N, expand_of_not_lastHasParent hlen0B hnB N]
        simp only [entries2, entries, withZero]
        rw [show (dropLast (ofList2 (withZero l))).len = l.length - 1 from by
            simp only [dropLast, ofList2_len],
          show (dropLast (ofList l)).len = l.length - 1 from rfl, List.map_map]
        refine List.map_congr_left (fun i _ => ?_)
        show ((ofList2 (withZero l)).col i 0, (ofList2 (withZero l)).col i 1)
          = ((ofList l).col i 0, 0)
        rw [(col_zero_row_all l i).1, (col_zero_row_all l i).2]
  rw [← hB, ← entries2_expand, hkey, entries_expand' (ofList l) N (by rw [hA]; exact hc), hA]

end Googology.Trans.BMS
