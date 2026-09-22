import Googology.Trans.BMS.Anc
import Googology.Trans.BMS.TwoRow

/-!
# Two rows, on the entries

`BMS/Entries.lean` matches `BM4.expand` on `BM4.Arr 1` against a rule on the
entries.  This file does the same for two rows, where the rule is no longer a
copy.

`entries2` reads an array off as a list of pairs.  `parAt1` computes the row-`1`
parent — the last strict row-`0` ancestor before the column whose second entry
is smaller — and `badRootL` picks the bad root, reporting whether the maximal
parent row is `1`.  `expand2L` is then expansion written out: copy the good
part, write the bad part `N + 1` times, and on copy `q` add `q` increments to
the first row of a column when its position is a row-`0` descendant of the bad
root and the maximal parent row is `1`.

`entries2_expand` is the match.  Like the one-row proof it keeps both sides as
maps over ranges, so no entry is indexed by hand; the only new work is that
the block now depends on which copy it is in and on the ancestor test, and
`BMS/Anc.lean` supplies the second.

`expand2L_terminates` is what comes out for free: a run of two-row expansions
computed on the entries reaches the empty matrix.  Termination is
`Notation.BMS.bms_terminates 2`; what is added is that the step is a function
that runs, which the array version is not — `BM4.expand` is `noncomputable`.

What is still missing for a two-row translation is the reading.  It has to use
`ψ` at every finite subscript, because the two-row generators climb through
`ψ_0(Ω_n)`; see the plan.
-/

namespace Googology.Trans.BMS

open BM4 Pat

/-- Both rows of a two-row array, as a list of pairs. -/
def entries2 (A : Arr 2) : List (Nat × Nat) :=
  (List.range A.len).map (fun i => (A.col i 0, A.col i 1))

@[simp] theorem entries2_length (A : Arr 2) : (entries2 A).length = A.len := by
  rw [entries2, List.length_map, List.length_range]

theorem entries2_getElem (A : Arr 2) (i : Nat) (h : i < A.len) :
    (entries2 A)[i]! = (A.col i 0, A.col i 1) := by
  rw [entries2, getElem!_pos _ _ (by simpa using h), List.getElem_map, List.getElem_range]

/-- The first row of the pairs is the row-`0` entries. -/
theorem entries2_map_fst (A : Arr 2) : (entries2 A).map Prod.fst = entries A := by
  rw [entries2, entries, List.map_map]
  rfl

/-! ### The row-1 parent -/

/-- `j` is the row-`1` parent of `i`: the last strict row-`0` ancestor of `i`
before it whose second entry is smaller. -/
def ParL1 (l : List (Nat × Nat)) (j i : Nat) : Prop :=
  j < i ∧ AncL (l.map Prod.fst) j i ∧ (l[j]!).2 < (l[i]!).2 ∧
    ∀ j', j < j' → j' < i → AncL (l.map Prod.fst) j' i → (l[i]!).2 ≤ (l[j']!).2

/-- The row-`1` parent of `i`, computed from the entries. -/
def parAt1 (l : List (Nat × Nat)) (i : Nat) : Option Nat :=
  lastAux (fun j => ancAtB (l.map Prod.fst) j i) (fun j => (l[j]!).2) ((l[i]!).2) i

theorem parAt1_eq_some (l : List (Nat × Nat)) (i j : Nat) :
    parAt1 l i = some j ↔ ParL1 l j i := by
  rw [parAt1, lastAux_eq_some, ParL1]
  simp only [ancAtB_iff]

instance (l : List (Nat × Nat)) (j i : Nat) : Decidable (ParL1 l j i) :=
  decidable_of_iff (parAt1 l i = some j) (parAt1_eq_some l i j)

theorem anc_lt_len {r : Nat} {A : Arr r} {j i : Nat} (h : anc A 0 j i) : i < A.len := by
  rw [anc_zero_eq] at h
  obtain ⟨b, _, hb⟩ := Relation.TransGen.tail'_iff.mp h
  exact hb.2.2.2.2.2

/-- **Being the row-`1` parent is a condition on the entries.** -/
theorem ParL1_iff_parent1 (A : Arr 2) (j i : Nat) :
    ParL1 (entries2 A) j i ↔ parent A 1 j i := by
  rw [parent_one_iff, ParL1, entries2_map_fst]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hanc := (AncL_iff_anc (by omega) A j i).mp h2
    have hi : i < A.len := anc_lt_len hanc
    rw [entries2_getElem A j (by omega), entries2_getElem A i hi] at h3
    refine ⟨h1, hanc, h3, ?_, hi⟩
    intro j' a b hc
    have := h4 j' a b ((AncL_iff_anc (by omega) A j' i).mpr hc)
    rwa [entries2_getElem A i hi, entries2_getElem A j' (by omega)] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, (AncL_iff_anc (by omega) A j i).mpr h2, ?_, ?_⟩
    · rw [entries2_getElem A j (by omega), entries2_getElem A i h5]; exact h3
    · intro j' a b hc
      rw [entries2_getElem A i h5, entries2_getElem A j' (by omega)]
      exact h4 j' a b ((AncL_iff_anc (by omega) A j' i).mp hc)

theorem parAt1_eq_none {l : List (Nat × Nat)} {i : Nat} (h : parAt1 l i = none) (j : Nat) :
    ¬ ParL1 l j i := by
  intro hp
  rw [← parAt1_eq_some] at hp
  rw [h] at hp
  exact absurd hp (by simp)

theorem parAt_eq_none {l : List Nat} {i : Nat} (h : parAt l i = none) (j : Nat) :
    ¬ ParL l j i := by
  intro hp
  rw [← parAt_eq_some] at hp
  rw [h] at hp
  exact absurd hp (by simp)

/-! ### The bad root -/

/-- The bad root, and whether the maximal parent row is `1`. -/
def badRootL (l : List (Nat × Nat)) : Option (Nat × Bool) :=
  if l.isEmpty then none else
  match parAt1 l (l.length - 1) with
  | some p => some (p, true)
  | none =>
      match parAt (l.map Prod.fst) (l.length - 1) with
      | some p => some (p, false)
      | none => none

theorem hasParent1_iff (A : Arr 2) :
    HasParent A 1 (A.len - 1) ↔ ∃ p, parAt1 (entries2 A) (A.len - 1) = some p := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (parAt1_eq_some _ _ _).mpr ((ParL1_iff_parent1 A p _).mpr hp)⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (ParL1_iff_parent1 A p _).mp ((parAt1_eq_some _ _ _).mp hp)⟩

theorem badRootL_true {A : Arr 2} {p : Nat} (h : badRootL (entries2 A) = some (p, true)) :
    HasParent A 1 (A.len - 1) ∧ parent A 1 p (A.len - 1) := by
  rw [badRootL] at h
  rw [if_neg (by intro he; rw [he] at h; exact absurd h (by simp))] at h
  cases hp : parAt1 (entries2 A) ((entries2 A).length - 1) with
  | none =>
    rw [hp] at h
    cases hq : parAt (entries A) ((entries2 A).length - 1) with
    | none => rw [entries2_map_fst, hq] at h; exact absurd h (by simp)
    | some q => rw [entries2_map_fst, hq] at h; exact absurd h (by simp)
  | some q =>
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [entries2_length] at hp
    have hpar := (ParL1_iff_parent1 A q _).mp ((parAt1_eq_some _ _ _).mp hp)
    rw [h.1] at hpar
    exact ⟨⟨p, hpar⟩, hpar⟩

theorem badRootL_false {A : Arr 2} {p : Nat} (h : badRootL (entries2 A) = some (p, false)) :
    ¬ HasParent A 1 (A.len - 1) ∧ parent A 0 p (A.len - 1) := by
  rw [badRootL] at h
  rw [if_neg (by intro he; rw [he] at h; exact absurd h (by simp))] at h
  cases hp : parAt1 (entries2 A) ((entries2 A).length - 1) with
  | some q => rw [hp] at h; simp_all
  | none =>
    rw [hp] at h
    cases hq : parAt (entries A) ((entries2 A).length - 1) with
    | none => rw [entries2_map_fst, hq] at h; exact absurd h (by simp)
    | some q =>
      rw [entries2_map_fst, hq] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [entries2_length] at hp hq
      refine ⟨?_, ?_⟩
      · rw [hasParent1_iff]
        rintro ⟨s, hs⟩
        rw [hp] at hs
        exact absurd hs (by simp)
      · rw [← h.1]
        exact (ParL_iff_parent (by omega) A q _).mp ((parAt_eq_some _ _ _).mp hq)

theorem badRootL_none {A : Arr 2} (h : badRootL (entries2 A) = none) (h0 : A.len ≠ 0) :
    ¬ LastHasParent A := by
  rw [badRootL, if_neg (by
    simp only [List.isEmpty_iff]
    intro he
    exact h0 (by have := entries2_length A; rw [he] at this; exact this.symm))] at h
  cases hp : parAt1 (entries2 A) ((entries2 A).length - 1) with
  | some q => rw [hp] at h; exact absurd h (by simp)
  | none =>
    cases hq : parAt (entries A) ((entries2 A).length - 1) with
    | some q => rw [hp, entries2_map_fst, hq] at h; exact absurd h (by simp)
    | none =>
      rw [entries2_length] at hp hq
      rintro ⟨_, k, hk, hpk⟩
      interval_cases k
      · exact parAt_eq_none hq _ ((ParL_iff_parent (by omega) A _ _).mpr hpk.choose_spec)
      · exact parAt1_eq_none hp _ ((ParL1_iff_parent1 A _ _).mpr hpk.choose_spec)


/-! ### Expansion on the entries -/

theorem map_range_dropLast {α : Type} (n : Nat) (f : Nat → α) :
    ((List.range n).map f).dropLast = (List.range (n - 1)).map f := by
  cases n with
  | zero => rw [List.range_zero, List.map_nil]; rfl
  | succ m =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.dropLast_concat]
    rfl

/-- **Two-row expansion, written on the entries.**  The good part is copied,
then the bad part is written `N + 1` times, and on copy `q` the first row of a
column takes `q` increments when its position is a row-`0` descendant of the
bad root and the maximal parent row is `1`. -/
def expand2L (N : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  match badRootL l with
  | none => l.dropLast
  | some (p, m1) =>
      (List.range p).map (fun i => l[i]!)
        ++ (List.range ((N + 1) * (l.length - 1 - p))).map (fun t =>
              if m1 && ((p == p + t % (l.length - 1 - p))
                  || ancAtB (l.map Prod.fst) p (p + t % (l.length - 1 - p))) then
                ((l[p + t % (l.length - 1 - p)]!).1
                  + (t / (l.length - 1 - p)) * ((l[l.length - 1]!).1 - (l[p]!).1),
                 (l[p + t % (l.length - 1 - p)]!).2)
              else l[p + t % (l.length - 1 - p)]!)


/-- **The array and its entries expand the same way, with two rows.** -/
theorem entries2_expand (A : Arr 2) (N : Nat) :
    entries2 (expand A N) = expand2L N (entries2 A) := by
  cases hb : badRootL (entries2 A) with
  | none =>
    rw [expand2L, hb]
    dsimp only
    by_cases h0 : A.len = 0
    · rw [expand_of_len_zero h0, entries2, h0, List.range_zero, List.map_nil]
      rfl
    · rw [expand_of_not_lastHasParent h0 (badRootL_none hb h0) N, entries2, entries2,
        map_range_dropLast]
      rfl
  | some pm =>
    obtain ⟨p, m1⟩ := pm
    rw [expand2L, hb, entries2_length]
    dsimp only
    cases m1 with
    | true =>
      obtain ⟨hm, hpar⟩ := badRootL_true hb
      obtain ⟨hp1, _, _, _, hp5⟩ := parent_one_iff.mp hpar
      have hsp : 0 < A.len - 1 - p := by omega
      have hgood : ∀ i, i < p →
          ((expand A N).col i 0, (expand A N).col i 1) = (entries2 A)[i]! := by
        intro i hi
        have h0 := expand_two_col_one hm hpar N i 0
        have h1 := expand_two_col_one hm hpar N i 1
        rw [if_pos hi] at h0 h1
        rw [h0, h1, entries2_getElem A i (by omega)]
      have hbad : ∀ t : Nat,
          ((expand A N).col (p + t) 0, (expand A N).col (p + t) 1)
            = (if (true && ((p == p + t % (A.len - 1 - p))
                  || ancAtB (List.map Prod.fst (entries2 A)) p
                      (p + t % (A.len - 1 - p)))) = true then
                ((entries2 A)[p + t % (A.len - 1 - p)]!.1
                  + t / (A.len - 1 - p)
                    * ((entries2 A)[A.len - 1]!.1 - (entries2 A)[p]!.1),
                 (entries2 A)[p + t % (A.len - 1 - p)]!.2)
              else (entries2 A)[p + t % (A.len - 1 - p)]!) := by
        intro t
        have hmem : p + t % (A.len - 1 - p) < A.len := by
          have := Nat.mod_lt t hsp; omega
        have h0 := expand_two_col_one hm hpar N (p + t) 0
        have h1 := expand_two_col_one hm hpar N (p + t) 1
        rw [if_neg (show ¬(p + t < p) by omega), show p + t - p = t from by omega] at h0 h1
        rw [if_neg (show ¬((1 : Nat) = 0 ∧ ancEq A 1 p (p + t % (A.len - 1 - p))) from
          fun hx => absurd hx.1 (by decide))] at h1
        rw [h0, h1, entries2_getElem A (p + t % (A.len - 1 - p)) hmem,
          entries2_getElem A (A.len - 1) (by omega), entries2_getElem A p (by omega),
          entries2_map_fst, Bool.true_and]
        have hcond : ((p == p + t % (A.len - 1 - p))
            || ancAtB (entries A) p (p + t % (A.len - 1 - p))) = true
            ↔ ancEq A 0 p (p + t % (A.len - 1 - p)) := by
          rw [Bool.or_eq_true, beq_iff_eq, ancAtB_iff]
          exact AncEqL_iff (by omega) A p _
        by_cases hc : ancEq A 0 p (p + t % (A.len - 1 - p))
        · rw [if_pos (show (0 : Nat) = 0 ∧ _ from ⟨rfl, hc⟩), if_pos (hcond.mpr hc)]
        · rw [if_neg (fun hx => hc hx.2), if_neg (fun hx => hc (hcond.mp hx))]
      rw [entries2, expand_two_len_one hm hpar N, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · exact List.map_congr_left (fun i hi => hgood i (List.mem_range.mp hi))
      · exact List.map_congr_left (fun t _ => hbad t)
    | false =>
      obtain ⟨hm, hpar⟩ := badRootL_false hb
      obtain ⟨hp1, _, _, hp4⟩ := parent_zero_iff.mp hpar
      have hsp : 0 < A.len - 1 - p := by omega
      have hgood : ∀ i, i < p →
          ((expand A N).col i 0, (expand A N).col i 1) = (entries2 A)[i]! := by
        intro i hi
        have h0 := expand_two_col_zero hm hpar N i 0
        have h1 := expand_two_col_zero hm hpar N i 1
        rw [if_pos hi] at h0 h1
        rw [h0, h1, entries2_getElem A i (by omega)]
      have hbad : ∀ t : Nat,
          ((expand A N).col (p + t) 0, (expand A N).col (p + t) 1)
            = (entries2 A)[p + t % (A.len - 1 - p)]! := by
        intro t
        have hmem : p + t % (A.len - 1 - p) < A.len := by
          have := Nat.mod_lt t hsp; omega
        have h0 := expand_two_col_zero hm hpar N (p + t) 0
        have h1 := expand_two_col_zero hm hpar N (p + t) 1
        rw [if_neg (show ¬(p + t < p) by omega), show p + t - p = t from by omega] at h0 h1
        rw [h0, h1, entries2_getElem A (p + t % (A.len - 1 - p)) hmem]
      rw [entries2, expand_two_len_zero hm hpar N, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · exact List.map_congr_left (fun i hi => hgood i (List.mem_range.mp hi))
      · refine List.map_congr_left (fun t _ => ?_)
        simp only [Function.comp_apply, Bool.false_and, Bool.false_eq_true, if_false]
        exact hbad t

/-! ### Termination -/

/-- **A run of two-row expansions, computed on the entries, ends.**  The
matrices are the entries of a standard array, the step is `expand2L`, and the
run reaches the empty matrix.  Termination is `Notation.BMS.bms_terminates 2`;
what this adds is that the step is a function that runs. -/
theorem expand2L_terminates (A : Arr 2) (hA : Std 2 A) (f : Nat → List (Nat × Nat))
    (h0 : f 0 = entries2 A) (hf : ∀ n, ∃ k, f (n + 1) = expand2L k (f n)) :
    ∃ n, f n = [] := by
  choose k hk using hf
  -- the array sequence that tracks `f`
  let g : Nat → Arr 2 := fun n => Nat.rec A (fun m B => expand B (k m)) n
  have hgStd : ∀ n, Std 2 (g n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ m ih => exact Std.step (k m) ih
  have hgf : ∀ n, entries2 (g n) = f n := by
    intro n
    induction n with
    | zero => exact h0.symm
    | succ m ih =>
      show entries2 (expand (g m) (k m)) = f (m + 1)
      rw [entries2_expand, ih, ← hk m]
  obtain ⟨n, hn⟩ := Googology.Notation.BMS.bms_terminates 2
    (fun n => ⟨g n, hgStd n⟩) (fun n => ⟨k n, rfl⟩)
  refine ⟨n, ?_⟩
  rw [← hgf n, entries2]
  have : (g n).len = 0 := hn
  rw [this, List.range_zero, List.map_nil]

end Googology.Trans.BMS
