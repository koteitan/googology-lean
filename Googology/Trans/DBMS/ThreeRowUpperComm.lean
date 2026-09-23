import Googology.Trans.DBMS.ThreeRowUpper

/-!
# Where `t3` commutes with expansion

`ThreeRowUpper.lean` reduces the upper bound `rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)`
to `T3RankDesc`: `rkL 2 (t3 (C[N])) < rkL 2 (t3 C)` for `C ∈ SReach`.  This file
proves it wherever `t3` commutes with the expansion, and so reduces
`T3RankDesc` to a list of explicit shapes (`T3RankDescNC`).

Let `C` have `n ≥ 3` columns, column `1` equal to `(1,1,0)`, and let
`A = C.set 1 (1,1,1)` be `C` with column `1` raised.  Then rows `0` and `1` of
`A` and `C` are the same, so the row-`0` and row-`1` parents and ancestors are
the same (`ParR_congr_rows`).  The row-`2` parent of the last column is the
same too, unless that parent in `C` is column `1` and the last column has
row-`2` entry `1` (`ParR_two_last_iff`): only then does raising column `1`
move the parent to column `0`.  So `m₀` and the bad root agree
(`badRootR_set_one`), and when the bad root is not column `0` or `1` the copies
do not contain column `1`, which gives (`expandRL_set_one`)

    A[N] = (C[N]).set 1 (1,1,1).

If moreover `C[N]` still meets `T3Cond`, this is `t3 (C[N]) = (t3 C)[N]`, and
`rkL_lt` gives the instance of `T3RankDesc`.

The exception in `LastOK` (row-`2` parent column `1`) makes column `1` the
bad root, so it is covered by the second shape below (`lastOK_of_badRoot`).

**Reduced open statement** (`T3RankDescNC`): `T3RankDesc` for `C ∈ SReach`
meeting `T3Cond` and one of

* `C[N]` does not meet `T3Cond`;
* the bad root of `C` is column `0` or `1`.

`t3RankDesc_of_NC` proves `T3RankDescNC → T3RankDesc`, and
`rkL_cgen_two_four_eq_of_NC` gives `rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)` from
`T3RankDescNC`.  In the search of `ThreeRowUpper.lean` (19914 pairs `(C, N)`,
12000 of them with `T3Cond C`) the shapes occur 969 times (3 of the first kind,
966 of the second); on the other 11031 the commutation `(t3 C)[N] = t3 (C[N])`
was also checked numerically.  They are where the path from `t3 C` to
`t3 (C[N])` needs several expansions, and where `t3 (C[N])` can fail to be
standard (`not_t3Std`).
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

/-! ### Parents depend only on the rows up to their own -/

theorem ParR_congr_rows (l l' : List (List Nat)) : ∀ k : Nat,
    (∀ i k' : Nat, k' ≤ k → (l[i]!)[k']! = (l'[i]!)[k']!) → ∀ j i, ParR l k j i ↔ ParR l' k j i := by
  intro k
  induction k with
  | zero =>
    intro h j i
    have h0 : ∀ i : Nat, (l[i]!)[0]! = (l'[i]!)[0]! := fun i => h i 0 le_rfl
    simp only [ParR, h0]
  | succ m ih =>
    intro h j i
    have e : ParR l m = ParR l' m := by
      funext a b; exact propext (ih (fun i k' hk => h i k' (by omega)) a b)
    have h1 : ∀ i : Nat, (l[i]!)[m + 1]! = (l'[i]!)[m + 1]! := fun i => h i (m + 1) le_rfl
    simp only [ParR, e, h1]

theorem parAtR_congr {l l' : List (List Nat)} {k : Nat} (h : ∀ j i, ParR l k j i ↔ ParR l' k j i)
    (i : Nat) : parAtR l k i = parAtR l' k i := by
  apply Option.ext
  intro j
  rw [parAtR_eq_some, parAtR_eq_some]
  exact h j i

/-! ### Raising column `1` -/

section Raise

variable {C : List (List Nat)}

theorem set_one_get_ne (w : List Nat) {i : Nat} (hi : i ≠ 1) : (C.set 1 w)[i]! = C[i]! := by
  rw [getElem!_def, getElem!_def, List.getElem?_set_ne (by omega)]

theorem set_one_get_one (w : List Nat) (h : 1 < C.length) : (C.set 1 w)[1]! = w := by
  rw [getElem!_def, List.getElem?_set_self h]

theorem get_one_of (h : C[1]? = some [1, 1, 0]) : C[1]! = [1, 1, 0] := by
  rw [getElem!_def, h]

theorem set_one_rows01 (h : C[1]? = some [1, 1, 0]) (i k : Nat) (hk : k ≤ 1) :
    ((C.set 1 [1, 1, 1])[i]!)[k]! = (C[i]!)[k]! := by
  by_cases hi : i = 1
  · subst hi
    have hl : 1 < C.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at h
      exact absurd h (by simp)
    rw [set_one_get_one _ hl, get_one_of h]
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
  · rw [set_one_get_ne _ hi]

theorem ParR_set_one_low (h : C[1]? = some [1, 1, 0]) (k : Nat) (hk : k ≤ 1) (j i : Nat) :
    ParR (C.set 1 [1, 1, 1]) k j i ↔ ParR C k j i :=
  ParR_congr_rows _ _ k (fun i k' hk' => set_one_rows01 h i k' (by omega)) j i

theorem AncR_set_one_low (h : C[1]? = some [1, 1, 0]) (k : Nat) (hk : k ≤ 1) :
    Relation.TransGen (ParR (C.set 1 [1, 1, 1]) k) = Relation.TransGen (ParR C k) := by
  have e : ParR (C.set 1 [1, 1, 1]) k = ParR C k := by
    funext a b; exact propext (ParR_set_one_low h k hk a b)
  rw [e]

theorem ParR_two_def (l : List (List Nat)) (j i : Nat) : ParR l 2 j i ↔
    (j < i ∧ Relation.TransGen (ParR l 1) j i ∧ (l[j]!)[2]! < (l[i]!)[2]! ∧
      ∀ j', j < j' → j' < i → Relation.TransGen (ParR l 1) j' i → (l[i]!)[2]! ≤ (l[j']!)[2]!) :=
  Iff.rfl

/-- **The row-`2` parent of a column other than column `1`** is the same in the
raised list, unless it is column `1` and the entry is `1`. -/
theorem ParR_two_iff (h : C[1]? = some [1, 1, 0]) {i : Nat} (hi : i ≠ 1)
    (hH : ParR C 2 1 i → 2 ≤ (C[i]!)[2]!) (j : Nat) :
    ParR (C.set 1 [1, 1, 1]) 2 j i ↔ ParR C 2 j i := by
  have hl : 1 < C.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hA := AncR_set_one_low h 1 le_rfl
  have ei : ((C.set 1 [1, 1, 1])[i]!)[2]! = (C[i]!)[2]! := by rw [set_one_get_ne _ hi]
  have e1A : ((C.set 1 [1, 1, 1])[1]!)[2]! = 1 := by rw [set_one_get_one _ hl]; rfl
  have e1C : (C[1]!)[2]! = 0 := by rw [get_one_of h]; rfl
  have ej : ∀ j', j' ≠ 1 → ((C.set 1 [1, 1, 1])[j']!)[2]! = (C[j']!)[2]! := by
    intro j' hj'; rw [set_one_get_ne _ hj']
  rw [ParR_two_def, ParR_two_def, hA, ei]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hj1 : j = 1
    · subst hj1
      refine ⟨h1, h2, by rw [e1C]; rw [e1A] at h3; omega, fun j' a b c => ?_⟩
      have := h4 j' a b c
      rwa [ej j' (by omega)] at this
    · rw [ej j hj1] at h3
      by_cases hmid : j < 1 ∧ 1 < i ∧ Relation.TransGen (ParR C 1) 1 i
      · -- column `1` is a candidate between: in `C` it is the parent
        have h41 := h4 1 hmid.1 hmid.2.1 hmid.2.2
        rw [e1A] at h41
        have hp1 : ParR C 2 1 i := by
          refine (ParR_two_def C 1 i).mpr ⟨hmid.2.1, hmid.2.2, by rw [e1C]; omega, fun j' a b c => ?_⟩
          have := h4 j' (by omega) b c
          rwa [ej j' (by omega)] at this
        have := hH hp1
        omega
      · refine ⟨h1, h2, h3, fun j' a b c => ?_⟩
        by_cases hj' : j' = 1
        · subst hj'; exact absurd ⟨a, b, c⟩ hmid
        · have := h4 j' a b c
          rwa [ej j' hj'] at this
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hj1 : j = 1
    · subst hj1
      have hv := hH ((ParR_two_def C 1 i).mpr ⟨h1, h2, h3, h4⟩)
      refine ⟨h1, h2, by rw [e1A]; omega, fun j' a b c => ?_⟩
      have := h4 j' a b c
      rwa [← ej j' (by omega)] at this
    · refine ⟨h1, h2, by rw [ej j hj1]; exact h3, fun j' a b c => ?_⟩
      by_cases hj' : j' = 1
      · subst hj'
        have := h4 1 a b c
        rw [e1C] at this
        rw [e1A]; omega
      · have := h4 j' a b c
        rwa [← ej j' hj'] at this

/-- The hypothesis on the last column. -/
def LastOK (C : List (List Nat)) : Prop :=
  ParR C 2 1 (C.length - 1) → 2 ≤ (C[C.length - 1]!)[2]!

theorem parAtR_set_one_last (h : C[1]? = some [1, 1, 0]) (hn : 3 ≤ C.length) (hH : LastOK C)
    (k : Nat) (hk : k ≤ 2) :
    parAtR (C.set 1 [1, 1, 1]) k (C.length - 1) = parAtR C k (C.length - 1) := by
  apply Option.ext
  intro j
  rw [parAtR_eq_some, parAtR_eq_some]
  by_cases hk2 : k = 2
  · subst hk2
    exact ParR_two_iff h (by omega) hH j
  · exact ParR_set_one_low h k (by omega) j _

theorem m0L_set_one (h : C[1]? = some [1, 1, 0]) (hn : 3 ≤ C.length) (hH : LastOK C) :
    m0L 3 (C.set 1 [1, 1, 1]) = m0L 3 C := by
  rw [m0L, m0L, List.length_set]
  exact findGreatest_congr (3 - 1) (fun k hk => by
    rw [parAtR_set_one_last h hn hH k (by omega)])

theorem badRootR_set_one (h : C[1]? = some [1, 1, 0]) (hn : 3 ≤ C.length) (hH : LastOK C) :
    badRootR 3 (C.set 1 [1, 1, 1]) = badRootR 3 C := by
  have hne : C ≠ [] := by
    rintro rfl; simp at hn
  have hne' : C.set 1 [1, 1, 1] ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [List.length_set, List.length_nil] at this
    omega
  rw [badRootR, badRootR, if_neg (by simpa [List.isEmpty_iff] using hne'),
    if_neg (by simpa [List.isEmpty_iff] using hne), m0L_set_one h hn hH, List.length_set]
  exact parAtR_set_one_last h hn hH _ (by have := m0L_lt (by norm_num : 0 < 3) C; omega)

theorem ancAtR_set_one_low (h : C[1]? = some [1, 1, 0]) (k : Nat) (hk : k ≤ 1) (p x : Nat) :
    ancAtR (C.set 1 [1, 1, 1]) k p x = ancAtR C k p x := by
  have e : parAtR (C.set 1 [1, 1, 1]) k = parAtR C k :=
    funext (parAtR_congr (ParR_set_one_low h k hk))
  rw [ancAtR, ancAtR, e]

theorem map_range_set_one (h : C[1]? = some [1, 1, 0]) (p : Nat) :
    (List.range p).map (fun i => (C.set 1 [1, 1, 1])[i]!)
      = ((List.range p).map (fun i => C[i]!)).set 1 [1, 1, 1] := by
  have hl : 1 < C.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_set, List.getElem_map, List.getElem_map, List.getElem_range]
  split
  · rename_i he; subst he; exact set_one_get_one _ hl
  · rename_i he; exact set_one_get_ne _ (by omega)

theorem dropLast_set_one :
    (C.set 1 [1, 1, 1]).dropLast = C.dropLast.set 1 [1, 1, 1] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_dropLast, List.getElem_set, List.getElem_set, List.getElem_dropLast]

/-- **Raising column `1` commutes with expansion** when the bad root is not
column `0` or `1` and the last column meets `LastOK`. -/
theorem expandRL_set_one (h : C[1]? = some [1, 1, 0]) (hn : 3 ≤ C.length) (hH : LastOK C)
    (hb : ∀ p, badRootR 3 C = some p → 2 ≤ p) (N : Nat) :
    expandRL 3 N (C.set 1 [1, 1, 1]) = (expandRL 3 N C).set 1 [1, 1, 1] := by
  have hbr := badRootR_set_one h hn hH
  have hm := m0L_set_one h hn hH
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  cases hB : badRootR 3 C with
  | none =>
    rw [expandRL, hbr, hB, expandRL, hB]
    exact dropLast_set_one
  | some p =>
    have hp2 := hb p hB
    have hp : p + 1 < C.length := badRootR_lt hB
    rw [expandRL, hbr, hB, expandRL, hB]
    dsimp only
    rw [hm, List.length_set, List.set_append_left _ _ (by simp; omega), map_range_set_one h p]
    congr 1
    refine List.map_congr_left (fun t _ => ?_)
    have hs : 0 < C.length - 1 - p := by omega
    have hx : p + t % (C.length - 1 - p) ≠ 1 := by omega
    rw [set_one_get_ne _ hx, set_one_get_ne _ (i := C.length - 1) (by omega),
      set_one_get_ne _ (i := p) (by omega)]
    refine List.map_congr_left (fun k _ => ?_)
    by_cases hkm : k < m0L 3 C
    · rw [ancAtR_set_one_low h k (by omega)]
    · simp [hkm]

end Raise

/-! ### The reduction -/

theorem t3Cond_of_expand {C : List (List Nat)} (hv : Valid 2 C) (hR : Rooted C) {N : Nat}
    (hD : T3Cond (expandRL 3 N C)) : T3Cond C ∧ 3 ≤ C.length := by
  obtain ⟨v, hvm, hv2⟩ := hD.2
  obtain ⟨j, hj, hj2⟩ := exists_row2_pos_of_expandRL hvm hv2
  have hj0 : j ≠ 0 := by
    rintro rfl
    have := hR.1 2
    omega
  obtain ⟨Z, hZ⟩ := expandRL_eq_dropLast_append N hv
  have hC1 : (expandRL 3 N C)[1]? = C[1]? := by
    rw [hZ, List.getElem?_append_left (by simp; omega), List.getElem?_dropLast,
      if_pos (by omega)]
  exact ⟨⟨hC1 ▸ hD.1, C[j]!, getElem!_mem C j (by omega), hj2⟩, by omega⟩

/-- The shapes where `t3` need not commute with the expansion. -/
def NonComm (C : List (List Nat)) (N : Nat) : Prop :=
  T3Cond C ∧ (¬ T3Cond (expandRL 3 N C) ∨ ∃ p, badRootR 3 C = some p ∧ p ≤ 1)

/-- A bad root at column `2` or later gives `LastOK`: if column `1` were the
row-`2` parent of the last column, it would be the bad root. -/
theorem lastOK_of_badRoot {C : List (List Nat)} (hne : C ≠ [])
    (hb : ∀ p, badRootR 3 C = some p → 2 ≤ p) : LastOK C := by
  intro hp
  have hs : (parAtR C 2 (C.length - 1)).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨1, (parAtR_eq_some _ _ _ _).mpr hp⟩
  have hm : m0L 3 C = 2 := by
    rw [m0L]; exact Nat.findGreatest_eq hs
  have hb1 : badRootR 3 C = some 1 := by
    rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
    exact (parAtR_eq_some _ _ _ _).mpr hp
  exact absurd (hb 1 hb1) (by omega)

/-- **Open.**  `T3RankDesc` in the shapes `NonComm`. -/
def T3RankDescNC : Prop := ∀ C, SReach C → C ≠ [] → ∀ N, NonComm C N →
  rkL 2 (t3 (expandRL 3 N C)) < rkL 2 (t3 C)

theorem valid_set_one {C : List (List Nat)} (hv : Valid 2 C) : Valid 2 (C.set 1 [1, 1, 1]) := by
  intro v hv'
  rcases List.mem_or_eq_of_mem_set hv' with h | h
  · exact hv v h
  · rw [h]; rfl

/-- **`T3RankDesc` reduces to the shapes `NonComm`.** -/
theorem t3RankDesc_of_NC (h : T3RankDescNC) : T3RankDesc := by
  intro C hC hne N
  by_cases hnc : NonComm C N
  · exact h C hC hne N hnc
  · by_cases hD : T3Cond (expandRL 3 N C)
    · obtain ⟨hCc, hn⟩ := t3Cond_of_expand hC.valid hC.rooted hD
      have hb : ∀ p, badRootR 3 C = some p → 2 ≤ p := fun p hp => by
        by_contra hlt
        exact hnc ⟨hCc, Or.inr ⟨p, hp, by omega⟩⟩
      have hH : LastOK C := lastOK_of_badRoot hne hb
      have e : expandRL 3 N (t3 C) = t3 (expandRL 3 N C) := by
        rw [t3, if_pos hCc, t3, if_pos hD, expandRL_set_one hCc.1 hn hH hb N]
      rw [← e, t3, if_pos hCc]
      have hne' : C.set 1 [1, 1, 1] ≠ [] := by
        intro e'
        have := congrArg List.length e'
        rw [List.length_set, List.length_nil] at this
        omega
      exact rkL_lt (valid_set_one hC.valid) hne' N
    · have hCc : ¬ T3Cond C := fun hCc => hnc ⟨hCc, Or.inl hD⟩
      rw [t3, if_neg hD, t3, if_neg hCc]
      exact rkL_lt hC.valid hne N

/-- **The upper bound at `n = 2` under the reduced hypothesis.** -/
theorem rkL_cgen_two_four_eq_of_NC (h : T3RankDescNC) : rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of (t3RankDesc_of_NC h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.expandRL_set_one
#print axioms Googology.Trans.DBMS.t3RankDesc_of_NC
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_NC
