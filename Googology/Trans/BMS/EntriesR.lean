import Googology.Trans.BMS.Anc

/-!
# Parents and ancestors at every row

`BMS/Anc.lean` reads `BM4.parent A 0` and `BM4.anc A 0` off the entries, which
is what two rows need.  Three rows need row `1`'s as well, and `r` rows need
every row below `r`.  This file does all of them at once.

`entriesR` reads an array off column by column, each column as its `r`
entries.  `ParR l k` is being the row-`k` parent — the last candidate before
the column whose row-`k` entry is smaller — where row `0`'s candidates are all
the earlier columns and row `k + 1`'s are the strict row-`k` ancestors, so the
definition recurses on the row.  `ParR_iff_parent` and `AncR_iff_anc` say
these are `BM4.parent A k` and `BM4.anc A k` for every `k < r`.

`parAtR` computes the parent and `ancAtR` chases the chain.  The chase carries
fuel rather than a well-founded measure, because the parent function is a
parameter at the point of definition and its decrease is only available
afterwards; `chase_iff` is the correctness, and the fuel is the starting index,
which always suffices.

`expandRL` is then the whole expansion rule on the entries, for any number of
rows, and `entriesR_expand` says it is `BM4.expand`.  So every Bashicu matrix
expansion runs, which the array form does not — `BM4.expand` is
`noncomputable`.

`BMS/Anc.lean` stays: it is the row-`0` case on a flat list of entries, which
is the shape `BMS/Entries2.lean` uses.
-/

namespace Googology.Trans.BMS

open BM4

variable {r : Nat}

/-- Every row of an array, column by column. -/
def entriesR (A : Arr r) : List (List Nat) :=
  (List.range A.len).map (fun i => (List.range r).map (A.col i))

@[simp] theorem entriesR_length (A : Arr r) : (entriesR A).length = A.len := by
  rw [entriesR, List.length_map, List.length_range]

theorem entriesR_col (A : Arr r) {i : Nat} (hi : i < A.len) :
    (entriesR A)[i]! = (List.range r).map (A.col i) := by
  rw [entriesR, getElem!_pos _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem entriesR_getElem (A : Arr r) {i k : Nat} (hi : i < A.len) (hk : k < r) :
    ((entriesR A)[i]!)[k]! = A.col i k := by
  rw [entriesR_col A hi, getElem!_pos _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range]

theorem entriesR_getElem_of_ge (A : Arr r) {i : Nat} (hi : ¬ i < A.len) (k : Nat) :
    ((entriesR A)[i]!)[k]! = 0 := by
  rw [getElem!_neg (entriesR A) i (by rw [entriesR_length]; exact hi)]
  rfl

/-- Being the row-`k` parent, on the entries: the last candidate before `i`
whose row-`k` entry is smaller.  Row `0`'s candidates are all the earlier
columns; row `k + 1`'s are the strict row-`k` ancestors. -/
def ParR (l : List (List Nat)) : Nat → Nat → Nat → Prop
  | 0, j, i => j < i ∧ (l[j]!)[0]! < (l[i]!)[0]! ∧
      ∀ j', j < j' → j' < i → (l[i]!)[0]! ≤ (l[j']!)[0]!
  | k + 1, j, i => j < i ∧ Relation.TransGen (ParR l k) j i ∧
      (l[j]!)[k + 1]! < (l[i]!)[k + 1]! ∧
      ∀ j', j < j' → j' < i → Relation.TransGen (ParR l k) j' i →
        (l[i]!)[k + 1]! ≤ (l[j']!)[k + 1]!

/-- Being a strict row-`k` ancestor. -/
def AncR (l : List (List Nat)) (k : Nat) : Nat → Nat → Prop :=
  Relation.TransGen (ParR l k)

theorem anc_eq (A : Arr r) (k : Nat) : anc A k = Relation.TransGen (parent A k) := by
  cases k <;> rfl

theorem parent_lt_len {A : Arr r} {k j i : Nat} (h : parent A k j i) : i < A.len :=
  h.2.2.2.2.2

theorem ancR_lt_len {A : Arr r} {k j i : Nat} (h : anc A k j i) : i < A.len := by
  rw [anc_eq] at h
  obtain ⟨b, _, hb⟩ := Relation.TransGen.tail'_iff.mp h
  exact parent_lt_len hb

/-- **Being the row-`k` parent is a condition on the entries**, for every row
of the array. -/
theorem ParR_iff_parent (A : Arr r) : ∀ (k : Nat), k < r → ∀ (j i : Nat),
    ParR (entriesR A) k j i ↔ parent A k j i := by
  intro k
  induction k with
  | zero =>
    intro hk j i
    rw [parent_row0_iff (by omega), ParR]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hi : i < A.len := by
        by_contra hc
        rw [entriesR_getElem_of_ge A hc 0] at h2
        omega
      rw [entriesR_getElem A (by omega) hk, entriesR_getElem A hi hk] at h2
      refine ⟨h1, h2, ?_, hi⟩
      intro j' a b
      have := h3 j' a b
      rwa [entriesR_getElem A hi hk, entriesR_getElem A (show j' < A.len by omega) hk] at this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [entriesR_getElem A (show j < A.len by omega) hk, entriesR_getElem A h4 hk]
        exact h2
      · intro j' a b
        rw [entriesR_getElem A h4 hk, entriesR_getElem A (show j' < A.len by omega) hk]
        exact h3 j' a b
  | succ m ih =>
    intro hk j i
    have ihm : ∀ a b, ParR (entriesR A) m a b ↔ parent A m a b := ih (by omega)
    have hanc : ∀ a b, Relation.TransGen (ParR (entriesR A) m) a b ↔ anc A m a b := by
      intro a b
      rw [anc_eq]
      constructor
      · intro h
        induction h with
        | single hp => exact Relation.TransGen.single ((ihm _ _).mp hp)
        | tail _ hp ih2 => exact Relation.TransGen.tail ih2 ((ihm _ _).mp hp)
      · intro h
        induction h with
        | single hp => exact Relation.TransGen.single ((ihm _ _).mpr hp)
        | tail _ hp ih2 => exact Relation.TransGen.tail ih2 ((ihm _ _).mpr hp)
    rw [ParR]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have ha := (hanc j i).mp h2
      have hi : i < A.len := ancR_lt_len ha
      rw [entriesR_getElem A (show j < A.len by omega) hk, entriesR_getElem A hi hk] at h3
      refine ⟨h1, ha, h3, ?_, by omega, hi⟩
      intro j' a b hc
      have := h4 j' a b ((hanc j' i).mpr hc)
      rwa [entriesR_getElem A hi hk, entriesR_getElem A (show j' < A.len by omega) hk] at this
    · rintro ⟨h1, h2, h3, h4, _, h6⟩
      refine ⟨h1, (hanc j i).mpr h2, ?_, ?_⟩
      · rw [entriesR_getElem A (show j < A.len by omega) hk, entriesR_getElem A h6 hk]
        exact h3
      · intro j' a b hc
        rw [entriesR_getElem A h6 hk, entriesR_getElem A (show j' < A.len by omega) hk]
        exact h4 j' a b ((hanc j' i).mp hc)

/-- **And so is being a strict row-`k` ancestor.** -/
theorem AncR_iff_anc (A : Arr r) (k : Nat) (hk : k < r) (j i : Nat) :
    AncR (entriesR A) k j i ↔ anc A k j i := by
  rw [AncR, anc_eq]
  constructor
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((ParR_iff_parent A k hk _ _).mp hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((ParR_iff_parent A k hk _ _).mp hp)
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((ParR_iff_parent A k hk _ _).mpr hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((ParR_iff_parent A k hk _ _).mpr hp)

/-! ### Computing it -/

/-- Chase a parent function down from `i`, at most `fuel` steps. -/
def chase (par : Nat → Option Nat) (p : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
      match par i with
      | none => false
      | some j => (j == p) || chase par p fuel j

/-- **Chasing finds the ancestors**, as long as the parent goes down and the
fuel covers the start. -/
theorem chase_iff (par : Nat → Option Nat) (hdec : ∀ i j, par i = some j → j < i)
    (p : Nat) : ∀ (fuel i : Nat), i ≤ fuel →
      (chase par p fuel i = true ↔ Relation.TransGen (fun a b => par b = some a) p i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    rw [chase]
    simp only [Bool.false_eq_true, false_iff]
    intro hA
    obtain ⟨b, _, hb⟩ := Relation.TransGen.tail'_iff.mp hA
    have := hdec i b hb
    omega
  | succ m ih =>
    intro i hi
    rw [chase]
    cases h : par i with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      intro hA
      obtain ⟨b, _, hb⟩ := Relation.TransGen.tail'_iff.mp hA
      rw [h] at hb
      exact absurd hb (by simp)
    | some j =>
      have hj : j < i := hdec i j h
      simp only [Bool.or_eq_true, beq_iff_eq]
      rw [ih j (by omega)]
      constructor
      · rintro (he | hA)
        · exact Relation.TransGen.single (by rw [he] at h; exact h)
        · exact Relation.TransGen.tail hA h
      · intro hA
        obtain ⟨b, hr, hb⟩ := Relation.TransGen.tail'_iff.mp hA
        rw [h] at hb
        rw [← Option.some.inj hb] at hr
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hr with he | ht
        · exact Or.inl he
        · exact Or.inr ht

/-- The row-`k` parent of `i`, computed from the entries. -/
def parAtR (l : List (List Nat)) : Nat → Nat → Option Nat
  | 0, i => lastAux (fun _ => true) (fun j => (l[j]!)[0]!) ((l[i]!)[0]!) i
  | k + 1, i =>
      lastAux (fun j => chase (parAtR l k) j i i) (fun j => (l[j]!)[k + 1]!)
        ((l[i]!)[k + 1]!) i

theorem parAtR_lt (l : List (List Nat)) : ∀ (k i j : Nat), parAtR l k i = some j → j < i := by
  intro k
  cases k with
  | zero => intro i j h; exact ((lastAux_eq_some _ _ _ i j).mp h).1
  | succ m => intro i j h; exact ((lastAux_eq_some _ _ _ i j).mp h).1

/-- **The computed parent is the row-`k` parent.** -/
theorem parAtR_eq_some (l : List (List Nat)) : ∀ (k i j : Nat),
    parAtR l k i = some j ↔ ParR l k j i := by
  intro k
  induction k with
  | zero =>
    intro i j
    rw [parAtR, lastAux_eq_some, ParR]
    simp only [forall_const]
    constructor
    · rintro ⟨h1, _, h3, h4⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, trivial, h2, h3⟩
  | succ m ih =>
    intro i j
    have hanc : ∀ a b : Nat, Relation.TransGen (fun x y => parAtR l m y = some x) a b
        ↔ Relation.TransGen (ParR l m) a b := by
      intro a b
      constructor
      · intro h
        induction h with
        | single hp => exact Relation.TransGen.single ((ih _ _).mp hp)
        | tail _ hp ih2 => exact Relation.TransGen.tail ih2 ((ih _ _).mp hp)
      · intro h
        induction h with
        | single hp => exact Relation.TransGen.single ((ih _ _).mpr hp)
        | tail _ hp ih2 => exact Relation.TransGen.tail ih2 ((ih _ _).mpr hp)
    rw [parAtR, lastAux_eq_some, ParR]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, h3, ?_⟩
      · exact (hanc j i).mp ((chase_iff _ (parAtR_lt l m) j i i (Nat.le_refl i)).mp h2)
      · intro j' a b hc
        exact h4 j' a b ((chase_iff _ (parAtR_lt l m) j' i i (Nat.le_refl i)).mpr
          ((hanc j' i).mpr hc))
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, h3, ?_⟩
      · exact (chase_iff _ (parAtR_lt l m) j i i (Nat.le_refl i)).mpr ((hanc j i).mpr h2)
      · intro j' a b hc
        exact h4 j' a b ((hanc j' i).mp
          ((chase_iff _ (parAtR_lt l m) j' i i (Nat.le_refl i)).mp hc))

instance (l : List (List Nat)) (k j i : Nat) : Decidable (ParR l k j i) :=
  decidable_of_iff (parAtR l k i = some j) (parAtR_eq_some l k i j)

/-- Whether `p` is a strict row-`k` ancestor of `i`, computed. -/
def ancAtR (l : List (List Nat)) (k p i : Nat) : Bool := chase (parAtR l k) p i i

theorem ancAtR_iff (l : List (List Nat)) (k p i : Nat) :
    ancAtR l k p i = true ↔ AncR l k p i := by
  rw [ancAtR, AncR, chase_iff _ (parAtR_lt l k) p i i (Nat.le_refl i)]
  constructor
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((parAtR_eq_some l k _ _).mp hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((parAtR_eq_some l k _ _).mp hp)
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((parAtR_eq_some l k _ _).mpr hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((parAtR_eq_some l k _ _).mpr hp)


/-! ### Expansion -/

theorem findGreatest_congr {P Q : Nat → Prop} [DecidablePred P] [DecidablePred Q] :
    ∀ n : Nat, (∀ k, k ≤ n → (P k ↔ Q k)) → Nat.findGreatest P n = Nat.findGreatest Q n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [Nat.findGreatest, Nat.findGreatest, ih (fun k hk => h k (by omega))]
    by_cases hp : P (m + 1)
    · rw [if_pos hp, if_pos ((h (m + 1) (Nat.le_refl _)).mp hp)]
    · rw [if_neg hp, if_neg (fun hq => hp ((h (m + 1) (Nat.le_refl _)).mpr hq))]

theorem hasParent_iff (A : Arr r) (k : Nat) (hk : k < r) (i : Nat) :
    HasParent A k i ↔ (parAtR (entriesR A) k i).isSome = true := by
  constructor
  · rintro ⟨j, hj⟩
    rw [Option.isSome_iff_exists]
    exact ⟨j, (parAtR_eq_some _ _ _ _).mpr ((ParR_iff_parent A k hk j i).mpr hj)⟩
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, (ParR_iff_parent A k hk j i).mp ((parAtR_eq_some _ _ _ _).mp hj)⟩

/-- The maximal parent row of the last column, computed from the entries. -/
def m0L (r : Nat) (l : List (List Nat)) : Nat :=
  Nat.findGreatest (fun k => (parAtR l k (l.length - 1)).isSome = true) (r - 1)

open Classical in
theorem m0L_eq (hr : 0 < r) (A : Arr r) : m0L r (entriesR A) = m₀ A := by
  rw [m0L, m₀, entriesR_length]
  exact findGreatest_congr (r - 1) (fun k hk =>
    (hasParent_iff A k (by omega) (A.len - 1)).symm)

/-- The bad root, computed from the entries. -/
def badRootR (r : Nat) (l : List (List Nat)) : Option Nat :=
  if l.isEmpty then none else parAtR l (m0L r l) (l.length - 1)

theorem badRootR_some (hr : 0 < r) {A : Arr r} {p : Nat}
    (h : badRootR r (entriesR A) = some p) : parent A (m₀ A) p (A.len - 1) := by
  rw [badRootR] at h
  rw [if_neg (by
    simp only [List.isEmpty_iff]
    intro he
    rw [he] at h
    exact absurd h (by simp))] at h
  rw [entriesR_length, m0L_eq hr A] at h
  exact (ParR_iff_parent A (m₀ A) (m₀_lt hr) p _).mp ((parAtR_eq_some _ _ _ _).mp h)

theorem badRootR_none (hr : 0 < r) {A : Arr r} (h : badRootR r (entriesR A) = none)
    (h0 : A.len ≠ 0) : ¬ LastHasParent A := by
  rw [badRootR, if_neg (by
    simp only [List.isEmpty_iff]
    intro he
    exact h0 (by have := entriesR_length A; rw [he] at this; exact this.symm))] at h
  rw [entriesR_length, m0L_eq hr A] at h
  rintro ⟨_, k, hk, hpk⟩
  have hm : HasParent A (m₀ A) (A.len - 1) := m₀_hasParent (A := A) ⟨by omega, k, hk, hpk⟩
  rw [hasParent_iff A _ (m₀_lt hr)] at hm
  rw [h] at hm
  exact absurd hm (by simp)

/-- **Expansion, written on the entries, for any number of rows.** -/
def expandRL (r : Nat) (N : Nat) (l : List (List Nat)) : List (List Nat) :=
  match badRootR r l with
  | none => l.dropLast
  | some p =>
      (List.range p).map (fun i => l[i]!)
        ++ (List.range ((N + 1) * (l.length - 1 - p))).map (fun t =>
              (List.range r).map (fun k =>
                if decide (k < m0L r l) && ((p == p + t % (l.length - 1 - p))
                    || ancAtR l k p (p + t % (l.length - 1 - p))) then
                  (l[p + t % (l.length - 1 - p)]!)[k]!
                    + (t / (l.length - 1 - p))
                      * ((l[l.length - 1]!)[k]! - (l[p]!)[k]!)
                else (l[p + t % (l.length - 1 - p)]!)[k]!))

/-- **The array and its entries expand the same way, for any number of
rows.** -/
theorem entriesR_expand (hr : 0 < r) (A : Arr r) (N : Nat) :
    entriesR (expand A N) = expandRL r N (entriesR A) := by
  cases hb : badRootR r (entriesR A) with
  | none =>
    rw [expandRL, hb]
    dsimp only
    by_cases h0 : A.len = 0
    · rw [expand_of_len_zero h0, entriesR, h0, List.range_zero, List.map_nil]
      rfl
    · rw [expand_of_not_lastHasParent h0 (badRootR_none hr hb h0) N, entriesR, entriesR,
        map_range_dropLast]
      rfl
  | some p =>
    have hpar := badRootR_some hr hb
    have hp1 : p < A.len - 1 := hpar.1
    have hp6 : A.len - 1 < A.len := hpar.2.2.2.2.2
    have hsp : 0 < A.len - 1 - p := by omega
    rw [expandRL, hb, entriesR_length]
    dsimp only
    have hgood : ∀ i, i < p →
        (List.range r).map ((expand A N).col i) = (entriesR A)[i]! := by
      intro i hi
      rw [entriesR_col A (by omega)]
      refine List.map_congr_left (fun k _ => ?_)
      rw [expand_col_of_parent hr hpar N i k, tildeCol_lt A p (m₀ A) _ i k hi]
    have hbad : ∀ t : Nat,
        (List.range r).map ((expand A N).col (p + t))
          = (List.range r).map (fun k =>
              if decide (k < m₀ A) && ((p == p + t % (A.len - 1 - p))
                  || ancAtR (entriesR A) k p (p + t % (A.len - 1 - p))) then
                ((entriesR A)[p + t % (A.len - 1 - p)]!)[k]!
                  + (t / (A.len - 1 - p))
                    * (((entriesR A)[A.len - 1]!)[k]! - ((entriesR A)[p]!)[k]!)
              else ((entriesR A)[p + t % (A.len - 1 - p)]!)[k]!) := by
      intro t
      have hmem : p + t % (A.len - 1 - p) < A.len := by
        have := Nat.mod_lt t hsp; omega
      refine List.map_congr_left (fun k hk0 => ?_)
      have hk : k < r := List.mem_range.mp hk0
      rw [expand_col_of_parent hr hpar N (p + t) k,
        tildeCol_ge A p (m₀ A) _ (p + t) k (by omega),
        show p + t - p = t from by omega,
        entriesR_getElem A hmem hk, entriesR_getElem A hp6 hk,
        entriesR_getElem A (by omega) hk]
      have hcond : ((p == p + t % (A.len - 1 - p))
          || ancAtR (entriesR A) k p (p + t % (A.len - 1 - p))) = true
          ↔ ancEq A k p (p + t % (A.len - 1 - p)) := by
        rw [Bool.or_eq_true, beq_iff_eq, ancAtR_iff, ancEq]
        exact or_congr Iff.rfl (AncR_iff_anc A k hk p _)
      by_cases hm : k < m₀ A
      · by_cases hc : ancEq A k p (p + t % (A.len - 1 - p))
        · rw [if_pos ⟨hm, hc⟩, if_pos (by
            rw [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hm, hcond.mpr hc⟩)]
        · rw [if_neg (fun hx => hc hx.2), if_neg (by
            rw [Bool.and_eq_true, decide_eq_true_eq]
            exact fun hx => hc (hcond.mp hx.2))]
      · rw [if_neg (fun hx => hm hx.1), if_neg (by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact fun hx => hm hx.1)]
    rw [entriesR, expand_len_of_parent hr hpar N, List.range_add, List.map_append,
      List.map_map]
    congr 1
    · exact List.map_congr_left (fun i hi => hgood i (List.mem_range.mp hi))
    · refine List.map_congr_left (fun t _ => ?_)
      simp only [Function.comp_apply]
      rw [hbad t, m0L_eq hr A]

end Googology.Trans.BMS
