import Googology.Trans.BMS.Agree

/-!
# Expansion only looks at the last block

A matrix whose columns start over — a column whose row-`0` entry is `0` —
begins a new block, and expansion never reaches back across one.  This file
proves that on the entries, at every number of rows.

The reason is the row-`0` parent: it is the last earlier column with a smaller
row-`0` entry, and a column with entry `0` has none at all, so a parent chain
that starts inside the last block stays there.  Row `k + 1`'s candidates are
row `k`'s ancestors, so the same holds at every row.

`ParR_append_ge` is that statement and `ParR_append_iff` is the translation
that comes with it.  What they give is `expandRL_append`: expanding `A ++ B`
is expanding `B`, with `A` in front.
-/

namespace Googology.Trans.BMS

open BM4

theorem getElem!_append_left (A B : List (List Nat)) {j : Nat} (h : j < A.length) :
    (A ++ B)[j]! = A[j]! := by
  rw [getElem!_pos (A ++ B) j (by rw [List.length_append]; omega), getElem!_pos A j h,
    List.getElem_append_left h]

theorem getElem!_append_right (A B : List (List Nat)) (i : Nat) :
    (A ++ B)[A.length + i]! = B[i]! := by
  by_cases h : i < B.length
  · rw [getElem!_pos (A ++ B) (A.length + i) (by rw [List.length_append]; omega),
      getElem!_pos B i h, List.getElem_append_right (by omega)]
    congr 1
    omega
  · rw [getElem!_neg (A ++ B) (A.length + i) (by rw [List.length_append]; omega),
      getElem!_neg B i h]

/-- **A parent never reaches back across a block boundary.**  `B` starts with a
column whose row-`0` entry is `0`, and such a column has no parent, so nothing
inside `B` has one outside it. -/
theorem ParR_append_ge (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ []) :
    ∀ (k j i : Nat), A.length ≤ i → ParR (A ++ B) k j i → A.length ≤ j := by
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hB
  intro k
  induction k with
  | zero =>
    intro j i hi hp
    rw [ParR] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    by_contra hc
    push Not at hc
    have hzero : ((A ++ B)[A.length]!)[0]! = 0 := by
      rw [show A.length = A.length + 0 from (Nat.add_zero _).symm, getElem!_append_right]
      exact h0
    rcases Nat.lt_or_ge A.length i with hlt | hge
    · have := h3 A.length hc hlt
      rw [hzero] at this
      omega
    · have hEq : i = A.length := by omega
      rw [hEq, hzero] at h2
      omega
  | succ m ih =>
    intro j i hi hp
    rw [ParR] at hp
    have hanc := hp.2.1
    clear hp
    revert hi
    induction hanc with
    | single hs => intro hi; exact ih _ _ hi hs
    | @tail b c _ hs ih2 => intro hi; exact ih2 (ih _ _ hi hs)

/-- **Inside the last block the parent relation is the block's own.** -/
theorem ParR_append_iff (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ []) :
    ∀ (k j i : Nat), ParR (A ++ B) k (A.length + j) (A.length + i) ↔ ParR B k j i := by
  intro k
  induction k with
  | zero =>
    intro j i
    rw [ParR, ParR]
    simp only [getElem!_append_right]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, fun j' a b => ?_⟩
      have := h3 (A.length + j') (by omega) (by omega)
      rwa [getElem!_append_right] at this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, fun j' a b => ?_⟩
      have hj' : j' = A.length + (j' - A.length) := by omega
      rw [hj', getElem!_append_right]
      exact h3 (j' - A.length) (by omega) (by omega)
  | succ m ih =>
    have hTGmp : ∀ (x y : Nat), Relation.TransGen (ParR (A ++ B) m) x y →
        ∀ b, y = A.length + b → ∃ a, x = A.length + a ∧ Relation.TransGen (ParR B m) a b := by
      intro x y hxy
      induction hxy with
      | @single y hs =>
        intro b hb
        subst hb
        have hx : A.length ≤ x := ParR_append_ge A B h0 hB m x _ (by omega) hs
        refine ⟨x - A.length, by omega, Relation.TransGen.single ?_⟩
        rw [← ih (x - A.length) b]
        rwa [show A.length + (x - A.length) = x from by omega]
      | @tail c y _ hs ih2 =>
        intro b hb
        subst hb
        have hc : A.length ≤ c := ParR_append_ge A B h0 hB m c _ (by omega) hs
        obtain ⟨a, ha, hpath⟩ := ih2 (c - A.length) (by omega)
        refine ⟨a, ha, Relation.TransGen.tail hpath ?_⟩
        rw [← ih (c - A.length) b]
        rwa [show A.length + (c - A.length) = c from by omega]
    have hTG : ∀ a b : Nat, Relation.TransGen (ParR (A ++ B) m) (A.length + a) (A.length + b)
        ↔ Relation.TransGen (ParR B m) a b := by
      intro a b
      constructor
      · intro h
        obtain ⟨a', ha', hpath⟩ := hTGmp _ _ h b rfl
        rwa [show a = a' from by omega]
      · intro h
        induction h with
        | single hs => exact Relation.TransGen.single ((ih _ _).mpr hs)
        | tail _ hs ih2 => exact Relation.TransGen.tail ih2 ((ih _ _).mpr hs)
    intro j i
    rw [ParR, ParR]
    simp only [getElem!_append_right]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨by omega, (hTG j i).mp h2, h3, fun j' a b hc => ?_⟩
      have := h4 (A.length + j') (by omega) (by omega) ((hTG j' i).mpr hc)
      rwa [getElem!_append_right] at this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨by omega, (hTG j i).mpr h2, h3, fun j' a b hc => ?_⟩
      have hj' : j' = A.length + (j' - A.length) := by omega
      rw [hj', getElem!_append_right]
      refine h4 (j' - A.length) (by omega) (by omega) ?_
      rw [← hTG (j' - A.length) i]
      rwa [← hj']

/-- **And so is the ancestor relation.** -/
theorem AncR_append_iff (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ [])
    (k a b : Nat) :
    AncR (A ++ B) k (A.length + a) (A.length + b) ↔ AncR B k a b := by
  have hmp : ∀ (x y : Nat), Relation.TransGen (ParR (A ++ B) k) x y →
      ∀ c, y = A.length + c → ∃ d, x = A.length + d ∧ Relation.TransGen (ParR B k) d c := by
    intro x y hxy
    induction hxy with
    | @single y hs =>
      intro c hc
      subst hc
      have hx : A.length ≤ x := ParR_append_ge A B h0 hB k x _ (by omega) hs
      refine ⟨x - A.length, by omega, Relation.TransGen.single ?_⟩
      rw [← ParR_append_iff A B h0 hB k (x - A.length) c]
      rwa [show A.length + (x - A.length) = x from by omega]
    | @tail e y _ hs ih2 =>
      intro c hc
      subst hc
      have he : A.length ≤ e := ParR_append_ge A B h0 hB k e _ (by omega) hs
      obtain ⟨d, hd, hpath⟩ := ih2 (e - A.length) (by omega)
      refine ⟨d, hd, Relation.TransGen.tail hpath ?_⟩
      rw [← ParR_append_iff A B h0 hB k (e - A.length) c]
      rwa [show A.length + (e - A.length) = e from by omega]
  rw [AncR, AncR]
  constructor
  · intro h
    obtain ⟨d, hd, hpath⟩ := hmp _ _ h b rfl
    rwa [show a = d from by omega]
  · intro h
    induction h with
    | single hs => exact Relation.TransGen.single ((ParR_append_iff A B h0 hB k _ _).mpr hs)
    | tail _ hs ih2 =>
      exact Relation.TransGen.tail ih2 ((ParR_append_iff A B h0 hB k _ _).mpr hs)

theorem ancAtR_append (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ [])
    (k p i : Nat) :
    ancAtR (A ++ B) k (A.length + p) (A.length + i) = ancAtR B k p i := by
  rw [Bool.eq_iff_iff, ancAtR_iff, ancAtR_iff]
  exact AncR_append_iff A B h0 hB k p i

/-! ### The computed pieces -/

theorem parAtR_append_some (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ [])
    (k i j : Nat) :
    parAtR (A ++ B) k (A.length + i) = some (A.length + j) ↔ parAtR B k i = some j := by
  rw [parAtR_eq_some, parAtR_eq_some]
  exact ParR_append_iff A B h0 hB k j i

theorem parAtR_append_isSome (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ [])
    (k i : Nat) :
    (parAtR (A ++ B) k (A.length + i)).isSome = (parAtR B k i).isSome := by
  rw [Bool.eq_iff_iff, Option.isSome_iff_exists, Option.isSome_iff_exists]
  constructor
  · rintro ⟨j, hj⟩
    have hge : A.length ≤ j :=
      ParR_append_ge A B h0 hB k j _ (by omega) ((parAtR_eq_some _ _ _ _).mp hj)
    refine ⟨j - A.length, ?_⟩
    rw [← parAtR_append_some A B h0 hB k i (j - A.length),
      show A.length + (j - A.length) = j from by omega]
    exact hj
  · rintro ⟨j, hj⟩
    exact ⟨A.length + j, (parAtR_append_some A B h0 hB k i j).mpr hj⟩

theorem m0L_append (r : Nat) (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ []) :
    m0L r (A ++ B) = m0L r B := by
  have hlen : (A ++ B).length - 1 = A.length + (B.length - 1) := by
    have : 0 < B.length := List.length_pos_iff.mpr hB
    rw [List.length_append]
    omega
  rw [m0L, m0L, hlen]
  exact findGreatest_congr (r - 1) (fun k _ => by
    rw [parAtR_append_isSome A B h0 hB k (B.length - 1)])

theorem badRootR_append (r : Nat) (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0) (hB : B ≠ []) :
    badRootR r (A ++ B) = (badRootR r B).map (fun p => A.length + p) := by
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hB
  have hlen : (A ++ B).length - 1 = A.length + (B.length - 1) := by
    rw [List.length_append]; omega
  have hne : ¬ (A ++ B).isEmpty = true := by
    simp only [List.isEmpty_iff]
    intro hc
    exact hB (List.append_eq_nil_iff.mp hc).2
  have hneB : ¬ B.isEmpty = true := by
    simp only [List.isEmpty_iff]
    exact hB
  rw [badRootR, badRootR, if_neg hne, if_neg hneB, hlen, m0L_append r A B h0 hB]
  cases hb : parAtR B (m0L r B) (B.length - 1) with
  | none =>
    rw [Option.map_none]
    by_contra hc
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hc
    have hge : A.length ≤ j :=
      ParR_append_ge A B h0 hB _ j _ (by omega) ((parAtR_eq_some _ _ _ _).mp hj)
    have hsome : parAtR B (m0L r B) (B.length - 1) = some (j - A.length) := by
      rw [← parAtR_append_some A B h0 hB _ (B.length - 1) (j - A.length),
        show A.length + (j - A.length) = j from by omega]
      exact hj
    rw [hb] at hsome
    exact absurd hsome (by simp)
  | some p =>
    rw [Option.map_some]
    exact (parAtR_append_some A B h0 hB _ (B.length - 1) p).mpr hb

/-! ### Expansion -/

theorem map_range_append_left (A B : List (List Nat)) :
    (List.range A.length).map (fun i => (A ++ B)[i]!) = A := by
  refine Eq.trans (List.map_congr_left (fun i hi => ?_)) (listEta A)
  exact getElem!_append_left A B (List.mem_range.mp hi)

/-- **Expansion only looks at the last block.** -/
theorem expandRL_append (r N : Nat) (A B : List (List Nat)) (h0 : (B[0]!)[0]! = 0)
    (hB : B ≠ []) : expandRL r N (A ++ B) = A ++ expandRL r N B := by
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hB
  have hlen : (A ++ B).length = A.length + B.length := List.length_append
  cases hb : badRootR r B with
  | none =>
    rw [expandRL, badRootR_append r A B h0 hB, hb, Option.map_none]
    conv_rhs => rw [expandRL, hb]
    dsimp only
    exact List.dropLast_append_of_ne_nil hB
  | some p =>
    have hs : (A ++ B).length - 1 - (A.length + p) = B.length - 1 - p := by rw [hlen]; omega
    have hlast : (A ++ B).length - 1 = A.length + (B.length - 1) := by rw [hlen]; omega
    rw [expandRL, badRootR_append r A B h0 hB, hb, Option.map_some]
    conv_rhs => rw [expandRL, hb]
    dsimp only
    rw [hs, hlast, m0L_append r A B h0 hB, ← List.append_assoc]
    congr 1
    · rw [List.range_add, List.map_append, List.map_map, map_range_append_left]
      congr 1
      refine List.map_congr_left (fun t _ => ?_)
      show (A ++ B)[A.length + t]! = B[t]!
      exact getElem!_append_right A B t
    · refine List.map_congr_left (fun t _ => ?_)
      refine List.map_congr_left (fun k _ => ?_)
      have hidx : A.length + p + t % (B.length - 1 - p) = A.length + (p + t % (B.length - 1 - p)) :=
        by omega
      rw [hidx, getElem!_append_right, getElem!_append_right, getElem!_append_right,
        ancAtR_append A B h0 hB,
        show (A.length + p == A.length + (p + t % (B.length - 1 - p)))
          = (p == p + t % (B.length - 1 - p)) from by
            rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
            omega]

end Googology.Trans.BMS
