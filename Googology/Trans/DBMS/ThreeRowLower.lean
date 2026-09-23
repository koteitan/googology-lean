import Googology.Trans.DBMS.ThreeRowLift

/-!
# Three-row DBMS reaches at least as far as three-row BMS

`ThreeRowLift.lean` writes the content generators of three-row DBMS as lifted
BMS generators, `cgen 2 (n + 2) = lift 3 (bgen3 n)` with
`bgen3 n = (0,0,0)(1,1,1)⋯(n,n,n)`, and conjectures that the lift keeps the
rank there.  This file proves one half of the conjecture, for every `n`:

    rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n + 2))            (rkL_bgen3_le_cgen)

and so **the ordinal of three-row BMS is at most the ordinal of three-row
DBMS** (`iSup_rank_bmsL_two_le_dbmsL`).

It comes from a statement about every matrix of a simple shape, not only the
generators: **the lift never lowers the rank** (`rkL_le_rkL_lift`),

    rkL 2 X ≤ rkL 2 (lift 3 X)

for every three-row matrix `X` that is rooted (`Rooted`: the first column is
zero, and so is every column with a `0` in row `0`) and whose columns with a
`0` in row `1` have a `0` in row `2` (`Nice`).  Both conditions survive
expansion (`rooted_expandRL`, `nice_expandRL`).  The proof is by induction on
`X`; it needs, for every `N`, that `lift 3 (X[N])` is below `lift 3 X`
(`rkL_lift_expandRL_lt`).  Let `c` be the last column of `X`.

* `c` has a positive row-`1` entry: then `c` keeps its parents under the lift
  (`liftGood_of_nice`), so the lift commutes with expansion (`expandRL_lift`)
  and `lift 3 (X[N]) = (lift 3 X)[N]`.
* `c` is a zero column: `X[N]` drops it, and so does `[0]` on the lift.
* `c = (x,0,0)` with `x > 0`: the lift does **not** commute.  In `lift 3 X`
  the last column is `(x+1,1,0)`, whose row-`1` parent is the new zero column
  in front, so the bad root is column `0` with `m₀ = 1`
  (`badRootR_lift_of_row1_zero`), and `(lift 3 X)[1]` starts with
  `liftTail X = (lift 3 X).dropLast ++ [(x+1,0,0)]` (`expandRL_one_lift_eq`).
  That tail expands exactly as `X` does: `(liftTail X)[N] = lift 3 (X[N])`
  (`expandRL_liftTail`).  So `lift 3 (X[N])` is below `liftTail X`, which is
  at most `(lift 3 X)[1]` (a prefix), which is below `lift 3 X`.

**What is not proved here** is the other half,
`rkL 2 (cgen 2 (n + 2)) ≤ rkL 2 (bgen3 n)`.  The lift itself does not keep
the rank state by state: already at `n = 1`,
`(bgen3 1)[N] = (0,0,0)(1,1,0)⋯(N,N,0)` and its lift is `(bgen3 1)[N + 1]`,
of strictly larger rank.  (This rules out the lift as a rank-preserving map;
it does not rule out every map that commutes with expansion.)
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

/-! ### The shape -/

/-- A column whose row-`1` entry is `0` has row-`2` entry `0`. -/
def Nice (X : List (List Nat)) : Prop := ∀ i : Nat, (X[i]!)[1]! = 0 → (X[i]!)[2]! = 0

/-- A parent in row `k + 1` exists as soon as some row-`k` ancestor is smaller in
row `k + 1`. -/
theorem exists_ParR_succ (l : List (List Nat)) (k : Nat) :
    ∀ d j i, i - j = d → AncR l k j i → (l[j]!)[k + 1]! < (l[i]!)[k + 1]! →
      ∃ p, ParR l (k + 1) p i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j i hd hji hv
    have hlt : j < i := transGen_lt (fun _ _ h => ParR_lt h) hji
    by_cases hall : ∀ j', j < j' → j' < i → Relation.TransGen (ParR l k) j' i →
        (l[i]!)[k + 1]! ≤ (l[j']!)[k + 1]!
    · exact ⟨j, hlt, hji, hv, hall⟩
    · push Not at hall
      obtain ⟨j', h1, h2, h3, h4⟩ := hall
      exact ih (i - j') (by omega) j' i rfl h3 h4

/-- A column whose row-`1` entry is `0` has no parent in rows `1, 2, …`. -/
theorem not_ParR_succ_of_row1_zero {l : List (List Nat)} {i : Nat} (h0 : (l[i]!)[1]! = 0) :
    ∀ k j, ¬ ParR l (k + 1) j i := by
  intro k
  induction k with
  | zero =>
    intro j h
    have := h.2.2.1
    simp only [Nat.zero_add] at this
    omega
  | succ m ih =>
    intro j h
    obtain ⟨b, hb⟩ := exists_ParR_of_succ h
    exact ih b hb

theorem parAtR_succ_none_of_row1_zero {l : List (List Nat)} {i : Nat} (h0 : (l[i]!)[1]! = 0)
    (k : Nat) : parAtR l (k + 1) i = none := by
  cases h : parAtR l (k + 1) i with
  | none => rfl
  | some j => exact absurd ((parAtR_eq_some _ _ _ _).mp h) (not_ParR_succ_of_row1_zero h0 k j)

theorem m0L_eq_zero_of_row1_zero (r : Nat) {l : List (List Nat)}
    (h0 : (l[l.length - 1]!)[1]! = 0) : m0L r l = 0 := by
  rw [m0L, Nat.findGreatest_eq_zero_iff]
  intro k hk _ hsome
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [parAtR_succ_none_of_row1_zero h0 k'] at hsome
  exact absurd hsome (by simp)

/-- A column with a positive row-`1` entry has a row-`1` ancestor with row-`2`
entry `0`. -/
theorem exists_anc1_row2_zero {X : List (List Nat)} (hR : Rooted X) (hN : Nice X) :
    ∀ i, i < X.length → 0 < (X[i]!)[1]! → ∃ j, AncR X 1 j i ∧ (X[j]!)[2]! = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi h1
    have hne : (X[i]!)[0]! ≠ 0 := fun h0 => by
      have := hR.2 i h0 1
      omega
    obtain ⟨z, hz, hZ⟩ := exists_zero_anc hR i hi hne
    obtain ⟨q, hq⟩ := exists_ParR_succ X 0 _ z i rfl hz (by rw [hZ 1]; exact h1)
    have hqi : q < i := ParR_lt hq
    by_cases hq1 : (X[q]!)[1]! = 0
    · exact ⟨q, Relation.TransGen.single hq, hN q hq1⟩
    · obtain ⟨j, hj, h2⟩ := ih q hqi (by omega) (by omega)
      exact ⟨j, Relation.TransGen.tail hj hq, h2⟩

/-- **The last column keeps its parents under the lift** when its row-`1`
entry is positive. -/
theorem liftGood_of_nice {X : List (List Nat)} (hv : Valid 2 X) (hR : Rooted X) (hN : Nice X)
    (hne : X ≠ []) (h1 : 0 < (X[X.length - 1]!)[1]!) : LiftGood X := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  have hne0 : (X[X.length - 1]!)[0]! ≠ 0 := fun h0 => by
    have := hR.2 _ h0 1
    omega
  obtain ⟨z, hz, hZ⟩ := exists_zero_anc hR _ (by omega) hne0
  obtain ⟨q, hq⟩ := exists_ParR_succ X 0 _ z _ rfl hz (by rw [hZ 1]; exact h1)
  refine ⟨hne, Option.isSome_iff_exists.mpr ⟨q, (parAtR_eq_some _ _ _ _).mpr hq⟩, ?_⟩
  intro k hk
  by_cases hk2 : k = 2
  · subst hk2
    by_cases h2 : (X[X.length - 1]!)[2]! = 0
    · exact Or.inr h2
    · left
      obtain ⟨j, hj, hj2⟩ := exists_anc1_row2_zero hR hN _ (by omega) h1
      obtain ⟨p, hp⟩ := exists_ParR_succ X 1 _ j _ rfl hj
        (by show (X[j]!)[2]! < (X[X.length - 1]!)[2]!; omega)
      exact Option.isSome_iff_exists.mpr ⟨p, (parAtR_eq_some _ _ _ _).mpr hp⟩
  · right
    have hmem := getElem!_mem X (X.length - 1) (by omega)
    exact getElem!_neg _ k (by rw [hv _ hmem]; omega)

/-! ### What expansion does to a column -/

/-- Every column of an expansion is empty or comes from a column of the
matrix, with entries no smaller, and unchanged from row `m₀` on. -/
theorem expandRL_col_from (r N : Nat) (l : List (List Nat)) (hlen : ∀ v ∈ l, v.length = r)
    (i : Nat) :
    (expandRL r N l)[i]! = [] ∨ ∃ j : Nat, (∀ k : Nat, (l[j]!)[k]! ≤ ((expandRL r N l)[i]!)[k]!) ∧
      (∀ k : Nat, m0L r l ≤ k → ((expandRL r N l)[i]!)[k]! = (l[j]!)[k]!) := by
  cases hb : badRootR r l with
  | none =>
    rw [expandRL, hb]
    dsimp only
    rw [getElem!_dropLast']
    split
    · exact Or.inr ⟨i, fun k => le_refl _, fun k _ => rfl⟩
    · exact Or.inl rfl
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    have hs : 0 < l.length - 1 - p := by omega
    rw [expandRL, hb]
    dsimp only
    by_cases hip : i < p
    · rw [getElem!_append_left _ _ (by simpa using hip), getElem!_map_range _ _ hip]
      exact Or.inr ⟨i, fun k => le_refl _, fun k _ => rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, i = p + t := ⟨i - p, by omega⟩
      have hlenG : ((List.range p).map (fun i => l[i]!)).length = p := by simp
      have key : ∀ (G C : List (List Nat)), G.length = p → (G ++ C)[p + t]! = C[t]! := by
        intro G C h; rw [← h]; exact getElem!_append_right G C t
      rw [key _ _ hlenG]
      by_cases ht : t < (N + 1) * (l.length - 1 - p)
      · rw [getElem!_map_range _ _ ht]
        have hj : p + t % (l.length - 1 - p) < l.length := by
          have := Nat.mod_lt t hs; omega
        have hjl : (l[p + t % (l.length - 1 - p)]!).length = r :=
          hlen _ (getElem!_mem l _ hj)
        refine Or.inr ⟨p + t % (l.length - 1 - p), fun k => ?_, fun k hk => ?_⟩
        · rw [getElem!_map_range_nat]
          split
          · split
            · exact Nat.le_add_right _ _
            · exact le_refl _
          · rename_i hk
            exact le_of_eq (getElem!_neg _ k (by omega))
        · rw [getElem!_map_range_nat]
          split
          · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro h; omega)]
          · rename_i hk'
            exact (getElem!_neg _ k (by omega)).symm
      · exact Or.inl (getElem!_neg _ t (by simpa using ht))

/-- **The shape survives expansion.** -/
theorem nice_expandRL (N : Nat) {X : List (List Nat)} (hv : Valid 2 X) (hN : Nice X) :
    Nice (expandRL 3 N X) := by
  intro i h1
  rcases expandRL_col_from 3 N X hv i with he | ⟨j, hle, heq⟩
  · rw [he]; rfl
  · have hj1 : (X[j]!)[1]! = 0 := by have := hle 1; omega
    rw [heq 2 (by have := m0L_lt (show 0 < 3 by norm_num) X; omega)]
    exact hN j hj1

/-! ### Small facts -/

theorem valid_lift {X : List (List Nat)} (hv : Valid 2 X) : Valid 2 (lift 3 X) := by
  intro v hv'
  rcases List.mem_cons.mp hv' with h | h
  · rw [h, zcol, List.length_replicate]
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    rw [up01_length (by rw [hv w hw]; omega)]
    exact hv w hw

theorem repN_map {α β : Type} (f : α → β) (l : List α) :
    ∀ n, (repN n l).map f = repN n (l.map f) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [repN, repN, List.map_append, ih]

theorem rkL_le_append {r : Nat} (P X : List (List Nat)) (hv : Valid r (P ++ X)) :
    rkL r P ≤ rkL r (P ++ X) := by
  by_cases hX : X = []
  · rw [hX, List.append_nil]
  · exact le_of_lt (rkL_lt_append P X.length X rfl hX hv)

/-- Being a row-`0` parent reads only row `0`. -/
theorem ParR_zero_congr {l l' : List (List Nat)} {i : Nat}
    (h : ∀ m, m ≤ i → (l[m]!)[0]! = (l'[m]!)[0]!) (j : Nat) :
    ParR l 0 j i ↔ ParR l' 0 j i := by
  rw [ParR, ParR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by rw [← h j (by omega), ← h i le_rfl]; exact h2, fun j' a b => ?_⟩
    rw [← h j' (by omega), ← h i le_rfl]; exact h3 j' a b
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by rw [h j (by omega), h i le_rfl]; exact h2, fun j' a b => ?_⟩
    rw [h j' (by omega), h i le_rfl]; exact h3 j' a b

theorem not_ParR_succ_of_zero {l : List (List Nat)} {k i : Nat} (h0 : (l[i]!)[k + 1]! = 0)
    (j : Nat) : ¬ ParR l (k + 1) j i := by
  intro h
  have := h.2.2.1
  omega

/-! ### A last column `(x,0,0)` -/

section LastRowOneZero

variable {X : List (List Nat)}

/-- The tail that the lift's first copy starts with: the lift without its last
column, then `(x+1,0,0)`. -/
def liftTail (X : List (List Nat)) : List (List Nat) :=
  (lift 3 X).dropLast ++ [[(X[X.length - 1]!)[0]! + 1, 0, 0]]

theorem liftTail_length (hne : X ≠ []) : (liftTail X).length = X.length + 1 := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  simp [liftTail]

theorem liftTail_get_lt {i : Nat} (hi : i < X.length) : (liftTail X)[i]! = (lift 3 X)[i]! := by
  rw [liftTail, getElem!_append_left _ _ (by simp; omega), getElem!_dropLast', if_pos (by simp; omega)]

theorem liftTail_get_last (hne : X ≠ []) :
    (liftTail X)[X.length]! = [(X[X.length - 1]!)[0]! + 1, 0, 0] := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  have h := getElem!_append_right (lift 3 X).dropLast [[(X[X.length - 1]!)[0]! + 1, 0, 0]] 0
  rw [List.length_dropLast, lift_length, Nat.add_sub_cancel] at h
  simp only [Nat.add_zero] at h
  rw [liftTail, h]
  rfl

theorem lift_get_last (hne : X ≠ []) : (lift 3 X)[X.length]! = up01 (X[X.length - 1]!) := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  conv_lhs => rw [show X.length = (X.length - 1) + 1 from by omega]
  exact lift_get_succ 3 X (by omega)

theorem valid_liftTail (hv : Valid 2 X) : Valid 2 (liftTail X) := by
  intro v hv'
  rcases List.mem_append.mp hv' with h | h
  · exact valid_lift hv v (List.mem_of_mem_dropLast h)
  · rw [List.mem_singleton.mp h]; rfl

/-- **The tail expands as `X` does**, lifted. -/
theorem expandRL_liftTail (hv : Valid 2 X) (hR : Rooted X) (hne : X ≠ [])
    (h1 : (X[X.length - 1]!)[1]! = 0) (h0 : (X[X.length - 1]!)[0]! ≠ 0) (N : Nat) :
    expandRL 3 N (liftTail X) = lift 3 (expandRL 3 N X) := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  have hL1 : 0 < X.length - 1 := by
    by_contra hc
    exact h0 (by rw [show X.length - 1 = 0 from by omega]; exact hR.1 0)
  obtain ⟨p0, hp0⟩ := exists_ParR0 X _ 0 (X.length - 1) rfl hL1 (by rw [hR.1 0]; omega)
  have hp0L : p0 < X.length - 1 := ParR_lt hp0
  -- the bad root and `m₀` of `X`
  have hmX : m0L 3 X = 0 := m0L_eq_zero_of_row1_zero 3 h1
  have hbX : badRootR 3 X = some p0 := by
    rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hmX, parAtR_eq_some]
    exact hp0
  -- the bad root and `m₀` of the tail
  have hlenT := liftTail_length hne
  have hTL : (liftTail X)[(liftTail X).length - 1]! = [(X[X.length - 1]!)[0]! + 1, 0, 0] := by
    rw [hlenT, Nat.add_sub_cancel]; exact liftTail_get_last hne
  have hmT : m0L 3 (liftTail X) = 0 := m0L_eq_zero_of_row1_zero 3 (by rw [hTL]; rfl)
  have hparT : ParR (liftTail X) 0 (p0 + 1) X.length := by
    have hl : ParR (lift 3 X) 0 (p0 + 1) X.length := by
      rw [show X.length = (X.length - 1) + 1 from by omega, ParR_lift_succ]
      exact hp0
    refine (ParR_zero_congr (fun m hm => ?_) _).mpr hl
    by_cases hmL : m < X.length
    · rw [liftTail_get_lt hmL]
    · rw [show m = X.length from by omega, liftTail_get_last hne, lift_get_last hne, up01_get0]
      rfl
  have hbT : badRootR 3 (liftTail X) = some (p0 + 1) := by
    rw [badRootR, if_neg (by simp [liftTail]), hmT, parAtR_eq_some, hlenT, Nat.add_sub_cancel]
    exact hparT
  rw [expandRL_of_m0_zero 3 N _ _ hbT hmT (valid_liftTail hv),
    expandRL_of_m0_zero 3 N _ _ hbX hmX hv, lift_append, repN_map,
    lift_map_range 3 X (by omega), List.map_map, hlenT]
  congr 1
  · refine List.map_congr_left (fun i hi => ?_)
    have := List.mem_range.mp hi
    exact liftTail_get_lt (by omega)
  · congr 1
    rw [show X.length + 1 - 1 - (p0 + 1) = X.length - 1 - p0 from by omega]
    refine List.map_congr_left (fun i hi => ?_)
    have := List.mem_range.mp hi
    show (liftTail X)[p0 + 1 + i]! = up01 (X[p0 + i]!)
    rw [liftTail_get_lt (by omega), show p0 + 1 + i = (p0 + i) + 1 from by omega,
      lift_get_succ 3 X (by omega)]

/-- In the lift, the new zero column is the row-`1` parent of a last column
`(x+1,1,0)`, and there is no row-`2` parent: the bad root is column `0` and
`m₀ = 1`. -/
theorem badRootR_lift_of_row1_zero (hR : Rooted X) (hN : Nice X) (hne : X ≠ [])
    (h1 : (X[X.length - 1]!)[1]! = 0) (h0 : (X[X.length - 1]!)[0]! ≠ 0) :
    m0L 3 (lift 3 X) = 1 ∧ badRootR 3 (lift 3 X) = some 0 := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  have hlast := lift_get_last hne (X := X)
  have e1 : ((lift 3 X)[X.length]!)[1]! = 1 := by rw [hlast, up01_get1, h1]
  have e2 : ((lift 3 X)[X.length]!)[2]! = 0 := by
    rw [hlast, show (2 : Nat) = 0 + 2 from rfl, up01_get_add2]; exact hN _ h1
  have e0 : ((lift 3 X)[X.length]!)[0]! = (X[X.length - 1]!)[0]! + 1 := by rw [hlast, up01_get0]
  -- column `0` is a row-`0` ancestor of the last column
  obtain ⟨z, hz, hZ⟩ := exists_zero_anc hR _ (by omega) h0
  have hzL : z < X.length - 1 := transGen_lt (fun _ _ h => ParR_lt h) hz
  have hz' : AncR (lift 3 X) 0 (z + 1) X.length := by
    rw [show X.length = (X.length - 1) + 1 from by omega, AncR_lift_succ]; exact hz
  have hpz : ParR (lift 3 X) 0 0 (z + 1) := by
    refine ⟨by omega, ?_, fun j' a b => ?_⟩
    · rw [lift_get0, zcol_get, lift_get_succ 3 X (by omega), up01_get0, hZ 0]; omega
    · rw [lift_get_succ 3 X (by omega), up01_get0, hZ 0,
        show j' = (j' - 1) + 1 from by omega, lift_get_succ 3 X (by omega), up01_get0]
      omega
  have hanc : Relation.TransGen (ParR (lift 3 X) 0) 0 X.length :=
    Relation.TransGen.head hpz hz'
  have hp1 : ParR (lift 3 X) 1 0 X.length := by
    refine ⟨by omega, hanc, ?_, fun j' a b _ => ?_⟩
    · rw [lift_get0, zcol_get, e1]; omega
    · rw [e1, show j' = (j' - 1) + 1 from by omega, lift_get_succ 3 X (by omega), up01_get1]
      omega
  have hs1 : (parAtR (lift 3 X) 1 X.length).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨0, (parAtR_eq_some _ _ _ _).mpr hp1⟩
  have hs2 : ¬ (parAtR (lift 3 X) 2 X.length).isSome = true := by
    intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact not_ParR_succ_of_zero (k := 1) e2 j ((parAtR_eq_some _ _ _ _).mp hj)
  have hm : m0L 3 (lift 3 X) = 1 := by
    rw [m0L, lift_length, Nat.add_sub_cancel, show (3 - 1 : Nat) = 1 + 1 from rfl,
      Nat.findGreatest_succ, if_neg hs2, show (1 : Nat) = 0 + 1 from rfl,
      Nat.findGreatest_succ, if_pos hs1]
  refine ⟨hm, ?_⟩
  rw [badRootR, if_neg (by simp [lift]), hm, lift_length, Nat.add_sub_cancel, parAtR_eq_some]
  exact hp1

/-- **`(lift 3 X)[1]` starts with the tail.** -/
theorem expandRL_one_lift_eq (hv : Valid 2 X) (hR : Rooted X) (hN : Nice X) (hne : X ≠ [])
    (h1 : (X[X.length - 1]!)[1]! = 0) (h0 : (X[X.length - 1]!)[0]! ≠ 0) :
    ∃ E, expandRL 3 1 (lift 3 X) = liftTail X ++ E := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  obtain ⟨hm, hb⟩ := badRootR_lift_of_row1_zero hR hN hne h1 h0
  have hvl := valid_lift hv
  rw [expandRL, hb]
  dsimp only
  rw [hm, lift_length, Nat.add_sub_cancel, Nat.sub_zero, List.range_zero, List.map_nil,
    List.nil_append, show (1 + 1) * X.length = X.length + (0 + 1 + (X.length - 1)) from by omega,
    List.range_add, List.range_add, List.range_one]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [← List.singleton_append, ← List.append_assoc]
  refine ⟨_, congrArg (fun a => a ++ _) ?_⟩
  rw [liftTail]
  congr 1
  · rw [dropLast_eq_map_range, lift_length, Nat.add_sub_cancel]
    refine List.map_congr_left (fun t ht => ?_)
    have ht' : t < X.length := List.mem_range.mp ht
    rw [Nat.mod_eq_of_lt ht', Nat.div_eq_of_lt ht']
    simp only [Nat.zero_mul, Nat.add_zero, ite_self, Nat.zero_add]
    have hmem : ((lift 3 X)[t]!).length = 3 :=
      hvl _ (getElem!_mem _ t (by rw [lift_length]; omega))
    have he := listEta ((lift 3 X)[t]!)
    rw [hmem] at he
    exact he
  · simp only [Nat.add_zero, Nat.mod_self]
    rw [Nat.div_self hpos, lift_get0, lift_get_last hne,
      show (List.range 3 : List Nat) = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, zcol_get, up01_get0, Nat.one_mul, Nat.sub_zero,
      Nat.zero_add]
    rfl

end LastRowOneZero

/-! ### The lift never lowers the rank -/

/-- **One step of `X` stays below the lift.** -/
theorem rkL_lift_expandRL_lt {X : List (List Nat)} (hv : Valid 2 X) (hR : Rooted X) (hN : Nice X)
    (hne : X ≠ []) (N : Nat) : rkL 2 (lift 3 (expandRL 3 N X)) < rkL 2 (lift 3 X) := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr hne
  have hvl := valid_lift hv
  have hnel : lift 3 X ≠ [] := by simp [lift]
  by_cases h1 : (X[X.length - 1]!)[1]! = 0
  · by_cases h0 : (X[X.length - 1]!)[0]! = 0
    · -- a zero column last: both sides drop it
      have hZ := hR.2 _ h0
      have hX : expandRL 3 N X = X.dropLast := by
        rw [expandRL, badRootR_none_of_isZ 3 hZ]
      rw [hX, lift_dropLast 3 hne, ← expandRL_zero 3 _ hvl]
      exact rkL_lt hvl hnel 0
    · -- a last column `(x,0,0)`: through the tail
      obtain ⟨E, hE⟩ := expandRL_one_lift_eq hv hR hN hne h1 h0
      have hvT := valid_liftTail hv (X := X)
      have hneT : liftTail X ≠ [] := by simp [liftTail]
      rw [← expandRL_liftTail hv hR hne h1 h0 N]
      calc rkL 2 (expandRL 3 N (liftTail X)) < rkL 2 (liftTail X) := rkL_lt hvT hneT N
        _ ≤ rkL 2 (liftTail X ++ E) := rkL_le_append _ _ (by rw [← hE]; exact valid_expandRL hvl 1)
        _ = rkL 2 (expandRL 3 1 (lift 3 X)) := by rw [hE]
        _ < rkL 2 (lift 3 X) := rkL_lt hvl hnel 1
  · -- a positive row-`1` entry: the lift commutes
    rw [← expandRL_lift 3 N (by norm_num) (liftGood_of_nice hv hR hN hne (by omega))]
    exact rkL_lt hvl hnel N

theorem rkL_le_rkL_lift_aux : ∀ M : AllLState 2, Rooted M.1 → Nice M.1 →
    rkL 2 M.1 ≤ rkL 2 (lift 3 M.1) := by
  intro M
  induction M using WellFounded.induction (bmsAllL_wf 2) with
  | _ M ih =>
    intro hR hN
    by_cases hne : M.1 = []
    · rw [hne, rkL_nil]; exact zero_le
    · rw [rkL_step M.2 hne]
      refine Ordinal.iSup_le (fun N => succ_le_of_lt ?_)
      have ihN : rkL 2 (expandRL 3 N M.1) ≤ rkL 2 (lift 3 (expandRL 3 N M.1)) :=
        ih ((bmsAllL 2).step M N) (rel_of_ne M hne N) (rooted_expandRL 3 N hR)
          (nice_expandRL N M.2 hN)
      exact lt_of_le_of_lt ihN (rkL_lift_expandRL_lt M.2 hR hN hne N)

/-- **The lift never lowers the rank**, on rooted three-row matrices whose
columns with a `0` in row `1` have a `0` in row `2`. -/
theorem rkL_le_rkL_lift {X : List (List Nat)} (hv : Valid 2 X) (hR : Rooted X) (hN : Nice X) :
    rkL 2 X ≤ rkL 2 (lift 3 X) :=
  rkL_le_rkL_lift_aux ⟨X, hv⟩ hR hN

/-! ### The generators -/

theorem valid_bgen3 (n : Nat) : Valid 2 (bgen3 n) := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  simp

theorem bgen3_entry {n i k : Nat} (hi : i < n + 1) (hk : k < 3) : ((bgen3 n)[i]!)[k]! = i := by
  rw [bgen3_get hi, getElem!_replicate hk]

theorem rooted_bgen3 (n : Nat) : Rooted (bgen3 n) := by
  refine ⟨fun k => ?_, fun i hi k => ?_⟩
  · rw [bgen3_get (by omega)]; exact zcol_get 3 k
  · by_cases h : i < n + 1
    · rw [bgen3_entry h (by norm_num)] at hi
      subst hi
      rw [bgen3_get h]; exact zcol_get 3 k
    · rw [getElem!_neg _ i (by simpa [bgen3] using h)]; rfl

theorem nice_bgen3 (n : Nat) : Nice (bgen3 n) := by
  intro i h1
  by_cases h : i < n + 1
  · rw [bgen3_entry h (by norm_num)] at h1 ⊢
    exact h1
  · rw [getElem!_neg _ i (by simpa [bgen3] using h)]; rfl

/-- **The content generator of three-row DBMS has at least the rank of the
BMS generator `(0,0,0)(1,1,1)⋯(n,n,n)`.** -/
theorem rkL_bgen3_le_cgen (n : Nat) : rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n + 2)) := by
  rw [cgen_two_eq_lift]
  exact rkL_le_rkL_lift (valid_bgen3 n) (rooted_bgen3 n) (nice_bgen3 n)

/-- The rank of the three-row BMS generator, under the rule on all matrices. -/
theorem rank_bmsL_gen_eq_rkL (n : Nat) :
    @IsWellFounded.rank _ (bmsL 2).Rel ⟨bmsL_wf 2⟩ ((bmsLStd 2).gen n) = rkL 2 (bgen3 n) := by
  rw [show bgen3 n = ((bmsLHomAll 2).map ((bmsLStd 2).gen n)).1 from rfl,
    rkL_eq ((bmsLHomAll 2).map ((bmsLStd 2).gen n))]
  exact (rank_bmsAllL_of_bmsL 2 _).symm

/-- **The ordinal of three-row BMS is at most the ordinal of three-row DBMS**:
the suprema of `rank + 1` over the standard forms. -/
theorem iSup_rank_bmsL_two_le_dbmsL :
    ⨆ l : (bmsL 2).State, succ (@IsWellFounded.rank _ (bmsL 2).Rel ⟨bmsL_wf 2⟩ l)
      ≤ ⨆ l : (dbmsL 2).State, succ (Rewrite.rank (dbmsL_wf 2) l) := by
  haveI : IsWellFounded (bmsL 2).State (bmsL 2).Rel := ⟨bmsL_wf 2⟩
  refine Ordinal.iSup_le (fun l => ?_)
  obtain ⟨n, hn⟩ := rank_le_genB 2 l
  have h : IsWellFounded.rank (bmsL 2).Rel l ≤ Rewrite.rank (dbmsL_wf 2) (genL 2 (n + 2)) := by
    refine le_trans hn ?_
    rw [rank_bmsL_gen_eq_rkL, rank_genL_eq]
    exact le_trans (rkL_bgen3_le_cgen n) (Ordinal.right_le_opow _ one_lt_omega0)
  exact le_trans (succ_le_succ h)
    (Ordinal.le_iSup (fun l : (dbmsL 2).State => succ (Rewrite.rank (dbmsL_wf 2) l)) _)

end Googology.Trans.DBMS
