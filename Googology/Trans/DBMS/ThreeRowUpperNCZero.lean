import Googology.Trans.DBMS.ThreeRowUpperNCMain

/-!
# The shape `RaisedPar` at `N = 0`

`ThreeRowUpperNCMain.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `T3nRankDescRP`: the nested raise `t3n`
lowers the rank with every expansion `C[N]` of a reached matrix `C` in the
shape `RaisedPar`.  This file proves it at `N = 0`, for every reached `C`
(`rkL_t3n_expand_zero_lt`), and so reduces the open statement to `N ≥ 1`
(`T3nRankDescRP1`, `rkL_cgen_two_four_eq_of_RP1`).

At `N = 0` the expansion drops the last column, `C[0] = C.dropLast`.

* If column `n - 2` of `C` (`n` columns) is not raisable, then
  `t3n (C.dropLast) = (t3n C).dropLast = (t3n C)[0]` (`t3n_dropLast`).
* If column `y = n - 2` is raisable, `C = ⋯(a,1,0)(a+1,2,1)`, then
  `t3n (C.dropLast)` is `S₀ = (t3n C).dropLast` with its last column `(a,1,1)`
  lowered to `(a,1,0)`.  In `S₀` the row-`2` parent of `(a,1,1)` is the row-`1`
  parent `x = (b,0,0)` of `y`, so `x` is the bad root with `m₀ = 2`, and the
  first column of the second copy in `S₀[1]` is `x + (a - b, 1 - 0) = (a,1,0)`.
  So `t3n (C.dropLast)` is a prefix of `S₀[1]` (`t3n_dropLast_prefix`), and
  `rkL (t3n (C[0])) ≤ rkL (S₀[1]) < rkL S₀ < rkL (t3n C)`.

**Open.**  `T3nRankDescRP1`: `rkL 2 (t3n (C[N + 1])) < rkL 2 (t3n C)` for
`C ∈ SReach` with `RaisedPar C`.  Numerically (scripts outside the library):

* breadth-first from `lift 3 (trioGen v)`, `v ≤ 3`, depth `≤ 10`, at most `14`
  columns (`6639` matrices): `452` pairs `(C, N)` with `RaisedPar C` and
  `N ∈ {1, 2}`;
* depth `≤ 12`, at most `16` columns (`28741` matrices): `2448` pairs with
  `N ∈ {1, 2, 3}`.

On every one of them `t3n C` and `t3n (C[N])` are reached from a trio generator
by an explicit path of expansions (so both are in `TrioStdL`), and
`t3n (C[N]) < t3n C` in the dictionary order, which with `rkL_lt_of_trio`
gives the inequality at that pair.  Two observations that are not proved here:
when the raisable parent `y` is column `n - 2`, `t3n (C[N]) = W[N]` for
`W = t3n C` with `y` lowered back to `(a,1,0)`; when `y < n - 2`,
`t3n (C[N]) = E[N - 1]` for `E = t3n (C[1] ++ [z + Δ])` (`z` the last column,
`Δ` the increment of the expansion), and `E` is a trio standard form below
`t3n C`.  The paths from `t3n C` down to `E` found by greedy descent have up to
eleven steps and no common pattern.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

/-! ### Parents read only the columns up to their own -/

theorem ParR_congr_upto (l l' : List (List Nat)) : ∀ k i : Nat,
    (∀ m k', m ≤ i → k' ≤ k → (l[m]!)[k']! = (l'[m]!)[k']!) →
      ∀ j, ParR l k j i ↔ ParR l' k j i := by
  intro k
  induction k with
  | zero =>
    intro i h j
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, fun j' a b => ?_⟩
      · rw [← h j 0 (by omega) le_rfl, ← h i 0 le_rfl le_rfl]; exact h2
      · rw [← h j' 0 (by omega) le_rfl, ← h i 0 le_rfl le_rfl]; exact h3 j' a b
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, fun j' a b => ?_⟩
      · rw [h j 0 (by omega) le_rfl, h i 0 le_rfl le_rfl]; exact h2
      · rw [h j' 0 (by omega) le_rfl, h i 0 le_rfl le_rfl]; exact h3 j' a b
  | succ m ih =>
    intro i h j
    have step : ∀ b c, c ≤ i → (ParR l m b c ↔ ParR l' m b c) := fun b c hc =>
      ih c (fun m' k' hm hk => h m' k' (by omega) (by omega)) b
    have tg1 : ∀ a c, Relation.TransGen (ParR l m) a c → c ≤ i →
        Relation.TransGen (ParR l' m) a c := by
      intro a c hac
      induction hac with
      | single hs => intro hc; exact Relation.TransGen.single ((step _ _ hc).mp hs)
      | tail _ hs ih2 =>
        intro hc
        exact Relation.TransGen.tail (ih2 (by have := ParR_lt hs; omega)) ((step _ _ hc).mp hs)
    have tg2 : ∀ a c, Relation.TransGen (ParR l' m) a c → c ≤ i →
        Relation.TransGen (ParR l m) a c := by
      intro a c hac
      induction hac with
      | single hs => intro hc; exact Relation.TransGen.single ((step _ _ hc).mpr hs)
      | tail _ hs ih2 =>
        intro hc
        exact Relation.TransGen.tail (ih2 (by have := ParR_lt hs; omega)) ((step _ _ hc).mpr hs)
    rw [TrioCofinal.ParR_succ_iff, TrioCofinal.ParR_succ_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, tg1 _ _ h2 le_rfl, ?_, fun j' a b c => ?_⟩
      · rw [← h j (m + 1) (by omega) le_rfl, ← h i (m + 1) le_rfl le_rfl]; exact h3
      · have := h4 j' a b (tg2 _ _ c le_rfl)
        rwa [h j' (m + 1) (by omega) le_rfl, h i (m + 1) le_rfl le_rfl] at this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, tg2 _ _ h2 le_rfl, ?_, fun j' a b c => ?_⟩
      · rw [h j (m + 1) (by omega) le_rfl, h i (m + 1) le_rfl le_rfl]; exact h3
      · have := h4 j' a b (tg1 _ _ c le_rfl)
        rwa [← h j' (m + 1) (by omega) le_rfl, ← h i (m + 1) le_rfl le_rfl] at this

/-! ### Row-`1` parents on `SReach` -/

/-- **On `SReach` a column with a positive row-`1` entry has a row-`1` parent**
(trio's `parent1_exists`). -/
theorem exists_ParR1_of_sReach {C : List (List Nat)} (hC : SReach C) {j : Nat}
    (hj : j < C.length) (h1 : 0 < (C[j]!)[1]!) : ∃ x, ParR C 1 x j := by
  obtain ⟨M, rfl, hM⟩ := sReach_tInv hC
  rw [TrioCofinal.toL_e1] at h1
  rw [TrioCofinal.toL_length] at hj
  obtain ⟨k, hk⟩ := TrioCof.parent1_exists hM.1 hM.2.1 hj h1
  exact ⟨k, by rw [TrioCofinal.ParR1_eq]; exact hk⟩

/-! ### `t3n` and dropping the last column -/

theorem Rz_dropLast_iff {C : List (List Nat)} {i : Nat} (hi : i + 2 < C.length) :
    Rz C.dropLast i ↔ Rz C i := by
  have h1 : i < C.length - 1 := by omega
  have h2 : i + 1 < C.length - 1 := by omega
  have e0 : C.dropLast[i]! = C[i]! := by rw [getElem!_dropLast', if_pos h1]
  have e1 : C.dropLast[i + 1]! = C[i + 1]! := by rw [getElem!_dropLast', if_pos h2]
  unfold Rz
  rw [e0, e1, List.length_dropLast]
  constructor
  · rintro ⟨_, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨_, h⟩; exact ⟨by omega, h⟩

theorem not_Rz_dropLast_ge {C : List (List Nat)} {i : Nat} (hi : C.length ≤ i + 2) :
    ¬ Rz C.dropLast i := fun h => by
  have := h.1
  rw [List.length_dropLast] at this
  omega

/-- **Without a raisable column `n - 2`, `t3n` commutes with dropping the last
column.** -/
theorem t3n_dropLast {C : List (List Nat)} (hn : ¬ Rz C (C.length - 2)) :
    t3n C.dropLast = (t3n C).dropLast := by
  apply ext_getElem!' (by simp)
  intro i hi
  have hi' : i < C.length - 1 := by simpa using hi
  have eL : (t3n C).dropLast[i]! = (t3n C)[i]! := by
    rw [getElem!_dropLast', if_pos (by rw [t3n_length]; omega)]
  have eC : C.dropLast[i]! = C[i]! := by rw [getElem!_dropLast', if_pos hi']
  rw [eL, t3n_get (C := C.dropLast) (by rw [List.length_dropLast]; omega), t3n_get (by omega), eC]
  by_cases hi2 : i + 2 < C.length
  · by_cases hR : Rz C i
    · rw [if_pos hR, if_pos ((Rz_dropLast_iff hi2).mpr hR)]
    · rw [if_neg hR, if_neg (fun h => hR ((Rz_dropLast_iff hi2).mp h))]
  · have hR : ¬ Rz C i := by rw [show i = C.length - 2 from by omega]; exact hn
    rw [if_neg hR, if_neg (not_Rz_dropLast_ge (by omega))]

theorem getElem!_take_of_lt (l : List (List Nat)) {n i : Nat} (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  by_cases hi : i < l.length
  · rw [getElem!_pos _ i (by simp; omega), getElem!_pos l i hi, List.getElem_take]
  · rw [getElem!_neg _ i (by simp; omega), getElem!_neg l i hi]

/-! ### The raisable column `n - 2` -/

/-- **`t3n (C.dropLast)` is a prefix of `((t3n C).dropLast)[1]`** when column
`n - 2` is raisable. -/
theorem t3n_dropLast_prefix {C : List (List Nat)} (hC : SReach C)
    (hy : Rz C (C.length - 2)) :
    t3n C.dropLast = (expandRL 3 1 (t3n C).dropLast).take (C.length - 1) := by
  have hv := hC.valid
  have hyl := hy.1
  have hy1 := hy.2.1
  have hy2 := hy.2.2.1
  obtain ⟨x, hx⟩ := exists_ParR1_of_sReach hC (j := C.length - 2) (by omega)
    (by rw [hy1]; omega)
  have hxy : x < C.length - 2 := ParR_lt hx
  have hx1 : (C[x]!)[1]! = 0 := by
    have := ((ParR_one_iff C x _).mp hx).2.2.1
    omega
  have hx2 : (C[x]!)[2]! = 0 := low2_of_sReach hC x (by omega)
  have hxR : ¬ Rz C x := fun h => by have := h.2.1; omega
  have hx0 : (C[x]!)[0]! < (C[C.length - 2]!)[0]! :=
    AncR_entry_lt (AncR_zero_of (k := 1) (Relation.TransGen.single hx))
  -- the list `S₀`
  set S0 := (t3n C).dropLast with hS0
  have hS0len : S0.length = C.length - 1 := by simp [hS0]
  have hS0get : ∀ m, m < C.length - 1 → S0[m]! = (t3n C)[m]! := by
    intro m hm
    rw [hS0, getElem!_dropLast', if_pos (by rw [t3n_length]; omega)]
  have hlow : ∀ m k, m < C.length - 1 → k ≤ 1 → (S0[m]!)[k]! = (C[m]!)[k]! := by
    intro m k hm hk
    rw [hS0get m hm, t3n_entry_low C m k hk]
  have hS0x2 : (S0[x]!)[2]! = 0 := by
    rw [hS0get x (by omega), t3n_entry_two, if_neg hxR, hx2]
  have hS0y2 : (S0[C.length - 2]!)[2]! = 1 := by
    rw [hS0get _ (by omega), t3n_entry_two, if_pos hy]
  -- `x` is the row-`2` parent of the last column of `S₀`
  have hP1 : ParR S0 1 x (C.length - 2) :=
    (ParR_congr_upto S0 C 1 _ (fun m k' hm hk => hlow m k' (by omega) hk) x).mpr hx
  have hP2 : ParR S0 2 x (C.length - 2) := by
    refine (ParR_two_iff' S0 x _).mpr ⟨hxy, Relation.TransGen.single hP1, ?_, fun j' a b c => ?_⟩
    · rw [hS0x2, hS0y2]; omega
    · exfalso
      rcases (AncR_of_ParR_iff hP1 j').mp c with h | h
      · omega
      · have := transGen_lt (fun _ _ h => ParR_lt h) h
        omega
  have hlast : S0.length - 1 = C.length - 2 := by omega
  have hne : S0 ≠ [] := by
    intro e; rw [e] at hS0len; simp at hS0len; omega
  have hm : m0L 3 S0 = 2 := by
    have hs : (parAtR S0 2 (S0.length - 1)).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨x, (parAtR_eq_some _ _ _ _).mpr (by rw [hlast]; exact hP2)⟩
    rw [m0L]; exact Nat.findGreatest_eq hs
  have hb : badRootR 3 S0 = some x := by
    rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
    exact (parAtR_eq_some _ _ _ _).mpr (by rw [hlast]; exact hP2)
  -- the expansion
  have hvS0 : Valid 2 S0 := by
    rw [hS0, ← expandRL_zero 3 (t3n C) (valid_t3n hv)]
    exact valid_expandRL (valid_t3n hv) 0
  have hvE : Valid 2 (expandRL 3 1 S0) := valid_expandRL hvS0 1
  have hElen := expandRL_length_some hb 1
  have hvT : Valid 2 (t3n C.dropLast) := by
    rw [← expandRL_zero 3 C hv]
    exact valid_t3n (valid_expandRL hv 0)
  have hL : S0.length - 1 - x = C.length - 2 - x := by omega
  apply ext_getElem!' (by rw [t3n_length, List.length_dropLast, List.length_take, hElen]; omega)
  intro i hi
  have hi' : i < C.length - 1 := by simpa using hi
  rw [getElem!_take_of_lt _ hi']
  apply col_ext3 (hvT _ (getElem!_mem _ i hi))
    (hvE _ (getElem!_mem _ i (by rw [hElen]; omega)))
  intro k hk
  -- the entries of `t3n (C.dropLast)`
  have hT : ∀ k, k < 3 → ((t3n C.dropLast)[i]!)[k]! =
      if i < C.length - 2 then ((t3n C)[i]!)[k]! else (C[i]!)[k]! := by
    intro k hk
    by_cases hk2 : k = 2
    · subst hk2
      rw [t3n_entry_two, t3n_entry_two, getElem!_dropLast', if_pos hi']
      by_cases hiy : i < C.length - 2
      · rw [if_pos hiy]
        by_cases hR : Rz C i
        · rw [if_pos hR, if_pos ((Rz_dropLast_iff (by omega)).mpr hR)]
        · rw [if_neg hR, if_neg (fun h => hR ((Rz_dropLast_iff (by omega)).mp h))]
      · rw [if_neg hiy, if_neg (not_Rz_dropLast_ge (by omega))]
    · rw [t3n_entry_low _ i k (by omega), getElem!_dropLast', if_pos hi']
      split
      · rw [t3n_entry_low C i k (by omega)]
      · rfl
  rw [hT k hk]
  by_cases hix : i < x
  · rw [if_pos (by omega), expandRL_get_pre hb 1 hix, hS0get i (by omega)]
  · obtain ⟨t, rfl⟩ : ∃ t, i = x + t := ⟨i - x, by omega⟩
    have ht : t < (1 + 1) * (S0.length - 1 - x) := by omega
    rw [expandRL_get_copy hb 1 ht k hk, hm, hL]
    by_cases htL : t < C.length - 2 - x
    · rw [if_pos (by omega), Nat.mod_eq_of_lt htL, Nat.div_eq_of_lt htL, Nat.zero_mul,
        hS0get (x + t) (by omega)]
      simp
    · have htL' : t = C.length - 2 - x := by omega
      rw [if_neg (by omega), htL', Nat.mod_self, Nat.div_self (by omega), Nat.one_mul,
        Nat.add_zero, hlast, show x + (C.length - 2 - x) = C.length - 2 from by omega]
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
      · rw [if_pos ⟨by omega, Or.inl rfl⟩, hlow x 0 (by omega) (by omega),
          hlow _ 0 (by omega) (by omega)]
        omega
      · rw [if_pos ⟨by omega, Or.inl rfl⟩, hlow x 1 (by omega) (by omega),
          hlow _ 1 (by omega) (by omega), hx1, hy1]
      · rw [if_neg (by omega), hS0x2, hy2]

/-! ### `N = 0` -/

/-- **At `N = 0`, `t3n` lowers the rank** on every reached matrix. -/
theorem rkL_t3n_expand_zero_lt {C : List (List Nat)} (hC : SReach C) (hne : C ≠ []) :
    rkL 2 (t3n (expandRL 3 0 C)) < rkL 2 (t3n C) := by
  have hv := hC.valid
  have hS : t3n C ≠ [] := t3n_ne_nil hne
  have hvS := valid_t3n hv
  rw [expandRL_zero 3 C hv]
  by_cases hy : Rz C (C.length - 2)
  · have hS0 : (t3n C).dropLast ≠ [] := by
      intro e
      have h1 := congrArg List.length e
      rw [List.length_dropLast, t3n_length, List.length_nil] at h1
      have := hy.1
      omega
    have hvS0 : Valid 2 (t3n C).dropLast := by
      rw [← expandRL_zero 3 (t3n C) hvS]; exact valid_expandRL hvS 0
    have hvE := valid_expandRL hvS0 1
    have h1 : rkL 2 (t3n C.dropLast) ≤ rkL 2 (expandRL 3 1 (t3n C).dropLast) := by
      rw [t3n_dropLast_prefix hC hy]
      have := rkL_le_append ((expandRL 3 1 (t3n C).dropLast).take (C.length - 1))
        ((expandRL 3 1 (t3n C).dropLast).drop (C.length - 1))
        (by rw [List.take_append_drop]; exact hvE)
      rwa [List.take_append_drop] at this
    have h2 := rkL_lt hvS0 hS0 1
    have h3 := rkL_lt hvS hS 0
    rw [expandRL_zero 3 (t3n C) hvS] at h3
    exact lt_of_le_of_lt h1 (lt_trans h2 h3)
  · rw [t3n_dropLast hy, ← expandRL_zero 3 (t3n C) hvS]
    exact rkL_lt hvS hS 0

/-! ### The reduction to `N ≥ 1` -/

/-- **Open.**  `T3nRankDescRP` for `N ≥ 1`. -/
def T3nRankDescRP1 : Prop :=
  ∀ C, SReach C → RaisedPar C → ∀ N, rkL 2 (t3n (expandRL 3 (N + 1) C)) < rkL 2 (t3n C)

theorem ne_nil_of_raisedPar {C : List (List Nat)} (h : RaisedPar C) : C ≠ [] := by
  rintro rfl
  obtain ⟨y, hy, _⟩ := h
  have := ParR_lt hy
  simp at this

theorem t3nRankDescRP_of_RP1 (h : T3nRankDescRP1) : T3nRankDescRP := by
  intro C hC hR N
  cases N with
  | zero => exact rkL_t3n_expand_zero_lt hC (ne_nil_of_raisedPar hR)
  | succ N => exact h C hC hR N

/-- **The upper bound at `n = 2` under `T3nRankDescRP1`.** -/
theorem rkL_cgen_two_four_eq_of_RP1 (h : T3nRankDescRP1) :
    rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_RP (t3nRankDescRP_of_RP1 h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.rkL_t3n_expand_zero_lt
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_RP1
