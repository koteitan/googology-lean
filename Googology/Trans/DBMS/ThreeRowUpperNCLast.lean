import Googology.Trans.DBMS.ThreeRowUpperNCZero

/-!
# The shape `RaisedPar` when the raisable parent is the column before the last

`ThreeRowUpperNCZero.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `T3nRankDescRP1`: for a reached matrix
`C` (`SReach`) whose last column `z` has a raisable row-`2` parent `y`
(`RaisedPar`), `rkL 2 (t3n (C[N + 1])) < rkL 2 (t3n C)`.  This file proves it
when `y` is the column before the last, `y = n - 2` (`n` columns), under one
structural statement about the reached matrices, and so splits the open
statement in two (`rkL_cgen_two_four_eq_of_last`):

* `RPLastShape` (structural): if `C` ends in a raisable pair
  `(a,1,0)(a+1,2,1)` and `x = (b,0,0)` is the row-`1` parent of `(a,1,0)`,
  then `x` is the column just before, or the column after `x` is raisable too.
* `T3nRankDescRPInner` (rank): `T3nRankDescRP1` when `y < n - 2`.

**The proof for `y = n - 2`.**  Write `S = t3n C` and `S₀ = S.dropLast`.

* A list ending in a raisable pair expands to a ladder (`expandRL_of_Rz_last`):
  `W[N] = W.take (n-2) ++ (a,1,0)(a+1,2,0)⋯(a+N,N+1,0)`, because the bad root
  is the column `(a,1,0)` with `m₀ = 2` and the bad part is that one column.
  So `t3n (C[N]) = S.take (n-2) ++ ladder` (`t3n_expandRL_of_Rz_last`): no
  column of the ladder is raisable.
* In `S₀` the last column is the raised `(a,1,1)`, its row-`2` parent is `x`,
  so `x` is the bad root of `S₀` with `m₀ = 2` (`dropLast_t3n_badRoot`), and
  the first two columns of the second copy in `S₀[1]` are `x + (a-b, 1)` and
  `(x+1) + (a-b, 1)`.
* If `x = n - 3`, the bad part of `S₀` is `x` alone and
  `t3n (C[N]) = S₀[N + 1]` (`t3n_expandRL_eq_dropLast_expand`).
* If `x + 1` is raisable, `x + 1 = (b+1,1,1)` in `S`, and the first `n`
  columns of `S₀[1]` are `W = S.take (n-2) ++ (a,1,0)(a+1,2,1)`; then
  `t3n (C[N]) = W[N]` and `rkL W ≤ rkL (S₀[1])` (a prefix).

In both cases the rank goes down along explicit expansions and prefixes,
`rkL 2 (t3n (C[N])) < rkL 2 S₀ < rkL 2 S` (`rkL_t3n_expand_lt_of_Rz_last`), for
every `N`, with no appeal to standard forms.

**Open.**

* `RPLastShape`.  Numerically (breadth-first from `lift 3 (trioGen v)`,
  `v ≤ 3`, depth `≤ 12`, at most `16` columns, `28741` matrices): `167`
  matrices end in a raisable pair; in `30` the row-`1` parent is the column
  just before, in the other `137` the column after it is raisable, and there
  is no other case.  (At depth `≤ 10`, `≤ 14` columns, the stronger statement
  for every raisable column, not only the one before the last, holds on all
  `4469` raisable columns.)
* `T3nRankDescRPInner`.  Numerically (same search, `28741` matrices): `649`
  matrices have `RaisedPar` with `y < n - 2`; on all `1947` pairs `(C, N)`
  with `1 ≤ N ≤ 3`, both `t3n C` and `t3n (C[N])` have an explicit path of
  expansions from a trio generator (so both are in `TrioStdL`), and
  `t3n (C[N]) < t3n C` in the dictionary order, which with `rkL_lt_of_trio`
  gives the inequality at that pair.  When `y < n - 2`,
  `t3n (C[N]) = E[N - 1]` with `E = t3n (C[1] ++ [z + Δ])`, `E` a trio
  standard form below `t3n C`; the greedy paths from `t3n C` down to `E` start
  with `[1]` (the bad root of `t3n C` is the row-`1` parent `x` of `y`, and the
  copy of `x` in `(t3n C)[1]` is the first column `(z₀, z₁, 0)` of the second
  copy in `E`) and then rebuild the subtree of `y` out of the copied subtree
  of `x`; they have up to about ten steps and no common pattern, so this case
  is not reduced further here.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

/-! ### Small facts about lists -/

/-- The ladder `(a,1,0)(a+1,2,0)⋯(a+N,N+1,0)`. -/
def ladder (a N : Nat) : List (List Nat) :=
  (List.range (N + 1)).map (fun q => [a + q, 1 + q, 0])

@[simp] theorem ladder_length (a N : Nat) : (ladder a N).length = N + 1 := by
  simp [ladder]

theorem ladder_get (a N : Nat) {q : Nat} (hq : q < N + 1) :
    (ladder a N)[q]! = [a + q, 1 + q, 0] := by
  rw [ladder, getElem!_map_range _ _ hq]

theorem take_append_get_lt (l B : List (List Nat)) {m i : Nat} (hm : m ≤ l.length)
    (hi : i < m) : (l.take m ++ B)[i]! = l[i]! := by
  rw [getElem!_append_left _ _ (by rw [List.length_take]; omega), getElem!_take_of_lt _ hi]

theorem take_append_get_ge (l B : List (List Nat)) {m : Nat} (hm : m ≤ l.length) (q : Nat) :
    (l.take m ++ B)[m + q]! = B[q]! := by
  have h : (l.take m).length = m := by rw [List.length_take]; omega
  have := getElem!_append_right (l.take m) B q
  rwa [h] at this

theorem valid_take {l : List (List Nat)} (hv : Valid 2 l) (m : Nat) : Valid 2 (l.take m) :=
  fun v hv' => hv v (List.mem_of_mem_take hv')

theorem valid_dropLast {l : List (List Nat)} (hv : Valid 2 l) : Valid 2 l.dropLast :=
  fun v hv' => hv v (List.dropLast_subset _ hv')

/-- A prefix has at most the rank of the list. -/
theorem rkL_take_le {l : List (List Nat)} (hv : Valid 2 l) (m : Nat) :
    rkL 2 (l.take m) ≤ rkL 2 l := by
  have := rkL_le_append (r := 2) (l.take m) (l.drop m) (by rw [List.take_append_drop]; exact hv)
  rwa [List.take_append_drop] at this

/-- `[0]` lowers the rank. -/
theorem rkL_dropLast_lt {l : List (List Nat)} (hv : Valid 2 l) (hne : l ≠ []) :
    rkL 2 l.dropLast < rkL 2 l := by
  have := rkL_lt hv hne 0
  rwa [expandRL_zero 3 l hv] at this

/-- The only row-`0` ancestor of a column just before it is its parent. -/
theorem ParR_of_AncR_succ {l : List (List Nat)} {k x : Nat} (h : AncR l k x (x + 1)) :
    ParR l k x (x + 1) := by
  obtain ⟨b, hb, hr⟩ := transGen_head_split h
  have hxb := ParR_lt hb
  rcases hr with rfl | hr
  · exact hb
  · have := transGen_lt (fun _ _ h => ParR_lt h) hr
    omega

/-! ### A raisable pair at the end expands to a ladder -/

/-- **A list ending in a raisable pair has its bad root there**, with `m₀ = 2`. -/
theorem badRootR_of_Rz_last {W : List (List Nat)} (h : Rz W (W.length - 2)) :
    badRootR 3 W = some (W.length - 2) ∧ m0L 3 W = 2 := by
  have hl := h.1
  have hp : ParR W 2 (W.length - 2) (W.length - 1) := by
    have := ParR2_of_Rz h
    rwa [show W.length - 2 + 1 = W.length - 1 from by omega] at this
  have hs : (parAtR W 2 (W.length - 1)).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨_, (parAtR_eq_some _ _ _ _).mpr hp⟩
  have hm : m0L 3 W = 2 := by
    rw [m0L]; exact Nat.findGreatest_eq hs
  have hne : W ≠ [] := by
    rintro rfl; simp at hl
  refine ⟨?_, hm⟩
  rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
  exact (parAtR_eq_some _ _ _ _).mpr hp

/-- **A list ending in a raisable pair `(a,1,0)(a+1,2,1)` expands to a ladder**:
`W[N] = W.take (n-2) ++ (a,1,0)(a+1,2,0)⋯(a+N,N+1,0)`. -/
theorem expandRL_of_Rz_last {W : List (List Nat)} (hv : Valid 2 W) (h : Rz W (W.length - 2))
    (N : Nat) :
    expandRL 3 N W = W.take (W.length - 2) ++ ladder ((W[W.length - 2]!)[0]!) N := by
  obtain ⟨hb, hm⟩ := badRootR_of_Rz_last h
  have hl := h.1
  have hL : W.length - 1 - (W.length - 2) = 1 := by omega
  have hn : W.length - 2 ≤ W.length := by omega
  have hvE := valid_expandRL hv N
  have hlen := expandRL_length_some hb N
  rw [hL] at hlen
  have hvR : Valid 2 (W.take (W.length - 2) ++ ladder ((W[W.length - 2]!)[0]!) N) := by
    intro v hv'
    rcases List.mem_append.mp hv' with h' | h'
    · exact valid_take hv _ v h'
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h'
      rfl
  apply ext_getElem!' (by
    rw [hlen, List.length_append, List.length_take, ladder_length]; omega)
  intro i hi
  rw [hlen] at hi
  apply col_ext3 (hvE _ (getElem!_mem _ i (by rw [hlen]; omega)))
    (hvR _ (getElem!_mem _ i (by
      rw [List.length_append, List.length_take, ladder_length]; omega)))
  intro k hk
  by_cases hip : i < W.length - 2
  · rw [expandRL_get_pre hb N hip, take_append_get_lt _ _ hn hip]
  · obtain ⟨t, rfl⟩ : ∃ t, i = W.length - 2 + t := ⟨i - (W.length - 2), by omega⟩
    have ht : t < (N + 1) * (W.length - 1 - (W.length - 2)) := by rw [hL]; omega
    rw [expandRL_get_copy hb N ht k hk, hm, hL, Nat.mod_one, Nat.div_one, Nat.add_zero,
      take_append_get_ge _ _ hn t, ladder_get _ _ (by omega),
      show W.length - 1 = W.length - 2 + 1 from by omega]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [if_pos ⟨by omega, Or.inl rfl⟩, h.2.2.2.1]
      simp
    · rw [if_pos ⟨by omega, Or.inl rfl⟩, h.2.2.2.2.1, h.2.1]
      simp
    · rw [if_neg (by omega), h.2.2.1]
      simp

/-- The column before the last of a list ending in a raisable pair. -/
theorem get_eq_of_Rz_last {C : List (List Nat)} (hv : Valid 2 C) (hy : Rz C (C.length - 2))
    {a : Nat} (ha : (C[C.length - 2]!)[0]! = a) : C[C.length - 2]! = [a, 1, 0] := by
  have hl := hy.1
  apply col_ext3 (hv _ (getElem!_mem C _ (by omega))) rfl
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
  · rw [ha]; rfl
  · rw [hy.2.1]; rfl
  · rw [hy.2.2.1]; rfl

/-- **`t3n` of the ladder**: no column of the ladder is raisable, so
`t3n (C[N]) = (t3n C).take (n-2) ++ (a,1,0)(a+1,2,0)⋯(a+N,N+1,0)`. -/
theorem t3n_expandRL_of_Rz_last {C : List (List Nat)} (hv : Valid 2 C)
    (hy : Rz C (C.length - 2)) {a : Nat} (ha : (C[C.length - 2]!)[0]! = a) (N : Nat) :
    t3n (expandRL 3 N C) = (t3n C).take (C.length - 2) ++ ladder a N := by
  have hl := hy.1
  have hn : C.length - 2 ≤ C.length := by omega
  have hnT : C.length - 2 ≤ (t3n C).length := by rw [t3n_length]; omega
  have hCy := get_eq_of_Rz_last hv hy ha
  rw [expandRL_of_Rz_last hv hy N, ha]
  set E := C.take (C.length - 2) ++ ladder a N with hEdef
  have hElen : E.length = C.length - 2 + (N + 1) := by
    rw [hEdef, List.length_append, List.length_take, ladder_length]; omega
  have hElow : ∀ j, j ≤ C.length - 2 → E[j]! = C[j]! := by
    intro j hj
    rcases Nat.lt_or_ge j (C.length - 2) with h | h
    · exact take_append_get_lt C _ hn h
    · have e := take_append_get_ge C (ladder a N) hn 0
      rw [Nat.add_zero, ladder_get a N (by omega)] at e
      rw [show j = C.length - 2 from by omega, e, hCy]
      simp
  have hEhigh : ∀ q, q ≤ N → E[C.length - 2 + q]! = [a + q, 1 + q, 0] := by
    intro q hq
    rw [take_append_get_ge C _ hn q, ladder_get a N (by omega)]
  apply ext_getElem!' (by
    rw [t3n_length, hElen, List.length_append, List.length_take, ladder_length, t3n_length]
    omega)
  intro i hi
  rw [t3n_length, hElen] at hi
  rcases Nat.lt_or_ge i (C.length - 2) with h | h
  · rw [take_append_get_lt _ _ hnT h, t3n_get (by rw [hElen]; omega), t3n_get (by omega),
      hElow i (by omega)]
    have hiff : Rz E i ↔ Rz C i := by
      unfold Rz
      rw [hElow i (by omega), hElow (i + 1) (by omega), hElen]
      constructor
      · rintro ⟨_, h'⟩; exact ⟨by omega, h'⟩
      · rintro ⟨_, h'⟩; exact ⟨by omega, h'⟩
    by_cases hR : Rz C i
    · rw [if_pos hR, if_pos (hiff.mpr hR)]
    · rw [if_neg hR, if_neg (fun h' => hR (hiff.mp h'))]
  · obtain ⟨q, rfl⟩ : ∃ q, i = C.length - 2 + q := ⟨i - (C.length - 2), by omega⟩
    have hnR : ¬ Rz E (C.length - 2 + q) := by
      rintro ⟨h1, _, _, _, _, h5⟩
      rw [hElen] at h1
      rw [show C.length - 2 + q + 1 = C.length - 2 + (q + 1) from by omega,
        hEhigh (q + 1) (by omega)] at h5
      simp at h5
    rw [t3n_get_of_not hnR, hEhigh q (by omega), take_append_get_ge _ _ hnT q,
      ladder_get a N (by omega)]

/-! ### `S₀ = (t3n C).dropLast` -/

section Last

variable {C : List (List Nat)}

/-- **The bad root of `S₀`** is the row-`1` parent `x` of the raisable column
`n - 2`, with `m₀ = 2`: in `S₀` that column is `(a,1,1)`, the last. -/
theorem dropLast_t3n_badRoot (hC : SReach C) (hy : Rz C (C.length - 2)) {x : Nat}
    (hx : ParR C 1 x (C.length - 2)) :
    badRootR 3 (t3n C).dropLast = some x ∧ m0L 3 (t3n C).dropLast = 2 := by
  have hyl := hy.1
  have hxy : x < C.length - 2 := ParR_lt hx
  have hx1 : (C[x]!)[1]! = 0 := by
    have := ((ParR_one_iff C x _).mp hx).2.2.1
    rw [hy.2.1] at this
    omega
  have hx2 : (C[x]!)[2]! = 0 := low2_of_sReach hC x (by omega)
  have hxR : ¬ Rz C x := fun h => by have := h.2.1; omega
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
  have hP1 : ParR S0 1 x (C.length - 2) :=
    (ParR_congr_upto S0 C 1 _ (fun m k' hm hk => hlow m k' (by omega) hk) x).mpr hx
  have hP2 : ParR S0 2 x (C.length - 2) := by
    refine (ParR_two_iff' S0 x _).mpr ⟨hxy, Relation.TransGen.single hP1, ?_,
      fun j' a b c => ?_⟩
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
  refine ⟨?_, hm⟩
  rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
  exact (parAtR_eq_some _ _ _ _).mpr (by rw [hlast]; exact hP2)

/-- The facts about `x`, `x + 1` and the last column of `S₀` used below. -/
theorem last_facts (hC : SReach C) (hy : Rz C (C.length - 2)) {x : Nat}
    (hx : ParR C 1 x (C.length - 2)) :
    x < C.length - 2 ∧ (C[x]!)[1]! = 0 ∧ (C[x]!)[2]! = 0 ∧ ¬ Rz C x ∧
      (C[x]!)[0]! < (C[C.length - 2]!)[0]! ∧ AncR C 0 x (C.length - 2) := by
  have hyl := hy.1
  have hxy : x < C.length - 2 := ParR_lt hx
  have hx1 : (C[x]!)[1]! = 0 := by
    have := ((ParR_one_iff C x _).mp hx).2.2.1
    rw [hy.2.1] at this
    omega
  have hx2 : (C[x]!)[2]! = 0 := low2_of_sReach hC x (by omega)
  have hA : AncR C 0 x (C.length - 2) := AncR_zero_of (k := 1) (Relation.TransGen.single hx)
  exact ⟨hxy, hx1, hx2, fun h => by have := h.2.1; omega, AncR_entry_lt hA, hA⟩

/-- **When `x` is the column just before the raisable one**, the bad part of
`S₀` is `x` alone, and `t3n (C[N]) = S₀[N + 1]`. -/
theorem t3n_expandRL_eq_dropLast_expand (hC : SReach C) (hy : Rz C (C.length - 2)) {x : Nat}
    (hx : ParR C 1 x (C.length - 2)) (hx1 : x + 1 = C.length - 2) (N : Nat) :
    t3n (expandRL 3 N C) = expandRL 3 (N + 1) (t3n C).dropLast := by
  have hv := hC.valid
  have hl := hy.1
  obtain ⟨hxy, hxr1, hxr2, hxR, hx0lt, hA⟩ := last_facts hC hy hx
  obtain ⟨hb, hm⟩ := dropLast_t3n_badRoot hC hy hx
  obtain ⟨a, ha⟩ : ∃ a, (C[C.length - 2]!)[0]! = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (C[x]!)[0]! = c := ⟨_, rfl⟩
  -- `x` is the row-`0` parent of `x + 1`, so `a = c + 1`
  have hpar0 : ParR C 0 x (x + 1) := by
    apply ParR_of_AncR_succ
    rw [hx1]; exact hA
  have hac : c + 1 = a := by
    have := r0_of_sReach hC x (x + 1) hpar0
    rw [hc, hx1, ha] at this
    exact this
  rw [t3n_expandRL_of_Rz_last hv hy ha N]
  set S0 := (t3n C).dropLast with hS0
  have hS0len : S0.length = C.length - 1 := by simp [hS0]
  have hS0get : ∀ m, m < C.length - 1 → S0[m]! = (t3n C)[m]! := by
    intro m hm
    rw [hS0, getElem!_dropLast', if_pos (by rw [t3n_length]; omega)]
  have hSx : S0[x]! = C[x]! := by rw [hS0get x (by omega), t3n_get_of_not hxR]
  have hSlast : S0[S0.length - 1]! = [a, 1, 1] := by
    rw [hS0len, show C.length - 1 - 1 = C.length - 2 from by omega, hS0get _ (by omega),
      t3n_get (by omega), if_pos hy, ha]
  have hL : S0.length - 1 - x = 1 := by omega
  have hvS := valid_t3n hv
  have hvS0 : Valid 2 S0 := valid_dropLast hvS
  have hvE := valid_expandRL hvS0 (N + 1)
  have hlen1 := expandRL_length_some hb (N + 1)
  rw [hL] at hlen1
  have hnT : C.length - 2 ≤ (t3n C).length := by rw [t3n_length]; omega
  have hvR : Valid 2 ((t3n C).take (C.length - 2) ++ ladder a N) := by
    intro v hv'
    rcases List.mem_append.mp hv' with h' | h'
    · exact valid_take hvS _ v h'
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h'
      rfl
  apply ext_getElem!' (by
    rw [hlen1, List.length_append, List.length_take, ladder_length, t3n_length]; omega)
  intro i hi
  rw [List.length_append, List.length_take, ladder_length, t3n_length] at hi
  apply col_ext3 (hvR _ (getElem!_mem _ i (by
      rw [List.length_append, List.length_take, ladder_length, t3n_length]; omega)))
    (hvE _ (getElem!_mem _ i (by rw [hlen1]; omega)))
  intro k hk
  by_cases hix : i < x
  · rw [take_append_get_lt _ _ hnT (by omega), expandRL_get_pre hb _ hix, hS0get i (by omega)]
  · obtain ⟨t, rfl⟩ : ∃ t, i = x + t := ⟨i - x, by omega⟩
    have ht : t < (N + 1 + 1) * (S0.length - 1 - x) := by rw [hL]; omega
    rw [expandRL_get_copy hb (N + 1) ht k hk, hm, hL, Nat.mod_one, Nat.div_one, Nat.add_zero,
      hSx, hSlast]
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · -- the column `x` itself
      rw [Nat.add_zero, take_append_get_lt _ _ hnT (by omega), t3n_get_of_not hxR, Nat.zero_mul]
      split <;> rfl
    · -- a column of the ladder
      rw [show x + t = C.length - 2 + (t - 1) from by omega, take_append_get_ge _ _ hnT,
        ladder_get a N (by omega)]
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
      · rw [if_pos ⟨by omega, Or.inl rfl⟩, hc]
        simp only [List.getElem!_cons_zero]
        rw [show a - c = 1 from by omega, Nat.mul_one]
        omega
      · rw [if_pos ⟨by omega, Or.inl rfl⟩, hxr1]
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
        omega
      · rw [if_neg (by omega), hxr2]
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]

/-- **When the column after `x` is raisable**, the first `n` columns of `S₀[1]`
are `S.take (n-2) ++ (a,1,0)(a+1,2,1)`. -/
theorem take_dropLast_expand_one (hC : SReach C) (hy : Rz C (C.length - 2)) {x : Nat}
    (hx : ParR C 1 x (C.length - 2)) (hx1 : x + 1 < C.length - 2) (hR : Rz C (x + 1))
    {a : Nat} (ha : (C[C.length - 2]!)[0]! = a) :
    ((expandRL 3 1 (t3n C).dropLast).take C.length).length = C.length ∧
      (∀ i, i < C.length - 2 →
        ((expandRL 3 1 (t3n C).dropLast).take C.length)[i]! = (t3n C)[i]!) ∧
      ((expandRL 3 1 (t3n C).dropLast).take C.length)[C.length - 2]! = [a, 1, 0] ∧
      ((expandRL 3 1 (t3n C).dropLast).take C.length)[C.length - 1]! = [a + 1, 2, 1] := by
  have hv := hC.valid
  have hl := hy.1
  obtain ⟨hxy, hxr1, hxr2, hxR, hx0lt, hA⟩ := last_facts hC hy hx
  obtain ⟨hb, hm⟩ := dropLast_t3n_badRoot hC hy hx
  obtain ⟨c, hc⟩ : ∃ c, (C[x]!)[0]! = c := ⟨_, rfl⟩
  rw [ha, hc] at hx0lt
  -- `x` is the row-`0` and the row-`1` parent of `x + 1`
  have hpar0 : ParR C 0 x (x + 1) :=
    ParR_of_AncR_succ (AncR_zero_between hA (x + 1) (by omega) (by omega))
  have hc1 : (C[x + 1]!)[0]! = c + 1 := by
    have := r0_of_sReach hC x (x + 1) hpar0
    rw [hc] at this
    omega
  have hpar1 : ParR C 1 x (x + 1) :=
    (ParR_one_iff C x (x + 1)).mpr ⟨by omega, Relation.TransGen.single hpar0,
      by rw [hxr1, hR.2.1]; omega, fun j' a b _ => by omega⟩
  set S0 := (t3n C).dropLast with hS0
  have hS0len : S0.length = C.length - 1 := by simp [hS0]
  have hS0get : ∀ m, m < C.length - 1 → S0[m]! = (t3n C)[m]! := by
    intro m hm
    rw [hS0, getElem!_dropLast', if_pos (by rw [t3n_length]; omega)]
  have hlow : ∀ m k, m < C.length - 1 → k ≤ 1 → (S0[m]!)[k]! = (C[m]!)[k]! := by
    intro m k hm hk
    rw [hS0get m hm, t3n_entry_low C m k hk]
  have hSx : S0[x]! = C[x]! := by rw [hS0get x (by omega), t3n_get_of_not hxR]
  have hSx1 : S0[x + 1]! = [c + 1, 1, 1] := by
    rw [hS0get (x + 1) (by omega), t3n_get (by omega), if_pos hR, hc1]
  have hSlast : S0[S0.length - 1]! = [a, 1, 1] := by
    rw [hS0len, show C.length - 1 - 1 = C.length - 2 from by omega, hS0get _ (by omega),
      t3n_get (by omega), if_pos hy, ha]
  have hS0par : ∀ k, k ≤ 1 → ParR S0 k x (x + 1) := by
    intro k hk
    have e := ParR_congr_upto S0 C k (x + 1)
      (fun m k' hm hk' => hlow m k' (by omega) (by omega)) x
    rcases (show k = 0 ∨ k = 1 from by omega) with rfl | rfl
    · exact e.mpr hpar0
    · exact e.mpr hpar1
  set L := S0.length - 1 - x with hLdef
  have hL : L = C.length - 2 - x := by omega
  have hL2 : 2 ≤ L := by omega
  have hlen1 := expandRL_length_some hb 1
  rw [← hLdef] at hlen1
  have hlenT : ((expandRL 3 1 S0).take C.length).length = C.length := by
    rw [List.length_take, hlen1]; omega
  have hget : ∀ i, i < C.length → ((expandRL 3 1 S0).take C.length)[i]! = (expandRL 3 1 S0)[i]! :=
    fun i hi => getElem!_take_of_lt _ hi
  have hvE := valid_expandRL (valid_dropLast (valid_t3n hv)) 1
  refine ⟨hlenT, fun i hi => ?_, ?_, ?_⟩
  · rw [hget i (by omega)]
    by_cases hix : i < x
    · rw [expandRL_get_pre hb 1 hix, hS0get i (by omega)]
    · obtain ⟨t, rfl⟩ : ∃ t, i = x + t := ⟨i - x, by omega⟩
      have ht : t < (1 + 1) * (S0.length - 1 - x) := by rw [← hLdef]; omega
      have hvS := valid_t3n hv
      apply col_ext3 (hvE _ (getElem!_mem _ _ (by rw [hlen1]; omega)))
        (hvS _ (getElem!_mem _ _ (by rw [t3n_length]; omega)))
      intro k hk
      rw [expandRL_get_copy hb 1 ht k hk, ← hLdef, Nat.mod_eq_of_lt (by omega),
        Nat.div_eq_of_lt (by omega), Nat.zero_mul, hS0get (x + t) (by omega)]
      split <;> rfl
  · rw [hget _ (by omega)]
    have ht : L < (1 + 1) * (S0.length - 1 - x) := by rw [← hLdef]; omega
    apply col_ext3 (hvE _ (getElem!_mem _ _ (by rw [hlen1]; omega))) rfl
    intro k hk
    rw [show C.length - 2 = x + L from by omega, expandRL_get_copy hb 1 ht k hk, ← hLdef,
      Nat.mod_self, Nat.div_self (by omega), Nat.one_mul, Nat.add_zero, hm, hSx, hSlast]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [if_pos ⟨by omega, Or.inl rfl⟩, hc]
      simp only [List.getElem!_cons_zero]
      omega
    · rw [if_pos ⟨by omega, Or.inl rfl⟩, hxr1]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    · rw [if_neg (by omega), hxr2]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
  · rw [hget _ (by omega)]
    have ht : L + 1 < (1 + 1) * (S0.length - 1 - x) := by rw [← hLdef]; omega
    apply col_ext3 (hvE _ (getElem!_mem _ _ (by rw [hlen1]; omega))) rfl
    intro k hk
    have hmod : (L + 1) % L = 1 := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : (L + 1) / L = 1 := by
      rw [Nat.add_div_left _ (by omega), Nat.div_eq_of_lt (by omega)]
    rw [show C.length - 1 = x + (L + 1) from by omega, expandRL_get_copy hb 1 ht k hk, ← hLdef,
      hmod, hdiv, Nat.one_mul, hm, hSx, hSx1, hSlast]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [if_pos ⟨by omega, Or.inr (Relation.TransGen.single (hS0par 0 (by omega)))⟩, hc]
      simp only [List.getElem!_cons_zero]
      omega
    · rw [if_pos ⟨by omega, Or.inr (Relation.TransGen.single (hS0par 1 le_rfl))⟩, hxr1]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    · rw [if_neg (by omega)]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]

/-- **The rank goes down when the raisable parent is the column before the
last**, provided the row-`1` parent `x` of that column is the column just
before it or is followed by a raisable column. -/
theorem rkL_t3n_expand_lt_of_Rz_last (hC : SReach C) (hy : Rz C (C.length - 2))
    (hshape : ∀ x, ParR C 1 x (C.length - 2) → x + 1 = C.length - 2 ∨ Rz C (x + 1))
    (N : Nat) : rkL 2 (t3n (expandRL 3 N C)) < rkL 2 (t3n C) := by
  have hv := hC.valid
  have hl := hy.1
  have hvS := valid_t3n hv
  have hvS0 : Valid 2 (t3n C).dropLast := valid_dropLast hvS
  have hSne : t3n C ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [t3n_length, List.length_nil] at this
    omega
  have hS0ne : (t3n C).dropLast ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [List.length_dropLast, t3n_length, List.length_nil] at this
    omega
  have h0 : rkL 2 (t3n C).dropLast < rkL 2 (t3n C) := rkL_dropLast_lt hvS hSne
  obtain ⟨x, hx⟩ := exists_ParR1_of_sReach hC (j := C.length - 2) (by omega)
    (by rw [hy.2.1]; omega)
  have hxy := ParR_lt hx
  obtain ⟨a, ha⟩ : ∃ a, (C[C.length - 2]!)[0]! = a := ⟨_, rfl⟩
  by_cases hx1 : x + 1 = C.length - 2
  · rw [t3n_expandRL_eq_dropLast_expand hC hy hx hx1 N]
    exact lt_trans (rkL_lt hvS0 hS0ne (N + 1)) h0
  · have hR : Rz C (x + 1) := (hshape x hx).resolve_left hx1
    obtain ⟨hWlen, hWlow, hWy, hWz⟩ :=
      take_dropLast_expand_one hC hy hx (by omega) hR ha
    obtain ⟨W, hW⟩ : ∃ W, W = (expandRL 3 1 (t3n C).dropLast).take C.length := ⟨_, rfl⟩
    rw [← hW] at hWlen hWlow hWy hWz
    have hvW : Valid 2 W := by rw [hW]; exact valid_take (valid_expandRL hvS0 1) _
    have hRz : Rz W (W.length - 2) := by
      rw [hWlen]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hWy]; rfl
      · rw [hWy]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz, hWy]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz]; rfl
    have hWa : (W[W.length - 2]!)[0]! = a := by rw [hWlen, hWy]; rfl
    have hWt : W.take (C.length - 2) = (t3n C).take (C.length - 2) := by
      apply ext_getElem!' (by rw [List.length_take, List.length_take, hWlen, t3n_length])
      intro i hi
      rw [List.length_take, hWlen] at hi
      rw [getElem!_take_of_lt _ (by omega), getElem!_take_of_lt _ (by omega), hWlow i (by omega)]
    have hWN : expandRL 3 N W = t3n (expandRL 3 N C) := by
      rw [t3n_expandRL_of_Rz_last hv hy ha N, expandRL_of_Rz_last hvW hRz N, hWa, hWlen, hWt]
    have hWne : W ≠ [] := by
      intro e
      have := congrArg List.length e
      rw [hWlen, List.length_nil] at this
      omega
    rw [← hWN]
    calc rkL 2 (expandRL 3 N W) < rkL 2 W := rkL_lt hvW hWne N
      _ ≤ rkL 2 (expandRL 3 1 (t3n C).dropLast) := by
          rw [hW]; exact rkL_take_le (valid_expandRL hvS0 1) _
      _ < rkL 2 (t3n C).dropLast := rkL_lt hvS0 hS0ne 1
      _ < rkL 2 (t3n C) := h0

end Last

/-! ### The reduction -/

/-- **Open (structural).**  If a reached matrix ends in a raisable pair, the
row-`1` parent `x` of its raisable column is the column just before it, or the
column after `x` is raisable. -/
def RPLastShape : Prop :=
  ∀ C, SReach C → Rz C (C.length - 2) → ∀ x, ParR C 1 x (C.length - 2) →
    x + 1 = C.length - 2 ∨ Rz C (x + 1)

/-- **Open (rank).**  `T3nRankDescRP1` when the raisable parent is not the
column before the last. -/
def T3nRankDescRPInner : Prop :=
  ∀ C, SReach C → RaisedPar C → ¬ Rz C (C.length - 2) →
    ∀ N, rkL 2 (t3n (expandRL 3 (N + 1) C)) < rkL 2 (t3n C)

/-- **Under `RPLastShape`, `T3nRankDescRP1` reduces to `T3nRankDescRPInner`.** -/
theorem t3nRankDescRP1_of_last (h1 : RPLastShape) (h2 : T3nRankDescRPInner) :
    T3nRankDescRP1 := by
  intro C hC hR N
  by_cases hy : Rz C (C.length - 2)
  · exact rkL_t3n_expand_lt_of_Rz_last hC hy (h1 C hC hy) (N + 1)
  · exact h2 C hC hR hy N

/-- **The upper bound at `n = 2` under `RPLastShape` and `T3nRankDescRPInner`**:
the DBMS content `(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix
`(0,0,0)(1,1,1)(2,2,2)` have the same rank. -/
theorem rkL_cgen_two_four_eq_of_last (h1 : RPLastShape) (h2 : T3nRankDescRPInner) :
    rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_RP1 (t3nRankDescRP1_of_last h1 h2)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.expandRL_of_Rz_last
#print axioms Googology.Trans.DBMS.rkL_t3n_expand_lt_of_Rz_last
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_last
