import Googology.Trans.DBMS.ThreeRowUpperRPInner

/-!
# `T3nInnerStd`, reduced to one matrix

`ThreeRowUpperRPInner.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `T3nInnerStd`: for a reached `C` whose
last column `z` has a raisable row-`2` parent `y` with `y < n - 2`
(`n` columns), if `t3n C` is in the trio fragment then so is every
`t3n (C[N + 1])`.  This file replaces the statement for every `N` by a
statement about one matrix.

**The pushed matrix.**  With `Δ = z - C[y]` in rows `0` and `1`,

    pushL C y = C[1] ++ [(z₀ + Δ₀, z₁ + Δ₁, z₂)].

`C[1] = G B B₁` with `B` the columns `y ⋯ n - 2` and `B₁` its copy; the new
last column is the copy of `z` in `B₁`'s frame.  Then:

* `expandRL_pushL`: `(pushL C y)[N] = C[N + 1]`.  The row-`2` parent of the
  last column of `pushL C y` is the copy `y + L` of `y` (`L = n - 1 - y`),
  with `m₀ = 2`, and `y + L` is a row-`k` ancestor (`k ≤ 1`) of the copy of a
  column exactly when `y` is one of the source in `C`.
* `pushL C y` has `Low2`, `R1` and not `RaisedPar`: the row-`2` parent `y + L`
  has row-`1` entry `z₁ ≥ 2`.  So `t3n` commutes with its expansions
  (`expandRL_t3n`) and
  `t3n (C[N + 1]) = (t3n (pushL C y))[N]` (`t3n_expand_eq_push`).

Hence `T3nPushStd` (one matrix) gives `T3nInnerStd`, and the upper bound
(`rkL_cgen_two_four_eq_of_push`).

The row-`1` ancestors are handled by the characterization `AncR1_iff`:
`j` is a row-`1` ancestor of `i` iff it is a row-`0` ancestor, its row-`1`
entry is smaller than that of `i`, and smaller than that of every row-`0`
ancestor of `i` after `j`.

**Open.**  `T3nPushStd`.  Numerically (breadth-first from
`lift 3 (trioGen v)`, `v ≤ 3`, `N ≤ 2` at each step, depth `≤ 14`, at most `20`
columns, `185482` matrices, `2892` of them in the shape): every
`t3n (pushL C y)` has an explicit path of expansions from a trio generator, and
it lies below `(t3n C)[1]` in the dictionary order.  A second run
(breadth-first from `lift 3 (trioGen v)`, `1 ≤ v ≤ 5`, `N ≤ 3` at each step,
depth `≤ 14`, at most `22` columns, `1615358` matrices, `13235` of them in the
shape) gives the same: every `t3n (pushL C y)` is reached from a trio generator
by a greedy path of expansions and is `≤ (t3n C)[1]`; no exception.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL)
open Classical

/-! ### Row-`1` ancestors -/

theorem AncR0_mid {l : List (List Nat)} {j m i : Nat} (hj : AncR l 0 j i) (hm : AncR l 0 m i)
    (hjm : j < m) : AncR l 0 j m := by
  have hmi := (AncR0_iff l m i).mp hm
  rw [AncR0_iff] at hj ⊢
  exact ⟨hjm, fun m' a b => hj.2 m' a (by omega)⟩

/-- **Row-`1` ancestors by row-`0` ancestors and row-`1` entries.** -/
theorem AncR1_iff (l : List (List Nat)) : ∀ i j, AncR l 1 j i ↔
    AncR l 0 j i ∧ (l[j]!)[1]! < (l[i]!)[1]! ∧
      ∀ m, j < m → m < i → AncR l 0 m i → (l[j]!)[1]! < (l[m]!)[1]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro j
  constructor
  · intro h
    exact ⟨AncR_zero_of h, AncR_entry_lt h, fun m a b c => row1_between_of_AncR1 i j m h c a b⟩
  · rintro ⟨h0, h1, hmid⟩
    have hji : j < i := transGen_lt (fun _ _ h => ParR_lt h) h0
    let P : Nat → Prop := fun m => j ≤ m ∧ AncR l 0 m i ∧ (l[m]!)[1]! < (l[i]!)[1]!
    have hPj : P j := ⟨le_rfl, h0, h1⟩
    have hPp : P (Nat.findGreatest P (i - 1)) := Nat.findGreatest_spec (P := P) (m := j)
      (by omega) hPj
    obtain ⟨p, hp⟩ : ∃ p, p = Nat.findGreatest P (i - 1) := ⟨_, rfl⟩
    rw [← hp] at hPp
    have hpi : p < i := transGen_lt (fun _ _ h => ParR_lt h) hPp.2.1
    have hmax : ∀ m, p < m → m < i → ¬ P m := fun m a b => by
      rw [hp] at a
      exact Nat.findGreatest_is_greatest (P := P) a (by omega)
    have hpar : ParR l 1 p i := by
      refine (ParR_one_iff l p i).mpr ⟨hpi, hPp.2.1, hPp.2.2, fun m a b c => ?_⟩
      by_contra hc
      exact hmax m a b ⟨by omega, c, by omega⟩
    rcases Nat.eq_or_lt_of_le hPp.1 with he | hlt
    · rw [he]; exact Relation.TransGen.single hpar
    · have hjp : AncR l 1 j p := (ih p hpi j).mpr ⟨AncR0_mid h0 hPp.2.1 hlt,
        hmid p hlt hpi hPp.2.1, fun m a b c => hmid m a (by omega) (Relation.TransGen.trans c hPp.2.1)⟩
      exact Relation.TransGen.tail hjp hpar

/-- A row-`0` ancestor of `t` after a row-`1` ancestor `y` of `t` is a row-`1`
descendant of `y`. -/
theorem AncR1_of_between {l : List (List Nat)} {y v t : Nat} (hyt : AncR l 1 y t)
    (hvt : AncR l 0 v t) (hyv : y < v) : AncR l 1 y v := by
  have hvt' := (AncR0_iff l v t).mp hvt
  refine (AncR1_iff l v y).mpr ⟨AncR0_mid (AncR_zero_of hyt) hvt hyv,
    row1_between_of_AncR1 t y v hyt hvt hyv hvt'.1, fun m a b c => ?_⟩
  exact row1_between_of_AncR1 t y m hyt (Relation.TransGen.trans c hvt) a (by omega)

/-! ### The bad root from a row-`2` parent -/

theorem badRoot_of_par2 {l : List (List Nat)} {p : Nat} (h : ParR l 2 p (l.length - 1)) :
    m0L 3 l = 2 ∧ badRootR 3 l = some p := by
  have hpl := ParR_lt h
  have hne : l ≠ [] := by rintro rfl; simp at hpl
  have hm : m0L 3 l = 2 := by
    have hs : (parAtR l 2 (l.length - 1)).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨p, (parAtR_eq_some _ _ _ _).mpr h⟩
    rw [m0L]; exact Nat.findGreatest_eq hs
  refine ⟨hm, ?_⟩
  rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
  exact (parAtR_eq_some _ _ _ _).mpr h

/-! ### The pushed matrix -/

/-- `C[1]` followed by the copy `(z₀ + Δ₀, z₁ + Δ₁, z₂)` of the last column,
`Δ = z - C[y]`. -/
def pushL (C : List (List Nat)) (y : Nat) : List (List Nat) :=
  expandRL 3 1 C ++
    [[(C[C.length - 1]!)[0]! + ((C[C.length - 1]!)[0]! - (C[y]!)[0]!),
      (C[C.length - 1]!)[1]! + ((C[C.length - 1]!)[1]! - (C[y]!)[1]!),
      (C[C.length - 1]!)[2]!]]

section Push

variable {C : List (List Nat)} {y : Nat}

theorem pushL_length (hb : badRootR 3 C = some y) :
    (pushL C y).length = y + (C.length - 1 - y) + (C.length - 1 - y) + 1 := by
  rw [pushL, List.length_append, expandRL_length_some hb 1]
  simp only [List.length_singleton]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem pushL_get_low (hb : badRootR 3 C = some y) {i : Nat}
    (hi : i < y + (C.length - 1 - y) + (C.length - 1 - y)) :
    (pushL C y)[i]! = (expandRL 3 1 C)[i]! := by
  rw [pushL, getElem!_append_left]
  rw [expandRL_length_some hb 1, Nat.add_mul, Nat.one_mul]
  omega

theorem pushL_get_last (hb : badRootR 3 C = some y) :
    (pushL C y)[y + (C.length - 1 - y) + (C.length - 1 - y)]! =
      [(C[C.length - 1]!)[0]! + ((C[C.length - 1]!)[0]! - (C[y]!)[0]!),
        (C[C.length - 1]!)[1]! + ((C[C.length - 1]!)[1]! - (C[y]!)[1]!),
        (C[C.length - 1]!)[2]!] := by
  have hl : (expandRL 3 1 C).length = y + (C.length - 1 - y) + (C.length - 1 - y) := by
    rw [expandRL_length_some hb 1, Nat.add_mul, Nat.one_mul]; omega
  have := getElem!_append_right (expandRL 3 1 C)
    [[(C[C.length - 1]!)[0]! + ((C[C.length - 1]!)[0]! - (C[y]!)[0]!),
      (C[C.length - 1]!)[1]! + ((C[C.length - 1]!)[1]! - (C[y]!)[1]!),
      (C[C.length - 1]!)[2]!]] 0
  rw [Nat.add_zero, hl] at this
  rw [pushL, this]
  rfl

/-- **The window of `pushL C y`**: the column `y + L + u` (`u ≤ L`) is the copy
of the column `y + u` of `C`, shifted by `Δ` in rows `k ≤ 1` when `u = 0` or
`y` is a row-`k` ancestor of `y + u`. -/
theorem pushL_win (hb : badRootR 3 C = some y) (hm : m0L 3 C = 2)
    (hyz : AncR C 1 y (C.length - 1)) {u : Nat} (hu : u ≤ C.length - 1 - y) (k : Nat)
    (hk : k < 3) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[k]! = (C[y + u]!)[k]! +
      (if k < 2 ∧ (u = 0 ∨ AncR C k y (y + u))
        then (C[C.length - 1]!)[k]! - (C[y]!)[k]! else 0) := by
  have hyl : y < C.length - 1 := by have := badRootR_lt hb; omega
  rcases Nat.lt_or_ge u (C.length - 1 - y) with hul | hul
  · rw [pushL_get_low hb (by omega)]
    have e := expandRL_get_cpos (N := 1) hb rfl (q := 1) le_rfl hul k hk
    rw [hm, Nat.one_mul, Nat.one_mul] at e
    rw [show y + (C.length - 1 - y) + u = y + (C.length - 1 - y + u) from by omega, e]
  · have hu' : u = C.length - 1 - y := by omega
    subst hu'
    rw [show y + (C.length - 1 - y) + (C.length - 1 - y) = y + (C.length - 1 - y) +
      (C.length - 1 - y) from rfl, pushL_get_last hb,
      show y + (C.length - 1 - y) = C.length - 1 from by omega]
    have h0 : AncR C 0 y (C.length - 1) := AncR_zero_of hyz
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [if_pos ⟨by omega, Or.inr h0⟩]; rfl
    · rw [if_pos ⟨by omega, Or.inr hyz⟩]; rfl
    · rw [if_neg (by omega)]; rfl

/-- The hypotheses of this section, from a row-`2` parent `y` of the last
column. -/
structure PushHyp (C : List (List Nat)) (y : Nat) : Prop where
  hb : badRootR 3 C = some y
  hm : m0L 3 C = 2
  hyz : AncR C 1 y (C.length - 1)
  hlt2 : (C[y]!)[2]! < (C[C.length - 1]!)[2]!
  hmid2 : ∀ j', y < j' → j' < C.length - 1 → AncR C 1 j' (C.length - 1) →
    (C[C.length - 1]!)[2]! ≤ (C[j']!)[2]!

theorem pushHyp_of (hyp : ParR C 2 y (C.length - 1)) : PushHyp C y := by
  obtain ⟨hm, hb⟩ := badRoot_of_par2 hyp
  obtain ⟨_, hT1, hlt2, hmid⟩ := (ParR_two_iff' C y _).mp hyp
  exact ⟨hb, hm, hT1, hlt2, hmid⟩

section Hyp

variable (H : PushHyp C y)
include H

theorem PushHyp.yl : y < C.length - 1 := by have := badRootR_lt H.hb; omega

theorem PushHyp.d0 : (C[y]!)[0]! < (C[C.length - 1]!)[0]! := AncR_entry_lt (AncR_zero_of H.hyz)

theorem PushHyp.d1 : (C[y]!)[1]! < (C[C.length - 1]!)[1]! := AncR_entry_lt H.hyz

/-- Row `0` of the window. -/
theorem PushHyp.w0 {u : Nat} (hu : u ≤ C.length - 1 - y) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[0]! = (C[y + u]!)[0]! +
      ((C[C.length - 1]!)[0]! - (C[y]!)[0]!) := by
  rw [pushL_win H.hb H.hm H.hyz hu 0 (by omega)]
  congr 1
  rcases Nat.eq_zero_or_pos u with h0 | h0
  · rw [if_pos ⟨by omega, Or.inl h0⟩]
  · rcases Nat.lt_or_ge u (C.length - 1 - y) with hul | hul
    · rw [if_pos ⟨by omega, Or.inr (AncR_zero_between (AncR_zero_of H.hyz) _ (by omega)
        (by have := H.yl; omega))⟩]
    · rw [if_pos ⟨by omega, Or.inr (by
        rw [show y + u = C.length - 1 from by have := H.yl; omega]; exact AncR_zero_of H.hyz)⟩]

/-- Row `1` of the window. -/
theorem PushHyp.w1 {u : Nat} (hu : u ≤ C.length - 1 - y) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[1]! = (C[y + u]!)[1]! +
      (if u = 0 ∨ AncR C 1 y (y + u) then (C[C.length - 1]!)[1]! - (C[y]!)[1]! else 0) := by
  rw [pushL_win H.hb H.hm H.hyz hu 1 (by omega)]
  congr 1
  by_cases hc : u = 0 ∨ AncR C 1 y (y + u)
  · rw [if_pos ⟨by omega, hc⟩, if_pos hc]
  · rw [if_neg (fun h => hc h.2), if_neg hc]

/-- Row `2` of the window. -/
theorem PushHyp.w2 {u : Nat} (hu : u ≤ C.length - 1 - y) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[2]! = (C[y + u]!)[2]! := by
  rw [pushL_win H.hb H.hm H.hyz hu 2 (by omega), if_neg (by omega), Nat.add_zero]

/-- The row-`1` entries of the window are at most `Δ₁` more, and exactly `Δ₁`
more on `y` and its row-`1` descendants. -/
theorem PushHyp.w1_le {u : Nat} (hu : u ≤ C.length - 1 - y) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[1]! ≤ (C[y + u]!)[1]! +
      ((C[C.length - 1]!)[1]! - (C[y]!)[1]!) := by
  rw [H.w1 hu]
  split <;> omega

theorem PushHyp.w1_eq {u : Nat} (hu : u ≤ C.length - 1 - y) (hc : u = 0 ∨ AncR C 1 y (y + u)) :
    ((pushL C y)[y + (C.length - 1 - y) + u]!)[1]! = (C[y + u]!)[1]! +
      ((C[C.length - 1]!)[1]! - (C[y]!)[1]!) := by
  rw [H.w1 hu, if_pos hc]

/-- **Row-`0` ancestors inside the window** are those of the sources. -/
theorem PushHyp.anc0 {u1 u2 : Nat} (h12 : u1 < u2) (hu2 : u2 ≤ C.length - 1 - y) :
    AncR (pushL C y) 0 (y + (C.length - 1 - y) + u1) (y + (C.length - 1 - y) + u2) ↔
      AncR C 0 (y + u1) (y + u2) := by
  rw [AncR0_iff, AncR0_iff]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨by omega, fun m a b => ?_⟩
    have := h (y + (C.length - 1 - y) + (m - y)) (by omega) (by omega)
    rw [H.w0 (by omega), H.w0 (by omega), show y + (m - y) = m from by omega] at this
    omega
  · rintro ⟨_, h⟩
    refine ⟨by omega, fun m a b => ?_⟩
    obtain ⟨u, rfl⟩ : ∃ u, m = y + (C.length - 1 - y) + u := ⟨m - (y + (C.length - 1 - y)), by omega⟩
    rw [H.w0 (by omega), H.w0 (by omega)]
    have := h (y + u) (by omega) (by omega)
    omega

/-- A column of `C` in `(y, n - 1)` that is a row-`0` ancestor of the last
column is a row-`1` descendant of `y`. -/
theorem PushHyp.desc_of_anc0 {u : Nat} (hu0 : 0 < u) (hul : u < C.length - 1 - y)
    (h : AncR C 0 (y + u) (C.length - 1)) : AncR C 1 y (y + u) :=
  AncR1_of_between H.hyz h (by omega)

/-- **Row-`1` ancestry from the window root** is that of `y`. -/
theorem PushHyp.anc1_root {u : Nat} (hu0 : 0 < u) (hu : u ≤ C.length - 1 - y) :
    AncR (pushL C y) 1 (y + (C.length - 1 - y)) (y + (C.length - 1 - y) + u) ↔
      AncR C 1 y (y + u) := by
  have e0 := H.w1_eq (u := 0) (by omega) (Or.inl rfl)
  simp only [Nat.add_zero] at e0
  have hL := H.yl
  constructor
  · intro h
    obtain ⟨h0, h1, hmid⟩ := (AncR1_iff _ _ _).mp h
    have h0' := (H.anc0 (u1 := 0) hu0 hu).mp (by rwa [Nat.add_zero])
    rw [Nat.add_zero] at h0'
    refine (AncR1_iff _ _ _).mpr ⟨h0', ?_, fun m a b c => ?_⟩
    · have := H.w1_le hu
      rw [e0] at h1
      omega
    · obtain ⟨v, rfl⟩ : ∃ v, m = y + v := ⟨m - y, by omega⟩
      have c' := (H.anc0 (u1 := v) (by omega) hu).mpr c
      have hv1 := hmid _ (by omega) (by omega) c'
      have hv2 := H.w1_le (u := v) (by omega)
      rw [e0] at hv1
      omega
  · intro h
    obtain ⟨h0, h1, hmid⟩ := (AncR1_iff _ _ _).mp h
    refine (AncR1_iff _ _ _).mpr ⟨?_, ?_, fun m a b c => ?_⟩
    · have := (H.anc0 (u1 := 0) hu0 hu).mpr (by rwa [Nat.add_zero])
      rwa [Nat.add_zero] at this
    · rw [e0, H.w1_eq hu (Or.inr h)]
      omega
    · obtain ⟨v, rfl⟩ : ∃ v, m = y + (C.length - 1 - y) + v :=
        ⟨m - (y + (C.length - 1 - y)), by omega⟩
      have c' := (H.anc0 (u1 := v) (by omega) hu).mp c
      have hv := hmid (y + v) (by omega) (by omega) c'
      have hyv : AncR C 1 y (y + v) := AncR1_of_between h c' (by omega)
      rw [e0, H.w1_eq (u := v) (by omega) (Or.inr hyv)]
      omega

/-- **Row-`1` ancestry to the last column of `pushL C y`** is that to `z`. -/
theorem PushHyp.anc1_last {u : Nat} (hu0 : 0 < u) (hul : u < C.length - 1 - y)
    (h : AncR (pushL C y) 1 (y + (C.length - 1 - y) + u)
      (y + (C.length - 1 - y) + (C.length - 1 - y))) :
    AncR C 1 (y + u) (C.length - 1) := by
  have hL := H.yl
  have hn : y + (C.length - 1 - y) = C.length - 1 := by omega
  obtain ⟨h0, h1, hmid⟩ := (AncR1_iff _ _ _).mp h
  have h0' := (H.anc0 hul le_rfl).mp h0
  rw [hn] at h0'
  have hdu := H.desc_of_anc0 hu0 hul h0'
  have eL := H.w1_eq (u := C.length - 1 - y) le_rfl (Or.inr (by rw [hn]; exact H.hyz))
  have ez : C[y + (C.length - 1 - y)]! = C[C.length - 1]! := by rw [hn]
  rw [ez] at eL
  refine (AncR1_iff _ _ _).mpr ⟨h0', ?_, fun m a b c => ?_⟩
  · rw [H.w1_eq (u := u) (by omega) (Or.inr hdu), eL] at h1
    omega
  · obtain ⟨v, rfl⟩ : ∃ v, m = y + v := ⟨m - y, by omega⟩
    have c' : AncR C 0 (y + v) (y + (C.length - 1 - y)) := by rw [hn]; exact c
    have c'' := (H.anc0 (u1 := v) (by omega) le_rfl).mpr c'
    have := hmid _ (by omega) (by omega) c''
    rw [H.w1_eq (u := u) (by omega) (Or.inr hdu),
      H.w1_eq (u := v) (by omega) (Or.inr (H.desc_of_anc0 (by omega) (by omega) c))] at this
    omega

/-- **The row-`2` parent of the last column of `pushL C y`** is `y + L`. -/
theorem PushHyp.par2 :
    ParR (pushL C y) 2 (y + (C.length - 1 - y)) ((pushL C y).length - 1) := by
  have hL := H.yl
  have hn : y + (C.length - 1 - y) = C.length - 1 := by omega
  rw [pushL_length H.hb, Nat.add_sub_cancel]
  refine (ParR_two_iff' _ _ _).mpr ⟨by omega, ?_, ?_, fun j' a b c => ?_⟩
  · exact (H.anc1_root (by omega) le_rfl).mpr (by rw [hn]; exact H.hyz)
  · have e1 := H.w2 (u := 0) (by omega)
    have e2 := H.w2 (u := C.length - 1 - y) le_rfl
    simp only [Nat.add_zero] at e1
    rw [e1, e2, hn]
    exact H.hlt2
  · obtain ⟨u, rfl⟩ : ∃ u, j' = y + (C.length - 1 - y) + u :=
      ⟨j' - (y + (C.length - 1 - y)), by omega⟩
    have hA := H.anc1_last (u := u) (by omega) (by omega) c
    rw [H.w2 (u := u) (by omega), H.w2 (u := C.length - 1 - y) le_rfl, hn]
    exact H.hmid2 (y + u) (by omega) (by omega) hA

theorem PushHyp.pushBad : m0L 3 (pushL C y) = 2 ∧
    badRootR 3 (pushL C y) = some (y + (C.length - 1 - y)) :=
  badRoot_of_par2 H.par2

/-- **`(pushL C y)[N] = C[N + 1]`.** -/
theorem PushHyp.expand (hv : Valid 2 C) (N : Nat) :
    expandRL 3 N (pushL C y) = expandRL 3 (N + 1) C := by
  have hL := H.yl
  obtain ⟨L, hLd⟩ : ∃ L, C.length - 1 - y = L := ⟨_, rfl⟩
  have hn : y + L = C.length - 1 := by omega
  obtain ⟨hmP, hbP⟩ := H.pushBad
  rw [hLd] at hbP
  have hPlen := pushL_length H.hb
  rw [hLd] at hPlen
  have hLdP : (pushL C y).length - 1 - (y + L) = L := by omega
  have hlenP := expandRL_length_some hbP N
  rw [hLdP] at hlenP
  have hlenC := expandRL_length_some H.hb (N + 1)
  rw [hLd] at hlenC
  have hvP : Valid 2 (pushL C y) := by
    intro v hv'
    rcases List.mem_append.mp hv' with h' | h'
    · exact valid_expandRL hv 1 v h'
    · rw [List.mem_singleton] at h'
      rw [h']; rfl
  have hvE := valid_expandRL hvP N
  have hvC := valid_expandRL hv (N + 1)
  apply ext_getElem!' (by rw [hlenP, hlenC, Nat.add_mul (N + 1) 1, Nat.one_mul]; omega)
  intro i hi
  rw [hlenP] at hi
  apply col_ext3 (hvE _ (getElem!_mem _ i (by rw [hlenP]; omega)))
    (hvC _ (getElem!_mem _ i (by rw [hlenC, Nat.add_mul (N + 1) 1, Nat.one_mul]; omega)))
  intro k hk
  rcases Nat.lt_or_ge i (y + L) with hiL | hiL
  · -- before the window: columns of `C`
    rw [expandRL_get_pre hbP N hiL, expandRL_get_low H.hb (N + 1) (by omega) hk,
      pushL_get_low H.hb (by omega), expandRL_get_low H.hb 1 (by omega) hk]
  · have hL0 : 0 < L := by omega
    obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < L ∧ i = y + L + (q * L + s) :=
      ⟨(i - (y + L)) / L, (i - (y + L)) % L, Nat.mod_lt _ hL0,
        by rw [Nat.div_add_mod']; omega⟩
    have hq : q ≤ N := by
      by_contra hc
      have := Nat.mul_le_mul_right L (show N + 1 ≤ q from by omega)
      omega
    have eP := expandRL_get_cpos (N := N) hbP hLdP hq hs k hk
    have eC := expandRL_get_cpos (N := N + 1) H.hb hLd (q := q + 1) (by omega) hs k hk
    rw [eP, show y + L + (q * L + s) = y + ((q + 1) * L + s) from by rw [Nat.add_mul]; omega,
      eC, hmP, H.hm]
    -- the window entries
    have ws := pushL_win H.hb H.hm H.hyz (u := s) (by omega) k hk
    have wL := pushL_win H.hb H.hm H.hyz (u := L) (by omega) k hk
    have w0 := pushL_win H.hb H.hm H.hyz (u := 0) (by omega) k hk
    rw [hLd] at ws wL w0
    simp only [Nat.add_zero] at w0
    rw [show y + L + L = (pushL C y).length - 1 from by omega] at wL
    rw [hn] at wL
    rw [ws, wL, w0]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · have hA : AncR C 0 y (C.length - 1) := AncR_zero_of H.hyz
      have d0 := H.d0
      rw [if_pos (show (0 : Nat) < 2 ∧ (L = 0 ∨ AncR C 0 y (C.length - 1)) from
          ⟨by omega, Or.inr hA⟩),
        if_pos (show (0 : Nat) < 2 ∧ (True ∨ AncR C 0 y y) from ⟨by omega, Or.inl trivial⟩),
        Nat.add_sub_add_right]
      have hiff : (s = 0 ∨ AncR (pushL C y) 0 (y + L) (y + L + s)) ↔ (s = 0 ∨ AncR C 0 y (y + s)) := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · simp [h0]
        · have := H.anc0 (u1 := 0) (u2 := s) h0 (by omega)
          rw [hLd] at this
          simp only [Nat.add_zero] at this
          rw [this]
      by_cases hc : s = 0 ∨ AncR C 0 y (y + s)
      · have c1 : (0 : Nat) < 2 ∧ (s = 0 ∨ AncR C 0 y (y + s)) := ⟨by omega, hc⟩
        have c2 : (0 : Nat) < 2 ∧ (s = 0 ∨ AncR (pushL C y) 0 (y + L) (y + L + s)) :=
          ⟨by omega, hiff.mpr hc⟩
        simp only [if_pos c1, if_pos c2]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have c1 : ¬ ((0 : Nat) < 2 ∧ (s = 0 ∨ AncR C 0 y (y + s))) := fun h => hc h.2
        have c2 : ¬ ((0 : Nat) < 2 ∧ (s = 0 ∨ AncR (pushL C y) 0 (y + L) (y + L + s))) :=
          fun h => hc (hiff.mp h.2)
        simp only [if_neg c1, if_neg c2]
    · have hA := H.hyz
      have d1 := H.d1
      rw [if_pos (show (1 : Nat) < 2 ∧ (L = 0 ∨ AncR C 1 y (C.length - 1)) from
          ⟨by omega, Or.inr hA⟩),
        if_pos (show (1 : Nat) < 2 ∧ (True ∨ AncR C 1 y y) from ⟨by omega, Or.inl trivial⟩),
        Nat.add_sub_add_right]
      have hiff : (s = 0 ∨ AncR (pushL C y) 1 (y + L) (y + L + s)) ↔ (s = 0 ∨ AncR C 1 y (y + s)) := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · simp [h0]
        · have := H.anc1_root (u := s) h0 (by omega)
          rw [hLd] at this
          rw [this]
      by_cases hc : s = 0 ∨ AncR C 1 y (y + s)
      · have c1 : (1 : Nat) < 2 ∧ (s = 0 ∨ AncR C 1 y (y + s)) := ⟨by omega, hc⟩
        have c2 : (1 : Nat) < 2 ∧ (s = 0 ∨ AncR (pushL C y) 1 (y + L) (y + L + s)) :=
          ⟨by omega, hiff.mpr hc⟩
        simp only [if_pos c1, if_pos c2]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have c1 : ¬ ((1 : Nat) < 2 ∧ (s = 0 ∨ AncR C 1 y (y + s))) := fun h => hc h.2
        have c2 : ¬ ((1 : Nat) < 2 ∧ (s = 0 ∨ AncR (pushL C y) 1 (y + L) (y + L + s))) :=
          fun h => hc (hiff.mp h.2)
        simp only [if_neg c1, if_neg c2]
    · simp only [lt_self_iff_false, false_and, ↓reduceIte, Nat.add_zero]

/-- **`pushL C y` has `Low2`.** -/
theorem PushHyp.low2 (hL2 : Low2 (expandRL 3 1 C)) : Low2 (pushL C y) := by
  have hL := H.yl
  have hn : y + (C.length - 1 - y) = C.length - 1 := by omega
  have hPlen := pushL_length H.hb
  intro i hi
  rcases Nat.lt_or_ge i (y + (C.length - 1 - y) + (C.length - 1 - y)) with h | h
  · rw [pushL_get_low H.hb h] at hi ⊢
    exact hL2 i hi
  · rcases Nat.eq_or_lt_of_le h with he | hgt
    · rw [← he] at hi
      have e := H.w1_eq (u := C.length - 1 - y) le_rfl (Or.inr (by rw [hn]; exact H.hyz))
      have ez : C[y + (C.length - 1 - y)]! = C[C.length - 1]! := by rw [hn]
      rw [ez] at e
      rw [e] at hi
      have := H.d1
      omega
    · rw [getElem!_neg _ i (by omega)]
      rfl

/-- **`pushL C y` has `R1`.** -/
theorem PushHyp.r1 (hC : SReach C) : R1 (pushL C y) := by
  have hL := H.yl
  obtain ⟨L, hLd⟩ : ∃ L, C.length - 1 - y = L := ⟨_, rfl⟩
  have hn : y + L = C.length - 1 := by omega
  have hPlen := pushL_length H.hb
  rw [hLd] at hPlen
  have hR1D : R1 (expandRL 3 1 C) := r1_of_sReach (hC.step 1)
  have hR1C : R1 C := r1_of_sReach hC
  have ez : C[y + L]! = C[C.length - 1]! := by rw [hn]
  have w0 : ∀ u, u ≤ L → ((pushL C y)[y + L + u]!)[0]! = (C[y + u]!)[0]! +
      ((C[C.length - 1]!)[0]! - (C[y]!)[0]!) := by
    intro u hu
    have := H.w0 (u := u) (by omega)
    rwa [hLd] at this
  intro p v hp
  have hvl := ParR_lt_len hp
  have hpv := ParR_lt hp
  rcases Nat.lt_or_ge v (y + L + L) with h | h
  · have hagree : ∀ m k', m ≤ v → k' ≤ 0 →
        ((pushL C y)[m]!)[k']! = ((expandRL 3 1 C)[m]!)[k']! := by
      intro m k' hm _
      rw [pushL_get_low H.hb (by omega)]
    have hpD := (ParR_congr_upto _ _ 0 v hagree p).mp hp
    rw [pushL_get_low H.hb (by omega), pushL_get_low H.hb (by omega)]
    exact hR1D p v hpD
  · have hv : v = y + L + L := by omega
    subst hv
    have d0 := H.d0
    have eL := w0 L le_rfl
    rw [ez] at eL
    have e00 := w0 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e00
    have hpL : y + L ≤ p := by
      by_contra hc
      have := hp.2.2 (y + L) (by omega) (by omega)
      rw [eL, e00] at this
      omega
    obtain ⟨u, rfl⟩ : ∃ u, p = y + L + u := ⟨p - (y + L), by omega⟩
    have hPC : ParR C 0 (y + u) (C.length - 1) := by
      refine ⟨by omega, ?_, fun j' a b => ?_⟩
      · have := hp.2.1
        rw [eL, w0 u (by omega)] at this
        omega
      · obtain ⟨u', rfl⟩ : ∃ u', j' = y + u' := ⟨j' - y, by omega⟩
        have := hp.2.2 (y + L + u') (by omega) (by omega)
        rw [eL, w0 u' (by omega)] at this
        omega
    have hr := hR1C _ _ hPC
    have e1L := H.w1_eq (u := C.length - 1 - y) le_rfl (Or.inr (by rw [hLd, hn]; exact H.hyz))
    rw [hLd, ez] at e1L
    have hc : u = 0 ∨ AncR C 1 y (y + u) := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (H.desc_of_anc0 h0 (by omega) (Relation.TransGen.single hPC))
    have e1u := H.w1_eq (u := u) (by omega) hc
    rw [hLd] at e1u
    rw [e1L, e1u]
    omega

/-- **`pushL C y` is not in the shape `RaisedPar`**: its row-`2` parent `y + L`
has row-`1` entry `z₁ ≥ 2`. -/
theorem PushHyp.not_rp (hyR : Rz C y) : ¬ RaisedPar (pushL C y) := by
  rintro ⟨y', hy'p, hy'R⟩
  have e := ParR_unique hy'p H.par2
  subst e
  have h1 := hy'R.2.1
  have e0 := H.w1_eq (u := 0) (by omega) (Or.inl rfl)
  simp only [Nat.add_zero] at e0
  rw [e0] at h1
  have := H.d1
  have := hyR.2.1
  omega

end Hyp

theorem pushL_valid (hv : Valid 2 C) : Valid 2 (pushL C y) := by
  intro v hv'
  rcases List.mem_append.mp hv' with h' | h'
  · exact valid_expandRL hv 1 v h'
  · rw [List.mem_singleton] at h'
    rw [h']; rfl

end Push

/-- **`t3n (C[N + 1]) = (t3n (pushL C y))[N]`** when the row-`2` parent `y` of
the last column is raisable. -/
theorem t3n_expand_eq_push {C : List (List Nat)} {y : Nat} (hC : SReach C)
    (hyp : ParR C 2 y (C.length - 1)) (hyR : Rz C y) (N : Nat) :
    t3n (expandRL 3 (N + 1) C) = expandRL 3 N (t3n (pushL C y)) := by
  have H := pushHyp_of hyp
  have hv := hC.valid
  rw [expandRL_t3n (pushL_valid hv) (H.low2 (low2_of_sReach (hC.step 1))) (H.r1 hC)
    (H.not_rp hyR) N, H.expand hv N]

/-! ### The reduction -/

/-- **Open.**  The pushed matrix of the shape `RaisedPar` with the raisable
parent before the column `n - 2` is in the trio fragment after `t3n`. -/
def T3nPushStd : Prop :=
  ∀ C y, SReach C → ParR C 2 y (C.length - 1) → Rz C y → ¬ Rz C (C.length - 2) →
    TrioStdL (t3n C) → TrioStdL (t3n (pushL C y))

/-- **`T3nPushStd` gives `T3nInnerStd`.** -/
theorem t3nInnerStd_of_push (h : T3nPushStd) : T3nInnerStd := by
  intro C hC hR hy hS N
  obtain ⟨y, hyp, hyR⟩ := hR
  rw [t3n_expand_eq_push hC hyp hyR N]
  exact TrioStdL.step N (h C y hC hyp hyR hy hS)

/-- **`T3nPushStd` gives `T3nRankDescRPInner`**, the open rank statement of
`ThreeRowUpperNCLast.lean`. -/
theorem t3nRankDescRPInner_of_push (h : T3nPushStd) : T3nRankDescRPInner :=
  t3nRankDescRPInner_of_innerStd (t3nInnerStd_of_push h)

/-- **The upper bound at `n = 2` under `T3nPushStd`**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)` have
the same rank. -/
theorem rkL_cgen_two_four_eq_of_push (h : T3nPushStd) :
    rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_innerStd (t3nInnerStd_of_push h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.AncR1_iff
#print axioms Googology.Trans.DBMS.PushHyp.expand
#print axioms Googology.Trans.DBMS.t3n_expand_eq_push
#print axioms Googology.Trans.DBMS.t3nInnerStd_of_push
#print axioms Googology.Trans.DBMS.t3nRankDescRPInner_of_push
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_push
