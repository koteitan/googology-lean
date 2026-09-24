import Googology.Trans.DBMS.ThreeRowUpperRPPush

/-!
# `T3nPushStd`, stated inside the trio fragment

`ThreeRowUpperRPPush.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `T3nPushStd`: for a reached `C` whose
last column `z` has a raisable row-`2` parent `y` (`y < n - 2`, `n` columns),
if `t3n C` is in the trio fragment then so is `t3n (pushL C y)`.  That
statement mixes the two systems: `pushL` is built from the DBMS matrix `C`.
This file writes `t3n (pushL C y)` as a map of `S = t3n C` alone, so that the
open statement is about the trio fragment only.

**The push of a trio matrix** (`pushS S y`).  Let `S` have `n` columns, last
column `z`, and let `y` be a row-`1` ancestor of `z`.  With `Δ = z - S[y]` in
rows `0` and `1`,

    pushS S y = S[0 .. n-2] ++ (z₀, z₁, 0) ++ (S[y+1 .. n-1] shifted by Δ),

where column `y + u` is shifted in row `k ≤ 1` exactly when `y` is a row-`k`
ancestor of it.  So the last column `z` is replaced by a copy of the columns
`y ⋯ n-1`, placed at `z`, whose first column gets the row-`2` entry `0`.

**What is proved.**

* `t3n_pushL_eq`: for three-row `C` with a raisable row-`2` parent `y` of the
  last column and column `n - 2` not raisable,
  `t3n (pushL C y) = pushS (t3n C) y`.  Raising commutes with the copy: a
  copied column is raisable exactly when its source is (the copy of a column
  `(a,1,0)` is not shifted in row `1`, since `y` itself has row-`1` entry `1`),
  and the copy `(z₀, z₁, 0)` of `y` has row-`1` entry `z₁ ≥ 2`.
* `pushHypS_of`: in `S = t3n C` the last column has a row-`2` parent `x < y`
  (the row-`1` parent of `y`), and `y` is a row-`1` ancestor of the last column.
* `t3nPushStd_of_trioPush`: `TrioPushStd → T3nPushStd`, and so
  `rkL_cgen_two_four_eq_of_trioPush`.

**Open** (`TrioPushStd`): for `S` in the trio fragment whose last column has
a row-`2` parent `x` (so `m₀ = 2` and `x` is the bad root), and every row-`1`
ancestor `y` of the last column with `x < y`, `pushS S y` is in the trio
fragment.

Numerically (scripts outside the library; standardness decided by greedy
descent from `S`, which is complete for `pushS S y < S` by `trio_cofinal`):
breadth-first from `trioGen v`, `v ≤ 5`, `N ≤ 3` at each step, depth `≤ 14`,
at most `22` columns: `1954010` matrices, `48438` pairs `(S, y)`, no exception,
greedy paths from `S` of at most `32` steps.  On the shape of `T3nPushStd`
(`178` reached matrices, breadth-first from `lift 3 (trioGen v)`, depth `≤ 10`)
`t3n (pushL C y) = pushS (t3n C) y` was also checked before it was proved.  The paths have no common shape: from
`S[1]` to `pushS S y` (smallest `y`) they take `0` to `15` steps, and from
`pushS S y` to `pushS S y'` (next `y'` on the chain) `0` to `15` steps.  Without the condition `x < y` the
statement is false: at `y = x` (and at `y < x`) `pushS S y` is often not
standard, e.g. `S = (0,0,0)(1,1,1)(2,2,1)(3,3,1)(4,4,0)(5,5,1)(6,6,1)(7,7,1)(8,7,0)(9,8,1)`,
`y = x = 8`.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL)
open Classical

/-! ### The push of a trio matrix -/

/-- **The push of `S` at `y`**: the last column `z` is replaced by the copy of
the columns `y ⋯ n - 1` placed at `z` (shifted by `z - S[y]` in the rows where
`y` is an ancestor), the copy of `y` getting row-`2` entry `0`. -/
def pushS (S : List (List Nat)) (y : Nat) : List (List Nat) :=
  S.dropLast ++ [[(S[S.length - 1]!)[0]!, (S[S.length - 1]!)[1]!, 0]] ++
    (List.range (S.length - 1 - y)).map (fun u =>
      [(S[y + u + 1]!)[0]! +
          (if ancAtR S 0 y (y + u + 1) then (S[S.length - 1]!)[0]! - (S[y]!)[0]! else 0),
        (S[y + u + 1]!)[1]! +
          (if ancAtR S 1 y (y + u + 1) then (S[S.length - 1]!)[1]! - (S[y]!)[1]! else 0),
        (S[y + u + 1]!)[2]!])

section PushS

variable {S : List (List Nat)} {y : Nat}

theorem pushS_length (hS : S ≠ []) :
    (pushS S y).length = S.length + (S.length - 1 - y) := by
  have : 0 < S.length := List.length_pos_iff.mpr hS
  simp [pushS]
  omega

theorem pushS_get_lt {i : Nat} (hi : i < S.length - 1) : (pushS S y)[i]! = S[i]! := by
  rw [pushS, getElem!_append_left _ _ (by simp; omega),
    getElem!_append_left _ _ (by simp; omega), getElem!_dropLast', if_pos hi]

theorem pushS_get_root (hS : S ≠ []) :
    (pushS S y)[S.length - 1]! =
      [(S[S.length - 1]!)[0]!, (S[S.length - 1]!)[1]!, 0] := by
  have hl : S.dropLast.length = S.length - 1 := List.length_dropLast
  have e := getElem!_append_right S.dropLast
    [[(S[S.length - 1]!)[0]!, (S[S.length - 1]!)[1]!, 0]] 0
  rw [Nat.add_zero, hl] at e
  have : 0 < S.length := List.length_pos_iff.mpr hS
  rw [pushS, getElem!_append_left _ _
    (by rw [List.length_append, hl, List.length_singleton]; omega), e]
  rfl

theorem pushS_get_win (hS : S ≠ []) {u : Nat} (hu : u < S.length - 1 - y) :
    (pushS S y)[S.length + u]! =
      [(S[y + u + 1]!)[0]! +
          (if ancAtR S 0 y (y + u + 1) then (S[S.length - 1]!)[0]! - (S[y]!)[0]! else 0),
        (S[y + u + 1]!)[1]! +
          (if ancAtR S 1 y (y + u + 1) then (S[S.length - 1]!)[1]! - (S[y]!)[1]! else 0),
        (S[y + u + 1]!)[2]!] := by
  have : 0 < S.length := List.length_pos_iff.mpr hS
  have hl : (S.dropLast ++ [[(S[S.length - 1]!)[0]!, (S[S.length - 1]!)[1]!, 0]]).length =
      S.length := by simp; omega
  have e := getElem!_append_right
    (S.dropLast ++ [[(S[S.length - 1]!)[0]!, (S[S.length - 1]!)[1]!, 0]])
    ((List.range (S.length - 1 - y)).map (fun u =>
      [(S[y + u + 1]!)[0]! +
          (if ancAtR S 0 y (y + u + 1) then (S[S.length - 1]!)[0]! - (S[y]!)[0]! else 0),
        (S[y + u + 1]!)[1]! +
          (if ancAtR S 1 y (y + u + 1) then (S[S.length - 1]!)[1]! - (S[y]!)[1]! else 0),
        (S[y + u + 1]!)[2]!])) u
  rw [hl, getElem!_map_range _ _ hu] at e
  rw [pushS, e]

end PushS

/-! ### `t3n (pushL C y) = pushS (t3n C) y` -/

section Main

variable {C : List (List Nat)} {y : Nat}

/-- The columns of `pushL C y` before `n - 1` are those of `C`. -/
theorem pushL_get_lt (H : PushHyp C y) (hv : Valid 2 C) {i : Nat} (hi : i < C.length - 1) :
    (pushL C y)[i]! = C[i]! := by
  have hyl := H.yl
  have hvP := pushL_valid (y := y) hv
  have hlen := pushL_length H.hb
  apply col_ext3 (hvP _ (getElem!_mem _ i (by omega))) (hv _ (getElem!_mem _ i (by omega)))
  intro k hk
  rw [pushL_get_low H.hb (by omega), expandRL_get_low H.hb 1 hi hk]

/-- **Raising commutes with the push.** -/
theorem t3n_pushL_eq (hv : Valid 2 C) (hyp : ParR C 2 y (C.length - 1)) (hyR : Rz C y)
    (hn2 : ¬ Rz C (C.length - 2)) : t3n (pushL C y) = pushS (t3n C) y := by
  have H := pushHyp_of hyp
  have hyl := H.yl
  obtain ⟨L, hLd⟩ : ∃ L, C.length - 1 - y = L := ⟨_, rfl⟩
  have hn : y + L = C.length - 1 := by omega
  have hPlen := pushL_length H.hb
  rw [hLd] at hPlen
  have hCne : C ≠ [] := by
    intro h; rw [h] at hyl; simp at hyl
  have hSne : t3n C ≠ [] := t3n_ne_nil hCne
  have hSlen := pushS_length (y := y) hSne
  rw [t3n_length] at hSlen
  have hvP := pushL_valid (y := y) hv
  have hy1 : (C[y]!)[1]! = 1 := hyR.2.1
  have hy2 : (C[y]!)[2]! = 0 := hyR.2.2.1
  have d0 := H.d0
  have d1 := H.d1
  -- the window of `pushL C y`
  have W0 : ∀ u, u ≤ L → ((pushL C y)[y + L + u]!)[0]! =
      (C[y + u]!)[0]! + ((C[C.length - 1]!)[0]! - (C[y]!)[0]!) := fun u hu => by
    have := H.w0 (u := u) (by omega); rwa [hLd] at this
  have W1 : ∀ u, u ≤ L → ((pushL C y)[y + L + u]!)[1]! = (C[y + u]!)[1]! +
      (if u = 0 ∨ AncR C 1 y (y + u) then (C[C.length - 1]!)[1]! - (C[y]!)[1]! else 0) :=
    fun u hu => by have := H.w1 (u := u) (by omega); rwa [hLd] at this
  have W2 : ∀ u, u ≤ L → ((pushL C y)[y + L + u]!)[2]! = (C[y + u]!)[2]! := fun u hu => by
    have := H.w2 (u := u) (by omega); rwa [hLd] at this
  -- the row-`1` shift is `0` on columns with row-`1` entry `≤ 2` after `y`
  have A0 : ∀ u, 0 < u → u ≤ L → AncR C 0 y (y + u) := by
    intro u hu0 huL
    rcases Nat.lt_or_ge (y + u) (C.length - 1) with h | h
    · exact AncR_zero_between (AncR_zero_of H.hyz) _ (by omega) h
    · rw [show y + u = C.length - 1 from by omega]; exact AncR_zero_of H.hyz
  apply ext_getElem!' (by rw [t3n_length, hPlen, hSlen]; omega)
  intro i hi
  rw [t3n_length, hPlen] at hi
  rcases Nat.lt_or_ge i (C.length - 1) with hi1 | hi1
  · -- before the copy: the columns of `C`
    rw [pushS_get_lt (by rw [t3n_length]; exact hi1), t3n_get (by rw [hPlen]; omega),
      t3n_get (by omega), pushL_get_lt H hv hi1]
    have hRz : Rz (pushL C y) i ↔ Rz C i := by
      rcases Nat.lt_or_ge (i + 1) (C.length - 1) with h | h
      · unfold Rz
        rw [pushL_get_lt H hv hi1, pushL_get_lt H hv h]
        constructor
        · rintro ⟨_, r⟩; exact ⟨by omega, r⟩
        · rintro ⟨_, r⟩; exact ⟨by rw [hPlen]; omega, r⟩
      · have hi2 : i = C.length - 2 := by omega
        constructor
        · intro h'
          have h2 := h'.2.2.2.2.2
          have e := W2 0 (by omega)
          rw [Nat.add_zero, Nat.add_zero, hn, hy2] at e
          rw [show i + 1 = C.length - 1 from by omega, e] at h2
          omega
        · intro h'; exact absurd (hi2 ▸ h') hn2
    by_cases h : Rz C i
    · rw [if_pos (hRz.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hRz.mp h')), if_neg h]
  rcases Nat.eq_or_lt_of_le hi1 with hi1 | hi1
  · -- the copy `(z₀, z₁, 0)` of `y`
    subst hi1
    have e0 := W0 0 (by omega)
    have e1 := W1 0 (by omega)
    have e2 := W2 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero, hn] at e0 e1 e2
    rw [if_pos (Or.inl rfl)] at e1
    have hnR : ¬ Rz (pushL C y) (C.length - 1) := fun h => by
      have := h.2.1; rw [e1] at this; omega
    rw [t3n_get (by rw [hPlen]; omega), if_neg hnR,
      show C.length - 1 = (t3n C).length - 1 from by rw [t3n_length], pushS_get_root hSne,
      t3n_length, t3n_entry_low C _ 0 (by omega), t3n_entry_low C _ 1 (by omega)]
    apply col_ext3 (hvP _ (getElem!_mem _ _ (by rw [hPlen]; omega))) rfl
    intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [e0]; show _ = (C[C.length - 1]!)[0]!; omega
    · rw [e1]; show _ = (C[C.length - 1]!)[1]!; omega
    · rw [e2, hy2]; rfl
  · -- the copy of the column `y + v + 1`
    obtain ⟨v, rfl⟩ : ∃ v, i = C.length + v := ⟨i - C.length, by omega⟩
    have hv1 : v + 1 ≤ L := by omega
    have ew := pushS_get_win (S := t3n C) (y := y) hSne (u := v) (by rw [t3n_length]; omega)
    rw [t3n_length] at ew
    rw [ew, show C.length + v = y + L + (v + 1) from by omega]
    simp only [t3n_entry_low C _ 0 (by omega), t3n_entry_low C _ 1 (by omega)]
    have hA0 : ancAtR (t3n C) 0 y (y + v + 1) = true :=
      (ancAtR_iff _ _ _ _).mpr ((AncR_t3n_low C 0 (by omega) _ _).mpr
        (A0 (v + 1) (by omega) hv1))
    rw [if_pos hA0]
    have hA1 : ancAtR (t3n C) 1 y (y + v + 1) = true ↔ AncR C 1 y (y + v + 1) := by
      rw [ancAtR_iff, AncR_t3n_low C 1 (by omega)]
    have e0 := W0 (v + 1) hv1
    have e1 := W1 (v + 1) hv1
    have e2 := W2 (v + 1) hv1
    rw [show y + (v + 1) = y + v + 1 from by omega] at e0 e1 e2
    have hne0 : ¬ (v + 1 = 0) := by omega
    -- a copied column is raisable exactly when its source is
    have hRz : Rz (pushL C y) (y + L + (v + 1)) ↔ Rz C (y + v + 1) := by
      constructor
      · intro h
        have hv2 : v + 2 ≤ L := by have := h.1; rw [hPlen] at this; omega
        have f0 := W0 (v + 2) hv2
        have f1 := W1 (v + 2) hv2
        have f2 := W2 (v + 2) hv2
        rw [show y + (v + 2) = y + v + 1 + 1 from by omega] at f0 f1 f2
        rw [show y + L + (v + 2) = y + L + (v + 1) + 1 from by omega] at f0 f1 f2
        obtain ⟨_, r1, r2, r3, r4, r5⟩ := h
        rw [e1] at r1
        rw [e2] at r2
        rw [f0, e0] at r3
        rw [f1] at r4
        rw [f2] at r5
        have c1 : ¬ AncR C 1 y (y + v + 1) := fun ha => by
          have := AncR_entry_lt ha
          rw [if_pos (Or.inr ha)] at r1
          omega
        rw [if_neg (fun hh => hh.elim hne0 c1)] at r1
        have c2 : ¬ AncR C 1 y (y + v + 1 + 1) := fun ha => by
          have := AncR_entry_lt ha
          rw [if_pos (Or.inr ha)] at r4
          omega
        rw [if_neg (fun hh => hh.elim (fun e => by omega) c2)] at r4
        exact ⟨by omega, by omega, r2, by omega, by omega, r5⟩
      · intro h
        have hv2 : v + 2 ≤ L := by have := h.1; omega
        have f0 := W0 (v + 2) hv2
        have f1 := W1 (v + 2) hv2
        have f2 := W2 (v + 2) hv2
        rw [show y + (v + 2) = y + v + 1 + 1 from by omega] at f0 f1 f2
        rw [show y + L + (v + 2) = y + L + (v + 1) + 1 from by omega] at f0 f1 f2
        have c1 : ¬ AncR C 1 y (y + v + 1) := fun ha => by
          have := AncR_entry_lt ha; rw [h.2.1] at this; omega
        have c2 : ¬ AncR C 1 y (y + v + 1 + 1) := fun ha => by
          rcases (AncR_of_ParR_iff (ParR1_of_Rz h) y).mp ha with e | e
          · omega
          · exact c1 e
        refine ⟨by rw [hPlen]; omega, ?_, ?_, ?_, ?_, ?_⟩
        · rw [e1, if_neg (fun hh => hh.elim hne0 c1), h.2.1]
        · rw [e2, h.2.2.1]
        · rw [f0, e0, h.2.2.2.1]; omega
        · rw [f1, if_neg (fun hh => hh.elim (fun e => by omega) c2), h.2.2.2.2.1]
        · rw [f2, h.2.2.2.2.2]
    rw [t3n_get (by rw [hPlen]; omega), t3n_entry_two]
    by_cases h : Rz C (y + v + 1)
    · have c1 : ¬ AncR C 1 y (y + v + 1) := fun ha => by
        have := AncR_entry_lt ha; rw [h.2.1] at this; omega
      rw [if_pos (hRz.mpr h), if_pos h, if_neg (fun hh => c1 (hA1.mp hh)), e0, h.2.1]
    · rw [if_neg (fun h' => h (hRz.mp h')), if_neg h]
      apply col_ext3 (hvP _ (getElem!_mem _ _ (by rw [hPlen]; omega))) rfl
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
      · rw [e0]; rfl
      · rw [e1]
        by_cases ha : AncR C 1 y (y + v + 1)
        · rw [if_pos (Or.inr ha), if_pos (hA1.mpr ha)]; rfl
        · rw [if_neg (fun hh => hh.elim hne0 ha), if_neg (fun hh => ha (hA1.mp hh))]; rfl
      · rw [e2]; rfl

end Main

/-! ### The hypotheses of the push, in `t3n C` -/

/-- Every row-`2` entry is at most `1`. -/
def Row2Le1 (C : List (List Nat)) : Prop := ∀ i : Nat, (C[i]!)[2]! ≤ 1

theorem row2Le1_expandRL {l : List (List Nat)} (h : ∀ j, j + 1 < l.length → (l[j]!)[2]! ≤ 1)
    (N : Nat) : Row2Le1 (expandRL 3 N l) := by
  intro i
  rcases expandRL_row2_from N l i with e | ⟨j, hj, e⟩
  · omega
  · rw [e]; exact h j hj

theorem row2Le1_of_sReach {C : List (List Nat)} (hC : SReach C) : Row2Le1 C := by
  induction hC with
  | gen v =>
    refine row2Le1_expandRL (fun j hj => ?_) v
    have hj' : j < 3 := by simp [cgen] at hj; omega
    have : ∀ j, j < 3 → ((cgen 2 4)[j]!)[2]! ≤ 1 := by decide
    exact this j hj'
  | step N _ ih => exact row2Le1_expandRL (fun j _ => ih j) N

/-- **In `S = t3n C` the last column has a row-`2` parent `x < y`** (the
row-`1` parent of `y`), and `y` is a row-`1` ancestor of the last column. -/
theorem pushHypS_of {C : List (List Nat)} {y : Nat} (hC : SReach C)
    (hyp : ParR C 2 y (C.length - 1)) (hyR : Rz C y) :
    ∃ x, ParR (t3n C) 2 x (C.length - 1) ∧ x < y ∧ AncR (t3n C) 1 y (C.length - 1) := by
  have H := pushHyp_of hyp
  have hyl := H.yl
  have hy1 : (C[y]!)[1]! = 1 := hyR.2.1
  have hy2 : (C[y]!)[2]! = 0 := hyR.2.2.1
  obtain ⟨x, hx⟩ := exists_ParR1_of_sReach hC (j := y) (by omega) (by omega)
  have hxy : x < y := ParR_lt hx
  have hx1 : (C[x]!)[1]! = 0 := by
    have := AncR_entry_lt (Relation.TransGen.single hx : AncR C 1 x y); omega
  have hx2 : (C[x]!)[2]! = 0 := low2_of_sReach hC x (by omega)
  have hxR : ¬ Rz C x := fun h => by have := h.2.1; omega
  have hlastR : ¬ Rz C (C.length - 1) := not_Rz_last C
  have hz2 : (C[C.length - 1]!)[2]! ≤ 1 := row2Le1_of_sReach hC _
  have hlt2 := H.hlt2
  have hAx : AncR C 1 x (C.length - 1) := Relation.TransGen.head hx H.hyz
  refine ⟨x, (ParR_two_iff' _ _ _).mpr ⟨by omega, (AncR_t3n_low C 1 le_rfl _ _).mpr hAx, ?_,
    fun j' a b c => ?_⟩, hxy, (AncR_t3n_low C 1 le_rfl _ _).mpr H.hyz⟩
  · rw [t3n_entry_two, if_neg hxR, t3n_entry_two, if_neg hlastR]
    omega
  · have c' : AncR C 1 j' (C.length - 1) := (AncR_t3n_low C 1 le_rfl _ _).mp c
    rw [t3n_entry_two C (C.length - 1), if_neg hlastR]
    rcases Nat.lt_trichotomy j' y with h | rfl | h
    · exfalso
      have hj'y : AncR C 1 j' y := AncR1_of_between c' (AncR_zero_of H.hyz) h
      rcases (AncR_of_ParR_iff hx j').mp hj'y with e | e
      · omega
      · have := transGen_lt (fun _ _ h => ParR_lt h) e; omega
    · rw [t3n_entry_two, if_pos hyR]; exact hz2
    · exact le_trans (H.hmid2 j' h b c') (t3n_entry_two_ge C j')

/-! ### The reduction -/

/-- **Open.**  The push of a member of the trio fragment at a row-`1` ancestor
`y` of the last column after the bad root `x` (with `m₀ = 2`) is in the trio
fragment. -/
def TrioPushStd : Prop :=
  ∀ S x y, TrioStdL S → ParR S 2 x (S.length - 1) → x < y → AncR S 1 y (S.length - 1) →
    TrioStdL (pushS S y)

/-- **`TrioPushStd` gives `T3nPushStd`.** -/
theorem t3nPushStd_of_trioPush (h : TrioPushStd) : T3nPushStd := by
  intro C y hC hyp hyR hn2 hS
  obtain ⟨x, hx, hxy, hA⟩ := pushHypS_of hC hyp hyR
  rw [t3n_pushL_eq hC.valid hyp hyR hn2]
  exact h (t3n C) x y hS (by rwa [t3n_length]) hxy (by rwa [t3n_length])

/-- **The upper bound at `n = 2` under `TrioPushStd`**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)` have
the same rank. -/
theorem rkL_cgen_two_four_eq_of_trioPush (h : TrioPushStd) :
    rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_push (t3nPushStd_of_trioPush h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.t3n_pushL_eq
#print axioms Googology.Trans.DBMS.pushHypS_of
#print axioms Googology.Trans.DBMS.t3nPushStd_of_trioPush
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_trioPush
