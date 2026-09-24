import Googology.Trans.DBMS.ThreeRowUpperNC

/-!
# `t3n` commutes with expansion, outside one shape

`ThreeRowUpperNC.lean` defines the nested raise `t3n` (every column `(a,1,0)`
followed by `(a+1,2,1)` becomes `(a,1,1)`) and reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `T3nRankDesc`.  This file proves

    (t3n C)[N] = t3n (C[N])                                  (expandRL_t3n)

for every three-row `C` with

* `Low2 C`: a column with row-`1` entry `≤ 1` has row-`2` entry `0`;
* `R1 C`: a column's row-`1` entry is at most one more than its row-`0` parent's;
* `¬ RaisedPar C`: the row-`2` parent of the last column is not raisable.

The first two hold on every matrix reached from `(cgen 2 4)[v]`
(`ThreeRowUpperNCInv.lean`).  The third is the one shape left open.

**How.**  Raising changes only row `2`, so the parents in rows `0` and `1` stay.
The row-`2` parent of the last column stays too unless it is raised, so `m₀`
and the bad root stay (`badRootR_t3n`).  The expansion never adds to row `2`
(`m₀ ≤ 2`), so `(t3n C)[N]` is `C[N]` with the row-`2` entry of each column
taken from its source column in `t3n C`.  What is left is that a column of
`C[N]` is raisable exactly when its source column in `C` is
(`Rz_expand_iff_*`):

* inside one copy of the bad part, a raisable pair `(a,1,0)(a+1,2,1)` gets the
  same increments on both columns, and none in row `1`: a row-`1` increment
  would make the bad root a column `(b,0,0)` that is the row-`2` parent of the
  last column, and `R1` with `Low2` rule that out (`not_ParR_two_of_row1_zero`);
  conversely a raisable pair of `C[N]` comes from a raisable pair of `C`,
  because every column between the bad root and the last column is a row-`0`
  descendant of the bad root (`AncR_zero_between`);
* across the seam between two copies no raisable pair arises (`Rz_seam`).
-/

namespace Googology.Trans.DBMS

open Googology.Trans.BMS
open Classical

/-! ### The invariants and the open shape -/

/-- A column with row-`1` entry `≤ 1` has row-`2` entry `0`. -/
def Low2 (C : List (List Nat)) : Prop := ∀ i : Nat, (C[i]!)[1]! ≤ 1 → (C[i]!)[2]! = 0

/-- A column's row-`1` entry is at most one more than its row-`0` parent's. -/
def R1 (C : List (List Nat)) : Prop :=
  ∀ p v, ParR C 0 p v → (C[v]!)[1]! ≤ (C[p]!)[1]! + 1

/-- **The open shape**: the row-`2` parent of the last column is raisable. -/
def RaisedPar (C : List (List Nat)) : Prop :=
  ∃ y, ParR C 2 y (C.length - 1) ∧ Rz C y

/-! ### Parents -/

theorem ParR_unique {l : List (List Nat)} {k j j' i : Nat} (h : ParR l k j i)
    (h' : ParR l k j' i) : j = j' := by
  have a := (parAtR_eq_some l k i j).mpr h
  have b := (parAtR_eq_some l k i j').mpr h'
  rw [a] at b
  exact Option.some.inj b

theorem ParR_one_iff (l : List (List Nat)) (j i : Nat) : ParR l 1 j i ↔
    (j < i ∧ Relation.TransGen (ParR l 0) j i ∧ (l[j]!)[1]! < (l[i]!)[1]! ∧
      ∀ j', j < j' → j' < i → Relation.TransGen (ParR l 0) j' i → (l[i]!)[1]! ≤ (l[j']!)[1]!) :=
  Iff.rfl

theorem ParR_two_iff' (l : List (List Nat)) (j i : Nat) : ParR l 2 j i ↔
    (j < i ∧ Relation.TransGen (ParR l 1) j i ∧ (l[j]!)[2]! < (l[i]!)[2]! ∧
      ∀ j', j < j' → j' < i → Relation.TransGen (ParR l 1) j' i → (l[i]!)[2]! ≤ (l[j']!)[2]!) :=
  Iff.rfl

/-- The ancestors of a column are its parent and the parent's ancestors. -/
theorem AncR_of_ParR_iff {l : List (List Nat)} {k x y : Nat} (hp : ParR l k x y) (a : Nat) :
    AncR l k a y ↔ a = x ∨ AncR l k a x := by
  constructor
  · intro h
    obtain ⟨b, hr, hb⟩ := Relation.TransGen.tail'_iff.mp h
    have e := ParR_unique hb hp
    subst e
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hr with he | ht
    · exact Or.inl he.symm
    · exact Or.inr ht
  · rintro (rfl | h)
    · exact Relation.TransGen.single hp
    · exact Relation.TransGen.tail h hp

/-- The first step of a chain of ancestors. -/
theorem transGen_head_split {R : Nat → Nat → Prop} {a c : Nat} (h : Relation.TransGen R a c) :
    ∃ b, R a b ∧ (b = c ∨ Relation.TransGen R b c) := by
  obtain ⟨b, hab, hbc⟩ := Relation.TransGen.head'_iff.mp h
  exact ⟨b, hab, (Relation.reflTransGen_iff_eq_or_transGen.mp hbc).imp Eq.symm id⟩

theorem ParR0_of_Rz {C : List (List Nat)} {i : Nat} (h : Rz C i) : ParR C 0 i (i + 1) :=
  ⟨by omega, by rw [h.2.2.2.1]; omega, fun j' a b => by omega⟩

theorem ParR1_of_Rz {C : List (List Nat)} {i : Nat} (h : Rz C i) : ParR C 1 i (i + 1) :=
  (ParR_one_iff C i (i + 1)).mpr ⟨by omega, Relation.TransGen.single (ParR0_of_Rz h),
    by rw [h.2.1, h.2.2.2.2.1]; omega, fun j' a b _ => by omega⟩

/-- **A raisable column is the row-`2` parent of the next one.** -/
theorem ParR2_of_Rz {C : List (List Nat)} {i : Nat} (h : Rz C i) : ParR C 2 i (i + 1) :=
  (ParR_two_iff' C i (i + 1)).mpr ⟨by omega, Relation.TransGen.single (ParR1_of_Rz h),
    by rw [h.2.2.1, h.2.2.2.2.2]; omega, fun j' a b _ => by omega⟩

theorem raisedPar_of_Rz_last {C : List (List Nat)} (h : Rz C (C.length - 2)) : RaisedPar C := by
  have hl := h.1
  refine ⟨C.length - 2, ?_, h⟩
  have := ParR2_of_Rz h
  rwa [show C.length - 2 + 1 = C.length - 1 from by omega] at this

theorem not_Rz_last_two {C : List (List Nat)} (hnp : ¬ RaisedPar C) : ¬ Rz C (C.length - 2) :=
  fun h => hnp (raisedPar_of_Rz_last h)

/-- **A column `(b,0,·)` is never the row-`2` parent**, under `Low2` and `R1`.
The row-`1` child `u` of `b` towards the child has a positive row-`2` entry, so
row-`1` entry `≥ 2`; the row-`0` child `v` of `b` towards `u` has row-`1` entry
`≥ 2` as well, one more than `R1` allows. -/
theorem not_ParR_two_of_row1_zero {C : List (List Nat)} (hL : Low2 C) (h1 : R1 C) {p i : Nat}
    (hp : ParR C 2 p i) (h0 : (C[p]!)[1]! = 0) : False := by
  obtain ⟨hpi, hT1, hlt2, hall2⟩ := (ParR_two_iff' C p i).mp hp
  obtain ⟨u, hpu, hu⟩ := transGen_head_split hT1
  have hu2 : 1 ≤ (C[u]!)[2]! := by
    rcases hu with rfl | hu
    · omega
    · have := hall2 u (ParR_lt hpu) (transGen_lt (fun _ _ h => ParR_lt h) hu) hu
      omega
  have hu1 : 2 ≤ (C[u]!)[1]! := by
    by_contra hc
    have := hL u (by omega)
    omega
  obtain ⟨_, hT0, _, hall1⟩ := (ParR_one_iff C p u).mp hpu
  obtain ⟨v, hpv, hv⟩ := transGen_head_split hT0
  have hv1 : 2 ≤ (C[v]!)[1]! := by
    rcases hv with rfl | hv
    · exact hu1
    · have := hall1 v (ParR_lt hpv) (transGen_lt (fun _ _ h => ParR_lt h) hv) hv
      omega
  have := h1 p v hpv
  omega

/-! ### Row-`0` descendants are contiguous -/

theorem between_row0_gt {l : List (List Nat)} {p z : Nat} (h : AncR l 0 p z) :
    ∀ x, p < x → x < z → (l[p]!)[0]! < (l[x]!)[0]! := by
  induction h with
  | single hpz =>
    intro x a b
    have h1 := hpz.2.1
    have h2 := hpz.2.2 x a b
    omega
  | @tail w z hpw hwz ih =>
    intro x a b
    have hwlt := ParR_lt hwz
    have hpw0 := AncR_entry_lt (k := 0) hpw
    by_cases hxw : x < w
    · exact ih x a hxw
    · by_cases hxw' : x = w
      · subst hxw'; exact hpw0
      · have h1 := hwz.2.1
        have h2 := hwz.2.2 x (by omega) b
        omega

/-- **Everything between a row-`0` ancestor and its descendant descends from it.** -/
theorem AncR_zero_between {l : List (List Nat)} {p z : Nat} (h : AncR l 0 p z) :
    ∀ x, p < x → x < z → AncR l 0 p x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro a b
    have hx := between_row0_gt h x a b
    obtain ⟨w, hw⟩ := exists_ParR0 l (x - p) p x rfl a hx
    have hwp : p ≤ w := by
      by_contra hc
      have := hw.2.2 p (by omega) a
      omega
    rcases Nat.eq_or_lt_of_le hwp with rfl | hlt
    · exact Relation.TransGen.single hw
    · exact Relation.TransGen.tail (ih w (ParR_lt hw) hlt (by have := ParR_lt hw; omega)) hw

theorem AncR_zero_of_badRoot {l : List (List Nat)} {p : Nat} (hb : badRootR 3 l = some p)
    (hm : 0 < m0L 3 l) : AncR l 0 p (l.length - 1) := by
  have hpar := badRootR_ParR hb
  obtain ⟨m, hm'⟩ : ∃ m, m0L 3 l = m + 1 := ⟨m0L 3 l - 1, by omega⟩
  rw [hm'] at hpar
  exact AncR_zero_of (k := m) hpar.2.1

/-! ### `t3n` keeps `m₀` and the bad root -/

theorem ParR_two_t3n_of {C : List (List Nat)} {q i : Nat} (hq : ParR C 2 q i) (hqR : ¬ Rz C q)
    (hiR : ¬ Rz C i) : ParR (t3n C) 2 q i := by
  obtain ⟨a1, a2, a3, a4⟩ := (ParR_two_iff' C q i).mp hq
  refine (ParR_two_iff' _ q i).mpr ⟨a1, by rw [ParR_t3n_low_eq C 1 le_rfl]; exact a2, ?_, ?_⟩
  · rw [t3n_entry_two, if_neg hqR, t3n_entry_two, if_neg hiR]; exact a3
  · intro j' b c d
    rw [ParR_t3n_low_eq C 1 le_rfl] at d
    have := a4 j' b c d
    have := t3n_entry_two_ge C j'
    rw [t3n_entry_two C i, if_neg hiR]
    omega

theorem exists_ParR_two_of_t3n {C : List (List Nat)} {j i : Nat} (h : ParR (t3n C) 2 j i)
    (hiR : ¬ Rz C i) : ∃ q, ParR C 2 q i := by
  obtain ⟨_, a2, a3, _⟩ := (ParR_two_iff' _ j i).mp h
  rw [ParR_t3n_low_eq C 1 le_rfl] at a2
  have e := t3n_entry_two_ge C j
  rw [t3n_entry_two C i, if_neg hiR] at a3
  exact exists_ParR_succ C 1 _ j i rfl a2 (by show (C[j]!)[2]! < (C[i]!)[2]!; omega)

theorem not_Rz_last (C : List (List Nat)) : ¬ Rz C (C.length - 1) := fun h => by
  have := h.1; omega

theorem parAtR_t3n_last {C : List (List Nat)} (hnp : ¬ RaisedPar C) (k : Nat) (hk : k ≤ 2) :
    parAtR (t3n C) k (C.length - 1) = parAtR C k (C.length - 1) := by
  by_cases hk2 : k = 2
  · subst hk2
    apply Option.ext
    intro j
    rw [parAtR_eq_some, parAtR_eq_some]
    have hiR := not_Rz_last C
    constructor
    · intro h
      obtain ⟨q, hq⟩ := exists_ParR_two_of_t3n h hiR
      have hqR : ¬ Rz C q := fun hR => hnp ⟨q, hq, hR⟩
      rw [ParR_unique h (ParR_two_t3n_of hq hqR hiR)]
      exact hq
    · intro h
      exact ParR_two_t3n_of h (fun hR => hnp ⟨j, h, hR⟩) hiR
  · exact parAtR_congr' (fun j i => ParR_t3n_low C k (by omega) j i) _

theorem m0L_t3n {C : List (List Nat)} (hnp : ¬ RaisedPar C) : m0L 3 (t3n C) = m0L 3 C := by
  rw [m0L, m0L, t3n_length]
  exact findGreatest_congr (3 - 1) (fun k hk => by rw [parAtR_t3n_last hnp k (by omega)])

theorem badRootR_t3n {C : List (List Nat)} (hnp : ¬ RaisedPar C) :
    badRootR 3 (t3n C) = badRootR 3 C := by
  by_cases hC : C = []
  · subst hC; rfl
  · have hne : ¬ (t3n C).isEmpty = true := by
      simpa [List.isEmpty_iff] using t3n_ne_nil hC
    have hne' : ¬ C.isEmpty = true := by simpa [List.isEmpty_iff] using hC
    rw [badRootR, badRootR, if_neg hne, if_neg hne', m0L_t3n hnp, t3n_length]
    exact parAtR_t3n_last hnp _ (by have := m0L_lt (show 0 < 3 by norm_num) C; omega)

/-! ### The entries of an expansion -/

theorem expandRL_length_some {l : List (List Nat)} {p : Nat} (hb : badRootR 3 l = some p)
    (N : Nat) : (expandRL 3 N l).length = p + (N + 1) * (l.length - 1 - p) := by
  rw [expandRL, hb]
  simp

theorem expandRL_get_pre {l : List (List Nat)} {p : Nat} (hb : badRootR 3 l = some p)
    (N : Nat) {i : Nat} (hi : i < p) : (expandRL 3 N l)[i]! = l[i]! := by
  rw [expandRL, hb]
  dsimp only
  rw [getElem!_append_left _ _ (by simpa using hi), getElem!_map_range _ _ hi]

/-- **The entries of a copy**: `C[N]` at `p + t` is the source column
`p + t % L` of the bad part, raised by `t / L` times the difference in the rows
below `m₀` where the source descends from the bad root. -/
theorem expandRL_get_copy {l : List (List Nat)} {p : Nat} (hb : badRootR 3 l = some p)
    (N : Nat) {t : Nat} (ht : t < (N + 1) * (l.length - 1 - p)) (k : Nat) (hk : k < 3) :
    ((expandRL 3 N l)[p + t]!)[k]! = (l[p + t % (l.length - 1 - p)]!)[k]!
      + (if k < m0L 3 l ∧ (t % (l.length - 1 - p) = 0 ∨ AncR l k p (p + t % (l.length - 1 - p)))
          then (t / (l.length - 1 - p)) * ((l[l.length - 1]!)[k]! - (l[p]!)[k]!) else 0) := by
  rw [expandRL, hb]
  dsimp only
  have hlenG : ((List.range p).map (fun i => l[i]!)).length = p := by simp
  have key : ∀ (G C : List (List Nat)), G.length = p → (G ++ C)[p + t]! = C[t]! := by
    intro G C h; rw [← h]; exact getElem!_append_right G C t
  rw [key _ _ hlenG, getElem!_map_range _ _ ht, getElem!_map_range_nat, if_pos hk]
  generalize t % (l.length - 1 - p) = s
  have hc : (decide (k < m0L 3 l) && ((p == p + s) || ancAtR l k p (p + s))) = true ↔
      (k < m0L 3 l ∧ (s = 0 ∨ AncR l k p (p + s))) := by
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ancAtR_iff]
    exact and_congr Iff.rfl (or_congr (by omega) Iff.rfl)
  by_cases h : k < m0L 3 l ∧ (s = 0 ∨ AncR l k p (p + s))
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun e => h (hc.mp e)), if_neg h, Nat.add_zero]

/-! ### Two small facts about division -/

theorem mod_succ_of_ne {t L : Nat} (hL : 0 < L) (h : (t + 1) % L ≠ 0) :
    (t + 1) % L = t % L + 1 ∧ (t + 1) / L = t / L := by
  have h1 := Nat.div_add_mod t L
  have h2 := Nat.mod_lt t hL
  have e : t + 1 = (t % L + 1) + L * (t / L) := by omega
  by_cases hlt : t % L + 1 < L
  · refine ⟨?_, ?_⟩
    · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · rw [e, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · exfalso
    apply h
    rw [e, Nat.add_mul_mod_self_left, show t % L + 1 = L from by omega, Nat.mod_self]

theorem mod_succ_of_eq {t L : Nat} (hL : 0 < L) (h : (t + 1) % L = 0) :
    t % L = L - 1 ∧ (t + 1) / L = t / L + 1 := by
  have h1 := Nat.div_add_mod t L
  have h2 := Nat.mod_lt t hL
  have e : t + 1 = (t % L + 1) + L * (t / L) := by omega
  rw [e, Nat.add_mul_mod_self_left] at h
  have hr : t % L + 1 = L := by
    by_contra hc
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  refine ⟨by omega, ?_⟩
  rw [e, hr, Nat.add_mul_div_left _ _ hL, Nat.div_self hL]
  omega

/-! ### Which columns of an expansion are raisable -/

section Expansion

variable {C : List (List Nat)} {p N : Nat}

/-- Before the bad root the columns are those of `C`. -/
theorem Rz_expand_pre (hb : badRootR 3 C = some p) {i : Nat} (hi : i + 1 ≤ p) :
    Rz (expandRL 3 N C) i ↔ Rz C i := by
  have hp : p + 1 < C.length := badRootR_lt hb
  have hlen := expandRL_length_some hb N
  have hL : 0 < C.length - 1 - p := by omega
  have hpos : 0 < (N + 1) * (C.length - 1 - p) := Nat.mul_pos (by omega) hL
  have hE : (expandRL 3 N C)[i]! = C[i]! := expandRL_get_pre hb N (by omega)
  have hE1 : ∀ k, k < 3 → ((expandRL 3 N C)[i + 1]!)[k]! = (C[i + 1]!)[k]! := by
    intro k hk
    rcases Nat.eq_or_lt_of_le hi with he | hlt
    · have := expandRL_get_copy hb N (t := 0) hpos k hk
      simp only [Nat.add_zero, Nat.zero_mod, Nat.zero_div, Nat.zero_mul, ite_self] at this
      rw [he, this]
    · rw [expandRL_get_pre hb N hlt]
  have hlt1 : i + 1 < (expandRL 3 N C).length := by rw [hlen]; omega
  unfold Rz
  rw [hE, hE1 0 (by omega), hE1 1 (by omega), hE1 2 (by omega)]
  constructor
  · rintro ⟨_, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨_, h⟩; exact ⟨hlt1, h⟩

/-- The core of `Rz_expand_block`, with the increments named `I`. -/
theorem Rz_block_core (hL2 : Low2 C) (h1 : R1 C) (hnp : ¬ RaisedPar C)
    (hb : badRootR 3 C = some p) (E : List (List Nat)) (e s q : Nat)
    (hsL : p + s + 1 < C.length - 1) (I : Nat → Nat → Nat)
    (hI : ∀ k x, I k x = if k < m0L 3 C ∧ (x = p ∨ AncR C k p x)
      then q * ((C[C.length - 1]!)[k]! - (C[p]!)[k]!) else 0)
    (hE0 : ∀ k, k < 3 → (E[e]!)[k]! = (C[p + s]!)[k]! + I k (p + s))
    (hE1 : ∀ k, k < 3 → (E[e + 1]!)[k]! = (C[p + s + 1]!)[k]! + I k (p + s + 1))
    (he : e + 1 < E.length) :
    Rz E e ↔ Rz C (p + s) := by
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  have hpar := badRootR_ParR hb
  have hI2 : ∀ x, I 2 x = 0 := fun x => by rw [hI]; exact if_neg (by omega)
  -- `I k x ≠ 0` only under its condition
  have hIc : ∀ k x, I k x ≠ 0 → k < m0L 3 C ∧ (x = p ∨ AncR C k p x) := by
    intro k x h
    rw [hI] at h
    by_contra hc
    exact h (if_neg hc)
  have hpar2 : 1 < m0L 3 C → ParR C 2 p (C.length - 1) := by
    intro hm
    rwa [show m0L 3 C = 2 from by omega] at hpar
  constructor
  · -- a raisable column of the expansion comes from a raisable column
    rintro ⟨_, a1, a2, a3, a4, a5⟩
    rw [hE0 1 (by omega)] at a1
    rw [hE0 2 (by omega), hI2] at a2
    rw [hE1 0 (by omega), hE0 0 (by omega)] at a3
    rw [hE1 1 (by omega)] at a4
    rw [hE1 2 (by omega), hI2] at a5
    have hs1 : 2 ≤ (C[p + s + 1]!)[1]! := by
      by_contra hc; have := hL2 (p + s + 1) (by omega); omega
    have hI1 : I 1 (p + s) = 0 := by
      by_contra hne
      obtain ⟨hm, hx⟩ := hIc 1 _ hne
      have hc0 : (C[p + s]!)[1]! = 0 := by omega
      rcases hx with hx | hx
      · rw [hx] at hc0
        exact not_ParR_two_of_row1_zero hL2 h1 (hpar2 hm) hc0
      · have := AncR_entry_lt hx; omega
    have hI0 : I 0 (p + s + 1) = I 0 (p + s) := by
      rw [hI, hI]
      by_cases hm : 0 < m0L 3 C
      · have hA := AncR_zero_of_badRoot hb hm
        have c1 : p + s + 1 = p ∨ AncR C 0 p (p + s + 1) :=
          Or.inr (AncR_zero_between hA _ (by omega) (by omega))
        have c2 : p + s = p ∨ AncR C 0 p (p + s) := by
          rcases Nat.eq_zero_or_pos s with hs0 | hs0
          · exact Or.inl (by omega)
          · exact Or.inr (AncR_zero_between hA _ (by omega) (by omega))
        rw [if_pos ⟨hm, c1⟩, if_pos ⟨hm, c2⟩]
      · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- a raisable column is copied to a raisable column
    intro hR
    have hp0 := ParR0_of_Rz hR
    have hp1 := ParR1_of_Rz hR
    have hsame : ∀ k, k ≤ 1 → I k (p + s + 1) = I k (p + s) := by
      intro k hk
      have hpk : ParR C k (p + s) (p + s + 1) := by
        rcases Nat.lt_or_ge k 1 with h | h
        · rw [show k = 0 from by omega]; exact hp0
        · rw [show k = 1 from by omega]; exact hp1
      rw [hI, hI]
      refine if_congr (and_congr Iff.rfl ?_) rfl rfl
      rw [AncR_of_ParR_iff hpk p]
      constructor
      · rintro (h | h | h)
        · omega
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr h)
    have hI1 : I 1 (p + s) = 0 := by
      by_contra hne
      obtain ⟨hm, hx⟩ := hIc 1 _ hne
      rcases hx with hx | hx
      · rw [hx] at hR
        exact hnp ⟨p, hpar2 hm, hR⟩
      · have := AncR_entry_lt hx
        have := hR.2.1
        exact not_ParR_two_of_row1_zero hL2 h1 (hpar2 hm) (by omega)
    obtain ⟨_, a1, a2, a3, a4, a5⟩ := hR
    have e0 := hsame 0 (by omega)
    have e1 := hsame 1 le_rfl
    refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hE0 1 (by omega)]; omega
    · rw [hE0 2 (by omega), hI2]; omega
    · rw [hE1 0 (by omega), hE0 0 (by omega)]; omega
    · rw [hE1 1 (by omega)]; omega
    · rw [hE1 2 (by omega), hI2]; omega

/-- **Inside one copy of the bad part**, a column is raisable exactly when its
source is. -/
theorem Rz_expand_block (hL2 : Low2 C) (h1 : R1 C) (hnp : ¬ RaisedPar C)
    (hb : badRootR 3 C = some p) {t : Nat} (ht : t + 1 < (N + 1) * (C.length - 1 - p))
    (hmod : (t + 1) % (C.length - 1 - p) ≠ 0) :
    Rz (expandRL 3 N C) (p + t) ↔ Rz C (p + t % (C.length - 1 - p)) := by
  have hp : p + 1 < C.length := badRootR_lt hb
  have hlen := expandRL_length_some hb N
  have hLpos : 0 < C.length - 1 - p := by omega
  obtain ⟨hm1, hd1⟩ := mod_succ_of_ne hLpos hmod
  have hsL' : t % (C.length - 1 - p) + 1 < C.length - 1 - p := by
    have := Nat.mod_lt (t + 1) hLpos; omega
  refine Rz_block_core hL2 h1 hnp hb _ (p + t) (t % (C.length - 1 - p))
    (t / (C.length - 1 - p)) (by omega) _ (fun k x => rfl) ?_ ?_ (by rw [hlen]; omega)
  · intro k hk
    rw [expandRL_get_copy hb N (by omega) k hk]
    congr 1
    exact if_congr (and_congr Iff.rfl (or_congr (by omega) Iff.rfl)) rfl rfl
  · intro k hk
    rw [show p + t + 1 = p + (t + 1) from by omega, expandRL_get_copy hb N ht k hk, hm1, hd1]
    rw [show p + (t % (C.length - 1 - p) + 1) = p + t % (C.length - 1 - p) + 1 from by omega]
    congr 1
    exact if_congr (and_congr Iff.rfl (or_congr (by omega) Iff.rfl)) rfl rfl

/-- **Across the seam between two copies** no raisable column arises. -/
theorem Rz_seam (hL2 : Low2 C) (hb : badRootR 3 C = some p) {t : Nat}
    (ht : t + 1 < (N + 1) * (C.length - 1 - p)) (hmod : (t + 1) % (C.length - 1 - p) = 0) :
    ¬ Rz (expandRL 3 N C) (p + t) := by
  have hp : p + 1 < C.length := badRootR_lt hb
  have hLpos : 0 < C.length - 1 - p := by omega
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  have hpar := badRootR_ParR hb
  obtain ⟨hm1, hd1⟩ := mod_succ_of_eq hLpos hmod
  have hs : p + t % (C.length - 1 - p) = C.length - 2 := by omega
  generalize hq : t / (C.length - 1 - p) = q at *
  have hE0 : ∀ k, k < 3 → ((expandRL 3 N C)[p + t]!)[k]! = (C[C.length - 2]!)[k]!
      + (if k < m0L 3 C ∧ (C.length - 2 = p ∨ AncR C k p (C.length - 2))
          then q * ((C[C.length - 1]!)[k]! - (C[p]!)[k]!) else 0) := by
    intro k hk
    rw [expandRL_get_copy hb N (by omega) k hk, hs, hq]
    congr 1
    exact if_congr (and_congr Iff.rfl (or_congr (by omega) Iff.rfl)) rfl rfl
  have hE1 : ∀ k, k < 3 → ((expandRL 3 N C)[p + t + 1]!)[k]! = (C[p]!)[k]!
      + (if k < m0L 3 C then (q + 1) * ((C[C.length - 1]!)[k]! - (C[p]!)[k]!) else 0) := by
    intro k hk
    rw [show p + t + 1 = p + (t + 1) from by omega, expandRL_get_copy hb N ht k hk, hmod, hd1,
      Nat.add_zero]
    congr 1
    exact if_congr (and_iff_left (Or.inl rfl)) rfl rfl
  rintro ⟨_, a1, a2, a3, a4, a5⟩
  rw [hE0 1 (by omega)] at a1
  rw [hE0 2 (by omega), if_neg (by omega)] at a2
  rw [hE1 0 (by omega), hE0 0 (by omega)] at a3
  rw [hE1 1 (by omega)] at a4
  rw [hE1 2 (by omega), if_neg (by omega)] at a5
  have hp1 : 2 ≤ (C[p]!)[1]! := by
    by_contra hc; have := hL2 p (by omega); omega
  -- `m₀ ≤ 1`: in row `1` the copy of the bad root would go up
  have hm1' : m0L 3 C ≤ 1 := by
    by_contra hc
    rw [show m0L 3 C = 2 from by omega] at hpar
    have := AncR_entry_lt (k := 1) ((ParR_two_iff' C p _).mp hpar).2.1
    rw [if_pos (by omega)] at a4
    have : 1 ≤ (q + 1) * ((C[C.length - 1]!)[1]! - (C[p]!)[1]!) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  rw [if_neg (by omega)] at a1 a4
  have hne : C.length - 2 ≠ p := fun h => by rw [h] at a1; omega
  rcases Nat.eq_zero_or_pos (m0L 3 C) with h0 | h0
  · -- `m₀ = 0`: the column before the last is at least as high as the last in row `0`
    rw [h0] at hpar
    rw [if_neg (by omega), if_neg (by omega)] at a3
    have c1 := hpar.2.1
    have c2 := hpar.2.2 (C.length - 2) (by omega) (by omega)
    omega
  · -- `m₀ = 1`: the column before the last would be its row-`0` parent, too low in row `1`
    have hm : m0L 3 C = 1 := by omega
    have hA := AncR_zero_of_badRoot hb h0
    have hAn := AncR_zero_between hA (C.length - 2) (by omega) (by omega)
    rw [if_pos (by omega), if_pos ⟨by omega, Or.inr hAn⟩] at a3
    have hlt0 := AncR_entry_lt (k := 0) hA
    rw [Nat.add_mul, Nat.one_mul] at a3
    have hpar0 : ParR C 0 (C.length - 2) (C.length - 1) :=
      ⟨by omega, by omega, fun j' a b => by omega⟩
    rw [hm] at hpar
    obtain ⟨_, _, b3, b4⟩ := (ParR_one_iff C p _).mp hpar
    have := b4 (C.length - 2) (by omega) (by omega) (Relation.TransGen.single hpar0)
    omega

end Expansion

/-! ### The commutation -/

theorem ext_getElem!' {l l' : List (List Nat)} (hlen : l.length = l'.length)
    (h : ∀ i, i < l.length → l[i]! = l'[i]!) : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  rwa [getElem!_pos l i h1, getElem!_pos l' i h2] at this

theorem col_ext3 {u w : List Nat} (hu : u.length = 3) (hw : w.length = 3)
    (h : ∀ k, k < 3 → u[k]! = w[k]!) : u = w := by
  apply List.ext_getElem (by omega)
  intro k h1 h2
  have := h k (by omega)
  rwa [getElem!_pos u k h1, getElem!_pos w k h2] at this

/-- **`t3n` commutes with expansion** when the row-`2` parent of the last column
is not raisable, under `Low2` and `R1`. -/
theorem expandRL_t3n {C : List (List Nat)} (hv : Valid 2 C) (hL2 : Low2 C) (h1 : R1 C)
    (hnp : ¬ RaisedPar C) (N : Nat) :
    expandRL 3 N (t3n C) = t3n (expandRL 3 N C) := by
  have hbr := badRootR_t3n hnp
  have hm := m0L_t3n hnp
  have hvE : Valid 2 (expandRL 3 N C) := valid_expandRL hv N
  have hvE' : Valid 2 (expandRL 3 N (t3n C)) := valid_expandRL (valid_t3n hv) N
  have hvT : Valid 2 (t3n (expandRL 3 N C)) := valid_t3n hvE
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  cases hb : badRootR 3 C with
  | none =>
    rw [expandRL, hbr, hb, expandRL, hb]
    dsimp only
    apply ext_getElem!' (by simp)
    intro i hi
    have hi' : i < C.length - 1 := by simpa using hi
    have hiff : Rz C.dropLast i ↔ Rz C i := by
      unfold Rz
      rw [getElem!_dropLast', getElem!_dropLast', if_pos hi', List.length_dropLast]
      by_cases hi2 : i + 1 < C.length - 1
      · rw [if_pos hi2]
        constructor
        · rintro ⟨_, h⟩; exact ⟨by omega, h⟩
        · rintro ⟨_, h⟩; exact ⟨by omega, h⟩
      · have hn := not_Rz_last_two hnp
        rw [show C.length - 2 = i from by omega] at hn
        constructor
        · rintro ⟨h, _⟩; omega
        · intro h; exact absurd h hn
    rw [getElem!_dropLast', if_pos (by rw [t3n_length]; omega), t3n_get (by omega),
      t3n_get (by rw [List.length_dropLast]; omega), getElem!_dropLast', if_pos hi']
    by_cases hR : Rz C i
    · rw [if_pos hR, if_pos (hiff.mpr hR)]
    · rw [if_neg hR, if_neg (fun h => hR (hiff.mp h))]
  | some p =>
    have hp : p + 1 < C.length := badRootR_lt hb
    have hLpos : 0 < C.length - 1 - p := by omega
    have hbT : badRootR 3 (t3n C) = some p := by rw [hbr, hb]
    have hlenE := expandRL_length_some hb N
    have hlenE' := expandRL_length_some hbT N
    rw [t3n_length] at hlenE'
    apply ext_getElem!' (by rw [hlenE', t3n_length, hlenE])
    intro i hi
    rw [hlenE'] at hi
    apply col_ext3 (hvE' _ (getElem!_mem _ i (by rw [hlenE']; exact hi)))
      (hvT _ (getElem!_mem _ i (by rw [t3n_length, hlenE]; exact hi)))
    intro k hk
    by_cases hip : i < p
    · -- before the bad root
      have hz := Rz_expand_pre (N := N) hb (i := i) (by omega)
      rw [expandRL_get_pre hbT N hip]
      by_cases hk2 : k = 2
      · subst hk2
        rw [t3n_entry_two C i, t3n_entry_two, expandRL_get_pre hb N hip]
        by_cases hR : Rz C i
        · rw [if_pos hR, if_pos (hz.mpr hR)]
        · rw [if_neg hR, if_neg (fun h => hR (hz.mp h))]
      · have hk1 : k ≤ 1 := by omega
        rw [t3n_entry_low C i k hk1, t3n_entry_low _ i k hk1, expandRL_get_pre hb N hip]
    · obtain ⟨t, rfl⟩ : ∃ t, i = p + t := ⟨i - p, by omega⟩
      have ht : t < (N + 1) * (C.length - 1 - p) := by omega
      have htT : t < (N + 1) * ((t3n C).length - 1 - p) := by rw [t3n_length]; exact ht
      -- raisable here iff at the source
      have hiff : Rz (expandRL 3 N C) (p + t) ↔ Rz C (p + t % (C.length - 1 - p)) := by
        by_cases hlast : t + 1 < (N + 1) * (C.length - 1 - p)
        · by_cases hmod : (t + 1) % (C.length - 1 - p) = 0
          · have hs := (mod_succ_of_eq hLpos hmod).1
            have hn := not_Rz_last_two hnp
            rw [show C.length - 2 = p + t % (C.length - 1 - p) from by omega] at hn
            exact ⟨fun h => absurd h (Rz_seam hL2 hb hlast hmod), fun h => absurd h hn⟩
          · exact Rz_expand_block hL2 h1 hnp hb hlast hmod
        · have hmod : (t + 1) % (C.length - 1 - p) = 0 := by
            rw [show t + 1 = (N + 1) * (C.length - 1 - p) from by omega, Nat.mul_mod_left]
          have hs := (mod_succ_of_eq hLpos hmod).1
          have hn := not_Rz_last_two hnp
          rw [show C.length - 2 = p + t % (C.length - 1 - p) from by omega] at hn
          refine ⟨fun h => absurd h.1 (by rw [hlenE]; omega), fun h => absurd h hn⟩
      by_cases hk2 : k = 2
      · subst hk2
        rw [t3n_entry_two (expandRL 3 N C) (p + t), expandRL_get_copy hbT N htT 2 (by omega),
          t3n_length, hm, t3n_entry_two C (p + t % (C.length - 1 - p)),
          expandRL_get_copy hb N ht 2 (by omega)]
        simp only [show ¬ (2 < m0L 3 C) from by omega, false_and, if_false, Nat.add_zero]
        by_cases hR : Rz C (p + t % (C.length - 1 - p))
        · rw [if_pos hR, if_pos (hiff.mpr hR)]
        · rw [if_neg hR, if_neg (fun h => hR (hiff.mp h))]
      · have hk1 : k ≤ 1 := by omega
        have e : ∀ j, ((t3n C)[j]!)[k]! = (C[j]!)[k]! := fun j => t3n_entry_low C j k hk1
        rw [t3n_entry_low (expandRL 3 N C) (p + t) k hk1, expandRL_get_copy hbT N htT k hk,
          t3n_length, hm, expandRL_get_copy hb N ht k hk]
        simp only [e, AncR_t3n_low C k hk1]

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.expandRL_t3n
