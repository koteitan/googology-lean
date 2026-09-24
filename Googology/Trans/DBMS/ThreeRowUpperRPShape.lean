import Googology.Trans.DBMS.ThreeRowUpperNCLast

/-!
# `RPLastShape` holds

`ThreeRowUpperNCLast.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to two open statements, `RPLastShape` and
`T3nRankDescRPInner`.  This file proves the first one (`rPLastShape`).

It follows from a stronger statement that holds on every reached matrix
(`sReach_rStrong`):

    RStrong C :  if column `j` is raisable and `x` is its row-`1` parent,
                 then column `x + 1` is raisable too.

(If `x + 1 = j` this is the hypothesis.)  `RStrong` holds at the start
`(0,0,0)(1,1,0)(2,2,1)(3,3,1)⋯`, where only column `1` is raisable, and every
expansion keeps it (`rStrong_expandRL`), using only `Low2` and `R1`.

**Why an expansion keeps it.**  Let `r` be the bad root, `L = n - 1 - r` the
length of the bad part, and `j` a raisable column of `C[N]`.

* If `j + 1 < n - 1`, both columns are columns of `C`, and so are all the
  columns the parents look at.
* A raisable pair never crosses the seam between two copies (`Rz_seam`).
* Otherwise `j` is the copy `q ≥ 1` of the column `u = r + s` (`s + 1 < L`).
  Its source `u` is raisable (`Rz_src_of_copy`): the row-`1` increment of a
  copy is positive only on columns with row-`1` entry `≥ 1` whose copy then has
  row-`1` entry `≥ 2` (`row1_cpos`).  Let `x` be the row-`1` parent of `j` in
  `C[N]`.
  - If `x` is in the same copy, `x = r + qL + s'`, then `r + s'` is the
    row-`1` parent of `u` in `C` (row `0` is shifted uniformly inside one copy,
    `AncR0_copy_iff`), so `r + s' + 1` is raisable, and so is its copy
    (`Rz_copy_of_src`).
  - If `x < r`, then `x` is the row-`1` parent of `u` in `C`, and `x + 1 ≤ r`
    is a column of `C`.
  - If `r ≤ x < r + qL` there is a contradiction: `x` would give a column of
    the bad part with row-`1` entry `0` that is a row-`0` ancestor of the last
    column, strictly above the bad root, while the bad root is a row-`1`
    ancestor of the last column (`row1_between_of_AncR1`); or the copy root
    `r + qL` has row-`1` entry `0` and sits between `x` and `j`.
-/

namespace Googology.Trans.DBMS

open Googology.Trans.BMS
open Classical

/-! ### Row-`0` ancestors by visibility -/

theorem AncR0_of_vis (l : List (List Nat)) (j : Nat) : ∀ i, j < i →
    (∀ m, j < m → m ≤ i → (l[j]!)[0]! < (l[m]!)[0]!) → AncR l 0 j i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hji hall
    obtain ⟨w, hw⟩ := exists_ParR0 l (i - j) j i rfl hji (hall i hji le_rfl)
    have hwi := ParR_lt hw
    have hwj : j ≤ w := by
      by_contra hc
      have h1 := hw.2.2 j (by omega) hji
      have h2 := hall i hji le_rfl
      omega
    rcases Nat.eq_or_lt_of_le hwj with rfl | hlt
    · exact Relation.TransGen.single hw
    · exact Relation.TransGen.tail (ih w hwi hlt (fun m a b => hall m a (by omega))) hw

/-- **A row-`0` ancestor is an earlier column lower than every column after it
up to the descendant.** -/
theorem AncR0_iff (l : List (List Nat)) (j i : Nat) :
    AncR l 0 j i ↔ j < i ∧ ∀ m, j < m → m ≤ i → (l[j]!)[0]! < (l[m]!)[0]! := by
  constructor
  · intro h
    refine ⟨transGen_lt (fun _ _ h => ParR_lt h) h, fun m hm1 hm2 => ?_⟩
    rcases Nat.lt_or_ge m i with hmi | hmi
    · exact between_row0_gt h m hm1 hmi
    · rw [show m = i from by omega]; exact AncR_entry_lt h
  · rintro ⟨hji, hall⟩
    exact AncR0_of_vis l j i hji hall

/-- **Row-`0` ancestors of `z` above a row-`1` ancestor `r` of `z` are higher
than `r` in row `1`.** -/
theorem row1_between_of_AncR1 {l : List (List Nat)} : ∀ z r v, AncR l 1 r z → AncR l 0 v z →
    r < v → v < z → (l[r]!)[1]! < (l[v]!)[1]! := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro r v hr hv hrv hvz
    obtain ⟨p, hrp, hpz⟩ := Relation.TransGen.tail'_iff.mp hr
    have hrp' : p = r ∨ AncR l 1 r p := Relation.reflTransGen_iff_eq_or_transGen.mp hrp
    obtain ⟨hpzlt, _, hp1, hall⟩ := (ParR_one_iff l p z).mp hpz
    have hrle : (l[r]!)[1]! ≤ (l[p]!)[1]! := by
      rcases hrp' with h | h
      · rw [h]
      · exact le_of_lt (AncR_entry_lt h)
    rcases lt_trichotomy v p with hvp | hvp | hvp
    · have hne : AncR l 1 r p := by
        rcases hrp' with h | h
        · omega
        · exact h
      have hvp0 : AncR l 0 v p := by
        rw [AncR0_iff] at hv ⊢
        exact ⟨hvp, fun m a b => hv.2 m a (by omega)⟩
      exact ih p hpzlt r v hne hvp0 hrv hvp
    · subst hvp
      rcases hrp' with h | h
      · omega
      · exact AncR_entry_lt h
    · have := hall v hvp hvz hv
      omega

/-- `Rz` reads only the columns up to `j + 1`. -/
theorem Rz_congr {l l' : List (List Nat)} {j : Nat}
    (h : ∀ m k, m ≤ j + 1 → k < 3 → (l[m]!)[k]! = (l'[m]!)[k]!)
    (hl : j + 1 < l.length) (hl' : j + 1 < l'.length) : Rz l j ↔ Rz l' j := by
  unfold Rz
  rw [h j 1 (by omega) (by omega), h j 2 (by omega) (by omega), h (j + 1) 0 le_rfl (by omega),
    h j 0 (by omega) (by omega), h (j + 1) 1 le_rfl (by omega), h (j + 1) 2 le_rfl (by omega)]
  exact ⟨fun ⟨_, x⟩ => ⟨hl', x⟩, fun ⟨_, x⟩ => ⟨hl, x⟩⟩

/-! ### The entries of a copy -/

theorem cpos_mod {L q s : Nat} (hs : s < L) : (q * L + s) % L = s := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem cpos_div {L q s : Nat} (hs : s < L) : (q * L + s) / L = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]

theorem cpos_lt {L q s N : Nat} (hq : q ≤ N) (hs : s < L) : q * L + s < (N + 1) * L := by
  have := Nat.mul_le_mul_right L (show q + 1 ≤ N + 1 from by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

section Strong

variable {C : List (List Nat)} {r N : Nat}

/-- The entries of the copy `q` of the column `r + s`. -/
theorem expandRL_get_cpos (hb : badRootR 3 C = some r) {L : Nat} (hLd : C.length - 1 - r = L)
    {q s : Nat} (hq : q ≤ N) (hs : s < L) (k : Nat) (hk : k < 3) :
    ((expandRL 3 N C)[r + (q * L + s)]!)[k]! = (C[r + s]!)[k]!
      + (if k < m0L 3 C ∧ (s = 0 ∨ AncR C k r (r + s))
          then q * ((C[C.length - 1]!)[k]! - (C[r]!)[k]!) else 0) := by
  subst hLd
  rw [expandRL_get_copy hb N (cpos_lt hq hs) k hk, cpos_mod hs, cpos_div hs]

/-- Every column of the bad part descends from the bad root in row `0` when
`m₀ > 0`. -/
theorem bad_anc0 (hb : badRootR 3 C = some r) (hm : 0 < m0L 3 C) {s : Nat}
    (hs : r + s < C.length - 1) : s = 0 ∨ AncR C 0 r (r + s) := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (AncR_zero_between (AncR_zero_of_badRoot hb hm) _ (by omega) hs)

/-- Row `0` of a copy: shifted by `q · Δ₀` when `m₀ > 0`. -/
theorem row0_cpos (hb : badRootR 3 C = some r) {L : Nat} (hLd : C.length - 1 - r = L)
    {q s : Nat} (hq : q ≤ N) (hs : s < L) :
    ((expandRL 3 N C)[r + (q * L + s)]!)[0]! = (C[r + s]!)[0]!
      + (if 0 < m0L 3 C then q * ((C[C.length - 1]!)[0]! - (C[r]!)[0]!) else 0) := by
  rw [expandRL_get_cpos hb hLd hq hs 0 (by omega)]
  congr 1
  by_cases hm : 0 < m0L 3 C
  · have hc := bad_anc0 hb hm (s := s) (by omega)
    rw [if_pos (And.intro hm hc), if_pos hm]
  · rw [if_neg (fun h => hm h.1), if_neg hm]

/-- Row `2` of a copy is that of its source. -/
theorem row2_cpos (hb : badRootR 3 C = some r) {L : Nat} (hLd : C.length - 1 - r = L)
    {q s : Nat} (hq : q ≤ N) (hs : s < L) :
    ((expandRL 3 N C)[r + (q * L + s)]!)[2]! = (C[r + s]!)[2]! := by
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  rw [expandRL_get_cpos hb hLd hq hs 2 (by omega), if_neg (fun h => absurd h.1 (by omega)),
    Nat.add_zero]

/-- A bad root with row-`1` entry `0` is not a row-`2` parent. -/
theorem no_row1_zero_root (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r)
    (hm : 1 < m0L 3 C) (h0 : (C[r]!)[1]! = 0) : False := by
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  have hpar := badRootR_ParR hb
  rw [show m0L 3 C = 2 from by omega] at hpar
  exact not_ParR_two_of_row1_zero hL2 h1 hpar h0

/-- **Row `1` of a copy**: it goes up only on sources with row-`1` entry `≥ 1`. -/
theorem row1_cpos (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs : s < L) :
    (C[r + s]!)[1]! ≤ ((expandRL 3 N C)[r + (q * L + s)]!)[1]! ∧
      (((expandRL 3 N C)[r + (q * L + s)]!)[1]! ≠ (C[r + s]!)[1]! →
        1 ≤ (C[r + s]!)[1]! ∧ (C[r + s]!)[1]! < ((expandRL 3 N C)[r + (q * L + s)]!)[1]!) := by
  rw [expandRL_get_cpos hb hLd hq hs 1 (by omega)]
  refine ⟨Nat.le_add_right _ _, fun hne => ?_⟩
  split_ifs at hne ⊢ with hc
  · refine ⟨?_, by omega⟩
    rcases hc.2 with h0 | hA
    · subst h0
      by_contra hz
      exact no_row1_zero_root hL2 h1 hb hc.1 (by simp only [Nat.add_zero] at hz ⊢; omega)
    · have := AncR_entry_lt hA
      omega
  · exact absurd (Nat.add_zero _) hne

theorem row1_cpos_zero (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs : s < L)
    (h : ((expandRL 3 N C)[r + (q * L + s)]!)[1]! = 0) : (C[r + s]!)[1]! = 0 := by
  have := (row1_cpos (N := N) hL2 h1 hb hLd hq hs).1
  omega

theorem row1_cpos_pos (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs : s < L)
    (h : 1 ≤ ((expandRL 3 N C)[r + (q * L + s)]!)[1]!) : 1 ≤ (C[r + s]!)[1]! := by
  obtain ⟨_, h2⟩ := row1_cpos (N := N) hL2 h1 hb hLd hq hs
  by_contra hc
  by_cases he : ((expandRL 3 N C)[r + (q * L + s)]!)[1]! = (C[r + s]!)[1]!
  · omega
  · have := (h2 he).1
    omega

theorem row1_cpos_one (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs : s < L)
    (h : ((expandRL 3 N C)[r + (q * L + s)]!)[1]! = 1) : (C[r + s]!)[1]! = 1 := by
  obtain ⟨h0, h2⟩ := row1_cpos (N := N) hL2 h1 hb hLd hq hs
  by_cases he : ((expandRL 3 N C)[r + (q * L + s)]!)[1]! = (C[r + s]!)[1]!
  · omega
  · have := h2 he
    omega

/-- The bad part is not lower than the bad root in row `0`. -/
theorem Rbase (hb : badRootR 3 C = some r) {s : Nat} (hs : r + s < C.length - 1) :
    (C[r]!)[0]! ≤ (C[r + s]!)[0]! := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; exact le_rfl
  by_cases hm : 0 < m0L 3 C
  · have := AncR_entry_lt (AncR_zero_between (AncR_zero_of_badRoot hb hm) (r + s) (by omega) hs)
    omega
  · have hpar := badRootR_ParR hb
    rw [show m0L 3 C = 0 from by omega] at hpar
    have a := hpar.2.1
    have b := hpar.2.2 (r + s) (by omega) hs
    omega

/-- Every column from the bad root on is not lower than the bad root in row `0`. -/
theorem Rbase_D (hb : badRootR 3 C = some r) {m : Nat} (hrm : r ≤ m)
    (hm : m < (expandRL 3 N C).length) :
    (C[r]!)[0]! ≤ ((expandRL 3 N C)[m]!)[0]! := by
  have hr := badRootR_lt hb
  obtain ⟨L, hLd⟩ : ∃ L, C.length - 1 - r = L := ⟨_, rfl⟩
  have hL : 0 < L := by omega
  have hlen := expandRL_length_some hb N
  rw [hLd] at hlen
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < L ∧ m = r + (q * L + s) :=
    ⟨(m - r) / L, (m - r) % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']; omega⟩
  have hq : q ≤ N := by
    by_contra hc
    have := Nat.mul_le_mul_right L (show N + 1 ≤ q from by omega)
    omega
  rw [row0_cpos hb hLd hq hs]
  have := Rbase hb (s := s) (by omega)
  omega

/-- **A raisable column inside a copy comes from a raisable column.** -/
theorem Rz_src_of_copy (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs : s + 1 < L)
    (h : Rz (expandRL 3 N C) (r + (q * L + s))) : Rz C (r + s) := by
  have hr := badRootR_lt hb
  obtain ⟨_, a1, a2, a3, a4, a5⟩ := h
  have i1 : r + (q * L + s) + 1 = r + (q * L + (s + 1)) := by omega
  rw [i1] at a3 a4 a5
  have i2 : r + (s + 1) = r + s + 1 := by omega
  have e0 := row0_cpos (N := N) hb hLd hq (show s < L from by omega)
  have e0' := row0_cpos (N := N) hb hLd hq hs
  have e2 := row2_cpos (N := N) hb hLd hq (show s < L from by omega)
  have e2' := row2_cpos (N := N) hb hLd hq hs
  rw [i2] at e0' e2'
  rw [e0, e0'] at a3
  rw [e2] at a2
  rw [e2'] at a5
  have c1 := row1_cpos_one hL2 h1 hb hLd hq (show s < L from by omega) a1
  have hs1 : 2 ≤ (C[r + s + 1]!)[1]! := by
    by_contra hc; have := hL2 (r + s + 1) (by omega); omega
  have c4 := (row1_cpos (N := N) hL2 h1 hb hLd hq hs).1
  rw [i2] at c4
  refine ⟨by omega, c1, a2, by omega, by omega, a5⟩

/-- **A raisable column of the bad part (not the root) is copied to a raisable
column.** -/
theorem Rz_copy_of_src (hL2 : Low2 C) (h1 : R1 C) (hb : badRootR 3 C = some r) {L : Nat}
    (hLd : C.length - 1 - r = L) {q s : Nat} (hq : q ≤ N) (hs0 : 0 < s) (hs : s + 1 < L)
    (h : Rz C (r + s)) : Rz (expandRL 3 N C) (r + (q * L + s)) := by
  have hr := badRootR_lt hb
  have hlen := expandRL_length_some hb N
  rw [hLd] at hlen
  have hnot : ¬ (1 < m0L 3 C ∧ AncR C 1 r (r + s)) := by
    rintro ⟨hm, hA⟩
    have := AncR_entry_lt hA
    have := h.2.1
    exact no_row1_zero_root hL2 h1 hb hm (by omega)
  have e1 := expandRL_get_cpos (N := N) hb hLd hq (show s < L from by omega) 1 (by omega)
  have e1' := expandRL_get_cpos (N := N) hb hLd hq hs 1 (by omega)
  rw [if_neg (fun hc => hnot ⟨hc.1, hc.2.resolve_left (by omega)⟩)] at e1
  rw [if_neg (fun hc => by
    rcases hc.2 with h0 | hA
    · omega
    · rcases (AncR_of_ParR_iff (ParR1_of_Rz h) r).mp (by rwa [show r + (s + 1) = r + s + 1 from by omega] at hA) with he | hA'
      · omega
      · exact hnot ⟨hc.1, hA'⟩)] at e1'
  have e0 := row0_cpos (N := N) hb hLd hq (show s < L from by omega)
  have e0' := row0_cpos (N := N) hb hLd hq hs
  have e2 := row2_cpos (N := N) hb hLd hq (show s < L from by omega)
  have e2' := row2_cpos (N := N) hb hLd hq hs
  have i1 : r + (q * L + s) + 1 = r + (q * L + (s + 1)) := by omega
  have i2 : r + (s + 1) = r + s + 1 := by omega
  rw [i2] at e0' e1' e2'
  obtain ⟨_, a1, a2, a3, a4, a5⟩ := h
  have hlt : r + (q * L + s) + 1 < (expandRL 3 N C).length := by
    have := cpos_lt (N := N) hq hs
    rw [hlen]; omega
  refine ⟨hlt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; omega
  · rw [e2]; exact a2
  · rw [i1, e0', e0]; omega
  · rw [i1, e1']; omega
  · rw [i1, e2']; exact a5

/-- **Inside one copy, row-`0` ancestry is that of the sources.** -/
theorem AncR0_copy_iff (hb : badRootR 3 C = some r) {L : Nat} (hLd : C.length - 1 - r = L)
    {q s1 s2 : Nat} (hq : q ≤ N) (h12 : s1 < s2) (hs2 : s2 < L) :
    AncR (expandRL 3 N C) 0 (r + (q * L + s1)) (r + (q * L + s2)) ↔
      AncR C 0 (r + s1) (r + s2) := by
  rw [AncR0_iff, AncR0_iff]
  have e := fun s'' (h : s'' < L) => row0_cpos (N := N) hb hLd hq h
  constructor
  · rintro ⟨_, h⟩
    refine ⟨by omega, fun m a b => ?_⟩
    have := h (r + (q * L + (m - r))) (by omega) (by omega)
    rw [e _ (by omega), e _ (by omega), show r + (m - r) = m from by omega] at this
    omega
  · rintro ⟨_, h⟩
    refine ⟨by omega, fun m a b => ?_⟩
    obtain ⟨s'', rfl⟩ : ∃ s'', m = r + (q * L + s'') := ⟨m - r - q * L, by omega⟩
    rw [e _ (by omega), e _ (by omega)]
    have := h (r + s'') (by omega) (by omega)
    omega

end Strong

/-! ### The invariant -/

/-- **The row-`1` parent of a raisable column is followed by a raisable column.** -/
def RStrong (C : List (List Nat)) : Prop :=
  ∀ j x, Rz C j → ParR C 1 x j → Rz C (x + 1)

/-- **Every expansion keeps `RStrong`**, under `Low2` and `R1`. -/
theorem rStrong_expandRL {C : List (List Nat)} (hL2 : Low2 C) (h1 : R1 C)
    (hS : RStrong C) (N : Nat) : RStrong (expandRL 3 N C) := by
  intro j x hj hx
  have hm3 : m0L 3 C < 3 := m0L_lt (by norm_num) C
  have hxj := ParR_lt hx
  cases hb : badRootR 3 C with
  | none =>
    have hD : expandRL 3 N C = C.dropLast := by rw [expandRL, hb]
    rw [hD] at hj hx ⊢
    have hlen : C.dropLast.length = C.length - 1 := List.length_dropLast
    have hagree : ∀ (m k : Nat), m < C.length - 1 → (C.dropLast[m]!)[k]! = (C[m]!)[k]! := by
      intro m k hm; rw [getElem!_dropLast', if_pos hm]
    have hj1 := hj.1
    rw [hlen] at hj1
    have hjC : Rz C j :=
      (Rz_congr (fun m k hm _ => hagree m k (by omega)) (by rw [hlen]; omega) (by omega)).mp hj
    have hxC : ParR C 1 x j :=
      (ParR_congr_upto _ C 1 j (fun m k' hm _ => hagree m k' (by omega)) x).mp hx
    exact (Rz_congr (fun m k hm _ => hagree m k (by omega)) (by rw [hlen]; omega)
      (by omega)).mpr (hS j x hjC hxC)
  | some r =>
    have hr := badRootR_lt hb
    obtain ⟨L, hLd⟩ : ∃ L, C.length - 1 - r = L := ⟨_, rfl⟩
    have hL : 0 < L := by omega
    have hlen := expandRL_length_some hb N
    rw [hLd] at hlen
    have hpar := badRootR_ParR hb
    -- the columns before `n - 1` are those of `C`
    have hlow : ∀ m k, m < C.length - 1 → k < 3 →
        ((expandRL 3 N C)[m]!)[k]! = (C[m]!)[k]! := by
      intro m k hm hk
      rcases Nat.lt_or_ge m r with hmr | hmr
      · rw [expandRL_get_pre hb N hmr]
      · have e := expandRL_get_cpos (N := N) hb hLd (q := 0) (Nat.zero_le _) (s := m - r)
          (by omega) k hk
        rw [Nat.zero_mul, Nat.zero_add, show r + (m - r) = m from by omega] at e
        rw [e]; simp
    have hj1 := hj.1
    rw [hlen] at hj1
    by_cases hjn : j + 1 < C.length - 1
    · have hjC : Rz C j :=
        (Rz_congr (fun m k hm hk => hlow m k (by omega) hk) (by rw [hlen]; omega)
          (by omega)).mp hj
      have hxC : ParR C 1 x j :=
        (ParR_congr_upto _ C 1 j (fun m k' hm hk' => hlow m k' (by omega) (by omega)) x).mp hx
      exact (Rz_congr (fun m k hm hk => hlow m k (by omega) hk) (by rw [hlen]; omega)
        (by omega)).mpr (hS j x hjC hxC)
    obtain ⟨t, rfl⟩ : ∃ t, j = r + t := ⟨j - r, by omega⟩
    obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < L ∧ t = q * L + s :=
      ⟨t / L, t % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']⟩
    have hs1 : s + 1 < L := by
      by_contra hc
      have he : q * L + s + 1 = (q + 1) * L := by rw [Nat.add_mul, Nat.one_mul]; omega
      have hm : (q * L + s + 1) % L = 0 := by rw [he]; exact Nat.mul_mod_left _ _
      refine Rz_seam (N := N) hL2 hb (t := q * L + s) ?_ (by rw [hLd]; exact hm) hj
      rw [hLd]; omega
    have hq1 : 1 ≤ q := by
      by_contra hc
      have : q = 0 := by omega
      subst this
      omega
    have hqN : q ≤ N := by
      by_contra hc
      have := Nat.mul_le_mul_right L (show N + 1 ≤ q from by omega)
      omega
    have hjpos : r + (q * L + s) < (expandRL 3 N C).length := by rw [hlen]; omega
    -- the source is raisable
    have hu : Rz C (r + s) := Rz_src_of_copy hL2 h1 hb hLd hqN hs1 hj
    have hj1' : ((expandRL 3 N C)[r + (q * L + s)]!)[1]! = 1 := hj.2.1
    obtain ⟨_, hA0, hx1lt, hmid⟩ := (ParR_one_iff _ x _).mp hx
    have hx10 : ((expandRL 3 N C)[x]!)[1]! = 0 := by omega
    have hqL : L ≤ q * L := by
      have := Nat.mul_le_mul_right L hq1
      rwa [Nat.one_mul] at this
    rcases Nat.lt_or_ge x (r + q * L) with hxq | hxq
    · rcases Nat.lt_or_ge x r with hxr | hxr
      · -- `x < r`: `x` is the row-`1` parent of the source
        have hDx : ∀ k, k < 3 → ((expandRL 3 N C)[x]!)[k]! = (C[x]!)[k]! :=
          fun k hk => hlow x k (by omega) hk
        have hPC : ParR C 1 x (r + s) := by
          refine (ParR_one_iff C x _).mpr ⟨by omega, ?_, ?_, ?_⟩
          · have hA0' : AncR (expandRL 3 N C) 0 x (r + (q * L + s)) := hA0
            show AncR C 0 x (r + s)
            rw [AncR0_iff] at hA0' ⊢
            refine ⟨by omega, fun m a b => ?_⟩
            have := hA0'.2 m a (by omega)
            rwa [hDx 0 (by omega), hlow m 0 (by omega) (by omega)] at this
          · rw [← hDx 1 (by omega), hx10, hu.2.1]; omega
          · intro m a b hm
            change AncR C 0 m (r + s) at hm
            rcases Nat.lt_or_ge m r with hmr | hmr
            · have hmD : AncR (expandRL 3 N C) 0 m (r + (q * L + s)) := by
                rw [AncR0_iff] at hm ⊢
                refine ⟨by omega, fun m' a' b' => ?_⟩
                rw [hlow m 0 (by omega) (by omega)]
                rcases Nat.lt_or_ge m' r with h' | h'
                · rw [hlow m' 0 (by omega) (by omega)]
                  exact hm.2 m' a' (by omega)
                · have c1 := hm.2 r (by omega) (by omega)
                  have c2 := Rbase_D (N := N) hb h' (by omega)
                  omega
              have := hmid m a (by omega) hmD
              rw [hlow m 1 (by omega) (by omega), hj1'] at this
              rw [hu.2.1]; exact this
            · obtain ⟨s'', rfl⟩ : ∃ s'', m = r + s'' := ⟨m - r, by omega⟩
              have hmD : AncR (expandRL 3 N C) 0 (r + (q * L + s'')) (r + (q * L + s)) :=
                (AncR0_copy_iff hb hLd hqN (by omega) hs).mpr hm
              have := hmid _ (by omega) (by omega) hmD
              rw [hj1'] at this
              rw [hu.2.1]
              exact row1_cpos_pos hL2 h1 hb hLd hqN (by omega) this
        have hR := hS _ x hu hPC
        exact (Rz_congr (fun m k hm hk => hlow m k (by omega) hk) (by rw [hlen]; omega)
          (by omega)).mpr hR
      · -- `r ≤ x < r + qL`: impossible
        exfalso
        obtain ⟨q', sx, hsx, rfl⟩ : ∃ q' sx, sx < L ∧ x = r + (q' * L + sx) :=
          ⟨(x - r) / L, (x - r) % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']; omega⟩
        have hq' : q' < q := by
          by_contra hc
          have := Nat.mul_le_mul_right L (show q ≤ q' from by omega)
          omega
        have hq'N : q' ≤ N := by omega
        have hq'L : (q' + 1) * L = q' * L + L := by rw [Nat.add_mul, Nat.one_mul]
        have hq'q : (q' + 1) * L ≤ q * L := Nat.mul_le_mul_right L hq'
        have hvis := ((AncR0_iff _ _ _).mp hA0).2
        have hC1 : (C[r + sx]!)[1]! = 0 := row1_cpos_zero hL2 h1 hb hLd hq'N hsx hx10
        have ex := row0_cpos (N := N) hb hLd hq'N hsx
        -- the next copy root
        have hnext := hvis (r + ((q' + 1) * L + 0)) (by omega) (by omega)
        rw [row0_cpos (N := N) hb hLd (show q' + 1 ≤ N from by omega) hL, ex,
          Nat.add_zero] at hnext
        by_cases hm : 0 < m0L 3 C
        · rw [if_pos hm, if_pos hm] at hnext
          have hrl : (C[r]!)[0]! < (C[C.length - 1]!)[0]! :=
            AncR_entry_lt (AncR_zero_of_badRoot hb hm)
          rw [Nat.add_mul, Nat.one_mul] at hnext
          rcases Nat.eq_zero_or_pos sx with hsx0 | hsx0
          · -- `x` is a copy root: row `1` of the root is `0`
            subst hsx0
            rw [Nat.add_zero] at hC1
            have hm1 : m0L 3 C = 1 := by
              by_contra hc
              exact no_row1_zero_root hL2 h1 hb (by omega) hC1
            have er := expandRL_get_cpos (N := N) hb hLd hqN hL 1 (by omega)
            rw [if_neg (by omega)] at er
            simp only [Nat.add_zero] at er
            rw [hC1] at er
            rcases Nat.eq_zero_or_pos s with hs0 | hs0
            · subst hs0
              rw [Nat.add_zero] at hj1'
              omega
            · have hmD : AncR (expandRL 3 N C) 0 (r + (q * L + 0)) (r + (q * L + s)) :=
                (AncR0_copy_iff hb hLd hqN hs0 hs).mpr
                  (AncR_zero_between (AncR_zero_of_badRoot hb hm) _ (by omega) (by omega))
              have := hmid _ (by omega) (by omega) hmD
              simp only [Nat.add_zero] at this
              omega
          · -- a column of the bad part with row-`1` entry `0` above the root
            have hv : AncR C 0 (r + sx) (C.length - 1) := by
              rw [AncR0_iff]
              refine ⟨by omega, fun m a b => ?_⟩
              rcases Nat.lt_or_ge m (C.length - 1) with hml | hml
              · have := hvis (r + (q' * L + (m - r))) (by omega) (by omega)
                rw [row0_cpos (N := N) hb hLd hq'N (show m - r < L from by omega), ex,
                  show r + (m - r) = m from by omega] at this
                omega
              · rw [show m = C.length - 1 from by omega]
                omega
            rcases (show m0L 3 C = 1 ∨ m0L 3 C = 2 from by omega) with hm1 | hm2
            · rw [hm1] at hpar
              obtain ⟨_, _, b3, b4⟩ := (ParR_one_iff C r _).mp hpar
              have := b4 (r + sx) (by omega) (by omega) hv
              omega
            · rw [hm2] at hpar
              have hA1 : AncR C 1 r (C.length - 1) := ((ParR_two_iff' C r _).mp hpar).2.1
              have := row1_between_of_AncR1 _ r (r + sx) hA1 hv (by omega) (by omega)
              omega
        · rw [if_neg hm, if_neg hm] at hnext
          have := Rbase hb (s := sx) (by omega)
          omega
    · -- `x` in the same copy
      obtain ⟨s', rfl⟩ : ∃ s', x = r + (q * L + s') := ⟨x - r - q * L, by omega⟩
      have hs' : s' < s := by omega
      have hPC : ParR C 1 (r + s') (r + s) := by
        refine (ParR_one_iff C _ _).mpr ⟨by omega, (AncR0_copy_iff hb hLd hqN hs' hs).mp hA0,
          ?_, ?_⟩
        · rw [row1_cpos_zero hL2 h1 hb hLd hqN (by omega) hx10, hu.2.1]; omega
        · intro m a b hm
          obtain ⟨s'', rfl⟩ : ∃ s'', m = r + s'' := ⟨m - r, by omega⟩
          have hmD : AncR (expandRL 3 N C) 0 (r + (q * L + s'')) (r + (q * L + s)) :=
            (AncR0_copy_iff hb hLd hqN (by omega) hs).mpr hm
          have := hmid _ (by omega) (by omega) hmD
          rw [hj1'] at this
          rw [hu.2.1]
          exact row1_cpos_pos hL2 h1 hb hLd hqN (by omega) this
      have hR := hS _ _ hu hPC
      rw [show r + (q * L + s') + 1 = r + (q * L + (s' + 1)) from by omega]
      exact Rz_copy_of_src hL2 h1 hb hLd hqN (by omega) (by omega)
        (by rwa [show r + (s' + 1) = r + s' + 1 from by omega])

/-- At the start only column `1` is raisable. -/
theorem rStrong_start (v : Nat) : RStrong (lift 3 (TrioCofinal.trioGen (v + 1))) := by
  intro j x hj hx
  have hlen : (lift 3 (TrioCofinal.trioGen (v + 1))).length = v + 3 := by
    simp [TrioCofinal.trioGen]
  have hj1 : j = 1 := by
    by_contra hne
    have hr := hj.2.1
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [lift_get0] at hr
      simp [zcol] at hr
    · obtain ⟨i', rfl⟩ : ∃ i', j = i' + 1 := ⟨j - 1, by omega⟩
      have := hj.1
      rw [lift_trioGen_get v (i := i') (by omega)] at hr
      simp at hr
      omega
  subst hj1
  have := ParR_lt hx
  rw [show x = 0 from by omega]
  exact hj

/-- **Every reached matrix has `RStrong`.** -/
theorem sReach_rStrong {C : List (List Nat)} (h : SReach C) : RStrong C := by
  induction h with
  | gen v => rw [expandRL_cgen_two_four]; exact rStrong_start v
  | step N hC ih => exact rStrong_expandRL (low2_of_sReach hC) (r1_of_sReach hC) ih N

/-- **`RPLastShape` holds.** -/
theorem rPLastShape : RPLastShape :=
  fun C hC hy x hx => Or.inr (sReach_rStrong hC _ x hy hx)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.rStrong_expandRL
#print axioms Googology.Trans.DBMS.sReach_rStrong
#print axioms Googology.Trans.DBMS.rPLastShape
