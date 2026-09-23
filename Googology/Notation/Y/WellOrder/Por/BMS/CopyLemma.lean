/-
Por.BMS.CopyLemma: the copy lemma of BMS (Lemma 2.5 of the BMS literature) for one BM4
expansion step, in the form the imported 0-Y / 1-Y core calls it (`Lemma25AtRow`,
`Lemma25`, `lemma25_all`, `first_copy_ancestor_of_lt`, `good_to_first_copies_all_rows`,
`parent_first_copies_eq_of_maximalRow_le`).

Written independently from the BM4 rule. The statements (names, binders, binder names) are
fixed by how the imported core (Phyrion1343/1Y-Well-Ordering-Lean,
`formalization/{ZeroY,OneY}`, Apache-2.0) calls them. The route of the proof (six claims
C1-C6 proved row by row in three stages) follows the mathematical proof of the copy lemma in
koteitan/bms-elem-pattern (https://github.com/koteitan/bms-elem-pattern); no code is copied
from there. The Lean code here is new and uses Lean core only (no Mathlib).

Notation in the comments: `A` is the array, `c` its last column (`lastIndex`), `m₀` the
largest row in which `c` has a parent (`maximalRow`), `p` the bad root (`parentColumn`),
`s = c - p` (`blockLength`). `R = expandRaw A n` is `A[n]` before deleting all-zero rows:
`R = A[0..p) ++ B⁽⁰⁾ ++ ... ++ B⁽ⁿ⁾`, and `pos q j = p + q s + j` is column `j` of copy `q`.
Deleting all-zero rows changes no parent (`parent_trimZeroRows_eq`), so the whole proof
works with `R`.

The six claims, for a row `k` (all copies `q ≤ n`, all `i j < s`, all `E < p`):
- C1: `pos q i ≺ₖ pos q j` in `R` iff `p+i ≺ₖ p+j` in `A`;
- C2: `E ≺ₖ pos q j` in `R` iff `E ≺ₖ p+j` in `A`;
- C3 (`k < m₀`, `q ≥ 1`): `pos (q-1) i ≺ₖ pos q 0` in `R` iff `p+i ≺ₖ c` in `A`;
- C4 (`k ≥ m₀`, `q ≥ 1`): every `k`-ancestor of `pos q 0` in `R` is `< p`;
- C5 (`j > 0`): the `k`-parent of `pos q j` in `R` is `< p` or in copy `q`;
- C6: for `a < q`, `pos a i ≺ₖ pos q j` iff `pos a i ≺ₖ pos (q+1) j` in `R`.
Taken from koteitan, 1y-wo-por, `Por/BMS/CopyLemma.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.Context

namespace Por.BMS

namespace CopyLemma

/-! ## Values and structural candidates in an arbitrary array -/

/-- The entry `A(column,row)` as a number (`0` if it is missing). -/
def val (array : BMSArray) (column row : Nat) : Nat :=
  (entry? array column row).getD 0

/-- Structural candidates for the row-`k` parent: in row `0` every column to the left, in
row `k+1` the strict row-`k` ancestors. -/
def Cand (array : BMSArray) : Nat → Nat → Nat → Prop
  | 0, candidate, target => candidate < target
  | row + 1, candidate, target => isAncestor array row candidate target = true

theorem val_eq_of_entry? {X : BMSArray} {x k v : Nat} (h : entry? X x k = some v) :
    val X x k = v := by
  simp [val, h]

theorem entry?_eq_some_val {X : BMSArray} {H x k : Nat} (hX : UniformHeight H X)
    (hx : x < X.length) (hk : k < H) : entry? X x k = some (val X x k) := by
  obtain ⟨v, hv⟩ := exists_entry_of_uniformHeight hX hx hk
  simp [val, hv]

theorem parentEligible_iff {X : BMSArray} {H k x y : Nat} (hX : UniformHeight H X)
    (hx : x < X.length) (hk : k < H) (hy : y < x) :
    parentEligible k X x y = true ↔ Cand X k y x ∧ val X y k < val X x k := by
  have hyl : y < X.length := Nat.lt_trans hy hx
  have hEy := entry?_eq_some_val hX hyl hk
  have hEx := entry?_eq_some_val hX hx hk
  cases k with
  | zero =>
      simp only [parentEligible, entryLt, hEy, hEx, Option.any_some, decide_eq_true_eq, Cand]
      exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
  | succ k =>
      simp only [parentEligible, entryLt, hEy, hEx, Option.any_some, decide_eq_true_eq,
        Bool.and_eq_true, Cand]

theorem parent_eq_some_iff {X : BMSArray} {H k x y : Nat} (hX : UniformHeight H X)
    (hk : k < H) :
    parent k X x = some y ↔
      x < X.length ∧ y < x ∧ Cand X k y x ∧ val X y k < val X x k ∧
        ∀ z, y < z → z < x → Cand X k z x → val X x k ≤ val X z k := by
  rw [parent_eq_greatestBelow? k X x]
  by_cases hx : x < X.length
  · rw [if_pos hx, greatestBelow?_eq_some_iff]
    constructor
    · rintro ⟨hy, hElig, hMax⟩
      obtain ⟨hc, hv⟩ := (parentEligible_iff hX hx hk hy).mp hElig
      refine ⟨hx, hy, hc, hv, ?_⟩
      intro z hyz hzx hcz
      apply Nat.le_of_not_lt
      intro hlt
      have := hMax z hzx ((parentEligible_iff hX hx hk hzx).mpr ⟨hcz, hlt⟩)
      omega
    · rintro ⟨_, hy, hc, hv, hMax⟩
      refine ⟨hy, (parentEligible_iff hX hx hk hy).mpr ⟨hc, hv⟩, ?_⟩
      intro z hzx hElig
      obtain ⟨hcz, hvz⟩ := (parentEligible_iff hX hx hk hzx).mp hElig
      apply Nat.le_of_not_lt
      intro hyz
      have := hMax z hyz hzx hcz
      omega
  · rw [if_neg hx]
    constructor
    · intro h
      cases h
    · intro h
      exact absurd h.1 hx

theorem lt_length_of_parent {X : BMSArray} {k x y : Nat} (h : parent k X x = some y) :
    x < X.length :=
  (parent_eq_some_facts h).1

theorem lt_height_of_parent {X : BMSArray} {H k x y : Nat} (hX : UniformHeight H X)
    (h : parent k X x = some y) : k < H := by
  obtain ⟨_, _, _, hr, _⟩ := parent_some_entry_lt h
  exact row_lt_uniformHeight_of_entry?_eq_some hX hr

theorem parent_val_lt {X : BMSArray} {k x y : Nat} (h : parent k X x = some y) :
    val X y k < val X x k := by
  obtain ⟨_, _, hl, hr, hlt⟩ := parent_some_entry_lt h
  rw [val_eq_of_entry? hl, val_eq_of_entry? hr]
  exact hlt

theorem anc_val_lt {X : BMSArray} {k x y : Nat} (h : isAncestor X k y x = true) :
    val X y k < val X x k := by
  obtain ⟨_, _, hl, hr, hlt⟩ := ancestor_entries_lt h
  rw [val_eq_of_entry? hl, val_eq_of_entry? hr]
  exact hlt

theorem lt_height_of_anc {X : BMSArray} {H k x y : Nat} (hX : UniformHeight H X)
    (h : isAncestor X k y x = true) : k < H := by
  obtain ⟨_, _, _, hr, _⟩ := ancestor_entries_lt h
  exact row_lt_uniformHeight_of_entry?_eq_some hX hr

theorem lt_length_of_anc {X : BMSArray} {k x y : Nat} (h : isAncestor X k y x = true) :
    x < X.length := by
  obtain ⟨u, hu, _⟩ := isAncestor_eq_true_iff_parent.mp h
  exact lt_length_of_parent hu

theorem cand_of_parent {X : BMSArray} {k x y : Nat} (h : parent k X x = some y) :
    Cand X k y x := by
  cases k with
  | zero => exact parent_some_lt h
  | succ k => exact isAncestor_of_parent_succ h

theorem cand_of_anc {X : BMSArray} {k x y : Nat} (h : isAncestor X k y x = true) :
    Cand X k y x := by
  cases k with
  | zero => exact isAncestor_lt h
  | succ k => exact isAncestor_of_succ_row h

theorem cand_lt {X : BMSArray} {k x y : Nat} (h : Cand X k y x) : y < x := by
  cases k with
  | zero => exact h
  | succ k => exact isAncestor_lt h

theorem parent_max {X : BMSArray} {H k x y z : Nat} (hX : UniformHeight H X)
    (h : parent k X x = some y) (hyz : y < z) (hzx : z < x) (hc : Cand X k z x) :
    val X x k ≤ val X z k :=
  ((parent_eq_some_iff hX (lt_height_of_parent hX h)).mp h).2.2.2.2 z hyz hzx hc

theorem exists_parent_of_valid {X : BMSArray} {H k x y : Nat} (hX : UniformHeight H X)
    (hx : x < X.length) (hk : k < H) (hc : Cand X k y x) (hv : val X y k < val X x k) :
    ∃ z, parent k X x = some z ∧ y ≤ z := by
  have hy := cand_lt hc
  have hElig := (parentEligible_iff hX hx hk hy).mpr ⟨hc, hv⟩
  rw [parent_eq_greatestBelow?, if_pos hx]
  cases hG : greatestBelow? x (parentEligible k X x) with
  | none =>
      have := greatestBelow?_eq_none_iff.mp hG y hy
      rw [hElig] at this
      cases this
  | some z => exact ⟨z, rfl, greatestBelow?_some_isGreatest hG y hy hElig⟩

/-- Two strict ancestors of the same column: the smaller one is an ancestor of the larger. -/
theorem anc_of_anc_of_anc_of_lt {X : BMSArray} {k u v w : Nat}
    (hu : isAncestor X k u w = true) (hv : isAncestor X k v w = true) (huv : u < v) :
    isAncestor X k u v = true := by
  have hDecrease : ∀ {larger smaller},
      parent k X larger = some smaller → smaller < larger := fun h => parent_some_lt h
  rcases parentTransGen_comparable hDecrease (isAncestor_iff_strictAncestor.mp hu)
      (isAncestor_iff_strictAncestor.mp hv) with h | h | h
  · omega
  · have := transGen_lt_of_decrease hDecrease h
    omega
  · exact isAncestor_iff_strictAncestor.mpr h

theorem anc_mono {X : BMSArray} {h k y x : Nat} (hle : h ≤ k)
    (hanc : isAncestor X k y x = true) : isAncestor X h y x = true := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact isAncestor_of_lt_row hlt hanc
  · subst heq
    exact hanc

/-- Core of convexity: a structural candidate strictly between a column and its parent is a
strict descendant of the parent. -/
theorem anc_of_parent_of_between {X : BMSArray} {H k u v : Nat} (hX : UniformHeight H X)
    (huv : parent k X v = some u) :
    ∀ w, u < w → w < v → Cand X k w v → isAncestor X k u w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro huw hwv hcw
    have hk : k < H := lt_height_of_parent hX huv
    have hvl : v < X.length := lt_length_of_parent huv
    have hcu : Cand X k u w := by
      cases k with
      | zero => exact huw
      | succ k => exact anc_of_anc_of_anc_of_lt (isAncestor_of_parent_succ huv) hcw huw
    have hwinv := parent_max hX huv huw hwv hcw
    have hvu : val X u k < val X w k := Nat.lt_of_lt_of_le (parent_val_lt huv) hwinv
    obtain ⟨z, hz, huz⟩ := exists_parent_of_valid hX (by omega) hk hcu hvu
    rcases Nat.lt_or_eq_of_le huz with hlt | heq
    · have hzw : z < w := parent_some_lt hz
      have hcz : Cand X k z v := by
        cases k with
        | zero => exact Nat.lt_trans hzw hwv
        | succ k => exact isAncestor_trans (isAncestor_of_parent_succ hz) hcw
      exact isAncestor_trans (ih z hzw hlt (by omega) hcz) (direct_parent_isAncestor hz)
    · subst heq
      exact direct_parent_isAncestor hz

private theorem convex_aux {X : BMSArray} {H k u : Nat} (hX : UniformHeight H X) :
    ∀ v w, isAncestor X k u v = true → u ≤ w → w ≤ v → (w = v ∨ Cand X k w v) →
      u = w ∨ isAncestor X k u w = true := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro w huv huw hwv hc
    obtain ⟨m', hm, hum⟩ := isAncestor_eq_true_iff_parent.mp huv
    have hmv : m' < v := parent_some_lt hm
    rcases Nat.lt_or_ge w m' with hwm | hmw
    · have hum' : isAncestor X k u m' = true := by
        rcases hum with h | h
        · omega
        · exact h
      apply ih m' hmv w hum' huw (Nat.le_of_lt hwm)
      right
      cases k with
      | zero => exact hwm
      | succ k =>
          have hcw : isAncestor X k w v = true := by
            rcases hc with h | h
            · omega
            · exact h
          exact anc_of_anc_of_anc_of_lt hcw (isAncestor_of_parent_succ hm) hwm
    · rcases Nat.lt_or_eq_of_le hmw with hmw' | heq
      · rcases Nat.lt_or_eq_of_le hwv with hwv' | hweq
        · have hcw : Cand X k w v := by
            rcases hc with h | h
            · omega
            · exact h
          have hmwAnc := anc_of_parent_of_between hX hm w hmw' hwv' hcw
          right
          rcases hum with h | h
          · subst h
            exact hmwAnc
          · exact isAncestor_trans h hmwAnc
        · subst hweq
          exact Or.inr huv
      · subst heq
        exact hum

/-- Convexity: a non-strict structural candidate `w` of `v` between a strict ancestor `u` of
`v` and `v` is a non-strict descendant of `u`. -/
theorem convex {X : BMSArray} {H k u v w : Nat} (hX : UniformHeight H X)
    (huv : isAncestor X k u v = true) (huw : u ≤ w) (hwv : w ≤ v)
    (hc : w = v ∨ Cand X k w v) : u = w ∨ isAncestor X k u w = true :=
  convex_aux hX v w huv huw hwv hc

/-- The exit point of a parent chain from `v` down to `y < b ≤ v`: the last column `u ≥ b` of
the chain and its parent `y' < b`. -/
theorem anc_exit_point {X : BMSArray} {k b : Nat} :
    ∀ v y, isAncestor X k y v = true → y < b → b ≤ v →
      ∃ u y', b ≤ u ∧ (u = v ∨ isAncestor X k u v = true) ∧ parent k X u = some y' ∧
        y' < b ∧ (y = y' ∨ isAncestor X k y y' = true) := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro y hyv hy hbv
    obtain ⟨m', hm, hym⟩ := isAncestor_eq_true_iff_parent.mp hyv
    rcases Nat.lt_or_ge m' b with hmb | hbm
    · exact ⟨v, m', hbv, Or.inl rfl, hm, hmb, hym⟩
    · have hym' : isAncestor X k y m' = true := by
        rcases hym with h | h
        · omega
        · exact h
      obtain ⟨u, y', hbu, huv, hu, hy', hyy'⟩ := ih m' (parent_some_lt hm) y hym' hy hbm
      refine ⟨u, y', hbu, Or.inr ?_, hu, hy', hyy'⟩
      rcases huv with h | h
      · subst h
        exact direct_parent_isAncestor hm
      · exact isAncestor_trans h (direct_parent_isAncestor hm)

/-- A least witness. -/
theorem val_eq_zero_of_le_height {X : BMSArray} {H x k : Nat} (hX : UniformHeight H X)
    (hk : H ≤ k) : val X x k = 0 := by
  unfold val
  cases h : entry? X x k with
  | none => rfl
  | some v =>
      have := row_lt_uniformHeight_of_entry?_eq_some hX h
      omega

theorem lt_height_of_val_lt {X : BMSArray} {H x y k : Nat} (hX : UniformHeight H X)
    (h : val X y k < val X x k) : k < H := by
  apply Nat.lt_of_not_le
  intro hk
  rw [val_eq_zero_of_le_height (x := x) hX hk] at h
  omega

theorem exists_least {P : Nat → Prop} {j : Nat} (h : P j) :
    ∃ i, P i ∧ ∀ i', i' < i → ¬ P i' := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
    by_cases hLess : ∃ i', i' < j ∧ P i'
    · obtain ⟨i', hi', hP⟩ := hLess
      exact ih i' hi' hP
    · exact ⟨j, h, fun i' hi' hP => hLess ⟨i', hi', hP⟩⟩

/-! ## Deleting all-zero rows changes no parent -/

theorem parent_trimZeroRows_eq (X : BMSArray) (k x : Nat) :
    parent k (trimZeroRows X) x = parent k X x := by
  by_cases hk : k < trimHeight X
  · exact parent_trimZeroRows_of_lt X hk x
  · rw [parent_trimZeroRows_eq_none_of_le X (Nat.le_of_not_lt hk) x]
    cases h : parent k X x with
    | none => rfl
    | some y =>
        obtain ⟨_, _, _, hr, hlt⟩ := parent_some_entry_lt h
        exact absurd (row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hr (by omega)) hk

theorem isAncestor_trimZeroRows_eq (X : BMSArray) (k y x : Nat) :
    isAncestor (trimZeroRows X) k y x = isAncestor X k y x := by
  have h : parent k (trimZeroRows X) = parent k X := funext (parent_trimZeroRows_eq X k)
  unfold isAncestor
  rw [h]

theorem parent_expand_eq (array : ValidArray) (n k x : Nat) :
    parent k (array.expand n).raw x = parent k (expandRaw array.raw n) x :=
  parent_trimZeroRows_eq (expandRaw array.raw n) k x

theorem isAncestor_expand_eq (array : ValidArray) (n k y x : Nat) :
    isAncestor (array.expand n).raw k y x = isAncestor (expandRaw array.raw n) k y x :=
  isAncestor_trimZeroRows_eq (expandRaw array.raw n) k y x

/-! ## The expansion context: positions -/

section Setup

variable {array : ValidArray} (C : ExpansionContext array)

theorem pos_eq (q j : Nat) :
    C.copyPosition q j = C.parentColumn + q * C.blockLength + j := rfl

theorem pos_zero_zero : C.copyPosition 0 0 = C.parentColumn := by
  simp [pos_eq]

theorem p_le_pos (q j : Nat) : C.parentColumn ≤ C.copyPosition q j := by
  rw [pos_eq]
  omega

theorem pos_lt_pos_same_iff {q i j : Nat} :
    C.copyPosition q i < C.copyPosition q j ↔ i < j := by
  rw [pos_eq, pos_eq]
  omega

theorem pos_le_pos_same_iff {q i j : Nat} :
    C.copyPosition q i ≤ C.copyPosition q j ↔ i ≤ j := by
  rw [pos_eq, pos_eq]
  omega

theorem pos_lt_pos_of_lt {a q i j : Nat} (ha : a < q) (hi : i < C.blockLength) :
    C.copyPosition a i < C.copyPosition q j := by
  have h1 : (a + 1) * C.blockLength ≤ q * C.blockLength := Nat.mul_le_mul_right _ ha
  have h2 : (a + 1) * C.blockLength = a * C.blockLength + C.blockLength := Nat.succ_mul _ _
  rw [pos_eq, pos_eq]
  omega

theorem pos_inj {a q i j : Nat} (hi : i < C.blockLength) (hj : j < C.blockLength)
    (h : C.copyPosition a i = C.copyPosition q j) : a = q ∧ i = j := by
  rcases Nat.lt_trichotomy a q with hlt | heq | hgt
  · have := pos_lt_pos_of_lt C (j := j) hlt hi
    omega
  · subst heq
    exact ⟨rfl, by rw [pos_eq, pos_eq] at h; omega⟩
  · have := pos_lt_pos_of_lt C (j := i) hgt hj
    omega

theorem exists_pos {x : Nat} (hx : C.parentColumn ≤ x) :
    ∃ q j, j < C.blockLength ∧ x = C.copyPosition q j := by
  have hPos := C.blockLength_pos
  refine ⟨(x - C.parentColumn) / C.blockLength, (x - C.parentColumn) % C.blockLength,
    Nat.mod_lt _ hPos, ?_⟩
  have hDiv := Nat.div_add_mod' (x - C.parentColumn) C.blockLength
  rw [pos_eq]
  omega

theorem lt_pos_cases {q j y : Nat} (hj : j < C.blockLength) (hy : y < C.copyPosition q j) :
    y < C.parentColumn ∨
      ∃ a i, i < C.blockLength ∧ y = C.copyPosition a i ∧ (a < q ∨ (a = q ∧ i < j)) := by
  rcases Nat.lt_or_ge y C.parentColumn with h | h
  · exact Or.inl h
  · obtain ⟨a, i, hi, rfl⟩ := exists_pos C h
    refine Or.inr ⟨a, i, hi, rfl, ?_⟩
    rcases Nat.lt_trichotomy a q with hlt | heq | hgt
    · exact Or.inl hlt
    · subst heq
      exact Or.inr ⟨rfl, (pos_lt_pos_same_iff C).mp hy⟩
    · have := pos_lt_pos_of_lt C (j := i) hgt hj
      omega

theorem between_same_copy {q i j y : Nat} (h1 : C.copyPosition q i < y)
    (h2 : y < C.copyPosition q j) :
    ∃ i', y = C.copyPosition q i' ∧ i < i' ∧ i' < j := by
  rw [pos_eq] at h1 h2
  refine ⟨y - (C.parentColumn + q * C.blockLength), ?_, ?_, ?_⟩
  · rw [pos_eq]
    omega
  · omega
  · omega

theorem prev_mul {q : Nat} (hq : 0 < q) (s : Nat) : q * s = (q - 1) * s + s := by
  have h : q = (q - 1) + 1 := by omega
  conv => lhs; rw [h]
  exact Nat.succ_mul _ _

theorem between_prev_copy {q i y : Nat} (hq : 0 < q) (h1 : C.copyPosition (q - 1) i < y)
    (h2 : y < C.copyPosition q 0) :
    ∃ i', y = C.copyPosition (q - 1) i' ∧ i < i' ∧ i' < C.blockLength := by
  have hMul := prev_mul hq C.blockLength
  rw [pos_eq] at h1 h2
  refine ⟨y - (C.parentColumn + (q - 1) * C.blockLength), ?_, ?_, ?_⟩
  · rw [pos_eq]
    omega
  · omega
  · omega

theorem pos_prev_lt {q i : Nat} (hq : 0 < q) (hi : i < C.blockLength) :
    C.copyPosition (q - 1) i < C.copyPosition q 0 :=
  pos_lt_pos_of_lt C (by omega) hi

theorem lastIndex_eq : C.lastIndex = C.parentColumn + C.blockLength := by
  have := C.parentColumn_lt_lastIndex
  simp only [ExpansionContext.blockLength]
  omega

theorem pos_one_zero : C.copyPosition 1 0 = C.lastIndex := by
  rw [pos_eq, lastIndex_eq C]
  omega

theorem lt_last_of_lt_s {j : Nat} (hj : j < C.blockLength) :
    C.parentColumn + j < C.lastIndex := by
  rw [lastIndex_eq C]
  omega

theorem length_A : array.raw.length = C.lastIndex + 1 := C.array_length

theorem length_R (n : Nat) :
    (expandRaw array.raw n).length = C.parentColumn + (n + 1) * C.blockLength :=
  C.length_expandRaw n

theorem pos_lt_length_R {n q j : Nat} (hq : q ≤ n) (hj : j < C.blockLength) :
    C.copyPosition q j < (expandRaw array.raw n).length := by
  have h1 : (q + 1) * C.blockLength ≤ (n + 1) * C.blockLength :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (q + 1) * C.blockLength = q * C.blockLength + C.blockLength := Nat.succ_mul _ _
  rw [length_R C, pos_eq]
  omega

theorem le_of_pos_lt_length_R {n q j : Nat}
    (h : C.copyPosition q j < (expandRaw array.raw n).length) : q ≤ n := by
  rw [length_R C, pos_eq] at h
  apply Nat.le_of_not_lt
  intro hlt
  have : (n + 1) * C.blockLength ≤ q * C.blockLength := Nat.mul_le_mul_right _ hlt
  omega

/-! ## The expansion context: entries -/

/-- The bad-part column `j` ascends in row `k`. -/
abbrev Asc (k j : Nat) : Prop :=
  ascending array.raw C.maximalRow C.parentColumn j k = true

/-- `Δₖ = A(c,k) - A(p,k)`. -/
def delta (k : Nat) : Nat :=
  val array.raw C.lastIndex k - val array.raw C.parentColumn k

theorem asc_iff {k j : Nat} :
    Asc C k j ↔ k < C.maximalRow ∧
      (j = 0 ∨ isAncestor array.raw k C.parentColumn (C.parentColumn + j) = true) := by
  simp [Asc, ascending]

theorem val_R_prefix (n : Nat) {x k : Nat} (hx : x < C.lastIndex) :
    val (expandRaw array.raw n) x k = val array.raw x k := by
  unfold val
  rw [C.entry?_expandRaw_eq_of_lt_lastIndex n hx]

theorem parent_R_prefix (n k : Nat) {x : Nat} (hx : x < C.lastIndex) :
    parent k (expandRaw array.raw n) x = parent k array.raw x :=
  C.parent_expandRaw_eq_of_lt_lastIndex n k hx

theorem anc_R_prefix (n k y : Nat) {x : Nat} (hx : x < C.lastIndex) :
    isAncestor (expandRaw array.raw n) k y x = isAncestor array.raw k y x :=
  isAncestor_congr_below (fun _ hcol => C.parent_expandRaw_eq_of_lt_lastIndex n k (by omega))

theorem val_copy {H : Nat} (hA : UniformHeight H array.raw) {n q j k : Nat} (hq : q ≤ n)
    (hj : j < C.blockLength) (hk : k < H) :
    val (expandRaw array.raw n) (C.copyPosition q j) k =
      if Asc C k j then val array.raw (C.parentColumn + j) k + q * delta C k
      else val array.raw (C.parentColumn + j) k := by
  obtain ⟨column, value, hColumn, hValue⟩ := C.exists_badPart_entry hA hj hk
  have hEntry : entry? C.badPart j k = some value :=
    entry?_eq_some_iff.mpr ⟨column, hColumn, hValue⟩
  rw [C.entry?_badPart hj] at hEntry
  have hv : val array.raw (C.parentColumn + j) k = value := val_eq_of_entry? hEntry
  have hLength := length_A C
  have hLt := C.parentColumn_lt_lastIndex
  have hHead : (C.badPart.head?.getD [])[k]? = some (val array.raw C.parentColumn k) := by
    rw [List.head?_eq_getElem?]
    apply ExpansionContext.getD_getElem?_of_entry?_eq_some
    rw [C.entry?_badPart C.blockLength_pos, Nat.add_zero]
    exact entry?_eq_some_val hA (by omega) hk
  have hLast : (array.raw[C.lastIndex]?.getD [])[k]? = some (val array.raw C.lastIndex k) :=
    ExpansionContext.getD_getElem?_of_entry?_eq_some _ (entry?_eq_some_val hA (by omega) hk)
  rw [show val (expandRaw array.raw n) (C.copyPosition q j) k =
      (entry? (expandRaw array.raw n) (C.copyPosition q j) k).getD 0 from rfl,
    C.entry?_expandRaw_copy hq hj,
    ExpansionContext.entry?_copyBlock _ _ _ _ _ _ _ _ _ _ hColumn hValue]
  subst hv
  simp only [Option.getD_some, ExpansionContext.copiedValue, copiedEntry, rowGap, hHead, hLast,
    Option.bind_some, Option.map_some, Asc, delta]
  split <;> simp

theorem val_copy_asc {H : Nat} (hA : UniformHeight H array.raw) {n q j k : Nat} (hq : q ≤ n)
    (hj : j < C.blockLength) (hk : k < H) (hAsc : Asc C k j) :
    val (expandRaw array.raw n) (C.copyPosition q j) k =
      val array.raw (C.parentColumn + j) k + q * delta C k := by
  rw [val_copy C hA hq hj hk, if_pos hAsc]

theorem val_copy_not_asc {H : Nat} (hA : UniformHeight H array.raw) {n q j k : Nat}
    (hq : q ≤ n) (hj : j < C.blockLength) (hk : k < H) (hAsc : ¬ Asc C k j) :
    val (expandRaw array.raw n) (C.copyPosition q j) k =
      val array.raw (C.parentColumn + j) k := by
  rw [val_copy C hA hq hj hk, if_neg hAsc]

theorem le_val_copy {H : Nat} (hA : UniformHeight H array.raw) {n q j k : Nat} (hq : q ≤ n)
    (hj : j < C.blockLength) (hk : k < H) :
    val array.raw (C.parentColumn + j) k ≤
      val (expandRaw array.raw n) (C.copyPosition q j) k := by
  rw [val_copy C hA hq hj hk]
  split <;> omega

/-! ## The expansion context: facts about `A` -/

theorem maximalRow_lt_height {H : Nat} (hA : UniformHeight H array.raw) :
    C.maximalRow < H :=
  lt_height_of_parent hA C.parent_eq

theorem anc_p_c {k : Nat} (hk : k ≤ C.maximalRow) :
    isAncestor array.raw k C.parentColumn C.lastIndex = true :=
  anc_mono hk (direct_parent_isAncestor C.parent_eq)

theorem val_p_lt_c {k : Nat} (hk : k ≤ C.maximalRow) :
    val array.raw C.parentColumn k < val array.raw C.lastIndex k :=
  anc_val_lt (anc_p_c C hk)

theorem asc_zero {k : Nat} (hk : k < C.maximalRow) : Asc C k 0 :=
  (asc_iff C).mpr ⟨hk, Or.inl rfl⟩

theorem not_asc_of_ge {k j : Nat} (hk : C.maximalRow ≤ k) : ¬ Asc C k j := by
  intro h
  have := ((asc_iff C).mp h).1
  omega

theorem asc_iff_of_anc {k i j : Nat}
    (h : isAncestor array.raw k (C.parentColumn + i) (C.parentColumn + j) = true) :
    Asc C k i ↔ Asc C k j := by
  unfold Asc
  rw [ExpansionContext.ascending_eq_of_ancestor _ _ _ h]

theorem asc_of_cand {H : Nat} (hA : UniformHeight H array.raw) {k i j : Nat}
    (hAsc : Asc C k j) (hc : Cand array.raw k (C.parentColumn + i) (C.parentColumn + j)) :
    Asc C k i := by
  obtain ⟨hk, hj⟩ := (asc_iff C).mp hAsc
  have hij := cand_lt hc
  have hAnc : isAncestor array.raw k C.parentColumn (C.parentColumn + j) = true := by
    rcases hj with h | h
    · omega
    · exact h
  rcases convex hA hAnc (Nat.le_add_right _ i) (Nat.le_of_lt hij) (Or.inr hc) with h | h
  · exact (asc_iff C).mpr ⟨hk, Or.inl (by omega)⟩
  · exact (asc_iff C).mpr ⟨hk, Or.inr h⟩

theorem asc_of_cand_c {H : Nat} (hA : UniformHeight H array.raw) {k i : Nat}
    (hk : k < C.maximalRow) (hc : Cand array.raw k (C.parentColumn + i) C.lastIndex) :
    Asc C k i := by
  have hlt := cand_lt hc
  rcases convex hA (anc_p_c C (Nat.le_of_lt hk)) (Nat.le_add_right _ i) (Nat.le_of_lt hlt)
      (Or.inr hc) with h | h
  · exact (asc_iff C).mpr ⟨hk, Or.inl (by omega)⟩
  · exact (asc_iff C).mpr ⟨hk, Or.inr h⟩

theorem val_c_le_of_cand_m {H : Nat} (hA : UniformHeight H array.raw) {i : Nat}
    (hi : 0 < i) (hlt : C.parentColumn + i < C.lastIndex)
    (hc : Cand array.raw C.maximalRow (C.parentColumn + i) C.lastIndex) :
    val array.raw C.lastIndex C.maximalRow ≤
      val array.raw (C.parentColumn + i) C.maximalRow :=
  parent_max hA C.parent_eq (by omega) hlt hc

theorem val_p_add_delta {k : Nat} (hk : k ≤ C.maximalRow) :
    val array.raw C.parentColumn k + delta C k = val array.raw C.lastIndex k := by
  have := val_p_lt_c C hk
  unfold delta
  omega

end Setup

/-! ## The six claims -/

section Claims

variable {array : ValidArray} (C : ExpansionContext array)

/-- C1: ancestry inside one copy is ancestry inside the bad part. -/
def Claim1 (n k : Nat) : Prop :=
  ∀ q, q ≤ n → ∀ i j, i < C.blockLength → j < C.blockLength →
    (isAncestor (expandRaw array.raw n) k (C.copyPosition q i) (C.copyPosition q j) = true ↔
      isAncestor array.raw k (C.parentColumn + i) (C.parentColumn + j) = true)

/-- C2: ancestry from the good part into a copy is ancestry into the bad part. -/
def Claim2 (n k : Nat) : Prop :=
  ∀ q, q ≤ n → ∀ j E, j < C.blockLength → E < C.parentColumn →
    (isAncestor (expandRaw array.raw n) k E (C.copyPosition q j) = true ↔
      isAncestor array.raw k E (C.parentColumn + j) = true)

/-- C3: the bridge from copy `q-1` to the first column of copy `q`. -/
def Claim3 (n k : Nat) : Prop :=
  ∀ q, q ≤ n → 0 < q → ∀ i, i < C.blockLength →
    (isAncestor (expandRaw array.raw n) k (C.copyPosition (q - 1) i) (C.copyPosition q 0) =
        true ↔
      isAncestor array.raw k (C.parentColumn + i) C.lastIndex = true)

/-- C4: in rows `≥ m₀`, every ancestor of the first column of a copy `q ≥ 1` is good. -/
def Claim4 (n : Nat) : Prop :=
  ∀ k, C.maximalRow ≤ k → ∀ q y, 0 < q →
    isAncestor (expandRaw array.raw n) k y (C.copyPosition q 0) = true → y < C.parentColumn

/-- C5: the parent of a non-first column of a copy is good or in the same copy. -/
def Claim5 (n k : Nat) : Prop :=
  ∀ q j y, j < C.blockLength → 0 < j →
    parent k (expandRaw array.raw n) (C.copyPosition q j) = some y →
      y < C.parentColumn ∨ ∃ i, y = C.copyPosition q i

/-- C6: ancestry from an earlier copy does not depend on which later copy is the target. -/
def Claim6 (n k : Nat) : Prop :=
  ∀ a b, a < b → b + 1 ≤ n → ∀ i j, i < C.blockLength → j < C.blockLength →
    (isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition b j) = true ↔
      isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition (b + 1) j) =
        true)

/-! ### C1 -/

theorem col_lt_iff_of_anc {H : Nat} (hA : UniformHeight H array.raw) {n q i j k : Nat}
    (hq : q ≤ n) (hi : i < C.blockLength) (hj : j < C.blockLength)
    (h : isAncestor array.raw k (C.parentColumn + i) (C.parentColumn + j) = true) :
    val (expandRaw array.raw n) (C.copyPosition q i) k <
        val (expandRaw array.raw n) (C.copyPosition q j) k ↔
      val array.raw (C.parentColumn + i) k < val array.raw (C.parentColumn + j) k := by
  have hk : k < H := lt_height_of_anc hA h
  by_cases hAsc : Asc C k j
  · have hAsci : Asc C k i := (asc_iff_of_anc C h).mpr hAsc
    rw [val_copy_asc C hA hq hi hk hAsci, val_copy_asc C hA hq hj hk hAsc]
    constructor <;> intro h' <;> omega
  · have hAsci : ¬ Asc C k i := fun hc => hAsc ((asc_iff_of_anc C h).mp hc)
    rw [val_copy_not_asc C hA hq hi hk hAsci, val_copy_not_asc C hA hq hj hk hAsc]

theorem col_le_of_le_of_cand {H : Nat} (hA : UniformHeight H array.raw) {n q i j k : Nat}
    (hq : q ≤ n) (hi : i < C.blockLength) (hj : j < C.blockLength) (hk : k < H)
    (hc : Cand array.raw k (C.parentColumn + i) (C.parentColumn + j))
    (hle : val array.raw (C.parentColumn + j) k ≤ val array.raw (C.parentColumn + i) k) :
    val (expandRaw array.raw n) (C.copyPosition q j) k ≤
      val (expandRaw array.raw n) (C.copyPosition q i) k := by
  by_cases hAsc : Asc C k j
  · have hAsci := asc_of_cand C hA hAsc hc
    rw [val_copy_asc C hA hq hj hk hAsc, val_copy_asc C hA hq hi hk hAsci]
    omega
  · rw [val_copy_not_asc C hA hq hj hk hAsc]
    exact Nat.le_trans hle (le_val_copy C hA hq hi hk)

theorem cand_copy_iff {n k : Nat} (ih : ∀ h, h < k → Claim1 C n h) {q i j : Nat}
    (hq : q ≤ n) (hi : i < C.blockLength) (hj : j < C.blockLength) :
    Cand (expandRaw array.raw n) k (C.copyPosition q i) (C.copyPosition q j) ↔
      Cand array.raw k (C.parentColumn + i) (C.parentColumn + j) := by
  cases k with
  | zero =>
      show C.copyPosition q i < C.copyPosition q j ↔ C.parentColumn + i < C.parentColumn + j
      rw [pos_lt_pos_same_iff C]
      exact ⟨fun h => by omega, fun h => by omega⟩
  | succ k => exact ih k (Nat.lt_succ_self k) q hq i j hi hj

theorem parent_copy_iff {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (ih : ∀ h, h < k → Claim1 C n h) {q i j : Nat}
    (hq : q ≤ n) (hi : i < C.blockLength) (hj : j < C.blockLength) :
    parent k (expandRaw array.raw n) (C.copyPosition q j) = some (C.copyPosition q i) ↔
      parent k array.raw (C.parentColumn + j) = some (C.parentColumn + i) := by
  have hR : UniformHeight H (expandRaw array.raw n) := uniformHeight_expandRaw hA
  have hjc := lt_last_of_lt_s C hj
  have hLA := length_A C
  constructor
  · intro hp
    have hk := lt_height_of_parent hR hp
    obtain ⟨_, hlt, hcR, hvR, hMaxR⟩ := (parent_eq_some_iff hR hk).mp hp
    have hij : i < j := (pos_lt_pos_same_iff C).mp hlt
    have hcA := (cand_copy_iff C ih hq hi hj).mp hcR
    have hval : val array.raw (C.parentColumn + i) k < val array.raw (C.parentColumn + j) k := by
      by_cases hAsc : Asc C k j
      · have hAsci := asc_of_cand C hA hAsc hcA
        rw [val_copy_asc C hA hq hi hk hAsci, val_copy_asc C hA hq hj hk hAsc] at hvR
        omega
      · rw [val_copy_not_asc C hA hq hj hk hAsc] at hvR
        exact Nat.lt_of_le_of_lt (le_val_copy C hA hq hi hk) hvR
    refine (parent_eq_some_iff hA hk).mpr ⟨by omega, by omega, hcA, hval, ?_⟩
    intro y hy1 hy2 hcy
    apply Nat.le_of_not_lt
    intro hcon
    obtain ⟨z, hz, hyz⟩ := exists_parent_of_valid hA (by omega) hk hcy hcon
    have hz1 : z < C.parentColumn + j := parent_some_lt hz
    have hi2 : z - C.parentColumn < C.blockLength := by omega
    have hzEq : z = C.parentColumn + (z - C.parentColumn) := by omega
    rw [hzEq] at hz
    have hcz := (cand_copy_iff C ih hq hi2 hj).mpr (cand_of_parent hz)
    have hlt2 := (col_lt_iff_of_anc C hA hq hi2 hj (direct_parent_isAncestor hz)).mpr
      (parent_val_lt hz)
    have hmax := hMaxR (C.copyPosition q (z - C.parentColumn))
      ((pos_lt_pos_same_iff C).mpr (by omega)) ((pos_lt_pos_same_iff C).mpr (by omega)) hcz
    omega
  · intro hp
    have hk := lt_height_of_parent hA hp
    obtain ⟨_, hlt, hcA, hvA, hMaxA⟩ := (parent_eq_some_iff hA hk).mp hp
    have hij : i < j := by omega
    refine (parent_eq_some_iff hR hk).mpr ⟨pos_lt_length_R C hq hj,
      (pos_lt_pos_same_iff C).mpr hij, (cand_copy_iff C ih hq hi hj).mpr hcA,
      (col_lt_iff_of_anc C hA hq hi hj (direct_parent_isAncestor hp)).mpr hvA, ?_⟩
    intro y hy1 hy2 hcy
    obtain ⟨i2, rfl, hlt1, hlt2⟩ := between_same_copy C hy1 hy2
    have hi2 : i2 < C.blockLength := by omega
    have hcA2 := (cand_copy_iff C ih hq hi2 hj).mp hcy
    exact col_le_of_le_of_cand C hA hq hi2 hj hk hcA2 (hMaxA _ (by omega) (by omega) hcA2)

theorem anc_copy_iff {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (ih : ∀ h, h < k → Claim1 C n h) {q : Nat} (hq : q ≤ n) :
    ∀ j, j < C.blockLength → ∀ i, i < C.blockLength →
      (isAncestor (expandRaw array.raw n) k (C.copyPosition q i) (C.copyPosition q j) = true ↔
        isAncestor array.raw k (C.parentColumn + i) (C.parentColumn + j) = true) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j IH =>
    intro hj i hi
    constructor
    · intro h
      obtain ⟨u, hu, hui⟩ := isAncestor_eq_true_iff_parent.mp h
      rcases hui with heq | hanc
      · rw [← heq] at hu
        exact direct_parent_isAncestor ((parent_copy_iff C hA ih hq hi hj).mp hu)
      · obtain ⟨i2, rfl, hlt1, hlt2⟩ :=
          between_same_copy C (isAncestor_lt hanc) (parent_some_lt hu)
        have hi2 : i2 < C.blockLength := by omega
        exact isAncestor_trans ((IH i2 hlt2 hi2 i hi).mp hanc)
          (direct_parent_isAncestor ((parent_copy_iff C hA ih hq hi2 hj).mp hu))
    · intro h
      obtain ⟨u, hu, hui⟩ := isAncestor_eq_true_iff_parent.mp h
      rcases hui with heq | hanc
      · rw [← heq] at hu
        exact direct_parent_isAncestor ((parent_copy_iff C hA ih hq hi hj).mpr hu)
      · have hlt1 := isAncestor_lt hanc
        have hlt2 := parent_some_lt hu
        have hu' : u = C.parentColumn + (u - C.parentColumn) := by omega
        rw [hu'] at hu hanc
        have hi2 : u - C.parentColumn < C.blockLength := by omega
        exact isAncestor_trans ((IH (u - C.parentColumn) (by omega) hi2 i hi).mpr hanc)
          (direct_parent_isAncestor ((parent_copy_iff C hA ih hq hi2 hj).mpr hu))

theorem claim1_of_lower {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (ih : ∀ h, h < k → Claim1 C n h) : Claim1 C n k := by
  intro q hq i j hi hj
  exact anc_copy_iff C hA ih hq j hj i hi

/-! ### C3 -/

theorem col_asc_eq {H : Nat} (hA : UniformHeight H array.raw) {n q i k : Nat} (hq : q ≤ n)
    (hk : k < C.maximalRow) (hi : i < C.blockLength)
    (hc : Cand array.raw k (C.parentColumn + i) C.lastIndex) :
    val (expandRaw array.raw n) (C.copyPosition q i) k =
      val array.raw (C.parentColumn + i) k + q * delta C k :=
  val_copy_asc C hA hq hi (Nat.lt_trans hk (maximalRow_lt_height C hA))
    (asc_of_cand_c C hA hk hc)

theorem col_lead_eq {H : Nat} (hA : UniformHeight H array.raw) {n q k : Nat} (hq : q ≤ n)
    (hk : k < C.maximalRow) (hq0 : 0 < q) :
    val (expandRaw array.raw n) (C.copyPosition q 0) k =
      val array.raw C.lastIndex k + (q - 1) * delta C k := by
  have hkH := Nat.lt_trans hk (maximalRow_lt_height C hA)
  rw [val_copy_asc C hA hq C.blockLength_pos hkH (asc_zero C hk), Nat.add_zero]
  have h1 := val_p_add_delta C (Nat.le_of_lt hk)
  have h2 := prev_mul hq0 (delta C k)
  omega

theorem cand_bridge {n k : Nat} (h3 : ∀ k', k = k' + 1 → Claim3 C n k') {q i : Nat}
    (hq : q ≤ n) (hq0 : 0 < q) (hi : i < C.blockLength) :
    Cand (expandRaw array.raw n) k (C.copyPosition (q - 1) i) (C.copyPosition q 0) ↔
      Cand array.raw k (C.parentColumn + i) C.lastIndex := by
  cases k with
  | zero =>
      show C.copyPosition (q - 1) i < C.copyPosition q 0 ↔ C.parentColumn + i < C.lastIndex
      exact ⟨fun _ => lt_last_of_lt_s C hi, fun _ => pos_prev_lt C hq0 hi⟩
  | succ k' => exact h3 k' rfl q hq hq0 i hi

theorem parent_bridge {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (hk : k < C.maximalRow) (h3 : ∀ k', k = k' + 1 → Claim3 C n k') {q i : Nat}
    (hq : q ≤ n) (hq0 : 0 < q) (hi : i < C.blockLength) :
    parent k (expandRaw array.raw n) (C.copyPosition q 0) = some (C.copyPosition (q - 1) i) ↔
      parent k array.raw C.lastIndex = some (C.parentColumn + i) := by
  have hR : UniformHeight H (expandRaw array.raw n) := uniformHeight_expandRaw hA
  have hkH := Nat.lt_trans hk (maximalRow_lt_height C hA)
  have hq1 : q - 1 ≤ n := by omega
  have hLA := length_A C
  have hic := lt_last_of_lt_s C hi
  have hcs := lastIndex_eq C
  constructor
  · intro hp
    obtain ⟨_, _, hcR, hvR, hMaxR⟩ := (parent_eq_some_iff hR hkH).mp hp
    have hcA := (cand_bridge C h3 hq hq0 hi).mp hcR
    rw [col_asc_eq C hA hq1 hk hi hcA, col_lead_eq C hA hq hk hq0] at hvR
    refine (parent_eq_some_iff hA hkH).mpr ⟨by omega, hic, hcA, by omega, ?_⟩
    intro y hy1 hy2 hcy
    have hy' : y = C.parentColumn + (y - C.parentColumn) := by omega
    rw [hy'] at hcy ⊢
    have hi' : y - C.parentColumn < C.blockLength := by omega
    have hcy' := (cand_bridge C h3 hq hq0 hi').mpr hcy
    have hkey := hMaxR _ ((pos_lt_pos_same_iff C).mpr (by omega)) (pos_prev_lt C hq0 hi') hcy'
    rw [col_asc_eq C hA hq1 hk hi' hcy, col_lead_eq C hA hq hk hq0] at hkey
    omega
  · intro hp
    obtain ⟨_, _, hcA, hvA, hMaxA⟩ := (parent_eq_some_iff hA hkH).mp hp
    refine (parent_eq_some_iff hR hkH).mpr ⟨pos_lt_length_R C hq C.blockLength_pos,
      pos_prev_lt C hq0 hi, (cand_bridge C h3 hq hq0 hi).mpr hcA, ?_, ?_⟩
    · rw [col_asc_eq C hA hq1 hk hi hcA, col_lead_eq C hA hq hk hq0]
      omega
    · intro y hy1 hy2 hcy
      obtain ⟨i', rfl, hii', hi's⟩ := between_prev_copy C hq0 hy1 hy2
      have hcA' := (cand_bridge C h3 hq hq0 hi's).mp hcy
      have hkey := hMaxA _ (by omega) (lt_last_of_lt_s C hi's) hcA'
      rw [col_asc_eq C hA hq1 hk hi's hcA', col_lead_eq C hA hq hk hq0]
      omega

theorem anc_bridge {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (hk : k < C.maximalRow) (h1 : Claim1 C n k) (h3 : ∀ k', k = k' + 1 → Claim3 C n k')
    {q i : Nat} (hq : q ≤ n) (hq0 : 0 < q) (hi : i < C.blockLength) :
    isAncestor (expandRaw array.raw n) k (C.copyPosition (q - 1) i) (C.copyPosition q 0) =
        true ↔
      isAncestor array.raw k (C.parentColumn + i) C.lastIndex = true := by
  have hcs := lastIndex_eq C
  constructor
  · intro h
    obtain ⟨u, hu, hui⟩ := isAncestor_eq_true_iff_parent.mp h
    rcases hui with heq | hanc
    · rw [← heq] at hu
      exact direct_parent_isAncestor ((parent_bridge C hA hk h3 hq hq0 hi).mp hu)
    · obtain ⟨i', rfl, hii', hi's⟩ :=
        between_prev_copy C hq0 (isAncestor_lt hanc) (parent_some_lt hu)
      exact isAncestor_trans ((h1 (q - 1) (by omega) i i' hi hi's).mp hanc)
        (direct_parent_isAncestor ((parent_bridge C hA hk h3 hq hq0 hi's).mp hu))
  · intro h
    obtain ⟨u, hu, hui⟩ := isAncestor_eq_true_iff_parent.mp h
    rcases hui with heq | hanc
    · rw [← heq] at hu
      exact direct_parent_isAncestor ((parent_bridge C hA hk h3 hq hq0 hi).mpr hu)
    · have hlt1 := isAncestor_lt hanc
      have hlt2 := parent_some_lt hu
      have hu' : u = C.parentColumn + (u - C.parentColumn) := by omega
      rw [hu'] at hu hanc
      have hi's : u - C.parentColumn < C.blockLength := by omega
      exact isAncestor_trans ((h1 (q - 1) (by omega) i _ hi hi's).mpr hanc)
        (direct_parent_isAncestor ((parent_bridge C hA hk h3 hq hq0 hi's).mpr hu))

theorem claim3_of {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (hk : k < C.maximalRow) (h1 : Claim1 C n k) (h3 : ∀ k', k = k' + 1 → Claim3 C n k') :
    Claim3 C n k := by
  intro q hq hq0 i hi
  exact anc_bridge C hA hk h1 h3 hq hq0 hi

/-- Iterating C3: the first columns of the copies form a chain in rows `< m₀`. -/
theorem chain_lead {n k : Nat} (hk : k < C.maximalRow) (h3 : Claim3 C n k) :
    ∀ a q, q ≤ n → a < q →
      isAncestor (expandRaw array.raw n) k (C.copyPosition a 0) (C.copyPosition q 0) =
        true := by
  intro a q
  induction q with
  | zero => intro _ h; omega
  | succ q ih =>
    intro hq haq
    have hpc : isAncestor array.raw k (C.parentColumn + 0) C.lastIndex = true := by
      rw [Nat.add_zero]
      exact anc_p_c C (Nat.le_of_lt hk)
    have hstep := (h3 (q + 1) hq (Nat.succ_pos q) 0 C.blockLength_pos).mpr hpc
    rw [Nat.add_sub_cancel] at hstep
    rcases Nat.lt_or_ge a q with hlt | hge
    · exact isAncestor_trans (ih (by omega) hlt) hstep
    · have : a = q := by omega
      subst this
      exact hstep

/-! ### C4 -/

theorem col_pos_m {H : Nat} (hA : UniformHeight H array.raw) {n q j : Nat} (hq : q ≤ n)
    (hj : j < C.blockLength) :
    val (expandRaw array.raw n) (C.copyPosition q j) C.maximalRow =
      val array.raw (C.parentColumn + j) C.maximalRow :=
  val_copy_not_asc C hA hq hj (maximalRow_lt_height C hA) (not_asc_of_ge C (Nat.le_refl _))

theorem anc_lt_p_of_no_valid {n k q y : Nat}
    (hno : ∀ z, C.parentColumn ≤ z → z < C.copyPosition q 0 →
      Cand (expandRaw array.raw n) k z (C.copyPosition q 0) →
      val (expandRaw array.raw n) z k < val (expandRaw array.raw n) (C.copyPosition q 0) k →
        False)
    (hanc : isAncestor (expandRaw array.raw n) k y (C.copyPosition q 0) = true) :
    y < C.parentColumn := by
  obtain ⟨u, hu, hyu⟩ := isAncestor_eq_true_iff_parent.mp hanc
  have hup : u < C.parentColumn := by
    apply Nat.lt_of_not_le
    intro hle
    exact hno u hle (parent_some_lt hu) (cand_of_parent hu) (parent_val_lt hu)
  rcases hyu with h | h
  · omega
  · have := isAncestor_lt h
    omega

theorem no_valid_of_entry {H : Nat} (hA : UniformHeight H array.raw) {n q : Nat} (hq : q ≤ n)
    (hentry : ∀ a i, a < q → i < C.blockLength →
      Cand (expandRaw array.raw n) C.maximalRow (C.copyPosition a i) (C.copyPosition q 0) →
        val array.raw C.parentColumn C.maximalRow ≤
          val array.raw (C.parentColumn + i) C.maximalRow) :
    ∀ z, C.parentColumn ≤ z → z < C.copyPosition q 0 →
      Cand (expandRaw array.raw n) C.maximalRow z (C.copyPosition q 0) →
      val (expandRaw array.raw n) z C.maximalRow <
        val (expandRaw array.raw n) (C.copyPosition q 0) C.maximalRow → False := by
  intro z hz hzq hc hv
  obtain ⟨a, i, hi, rfl⟩ := exists_pos C hz
  have haq : a < q := by
    rcases Nat.lt_or_ge a q with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_eq_of_le h with h' | h'
      · have := pos_lt_pos_of_lt C (i := 0) (j := i) h' C.blockLength_pos
        omega
      · subst h'
        have := (pos_lt_pos_same_iff C).mp hzq
        omega
  rw [col_pos_m C hA (by omega) hi, col_pos_m C hA hq C.blockLength_pos, Nat.add_zero] at hv
  have := hentry a i haq hi hc
  omega

theorem claim4_of_zero {H : Nat} (hA : UniformHeight H array.raw) {n : Nat}
    (hm : C.maximalRow = 0) : Claim4 C n := by
  intro k hk q y _ hanc
  have hanc' := anc_mono hk hanc
  have hq : q ≤ n := le_of_pos_lt_length_R C (lt_length_of_anc hanc)
  refine anc_lt_p_of_no_valid C (no_valid_of_entry C hA hq ?_) hanc'
  intro a i _ hi _
  rcases Nat.eq_zero_or_pos i with h0 | hi0
  · subst h0
    simp
  · have hcA : Cand array.raw C.maximalRow (C.parentColumn + i) C.lastIndex := by
      rw [hm]
      exact lt_last_of_lt_s C hi
    have h1 := val_c_le_of_cand_m C hA hi0 (lt_last_of_lt_s C hi) hcA
    have h2 := val_p_lt_c C (Nat.le_refl C.maximalRow)
    omega

theorem anc_lead_of_anc_lead {n k a i : Nat} (h6 : Claim6 C n k) (hi : i < C.blockLength) :
    ∀ q, q ≤ n → a < q →
      isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition q 0) = true →
      isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition (a + 1) 0) =
        true := by
  intro q
  induction q with
  | zero => intro _ h; omega
  | succ q ih =>
    intro hq haq hanc
    rcases Nat.lt_or_ge a q with hlt | hge
    · exact ih (by omega) hlt ((h6 a q hlt hq i 0 hi C.blockLength_pos).mpr hanc)
    · have : a = q := by omega
      subst this
      exact hanc

theorem claim4_of_pos {H : Nat} (hA : UniformHeight H array.raw) {n : Nat}
    (hm : 0 < C.maximalRow) (h3 : Claim3 C n (C.maximalRow - 1))
    (h6 : Claim6 C n (C.maximalRow - 1)) : Claim4 C n := by
  have hm' : C.maximalRow = (C.maximalRow - 1) + 1 := by omega
  intro k hk q y _ hanc
  have hanc' := anc_mono hk hanc
  have hq : q ≤ n := le_of_pos_lt_length_R C (lt_length_of_anc hanc)
  refine anc_lt_p_of_no_valid C (no_valid_of_entry C hA hq ?_) hanc'
  intro a i haq hi hc
  rcases Nat.eq_zero_or_pos i with h0 | hi0
  · subst h0
    simp
  · have hcanc : isAncestor (expandRaw array.raw n) (C.maximalRow - 1) (C.copyPosition a i)
        (C.copyPosition q 0) = true := by
      rw [hm'] at hc
      exact hc
    have hstep := anc_lead_of_anc_lead C h6 hi q hq haq hcanc
    have hbridge := h3 (a + 1) (by omega) (by omega) i hi
    rw [Nat.add_sub_cancel] at hbridge
    have hA' := hbridge.mp hstep
    have hcA : Cand array.raw C.maximalRow (C.parentColumn + i) C.lastIndex := by
      rw [hm']
      exact hA'
    have h1 := val_c_le_of_cand_m C hA hi0 (lt_last_of_lt_s C hi) hcA
    have h2 := val_p_lt_c C (Nat.le_refl C.maximalRow)
    omega

/-! ### C5 -/

theorem lead_anc_of_earlier {n h q j y : Nat} (h5 : Claim5 C n h) (hj : j < C.blockLength)
    (hj0 : 0 < j) (hyp : C.parentColumn ≤ y) (hylt : y < C.copyPosition q 0)
    (hanc : isAncestor (expandRaw array.raw n) h y (C.copyPosition q j) = true) :
    isAncestor (expandRaw array.raw n) h (C.copyPosition q 0) (C.copyPosition q j) = true := by
  obtain ⟨u, y', hu, huv, hy'u, hy', hyy'⟩ :=
    anc_exit_point (b := C.copyPosition q 0) _ _ hanc hylt
      ((pos_le_pos_same_iff C).mpr (Nat.zero_le j))
  have hule : u ≤ C.copyPosition q j := by
    rcases huv with h' | h'
    · omega
    · exact Nat.le_of_lt (isAncestor_lt h')
  have hu' := hu
  have hule' := hule
  rw [pos_eq] at hu' hule'
  obtain ⟨j', hj', rfl⟩ : ∃ j', j' ≤ j ∧ u = C.copyPosition q j' :=
    ⟨u - (C.parentColumn + q * C.blockLength), by omega, by rw [pos_eq]; omega⟩
  rcases Nat.eq_zero_or_pos j' with h0 | hj'0
  · subst h0
    rcases huv with h' | h'
    · have := (pos_inj C C.blockLength_pos hj h').2
      omega
    · exact h'
  · exfalso
    have hQy : C.parentColumn ≤ y' := by
      rcases hyy' with h' | h'
      · omega
      · have := isAncestor_lt h'
        omega
    rcases h5 q j' y' (by omega) hj'0 hy'u with hlt2 | ⟨i'', hi''⟩
    · omega
    · subst hi''
      have := (pos_lt_pos_same_iff C).mp hy'
      omega

theorem cand_p_of_lead {n k q j : Nat} (hq : q ≤ n) (hj : j < C.blockLength) (hj0 : 0 < j)
    (hlow : ∀ h, h < k → Claim1 C n h)
    (hlead : ∀ h, h < k →
      isAncestor (expandRaw array.raw n) h (C.copyPosition q 0) (C.copyPosition q j) = true) :
    Cand array.raw k C.parentColumn (C.parentColumn + j) := by
  cases k with
  | zero =>
      show C.parentColumn < C.parentColumn + j
      omega
  | succ k' =>
      have hc := (hlow k' (Nat.lt_succ_self k') q hq 0 j C.blockLength_pos hj).mp
        (hlead k' (Nat.lt_succ_self k'))
      rw [Nat.add_zero] at hc
      exact hc

theorem cand_lead_of_lead {n k q j : Nat} (hj0 : 0 < j)
    (hlead : ∀ h, h < k →
      isAncestor (expandRaw array.raw n) h (C.copyPosition q 0) (C.copyPosition q j) = true) :
    Cand (expandRaw array.raw n) k (C.copyPosition q 0) (C.copyPosition q j) := by
  cases k with
  | zero => exact (pos_lt_pos_same_iff C).mpr hj0
  | succ k' => exact hlead k' (Nat.lt_succ_self k')

theorem claim5_of {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (hlow : ∀ h, h < k → Claim1 C n h ∧ Claim5 C n h) (h1 : Claim1 C n k)
    (h3 : k < C.maximalRow → Claim3 C n k) (h4 : C.maximalRow ≤ k → Claim4 C n) :
    Claim5 C n k := by
  intro q j y hj hj0 hp
  have hR : UniformHeight H (expandRaw array.raw n) := uniformHeight_expandRaw hA
  have hq : q ≤ n := le_of_pos_lt_length_R C (lt_length_of_parent hp)
  have hk : k < H := lt_height_of_parent hR hp
  refine Classical.byContradiction fun hcon => ?_
  have hyp : C.parentColumn ≤ y := Nat.le_of_not_lt (fun h => hcon (Or.inl h))
  have hnotpos : ∀ i', y ≠ C.copyPosition q i' := fun i' h => hcon (Or.inr ⟨i', h⟩)
  rcases lt_pos_cases C hj (parent_some_lt hp) with hlt | ⟨a, i, hi, rfl, hcase⟩
  · omega
  have ha : a < q := by
    rcases hcase with h | ⟨haq, _⟩
    · exact h
    · subst haq
      exact absurd rfl (hnotpos i)
  have hQlt : C.copyPosition a i < C.copyPosition q 0 := pos_lt_pos_of_lt C ha hi
  -- no ancestor of the target at or after the first column of its copy
  have hno : ∀ z, isAncestor (expandRaw array.raw n) k z (C.copyPosition q j) = true →
      C.copyPosition q 0 ≤ z → False := by
    intro z hz hzge
    obtain ⟨u, hu, hzu⟩ := isAncestor_eq_true_iff_parent.mp hz
    rw [hp] at hu
    cases hu
    rcases hzu with h | h
    · omega
    · have := isAncestor_lt h
      omega
  -- the first column of the copy is a lower-row ancestor of the target
  have hlead : ∀ h, h < k →
      isAncestor (expandRaw array.raw n) h (C.copyPosition q 0) (C.copyPosition q j) = true := by
    intro h hh
    exact lead_anc_of_earlier C (hlow h hh).2 hj hj0 (p_le_pos C a i) hQlt
      (anc_mono (Nat.le_of_lt hh) (direct_parent_isAncestor hp))
  -- the target column does not ascend
  have hnotA : ¬ isAncestor array.raw k C.parentColumn (C.parentColumn + j) = true := by
    intro hc
    have hc' : isAncestor array.raw k (C.parentColumn + 0) (C.parentColumn + j) = true := by
      rw [Nat.add_zero]
      exact hc
    exact hno _ ((h1 q hq 0 j C.blockLength_pos hj).mpr hc') (Nat.le_refl _)
  have hnasc : ¬ Asc C k j := by
    intro hasc
    rcases ((asc_iff C).mp hasc).2 with h | h
    · omega
    · exact hnotA h
  have htgt := val_copy_not_asc C hA hq hj hk hnasc
  -- `A(p+j,k) ≤ A(p,k)`
  have hcandP := cand_p_of_lead C hq hj hj0 (fun h hh => (hlow h hh).1) hlead
  have hstep3 : val array.raw (C.parentColumn + j) k ≤ val array.raw C.parentColumn k := by
    apply Nat.le_of_not_lt
    intro hc
    have hLA := length_A C
    have hjc := lt_last_of_lt_s C hj
    obtain ⟨y', hy'p, hy'ge⟩ := exists_parent_of_valid hA (by omega) hk hcandP hc
    have hy'lt := parent_some_lt hy'p
    have hy'eq : y' = C.parentColumn + (y' - C.parentColumn) := by omega
    rw [hy'eq] at hy'p
    have hi's : y' - C.parentColumn < C.blockLength := by omega
    exact hno _ ((h1 q hq _ j hi's hj).mpr (direct_parent_isAncestor hy'p))
      ((pos_le_pos_same_iff C).mpr (Nat.zero_le _))
  -- convexity: the parent is an ancestor of the first column of the copy
  have hancQ : isAncestor (expandRaw array.raw n) k (C.copyPosition a i)
      (C.copyPosition q 0) = true := by
    rcases convex hR (direct_parent_isAncestor hp) (Nat.le_of_lt hQlt)
        ((pos_le_pos_same_iff C).mpr (Nat.zero_le j))
        (Or.inr (cand_lead_of_lead C hj0 hlead)) with h | h
    · omega
    · exact h
  rcases Nat.lt_or_ge k C.maximalRow with hkm | hkm
  · have hchain := chain_lead C hkm (h3 hkm)
    have hAq := hchain a q hq ha
    have hEq1 : C.copyPosition a 0 = C.copyPosition a i ∨
        isAncestor (expandRaw array.raw n) k (C.copyPosition a 0) (C.copyPosition a i) =
          true := by
      rcases Nat.eq_zero_or_pos i with h0 | hi0
      · subst h0
        exact Or.inl rfl
      · exact Or.inr (anc_of_anc_of_anc_of_lt hAq hancQ ((pos_lt_pos_same_iff C).mpr hi0))
    have hEq0 : C.copyPosition 0 0 = C.copyPosition a 0 ∨
        isAncestor (expandRaw array.raw n) k (C.copyPosition 0 0) (C.copyPosition a 0) =
          true := by
      rcases Nat.eq_zero_or_pos a with h0 | ha0
      · subst h0
        exact Or.inl rfl
      · exact Or.inr (hchain 0 a (by omega) ha0)
    have hPa : C.copyPosition 0 0 = C.copyPosition a i ∨
        isAncestor (expandRaw array.raw n) k (C.copyPosition 0 0) (C.copyPosition a i) =
          true := by
      rcases hEq0 with h0 | h0 <;> rcases hEq1 with h1' | h1'
      · exact Or.inl (h0.trans h1')
      · rw [h0]
        exact Or.inr h1'
      · rw [← h1']
        exact Or.inr h0
      · exact Or.inr (isAncestor_trans h0 h1')
    have hfin : isAncestor (expandRaw array.raw n) k (C.copyPosition 0 0)
        (C.copyPosition q j) = true := by
      rcases hPa with h0 | h0
      · rw [h0]
        exact direct_parent_isAncestor hp
      · exact isAncestor_trans h0 (direct_parent_isAncestor hp)
    have hval := anc_val_lt hfin
    rw [pos_zero_zero C, val_R_prefix C n C.parentColumn_lt_lastIndex, htgt] at hval
    omega
  · have := h4 hkm k hkm q (C.copyPosition a i) (by omega) hancQ
    have := p_le_pos C a i
    omega

/-! ### C6 -/

private theorem passing_aux {n k : Nat} (h5 : Claim5 C n k) {a b i : Nat} (hab : a < b)
    (hi : i < C.blockLength) :
    ∀ j, j < C.blockLength →
      isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition b j) = true →
      isAncestor (expandRaw array.raw n) k (C.copyPosition a i) (C.copyPosition b 0) = true ∧
        (C.copyPosition b 0 = C.copyPosition b j ∨
          isAncestor (expandRaw array.raw n) k (C.copyPosition b 0) (C.copyPosition b j) =
            true) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j IH =>
    intro hj h
    rcases Nat.eq_zero_or_pos j with h0 | hj0
    · subst h0
      exact ⟨h, Or.inl rfl⟩
    obtain ⟨u, hu, hui⟩ := isAncestor_eq_true_iff_parent.mp h
    have hle : C.copyPosition a i ≤ u := by
      rcases hui with h' | h'
      · omega
      · exact Nat.le_of_lt (isAncestor_lt h')
    rcases h5 b j u hj hj0 hu with hG | ⟨i', rfl⟩
    · have := p_le_pos C a i
      omega
    · have hlt : i' < j := (pos_lt_pos_same_iff C).mp (parent_some_lt hu)
      have hne : C.copyPosition a i ≠ C.copyPosition b i' :=
        Nat.ne_of_lt (pos_lt_pos_of_lt C hab hi)
      have hanc : isAncestor (expandRaw array.raw n) k (C.copyPosition a i)
          (C.copyPosition b i') = true := by
        rcases hui with h' | h'
        · exact absurd h' hne
        · exact h'
      obtain ⟨hA', hT⟩ := IH i' hlt (by omega) hanc
      refine ⟨hA', Or.inr ?_⟩
      rcases hT with h' | h'
      · rw [h']
        exact direct_parent_isAncestor hu
      · exact isAncestor_trans h' (direct_parent_isAncestor hu)

theorem ancEq_transport {n k q q' i j : Nat} (h1 : Claim1 C n k) (hq : q ≤ n) (hq' : q' ≤ n)
    (hi : i < C.blockLength) (hj : j < C.blockLength)
    (h : C.copyPosition q i = C.copyPosition q j ∨
      isAncestor (expandRaw array.raw n) k (C.copyPosition q i) (C.copyPosition q j) = true) :
    C.copyPosition q' i = C.copyPosition q' j ∨
      isAncestor (expandRaw array.raw n) k (C.copyPosition q' i) (C.copyPosition q' j) =
        true := by
  rcases h with h | h
  · have := (pos_inj C hi hj h).2
    subst this
    exact Or.inl rfl
  · exact Or.inr ((h1 q' hq' i j hi hj).mpr ((h1 q hq i j hi hj).mp h))

theorem claim6_of {n k : Nat} (h1 : Claim1 C n k) (h5 : Claim5 C n k)
    (h3 : k < C.maximalRow → Claim3 C n k) (h4 : C.maximalRow ≤ k → Claim4 C n) :
    Claim6 C n k := by
  intro a b hab hb i j hi hj
  rcases Nat.lt_or_ge k C.maximalRow with hk | hk
  · have hbr := chain_lead C hk (h3 hk) b (b + 1) hb (Nat.lt_succ_self b)
    constructor
    · intro h
      obtain ⟨hA', hT⟩ := passing_aux C h5 hab hi j hj h
      have hT' := ancEq_transport C h1 (q := b) (q' := b + 1) (by omega) hb
        C.blockLength_pos hj hT
      have hfirst := isAncestor_trans hA' hbr
      rcases hT' with h' | h'
      · rw [← h']
        exact hfirst
      · exact isAncestor_trans hfirst h'
    · intro h
      obtain ⟨hA', hT⟩ := passing_aux C h5 (show a < b + 1 by omega) hi j hj h
      have hA'' := anc_of_anc_of_anc_of_lt hA' hbr (pos_lt_pos_of_lt C hab hi)
      have hT' := ancEq_transport C h1 (q := b + 1) (q' := b) hb (by omega)
        C.blockLength_pos hj hT
      rcases hT' with h' | h'
      · rw [← h']
        exact hA''
      · exact isAncestor_trans hA'' h'
  · have h4' := h4 hk
    have hp := p_le_pos C a i
    constructor
    · intro h
      obtain ⟨hA', -⟩ := passing_aux C h5 hab hi j hj h
      have := h4' k hk b (C.copyPosition a i) (by omega) hA'
      omega
    · intro h
      obtain ⟨hA', -⟩ := passing_aux C h5 (show a < b + 1 by omega) hi j hj h
      have := h4' k hk (b + 1) (C.copyPosition a i) (by omega) hA'
      omega

/-! ### C2 -/

theorem claim2_asc {n k q j E : Nat}
    (h1 : Claim1 C n k) (h3 : k < C.maximalRow → Claim3 C n k) (hq : q ≤ n) (hq0 : 0 < q)
    (hj : j < C.blockLength) (hE : E < C.parentColumn) (hasc : Asc C k j) :
    isAncestor (expandRaw array.raw n) k E (C.copyPosition q j) = true ↔
      isAncestor array.raw k E (C.parentColumn + j) = true := by
  obtain ⟨hk, hj'⟩ := (asc_iff C).mp hasc
  have hlead := chain_lead C hk (h3 hk) 0 q hq hq0
  rw [pos_zero_zero C] at hlead
  have htail : C.copyPosition q 0 = C.copyPosition q j ∨
      isAncestor (expandRaw array.raw n) k (C.copyPosition q 0) (C.copyPosition q j) = true := by
    rcases hj' with h | h
    · subst h
      exact Or.inl rfl
    · right
      apply (h1 q hq 0 j C.blockLength_pos hj).mpr
      rw [Nat.add_zero]
      exact h
  have hbp : isAncestor (expandRaw array.raw n) k C.parentColumn (C.copyPosition q j) =
      true := by
    rcases htail with h | h
    · rw [← h]
      exact hlead
    · exact isAncestor_trans hlead h
  have hpc := C.parentColumn_lt_lastIndex
  constructor
  · intro h
    have hEp := anc_of_anc_of_anc_of_lt h hbp hE
    rw [anc_R_prefix C n k E hpc] at hEp
    rcases hj' with h' | h'
    · subst h'
      rw [Nat.add_zero]
      exact hEp
    · exact isAncestor_trans hEp h'
  · intro h
    have hEpA : isAncestor array.raw k E C.parentColumn = true := by
      rcases hj' with h' | h'
      · subst h'
        rw [Nat.add_zero] at h
        exact h
      · exact anc_of_anc_of_anc_of_lt h h' hE
    rw [← anc_R_prefix C n k E hpc] at hEpA
    exact isAncestor_trans hEpA hbp

theorem cand_agree {n k q i E : Nat} (h2low : ∀ h, h < k → Claim2 C n h) (hq : q ≤ n)
    (hi : i < C.blockLength) (hE : E < C.parentColumn) :
    Cand (expandRaw array.raw n) k E (C.copyPosition q i) ↔
      Cand array.raw k E (C.parentColumn + i) := by
  cases k with
  | zero =>
      have := p_le_pos C q i
      show E < C.copyPosition q i ↔ E < C.parentColumn + i
      exact ⟨fun _ => by omega, fun _ => by omega⟩
  | succ h => exact h2low h (Nat.lt_succ_self h) q hq i E hi hE

theorem parent_agree {H : Nat} (hA : UniformHeight H array.raw) {n k q i y : Nat}
    (h2low : ∀ h, h < k → Claim2 C n h) (hq : q ≤ n) (hi : i < C.blockLength)
    (hnasc : ¬ Asc C k i)
    (hnoR : ∀ z, C.parentColumn ≤ z → z < C.copyPosition q i →
      Cand (expandRaw array.raw n) k z (C.copyPosition q i) →
      val (expandRaw array.raw n) z k < val (expandRaw array.raw n) (C.copyPosition q i) k →
        False)
    (hnoA : ∀ z, C.parentColumn ≤ z → z < C.parentColumn + i →
      Cand array.raw k z (C.parentColumn + i) →
      val array.raw z k < val array.raw (C.parentColumn + i) k → False)
    (hy : y < C.parentColumn) :
    parent k (expandRaw array.raw n) (C.copyPosition q i) = some y ↔
      parent k array.raw (C.parentColumn + i) = some y := by
  have hR : UniformHeight H (expandRaw array.raw n) := uniformHeight_expandRaw hA
  have hple := p_le_pos C q i
  have hLA := length_A C
  have hic := lt_last_of_lt_s C hi
  have hpc := C.parentColumn_lt_lastIndex
  have hcoly : val (expandRaw array.raw n) y k = val array.raw y k :=
    val_R_prefix C n (by omega)
  constructor
  · intro hp
    have hk := lt_height_of_parent hR hp
    have hcolT := val_copy_not_asc C hA hq hi hk hnasc
    obtain ⟨_, _, hc, hv, hMax⟩ := (parent_eq_some_iff hR hk).mp hp
    refine (parent_eq_some_iff hA hk).mpr ⟨by omega, by omega,
      (cand_agree C h2low hq hi hy).mp hc, by rw [← hcolT, ← hcoly]; exact hv, ?_⟩
    intro z hz1 hz2 hz3
    rcases Nat.lt_or_ge z C.parentColumn with hzp | hzp
    · have hcz := (cand_agree C h2low hq hi hzp).mpr hz3
      have hmx := hMax z hz1 (by omega) hcz
      rw [hcolT, val_R_prefix C n (by omega)] at hmx
      exact hmx
    · exact Nat.le_of_not_lt (fun hcc => hnoA z hzp hz2 hz3 hcc)
  · intro hp
    have hk := lt_height_of_parent hA hp
    have hcolT := val_copy_not_asc C hA hq hi hk hnasc
    obtain ⟨_, _, hc, hv, hMax⟩ := (parent_eq_some_iff hA hk).mp hp
    refine (parent_eq_some_iff hR hk).mpr ⟨pos_lt_length_R C hq hi, by omega,
      (cand_agree C h2low hq hi hy).mpr hc, by rw [hcolT, hcoly]; exact hv, ?_⟩
    intro z hz1 hz2 hz3
    rcases Nat.lt_or_ge z C.parentColumn with hzp | hzp
    · have hcz := (cand_agree C h2low hq hi hzp).mp hz3
      have hmx := hMax z hz1 (by omega) hcz
      rw [hcolT, val_R_prefix C n (by omega)]
      exact hmx
    · exact Nat.le_of_not_lt (fun hcc => hnoR z hzp hz2 hz3 hcc)

/-- A column of a copy whose parents (in `A[n]` and in `A`) are both good has the same parent
in `A[n]` as its original in `A`. -/
theorem parent_eq_root {H : Nat} (hA : UniformHeight H array.raw) {n k q i : Nat}
    (h2low : ∀ h, h < k → Claim2 C n h) (hq : q ≤ n) (hi : i < C.blockLength)
    (hnasc : ¬ Asc C k i)
    (hminR : ∀ y, parent k (expandRaw array.raw n) (C.copyPosition q i) = some y →
      y < C.parentColumn)
    (hminA : ∀ y, parent k array.raw (C.parentColumn + i) = some y → y < C.parentColumn) :
    parent k (expandRaw array.raw n) (C.copyPosition q i) =
      parent k array.raw (C.parentColumn + i) := by
  have hR : UniformHeight H (expandRaw array.raw n) := uniformHeight_expandRaw hA
  have hLA := length_A C
  have hic := lt_last_of_lt_s C hi
  have hnoR : ∀ z, C.parentColumn ≤ z → z < C.copyPosition q i →
      Cand (expandRaw array.raw n) k z (C.copyPosition q i) →
      val (expandRaw array.raw n) z k < val (expandRaw array.raw n) (C.copyPosition q i) k →
        False := by
    intro z hz _ hc hv
    obtain ⟨u, hu, hzu⟩ := exists_parent_of_valid hR (pos_lt_length_R C hq hi)
      (lt_height_of_val_lt hR hv) hc hv
    have := hminR u hu
    omega
  have hnoA : ∀ z, C.parentColumn ≤ z → z < C.parentColumn + i →
      Cand array.raw k z (C.parentColumn + i) →
      val array.raw z k < val array.raw (C.parentColumn + i) k → False := by
    intro z hz _ hc hv
    obtain ⟨u, hu, hzu⟩ := exists_parent_of_valid hA (by omega)
      (lt_height_of_val_lt hA hv) hc hv
    have := hminA u hu
    omega
  cases hR' : parent k (expandRaw array.raw n) (C.copyPosition q i) with
  | none =>
      cases hA' : parent k array.raw (C.parentColumn + i) with
      | none => rfl
      | some y =>
          have := (parent_agree C hA h2low hq hi hnasc hnoR hnoA (hminA y hA')).mpr hA'
          rw [hR'] at this
          cases this
  | some y =>
      exact ((parent_agree C hA h2low hq hi hnasc hnoR hnoA (hminR y hR')).mp hR').symm

theorem anc_transfer_root {H : Nat} (hA : UniformHeight H array.raw) {n k q i : Nat}
    (h2low : ∀ h, h < k → Claim2 C n h) (hq : q ≤ n) (hi : i < C.blockLength)
    (hnasc : ¬ Asc C k i)
    (hminR : ∀ y, parent k (expandRaw array.raw n) (C.copyPosition q i) = some y →
      y < C.parentColumn)
    (hminA : ∀ y, parent k array.raw (C.parentColumn + i) = some y → y < C.parentColumn)
    (E : Nat) :
    isAncestor (expandRaw array.raw n) k E (C.copyPosition q i) = true ↔
      isAncestor array.raw k E (C.parentColumn + i) = true := by
  have hpc := C.parentColumn_lt_lastIndex
  have hEq := parent_eq_root C hA h2low hq hi hnasc hminR hminA
  constructor
  · intro h
    obtain ⟨u, hu, hEu⟩ := isAncestor_eq_true_iff_parent.mp h
    have hul := hminR u hu
    rw [hEq] at hu
    rcases hEu with h' | h'
    · rw [h']
      exact direct_parent_isAncestor hu
    · rw [anc_R_prefix C n k E (show u < C.lastIndex by omega)] at h'
      exact isAncestor_trans h' (direct_parent_isAncestor hu)
  · intro h
    obtain ⟨u, hu, hEu⟩ := isAncestor_eq_true_iff_parent.mp h
    have hul := hminA u hu
    rw [← hEq] at hu
    rcases hEu with h' | h'
    · rw [h']
      exact direct_parent_isAncestor hu
    · rw [← anc_R_prefix C n k E (show u < C.lastIndex by omega)] at h'
      exact isAncestor_trans h' (direct_parent_isAncestor hu)

theorem claim2_not_asc {H : Nat} (hA : UniformHeight H array.raw) {n k q j E : Nat}
    (h2low : ∀ h, h < k → Claim2 C n h) (h1 : Claim1 C n k) (h5 : Claim5 C n k)
    (h4 : C.maximalRow ≤ k → Claim4 C n) (hq : q ≤ n) (hq0 : 0 < q)
    (hj : j < C.blockLength) (hE : E < C.parentColumn) (hnasc : ¬ Asc C k j) :
    isAncestor (expandRaw array.raw n) k E (C.copyPosition q j) = true ↔
      isAncestor array.raw k E (C.parentColumn + j) = true := by
  obtain ⟨i₀, ⟨hi₀s, hi₀eq⟩, hmin⟩ := exists_least
    (P := fun i => i < C.blockLength ∧ (C.parentColumn + i = C.parentColumn + j ∨
      isAncestor array.raw k (C.parentColumn + i) (C.parentColumn + j) = true))
    (j := j) ⟨hj, Or.inl rfl⟩
  have hi₀j : i₀ ≤ j := by
    rcases hi₀eq with h | h
    · omega
    · have := isAncestor_lt h
      omega
  -- the column `p+i₀` does not ascend either
  have hnasc0 : ¬ Asc C k i₀ := by
    intro hasc
    apply hnasc
    rcases hi₀eq with h | h
    · have : i₀ = j := by omega
      rw [← this]
      exact hasc
    · exact (asc_iff_of_anc C h).mp hasc
  -- its parent in `A` is good
  have hminA : ∀ y, parent k array.raw (C.parentColumn + i₀) = some y → y < C.parentColumn := by
    intro y hp
    apply Nat.lt_of_not_le
    intro hy
    have hylt := parent_some_lt hp
    apply hmin (y - C.parentColumn) (by omega)
    refine ⟨by omega, Or.inr ?_⟩
    have hyEq : C.parentColumn + (y - C.parentColumn) = y := by omega
    rw [hyEq]
    rcases hi₀eq with h | h
    · rw [← h]
      exact direct_parent_isAncestor hp
    · exact isAncestor_trans (direct_parent_isAncestor hp) h
  -- its parent in `A[n]` is good
  have hminR : ∀ y, parent k (expandRaw array.raw n) (C.copyPosition q i₀) = some y →
      y < C.parentColumn := by
    intro y hp
    rcases Nat.eq_zero_or_pos i₀ with hz | hpos
    · have hkm : C.maximalRow ≤ k := by
        apply Nat.le_of_not_lt
        intro hlt
        exact hnasc0 (by rw [hz]; exact asc_zero C hlt)
      rw [hz] at hp
      exact h4 hkm k hkm q y hq0 (direct_parent_isAncestor hp)
    · rcases h5 q i₀ y hi₀s hpos hp with hg | ⟨i, rfl⟩
      · exact hg
      · exfalso
        have hii : i < i₀ := (pos_lt_pos_same_iff C).mp (parent_some_lt hp)
        have hiA := (h1 q hq i i₀ (by omega) hi₀s).mp (direct_parent_isAncestor hp)
        apply hmin i hii
        refine ⟨by omega, Or.inr ?_⟩
        rcases hi₀eq with h | h
        · rw [← h]
          exact hiA
        · exact isAncestor_trans hiA h
  -- collapse `p+j` to `p+i₀` on both sides
  have hTeq : C.copyPosition q i₀ = C.copyPosition q j ∨
      isAncestor (expandRaw array.raw n) k (C.copyPosition q i₀) (C.copyPosition q j) =
        true := by
    rcases hi₀eq with h | h
    · have : i₀ = j := by omega
      rw [this]
      exact Or.inl rfl
    · exact Or.inr ((h1 q hq i₀ j hi₀s hj).mpr h)
  have hcollR : isAncestor (expandRaw array.raw n) k E (C.copyPosition q j) = true ↔
      isAncestor (expandRaw array.raw n) k E (C.copyPosition q i₀) = true := by
    constructor
    · intro h
      rcases hTeq with heq | hanc
      · rw [heq]
        exact h
      · exact anc_of_anc_of_anc_of_lt h hanc (by have := p_le_pos C q i₀; omega)
    · intro h
      rcases hTeq with heq | hanc
      · rw [← heq]
        exact h
      · exact isAncestor_trans h hanc
  have hcollA : isAncestor array.raw k E (C.parentColumn + j) = true ↔
      isAncestor array.raw k E (C.parentColumn + i₀) = true := by
    constructor
    · intro h
      rcases hi₀eq with heq | hanc
      · rw [heq]
        exact h
      · exact anc_of_anc_of_anc_of_lt h hanc (by omega)
    · intro h
      rcases hi₀eq with heq | hanc
      · rw [← heq]
        exact h
      · exact isAncestor_trans h hanc
  rw [hcollR, hcollA]
  exact anc_transfer_root C hA h2low hq hi₀s hnasc0 hminR hminA E

theorem claim2_of {H : Nat} (hA : UniformHeight H array.raw) {n k : Nat}
    (h2low : ∀ h, h < k → Claim2 C n h) (h1 : Claim1 C n k) (h5 : Claim5 C n k)
    (h3 : k < C.maximalRow → Claim3 C n k) (h4 : C.maximalRow ≤ k → Claim4 C n) :
    Claim2 C n k := by
  intro q hq j E hj hE
  rcases Nat.eq_zero_or_pos q with h0 | hq0
  · subst h0
    rw [C.copyPosition_zero j, anc_R_prefix C n k E (lt_last_of_lt_s C hj)]
  · by_cases hasc : Asc C k j
    · exact claim2_asc C h1 h3 hq hq0 hj hE hasc
    · exact claim2_not_asc C hA h2low h1 h5 h4 hq hq0 hj hE hasc

/-! ### Assembly -/

/-- Stage 1: the rows below `m₀`, where C4 is not needed. -/
theorem stage1 {H : Nat} (hA : UniformHeight H array.raw) (n : Nat) :
    ∀ k, k < C.maximalRow →
      Claim1 C n k ∧ Claim3 C n k ∧ Claim5 C n k ∧ Claim2 C n k ∧ Claim6 C n k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    have hIH : ∀ h, h < k →
        Claim1 C n h ∧ Claim3 C n h ∧ Claim5 C n h ∧ Claim2 C n h ∧ Claim6 C n h :=
      fun h hh => ih h hh (by omega)
    have c1 : Claim1 C n k := claim1_of_lower C hA (fun h hh => (hIH h hh).1)
    have c3 : Claim3 C n k := claim3_of C hA hk c1 (fun k' hk' => (hIH k' (by omega)).2.1)
    have c5 : Claim5 C n k := claim5_of C hA (fun h hh => ⟨(hIH h hh).1, (hIH h hh).2.2.1⟩)
      c1 (fun _ => c3) (fun hc => absurd hc (by omega))
    have c2 : Claim2 C n k := claim2_of C hA (fun h hh => (hIH h hh).2.2.2.1) c1 c5
      (fun _ => c3) (fun hc => absurd hc (by omega))
    exact ⟨c1, c3, c5, c2, claim6_of C c1 c5 (fun _ => c3) (fun hc => absurd hc (by omega))⟩

/-- Stage 2: C4. -/
theorem claim4 {H : Nat} (hA : UniformHeight H array.raw) (n : Nat) : Claim4 C n := by
  rcases Nat.eq_zero_or_pos C.maximalRow with hm | hm
  · exact claim4_of_zero C hA hm
  · have h := stage1 C hA n (C.maximalRow - 1) (by omega)
    exact claim4_of_pos C hA hm h.2.1 h.2.2.2.2

/-- Stage 3: all rows. -/
theorem stage3 {H : Nat} (hA : UniformHeight H array.raw) (n : Nat) :
    ∀ k, Claim1 C n k ∧ Claim5 C n k ∧ Claim2 C n k ∧ Claim6 C n k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rcases Nat.lt_or_ge k C.maximalRow with hk | hk
    · have h := stage1 C hA n k hk
      exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have c1 : Claim1 C n k := claim1_of_lower C hA (fun h hh => (ih h hh).1)
      have c5 : Claim5 C n k := claim5_of C hA (fun h hh => ⟨(ih h hh).1, (ih h hh).2.1⟩)
        c1 (fun hc => absurd hc (by omega)) (fun _ => claim4 C hA n)
      have c2 : Claim2 C n k := claim2_of C hA (fun h hh => (ih h hh).2.2.1) c1 c5
        (fun hc => absurd hc (by omega)) (fun _ => claim4 C hA n)
      exact ⟨c1, c5, c2,
        claim6_of C c1 c5 (fun hc => absurd hc (by omega)) (fun _ => claim4 C hA n)⟩

end Claims

end CopyLemma

/-! ## Lemma 2.5 in the form the core uses -/

namespace ExpansionContext

/-- BMS Lemma 2.5 at one row `row` for `A[expansionIndex]`. -/
structure Lemma25AtRow {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex row : Nat) : Prop where
  good_to_copy :
    ∀ {goodColumn localColumn},
      goodColumn < context.parentColumn →
      localColumn < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition 0 localColumn) =
        isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition expansionIndex localColumn)
  inside_copy :
    ∀ {leftLocal rightLocal},
      leftLocal < context.blockLength →
      rightLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition expansionIndex leftLocal)
          (context.copyPosition expansionIndex rightLocal)
  previous_to_next :
    0 < expansionIndex → row < context.maximalRow →
    ∀ {localColumn}, localColumn < context.blockLength →
      isAncestor array.raw row (context.parentColumn + localColumn)
          context.lastIndex =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition (expansionIndex - 1) localColumn)
          (context.copyPosition expansionIndex 0)
  parent_locality :
    ∀ {localColumn found},
      0 < localColumn → localColumn < context.blockLength →
      parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex localColumn) = some found →
      found < context.parentColumn ∨ context.InCopy expansionIndex found

/-- BMS Lemma 2.5 at every row. -/
def Lemma25 {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) : Prop :=
  ∀ row, Lemma25AtRow context expansionIndex row

theorem first_copy_ancestor_of_lt {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row earlierCopy laterCopy : Nat}
    (hLater : laterCopy ≤ expansionIndex)
    (hCopies : earlierCopy < laterCopy)
    (hRow : row < context.maximalRow) :
    isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition earlierCopy 0)
      (context.copyPosition laterCopy 0) = true := by
  obtain ⟨H, hA⟩ := rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
  rw [CopyLemma.isAncestor_expand_eq]
  exact CopyLemma.chain_lead context hRow
    (CopyLemma.stage1 context hA expansionIndex row hRow).2.1 earlierCopy laterCopy hLater
    hCopies

theorem parent_first_copies_eq_of_maximalRow_le
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hBelow : ∀ lowerRow, lowerRow < row → ∀ {goodColumn},
      goodColumn < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition 0 0) =
        isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition expansionIndex 0)) :
    parent row (array.expand expansionIndex).raw
        (context.copyPosition 0 0) =
      parent row (array.expand expansionIndex).raw
        (context.copyPosition expansionIndex 0) := by
  -- `hBelow` is not needed: the claims C2 below `row` are proved outright.
  have _hBelow := hBelow
  obtain ⟨H, hA⟩ := rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
  rw [CopyLemma.parent_expand_eq, CopyLemma.parent_expand_eq]
  rcases Nat.eq_zero_or_pos expansionIndex with h0 | hn
  · subst h0
    rfl
  · have hnasc : ¬ CopyLemma.Asc context row 0 := CopyLemma.not_asc_of_ge context hMaximalRow
    have hminR : ∀ y, parent row (expandRaw array.raw expansionIndex)
        (context.copyPosition expansionIndex 0) = some y → y < context.parentColumn :=
      fun y hp => CopyLemma.claim4 context hA expansionIndex row hMaximalRow expansionIndex y hn
        (direct_parent_isAncestor hp)
    have hminA : ∀ y, parent row array.raw (context.parentColumn + 0) = some y →
        y < context.parentColumn := fun y hp => by
      have := parent_some_lt hp
      omega
    rw [CopyLemma.pos_zero_zero context,
      CopyLemma.parent_R_prefix context expansionIndex row context.parentColumn_lt_lastIndex,
      CopyLemma.parent_eq_root context hA
        (fun h _ => (CopyLemma.stage3 context hA expansionIndex h).2.2.1)
        (Nat.le_refl expansionIndex) context.blockLength_pos hnasc hminR hminA,
      Nat.add_zero]

theorem good_to_first_copies_all_rows
    {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) : ∀ row {goodColumn},
      goodColumn < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition 0 0) =
        isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition expansionIndex 0) := by
  intro row goodColumn hGood
  obtain ⟨H, hA⟩ := rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
  rw [CopyLemma.isAncestor_expand_eq, CopyLemma.isAncestor_expand_eq]
  have h2 := (CopyLemma.stage3 context hA expansionIndex row).2.2.1
  apply bool_eq_of_true_iff
  rw [h2 0 (Nat.zero_le _) 0 goodColumn context.blockLength_pos hGood,
    h2 expansionIndex (Nat.le_refl _) 0 goodColumn context.blockLength_pos hGood]

theorem lemma25_all {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) :
    Lemma25 context expansionIndex := by
  intro row
  obtain ⟨H, hA⟩ := rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
  have hS := CopyLemma.stage3 context hA expansionIndex row
  constructor
  · intro goodColumn localColumn hGood hLocal
    rw [CopyLemma.isAncestor_expand_eq, CopyLemma.isAncestor_expand_eq]
    apply bool_eq_of_true_iff
    rw [hS.2.2.1 0 (Nat.zero_le _) localColumn goodColumn hLocal hGood,
      hS.2.2.1 expansionIndex (Nat.le_refl _) localColumn goodColumn hLocal hGood]
  · intro leftLocal rightLocal hLeft hRight
    rw [CopyLemma.isAncestor_expand_eq, CopyLemma.isAncestor_expand_eq]
    apply bool_eq_of_true_iff
    rw [hS.1 0 (Nat.zero_le _) leftLocal rightLocal hLeft hRight,
      hS.1 expansionIndex (Nat.le_refl _) leftLocal rightLocal hLeft hRight]
  · intro hIndex hRow localColumn hLocal
    rw [CopyLemma.isAncestor_expand_eq]
    apply bool_eq_of_true_iff
    exact ((CopyLemma.stage1 context hA expansionIndex row hRow).2.1 expansionIndex
      (Nat.le_refl _) hIndex localColumn hLocal).symm
  · intro localColumn found hPos hLocal hParent
    rw [CopyLemma.parent_expand_eq] at hParent
    rcases hS.2.1 expansionIndex localColumn found hLocal hPos hParent with hG | ⟨i, rfl⟩
    · exact Or.inl hG
    · right
      have hlt := (CopyLemma.pos_lt_pos_same_iff context).mp (parent_some_lt hParent)
      exact context.inCopy_iff_exists_copyPosition.mpr ⟨i, by omega, rfl⟩

end ExpansionContext

end Por.BMS
