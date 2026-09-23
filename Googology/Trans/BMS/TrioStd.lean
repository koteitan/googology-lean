import Googology.Trans.BMS.Trio
import Googology.Trans.BMS.Reach
import Googology.Trans.BMS.ZeroRow
import Googology.Trans.BMS.Calibrate
import Googology.Trans.BMS.Append
import Googology.Trans.BMS.Equiv

/-!
# The trio matrix of `ψ_0(Ω_α)` is a standard form, for `α < ε₀`

`BMS/Trio.lean` transcribes the map `α ↦ M(α)` of
[koteitan/trio](https://github.com/koteitan/trio) (its
[algorithm for `α < ε₀`](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md))
and checks it with `#guard`.  This file proves what the `#guard`s and the
outside check with `bms -s` could only sample: **every `M(α)` is the entries of
a standard three-row array**, that is, it is reached from a generator
`(0,0,0)(1,1,1)⋯(n,n,n)` by expansions (`omegaIndexMatrix_std`,
`trioMatrix_std`, and `omegaIndexState`, the matrix as a state of `bmsL 2`).

The proof does not measure the three-row matrices by an ordinal.  It borrows
the descent that the one-row theory has already done: `reach_gen` in
`BMS/Reach.lean` says that a property of one-row matrices which holds at the
generators `(0)(1)⋯(n)` and survives every expansion holds at every standard
one-row matrix.  The property used is

    RTrio l  :=  M(read l) is reachable      (and read l is in Cantor shape),

so all that is needed is the local step: when the one-row matrix of `α` is
expanded, `M` of the result is reachable from `M(α)`.  That is
`step_add` / `step_mul`, by cases on the last summand, and each case is one
expansion of `M(α)` followed by cutting columns off the end (`reach3_prefix`:
a prefix of a reachable matrix is reachable, since `A[0]` drops the last
column).

* `α = β + 1`: `M(β)` is a prefix of `M(α)`.
* `α = β + ω^{X+1}`: the last column of `M(α)` is a root or a digit, `m₀ = 2`,
  the bad root is the add unit's anchor, and one expansion writes the add unit
  again, lifted by `(2, 1)` (`expandRL_anchor_root`, `expandRL_digit_unit`).
* the last summand of the exponent is `ω^{δ+1}`: the last column is an
  embedding column `(x, 0, 0)` whose parent is the digit, `m₀ = 0`, and one
  expansion copies the multiply unit (`expandRL_copy_block`).
* deeper: the expansion happens inside a primitive-sequence embedding and is
  the one-row expansion there (`expandRL_embed`, through `expandRL_one` and
  `expandRL_zeroRow`).

Two things make the cases local.  `expandRL_append_local`: a prefix does not
change an expansion whose bad root lies after it, as long as it does not
change `m₀`; this rests on `parR_shift`, parents inside a suffix do not see
the prefix.  And `exT`, the one-row expansion written on the terms, with
`expandL_unread` saying it is `expandL`.

Where the one-row expansion drops a leading `1` of an exponent (the term
`ω^{ω}` expands to `ω^{n+1}`, while the matrix `M(ω^ω)` expands to
`M(ω^{n+2})`), the target is a prefix of the expansion rather than equal to
it, and `reach3_prefix` absorbs the difference.

The generators reach the towers through `ψ_0(Ω_{ε₀})`
(`(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)`, `reach3_topE0`, six concrete
expansions checked by `decide`), whose `n`-th expansion is `M` of the `n`-th
one-row generator (`expandRL_topE0`, `omegaIndexMatrix_twr`).

Nothing here is taken from the Lean files of koteitan/trio: that project
proves termination of its own trio sequences and does not state this
standardness.
-/

namespace Googology.Trans.BMS
namespace TrioStd

open BM4 Pat
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### Reachable three-row matrices -/

/-- A three-row matrix is reachable when it is the entries of a standard
array: the states of `bmsL 2`. -/
def Reach3 (l : List (List Nat)) : Prop := ∃ A : Arr 3, Std 3 A ∧ entriesR A = l

theorem reach3_expand {l : List (List Nat)} (h : Reach3 l) (N : Nat) :
    Reach3 (expandRL 3 N l) := by
  obtain ⟨A, hA, hl⟩ := h
  exact ⟨expand A N, Std.step N hA, by rw [entriesR_expand (by decide), hl]⟩

theorem reach3_gen (n : Nat) :
    Reach3 ((List.range (n + 1)).map (fun i => List.replicate 3 i)) :=
  ⟨stair 3 n, Std.init n, entriesR_stair 3 n⟩

theorem map_getElem!_range {α : Type} [Inhabited α] (l : List α) :
    ∀ n, n ≤ l.length → (List.range n).map (fun i => l[i]!) = l.take n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, ih (by omega), List.map_singleton,
      getElem!_pos l m (by omega)]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl

theorem map_range_mul {α : Type} (L : Nat) (F : Nat → α) : ∀ M : Nat,
    (List.range (M * L)).map F
      = ((List.range M).map (fun c => (List.range L).map (fun s => F (c * L + s)))).flatten := by
  intro M
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ, List.map_append,
      List.flatten_append, List.map_map, List.map_singleton, List.flatten_singleton]
    rfl

/-- **Expansion with a bad root, copy by copy.** -/
theorem expandRL_some (r N : Nat) (l : List (List Nat)) (p : Nat) (hb : badRootR r l = some p) :
    expandRL r N l = l.take p ++ ((List.range (N + 1)).map (fun c =>
      (List.range (l.length - 1 - p)).map (fun s => (List.range r).map (fun k =>
        if decide (k < m0L r l) && ((p == p + s) || ancAtR l k p (p + s)) then
          (l[p + s]!)[k]! + c * ((l[l.length - 1]!)[k]! - (l[p]!)[k]!)
        else (l[p + s]!)[k]!)))).flatten := by
  have hp := badRootR_lt hb
  have hL : 0 < l.length - 1 - p := by omega
  rw [expandRL, hb]
  dsimp only
  rw [map_getElem!_range l p (by omega), map_range_mul _]
  congr 1
  refine congrArg List.flatten (List.map_congr_left (fun c _ => List.map_congr_left (fun s hs => ?_)))
  have hs' : s < l.length - 1 - p := List.mem_range.mp hs
  have h1 : (c * (l.length - 1 - p) + s) % (l.length - 1 - p) = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs']
  have h2 : (c * (l.length - 1 - p) + s) / (l.length - 1 - p) = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hs', Nat.zero_add]
  rw [h1, h2]

/-- Columns of height `r` are read back by their first `r` entries. -/
theorem col_eta {col : List Nat} {r : Nat} (h : col.length = r) :
    (List.range r).map (fun k => col[k]!) = col := by
  subst h; exact listEta col

theorem map_range_drop (l : List (List Nat)) (p : Nat) (hp : p + 1 < l.length) :
    (List.range (l.length - 1 - p)).map (fun s => l[p + s]!) = (l.drop p).dropLast := by
  rw [List.dropLast_eq_take, List.length_drop,
    ← map_getElem!_range (l.drop p) _ (by rw [List.length_drop]; omega),
    show l.length - p - 1 = l.length - 1 - p by omega]
  refine List.map_congr_left (fun s hs => ?_)
  have hs' := List.mem_range.mp hs
  rw [getElem!_pos (l.drop p) s (by rw [List.length_drop]; omega), List.getElem_drop,
    getElem!_pos l (p + s) (by omega)]

/-- **With `m₀ = 0`, the bad part is copied unchanged.** -/
theorem expandRL_m0_zero (r N : Nat) (l : List (List Nat)) (p : Nat)
    (hw : ∀ c ∈ l, c.length = r) (hb : badRootR r l = some p) (hm : m0L r l = 0) :
    expandRL r N l = l.take p ++ (List.replicate (N + 1) (l.drop p).dropLast).flatten := by
  have hp := badRootR_lt hb
  rw [expandRL_some r N l p hb, hm]
  congr 1
  rw [show List.replicate (N + 1) (l.drop p).dropLast
      = (List.range (N + 1)).map (fun _ => (l.drop p).dropLast) by simp]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  rw [← map_range_drop l p hp]
  refine List.map_congr_left (fun s hs => ?_)
  have hs' := List.mem_range.mp hs
  have hmem : l[p + s]! ∈ l := by
    rw [getElem!_pos l (p + s) (by omega)]; exact List.getElem_mem _
  simp only [Nat.not_lt_zero, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  exact col_eta (hw _ hmem)

/-- Expanding at `0` drops the last column. -/
theorem expandRL_zero (r : Nat) (l : List (List Nat)) (hw : ∀ c ∈ l, c.length = r) :
    expandRL r 0 l = l.dropLast := by
  cases hb : badRootR r l with
  | none => rw [expandRL, hb]
  | some p =>
    have hp := badRootR_lt hb
    rw [expandRL_some r 0 l p hb, List.range_one, List.map_singleton, List.flatten_singleton]
    have : (List.range (l.length - 1 - p)).map (fun s => (List.range r).map (fun k =>
        if decide (k < m0L r l) && ((p == p + s) || ancAtR l k p (p + s)) then
          (l[p + s]!)[k]! + 0 * ((l[l.length - 1]!)[k]! - (l[p]!)[k]!)
        else (l[p + s]!)[k]!)) = (l.drop p).dropLast := by
      rw [← map_range_drop l p hp]
      refine List.map_congr_left (fun s hs => ?_)
      have hs' := List.mem_range.mp hs
      have hmem : l[p + s]! ∈ l := by
        rw [getElem!_pos l (p + s) (by omega)]; exact List.getElem_mem _
      simp only [Nat.zero_mul, Nat.add_zero, ite_self]
      exact col_eta (hw _ hmem)
    rw [this, ← List.dropLast_append_of_ne_nil (by
      intro h; rw [List.drop_eq_nil_iff] at h; omega), List.take_append_drop]

theorem wf_append {A B : List (List Nat)} (hA : ∀ c ∈ A, c.length = 3)
    (hB : ∀ c ∈ B, c.length = 3) : ∀ c ∈ A ++ B, c.length = 3 := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hA c h
  · exact hB c h

theorem reach3_wf {l : List (List Nat)} (h : Reach3 l) : ∀ c ∈ l, c.length = 3 := by
  obtain ⟨A, _, rfl⟩ := h
  intro c hc
  rw [entriesR, List.mem_map] at hc
  obtain ⟨i, _, rfl⟩ := hc
  rw [List.length_map, List.length_range]

/-- **A prefix of a reachable matrix is reachable.** -/
theorem reach3_prefix : ∀ (m l : List (List Nat)), Reach3 (l ++ m) → Reach3 l := by
  intro m
  induction m with
  | nil => intro l h; rwa [List.append_nil] at h
  | cons c m ih =>
    intro l h
    have h1 : Reach3 (l ++ [c]) := ih (l ++ [c]) (by rwa [List.append_assoc])
    have h2 := reach3_expand h1 0
    rwa [expandRL_zero 3 _ (reach3_wf h1), List.dropLast_concat] at h2

/-! ### Parents inside a suffix -/

theorem tg_lt {R : Nat → Nat → Prop} (hlt : ∀ a b, R a b → a < b) {a b : Nat}
    (h : Relation.TransGen R a b) : a < b := by
  induction h with
  | single hr => exact hlt _ _ hr
  | tail _ hr ih => exact lt_trans ih (hlt _ _ hr)

theorem tg_shift {R R' : Nat → Nat → Prop} (n : Nat) (hlt : ∀ a b, R a b → a < b)
    (h : ∀ j i, R (n + j) (n + i) ↔ R' j i) :
    ∀ j i, Relation.TransGen R (n + j) (n + i) ↔ Relation.TransGen R' j i := by
  have key : ∀ a b, Relation.TransGen R a b → n ≤ a →
      Relation.TransGen R' (a - n) (b - n) := by
    intro a b hab
    induction hab with
    | single hr =>
      rename_i b
      intro ha
      have := hlt _ _ hr
      refine .single ((h _ _).mp ?_)
      rwa [Nat.add_sub_cancel' ha, Nat.add_sub_cancel' (by omega)]
    | tail hab' hr ih =>
      rename_i b c
      intro ha
      have h1 := tg_lt hlt hab'
      have h2 := hlt _ _ hr
      refine .tail (ih ha) ((h _ _).mp ?_)
      rwa [Nat.add_sub_cancel' (by omega), Nat.add_sub_cancel' (by omega)]
  intro j i
  constructor
  · intro hT
    have := key _ _ hT (by omega)
    rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at this
  · intro hT
    induction hT with
    | single hr => exact .single ((h _ _).mpr hr)
    | tail _ hr ih => exact .tail ih ((h _ _).mpr hr)

/-- **Parents inside a suffix do not see the prefix.** -/
theorem parR_shift (A B : List (List Nat)) : ∀ k j i,
    ParR (A ++ B) k (A.length + j) (A.length + i) ↔ ParR B k j i := by
  intro k
  induction k with
  | zero =>
    intro j i
    simp only [ParR, getElem!_append_right]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, fun j' hj1 hj2 => ?_⟩
      have := h3 (A.length + j') (by omega) (by omega)
      rwa [getElem!_append_right] at this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, fun j' hj1 hj2 => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, j' = A.length + d := ⟨j' - A.length, by omega⟩
      rw [getElem!_append_right]
      exact h3 d (by omega) (by omega)
  | succ m ih =>
    have htg := tg_shift A.length (fun _ _ h => ParR_lt h) ih
    intro j i
    simp only [ParR, getElem!_append_right]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨by omega, (htg j i).mp h2, h3, fun j' hj1 hj2 hj3 => ?_⟩
      have := h4 (A.length + j') (by omega) (by omega) ((htg j' i).mpr hj3)
      rwa [getElem!_append_right] at this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨by omega, (htg j i).mpr h2, h3, fun j' hj1 hj2 hj3 => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, j' = A.length + d := ⟨j' - A.length, by omega⟩
      rw [getElem!_append_right]
      exact h4 d (by omega) (by omega) ((htg d i).mp hj3)

theorem ancR_shift (A B : List (List Nat)) (k j i : Nat) :
    AncR (A ++ B) k (A.length + j) (A.length + i) ↔ AncR B k j i :=
  tg_shift A.length (fun _ _ h => ParR_lt h) (parR_shift A B k) j i

theorem ancAtR_shift (A B : List (List Nat)) (k j i : Nat) :
    ancAtR (A ++ B) k (A.length + j) (A.length + i) = ancAtR B k j i := by
  rw [Bool.eq_iff_iff, ancAtR_iff, ancAtR_iff]
  exact ancR_shift A B k j i

theorem parAtR_shift {A B : List (List Nat)} {k i j : Nat} (h : parAtR B k i = some j) :
    parAtR (A ++ B) k (A.length + i) = some (A.length + j) :=
  (parAtR_eq_some _ _ _ _).mpr ((parR_shift A B k j i).mpr ((parAtR_eq_some _ _ _ _).mp h))

theorem badRootR_eq {r : Nat} {l : List (List Nat)} (hne : l ≠ []) :
    badRootR r l = parAtR l (m0L r l) (l.length - 1) := by
  rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne)]

/-- **Expansion with the bad root in a suffix leaves the prefix alone**, as long
as the prefix does not change `m₀`. -/
theorem expandRL_append_local (r N : Nat) (A B : List (List Nat)) (p : Nat)
    (hb : badRootR r B = some p) (hm : m0L r (A ++ B) = m0L r B) :
    expandRL r N (A ++ B) = A ++ expandRL r N B := by
  have hp := badRootR_lt hb
  have hne : B ≠ [] := by intro h; rw [h] at hp; simp at hp
  have hlen : (A ++ B).length - 1 = A.length + (B.length - 1) := by
    rw [List.length_append]; omega
  have hb' : badRootR r (A ++ B) = some (A.length + p) := by
    rw [badRootR_eq (by simp [hne]), hm, hlen]
    rw [badRootR_eq hne] at hb
    exact parAtR_shift hb
  rw [expandRL_some r N (A ++ B) _ hb', expandRL_some r N B p hb, ← List.append_assoc,
    List.take_length_add_append, hm,
    show (A ++ B).length - 1 - (A.length + p) = B.length - 1 - p by
      rw [List.length_append]; omega, hlen]
  congr 1
  refine congrArg List.flatten (List.map_congr_left (fun c _ =>
    List.map_congr_left (fun s _ => List.map_congr_left (fun k _ => ?_))))
  have hbeq : ((A.length + p) == (A.length + p + s)) = (p == p + s) := by
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
  rw [hbeq, Nat.add_assoc, ancAtR_shift, getElem!_append_right, getElem!_append_right,
    getElem!_append_right]

/-! ### Parent facts -/

theorem parR0_exists (l : List (List Nat)) {j0 i : Nat} (hj : j0 < i)
    (hx : (l[j0]!)[0]! < (l[i]!)[0]!) : ∃ j, j0 ≤ j ∧ ParR l 0 j i := by
  classical
  let P : Nat → Prop := fun j => (l[j]!)[0]! < (l[i]!)[0]!
  refine ⟨Nat.findGreatest P (i - 1), Nat.le_findGreatest (by omega) hx, ?_⟩
  have hle : Nat.findGreatest P (i - 1) ≤ i - 1 := Nat.findGreatest_le _
  refine ⟨by omega, Nat.findGreatest_spec (P := P) (m := j0) (by omega) hx, fun j' h1 h2 => ?_⟩
  have := Nat.findGreatest_is_greatest (P := P) h1 (by omega)
  exact Nat.le_of_not_lt this

theorem parR_unique {l : List (List Nat)} {k j j' i : Nat} (h : ParR l k j i)
    (h' : ParR l k j' i) : j = j' := by
  cases k with
  | zero =>
    rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd (h.2.2 j' hlt h'.1) (Nat.not_le.mpr h'.2.1)
    · exact heq
    · exact absurd (h'.2.2 j hgt h.1) (Nat.not_le.mpr h.2.1)
  | succ m =>
    rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd (h.2.2.2 j' hlt h'.1 h'.2.1) (Nat.not_le.mpr h'.2.2.1)
    · exact heq
    · exact absurd (h'.2.2.2 j hgt h.1 h.2.1) (Nat.not_le.mpr h.2.2.1)

theorem not_parR_of_zero {l : List (List Nat)} {k j i : Nat} (hz : (l[i]!)[k + 1]! = 0) :
    ¬ ParR l (k + 1) j i := by
  intro h
  have := h.2.2.1
  omega

theorem parAtR_none_of_zero {l : List (List Nat)} {k i : Nat} (hz : (l[i]!)[k + 1]! = 0) :
    parAtR l (k + 1) i = none := by
  cases h : parAtR l (k + 1) i with
  | none => rfl
  | some j => exact absurd ((parAtR_eq_some _ _ _ _).mp h) (not_parR_of_zero hz)

theorem not_ancR_of_zero {l : List (List Nat)} {k j i : Nat} (hz : (l[i]!)[k + 1]! = 0) :
    ¬ AncR l (k + 1) j i := by
  intro h
  obtain ⟨c, _, hc⟩ := Relation.TransGen.tail'_iff.mp h
  exact not_parR_of_zero hz hc

theorem anc0_lt {l : List (List Nat)} {j i : Nat} (h : AncR l 0 j i) :
    (l[j]!)[0]! < (l[i]!)[0]! := by
  induction h with
  | single hr => exact hr.2.1
  | tail _ hr ih => exact lt_trans ih hr.2.1

/-- A first column below every later one is a row-`0` ancestor of each of them. -/
theorem anc0_of_min (l : List (List Nat)) (hmin : ∀ j, 0 < j → j < l.length →
    (l[0]!)[0]! < (l[j]!)[0]!) : ∀ i, 0 < i → i < l.length → AncR l 0 0 i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hil
    obtain ⟨j, -, hj⟩ := parR0_exists l hi (hmin i hi hil)
    have hji : j < i := hj.1
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; exact .single hj
    · exact .tail (ih j hji hpos (by omega)) hj

theorem m0L_three_two {l : List (List Nat)} (h : (parAtR l 2 (l.length - 1)).isSome = true) :
    m0L 3 l = 2 := by
  rw [m0L]
  exact Nat.findGreatest_eq h

theorem m0L_three_zero {l : List (List Nat)} (h1 : parAtR l 1 (l.length - 1) = none)
    (h2 : parAtR l 2 (l.length - 1) = none) : m0L 3 l = 0 := by
  rw [m0L, show 3 - 1 = 1 + 1 from rfl, Nat.findGreatest_of_not (by rw [h2]; simp),
    Nat.findGreatest_of_not (by rw [h1]; simp), Nat.findGreatest_zero]

theorem getElem!_mem_drop {α : Type} [Inhabited α] (l : List α) {d j : Nat} (h1 : d ≤ j)
    (h2 : j < l.length) : l[j]! ∈ l.drop d := by
  rw [getElem!_pos l j h2]
  have : l[j] = (l.drop d)[j - d]'(by rw [List.length_drop]; omega) := by
    rw [List.getElem_drop]; congr 1; omega
  rw [this]; exact List.getElem_mem _

/-! ### An anchor and a root -/

theorem flatten_map_single {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map (fun c => [f c])).flatten = l.map f := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **`(a, y, 0)(a+1, y+1, 1)` expands to the diagonal chain of `z0` columns.** -/
theorem m0L_append_two {A B : List (List Nat)} {p : Nat}
    (h : parAtR B 2 (B.length - 1) = some p) : m0L 3 (A ++ B) = 2 := by
  have hp := parAtR_lt _ _ _ _ h
  apply m0L_three_two
  rw [show (A ++ B).length - 1 = A.length + (B.length - 1) by simp; omega, parAtR_shift h]
  rfl

theorem expandRL_anchor_root (N a y : Nat) (A : List (List Nat)) :
    expandRL 3 N (A ++ [[a, y, 0], [a + 1, y + 1, 1]])
      = A ++ (List.range (N + 1)).map (fun t => [a + t, y + t, 0]) := by
  set B : List (List Nat) := [[a, y, 0], [a + 1, y + 1, 1]] with hB
  have h0 : ParR B 0 0 1 := ⟨by omega, by simp [hB], fun j' h1 h2 => by omega⟩
  have h1 : ParR B 1 0 1 := ⟨by omega, .single h0, by simp [hB], fun j' h1 h2 => by omega⟩
  have h2 : ParR B 2 0 1 := ⟨by omega, .single h1, by simp [hB], fun j' h1 h2 => by omega⟩
  have hp2 : parAtR B 2 (B.length - 1) = some 0 := (parAtR_eq_some _ _ _ _).mpr h2
  have hm : m0L 3 B = 2 := m0L_three_two (by rw [hp2]; rfl)
  have hb : badRootR 3 B = some 0 := by
    rw [badRootR_eq (by simp [hB]), hm]; exact hp2
  rw [expandRL_append_local 3 N A B 0 hb (by rw [hm, m0L_append_two hp2])]
  congr 1
  rw [expandRL_some 3 N B 0 hb, hm]
  simp [hB, List.range_succ, List.flatten]
  exact flatten_map_single _ _

/-! ### An add unit that ends in a digit -/

/-- A column after the root of an add unit whose anchor is `(a, y, 0)`: a digit
`(a+2, y+1, 1)`, or a column `(x, 0, 0)` of an embedding with `x ≥ a + 3`. -/
def TailCol (a y : Nat) (c : List Nat) : Prop :=
  c = [a + 2, y + 1, 1] ∨ ∃ x, a + 3 ≤ x ∧ c = [x, 0, 0]

/-- A column after the anchor: the root `(a+1, y+1, 1)` or a `TailCol`. -/
def BodyCol (a y : Nat) (c : List Nat) : Prop := c = [a + 1, y + 1, 1] ∨ TailCol a y c

/-- Copy `c` of a column of the bad part: row `0` goes up by `2c`, row `1` by
`c` unless it is `0`. -/
def ascCol (c : Nat) (col : List Nat) : List Nat :=
  [col[0]! + c * 2, if col[1]! = 0 then 0 else col[1]! + c * 1, col[2]!]

theorem bodyCol_x {a y : Nat} {col : List Nat} (h : BodyCol a y col) : a < col[0]! := by
  rcases h with rfl | rfl | ⟨x, hx, rfl⟩
  · simp
  · simp
  · simp; omega

theorem bodyCol_y {a y : Nat} {col : List Nat} (h : BodyCol a y col) (hx : col[0]! < a + 3) :
    col[1]! = y + 1 := by
  rcases h with rfl | rfl | ⟨x, hx', rfl⟩
  · simp
  · simp
  · simp at hx; omega

theorem bodyCol_y0 {a y : Nat} {col : List Nat} (h : BodyCol a y col) (hx : a + 3 ≤ col[0]!) :
    col[1]! = 0 := by
  rcases h with rfl | rfl | ⟨x, hx', rfl⟩
  · simp at hx
  · simp at hx
  · simp

theorem tailCol_x {a y : Nat} {col : List Nat} (h : TailCol a y col) : a + 2 ≤ col[0]! := by
  rcases h with rfl | ⟨x, hx, rfl⟩
  · simp
  · simp; omega

/-- **An add unit that ends in a digit expands to copies of itself without the
digit, each lifted by `(2, 1)`.** -/
theorem expandRL_digit_unit (N a y : Nat) (A D : List (List Nat))
    (hD : ∀ c ∈ D, TailCol a y c) :
    expandRL 3 N (A ++ (([a, y, 0] :: [a + 1, y + 1, 1] :: D) ++ [[a + 2, y + 1, 1]]))
      = A ++ ((List.range (N + 1)).map (fun c =>
          [a + c * 2, y + c * 1, 0] :: ([a + 1, y + 1, 1] :: D).map (ascCol c))).flatten := by
  set P0 : List (List Nat) := [a, y, 0] :: [a + 1, y + 1, 1] :: D with hP0
  set B : List (List Nat) := P0 ++ [[a + 2, y + 1, 1]] with hB
  have hlen : B.length = D.length + 3 := by simp [hB, hP0]
  have hlast : B[B.length - 1]! = [a + 2, y + 1, 1] := by
    rw [show B.length - 1 = P0.length + 0 by simp [hB, hP0], hB, getElem!_append_right]; rfl
  have hB0 : B[0]! = [a, y, 0] := by
    rw [hB, getElem!_append_left _ _ (by simp [hP0])]; rfl
  have hcol : ∀ j, 1 ≤ j → j < B.length → BodyCol a y (B[j]!) := by
    intro j h1 h2
    have hm := getElem!_mem_drop B h1 h2
    generalize B[j]! = col at hm ⊢
    rw [hB, hP0] at hm
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.mem_cons,
      List.mem_append] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (hD _ h)
    · simp at h; exact Or.inr (Or.inl h)
  have hcol2 : ∀ j, 2 ≤ j → j < B.length → TailCol a y (B[j]!) := by
    intro j h1 h2
    have hm := getElem!_mem_drop B h1 h2
    generalize B[j]! = col at hm ⊢
    rw [hB, hP0] at hm
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.mem_append] at hm
    rcases hm with h | h
    · exact hD _ h
    · simp at h; exact Or.inl h
  have hx0 : (B[0]!)[0]! = a := by rw [hB0]; rfl
  have hanc0 : ∀ j, 0 < j → j < B.length → AncR B 0 0 j :=
    anc0_of_min B (fun j h1 h2 => by rw [hx0]; exact bodyCol_x (hcol j h1 h2))
  have hp1 : ∀ j, 0 < j → j < B.length → (B[j]!)[0]! < a + 3 → ParR B 1 0 j := by
    intro j h1 h2 h3
    refine ⟨h1, hanc0 j h1 h2, ?_, fun j' hj1 hj2 hj3 => ?_⟩
    · rw [bodyCol_y (hcol j h1 h2) h3, hB0]; simp
    · have hx := anc0_lt hj3
      rw [bodyCol_y (hcol j h1 h2) h3,
        bodyCol_y (hcol j' hj1 (by omega)) (by omega)]
  have hnot1 : ∀ j, 0 < j → j < B.length → a + 3 ≤ (B[j]!)[0]! → ¬ AncR B 1 0 j := by
    intro j h1 h2 h3
    exact not_ancR_of_zero (k := 0) (bodyCol_y0 (hcol j h1 h2) h3)
  have hL : B.length - 1 = D.length + 2 := by omega
  have hlastx : (B[B.length - 1]!)[0]! < a + 3 := by rw [hlast]; simp
  have hp1l : ParR B 1 0 (B.length - 1) := hp1 _ (by omega) (by omega) hlastx
  have hp2 : ParR B 2 0 (B.length - 1) := by
    refine ⟨by omega, .single hp1l, by rw [hB0, hlast]; simp, fun j' hj1 hj2 hj3 => ?_⟩
    exfalso
    obtain ⟨c, hc1, hc2⟩ := Relation.TransGen.tail'_iff.mp hj3
    have hc0 := parR_unique hc2 hp1l
    subst hc0
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hc1 with he | ht
    · omega
    · have := tg_lt (fun _ _ h => ParR_lt h) ht; omega
  have hpar2 : parAtR B 2 (B.length - 1) = some 0 := (parAtR_eq_some _ _ _ _).mpr hp2
  have hm : m0L 3 B = 2 := m0L_three_two (by rw [hpar2]; rfl)
  have hb : badRootR 3 B = some 0 := by
    rw [badRootR_eq (by simp [hB]), hm]; exact hpar2
  have hlast' : B[D.length + 2]! = [a + 2, y + 1, 1] := by rw [← hL]; exact hlast
  rw [expandRL_append_local 3 N A B 0 hb (by rw [hm, m0L_append_two hpar2])]
  congr 1
  rw [expandRL_some 3 N B 0 hb, hm, List.take_zero, List.nil_append, Nat.sub_zero, hL]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  rw [show List.range (D.length + 2) = 0 :: (List.range (D.length + 1)).map Nat.succ from
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [hlast']; simp [hB0, List.range_succ]
  · have hR : [a + 1, y + 1, 1] :: D
        = (List.range (D.length + 1)).map (fun s => B[s + 1]!) := by
      conv_lhs => rw [← listEta ([a + 1, y + 1, 1] :: D)]
      rw [List.length_cons]
      refine List.map_congr_left (fun s hs => ?_)
      have hs' := List.mem_range.mp hs
      rw [hB, getElem!_append_left _ _ (by simp [hP0]; omega)]
      rfl
    rw [hR, List.map_map]
    refine List.map_congr_left (fun s hs => ?_)
    have hs' := List.mem_range.mp hs
    have hbc := hcol (s + 1) (by omega) (by omega)
    have ha0 : ancAtR B 0 0 (s + 1) = true := by
      rw [ancAtR_iff]; exact hanc0 _ (by omega) (by omega)
    have ha1 : ancAtR B 1 0 (s + 1) = decide ((B[s + 1]!)[0]! < a + 3) := by
      by_cases hx : (B[s + 1]!)[0]! < a + 3
      · rw [decide_eq_true hx, ancAtR_iff]
        exact .single (hp1 _ (by omega) (by omega) hx)
      · rw [decide_eq_false hx, Bool.eq_false_iff, ne_eq, ancAtR_iff]
        exact hnot1 _ (by omega) (by omega) (by omega)
    have hbeq : (0 == s + 1) = false := by simp
    simp only [Function.comp_apply, Nat.zero_add]
    simp only [List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.cons_append, hbeq, ha0, ha1,
      Bool.false_or, hB0, hlast']
    generalize B[s + 1]! = col at hbc
    rcases hbc with rfl | rfl | ⟨x, hx, rfl⟩
    · simp [ascCol]
    · simp [ascCol]
    · simp [ascCol]
      omega

/-! ### `m₀ = 0`: the bad part is copied unchanged -/

theorem expandRL_append_m0_zero (N : Nat) (A B : List (List Nat)) (p : Nat)
    (hw : ∀ c ∈ A ++ B, c.length = 3) (hp : ParR B 0 p (B.length - 1))
    (h1 : (B[B.length - 1]!)[1]! = 0) (h2 : (B[B.length - 1]!)[2]! = 0) :
    expandRL 3 N (A ++ B)
      = A ++ (B.take p ++ (List.replicate (N + 1) (B.drop p).dropLast).flatten) := by
  have hpl := hp.1
  have hlen : (A ++ B).length - 1 = A.length + (B.length - 1) := by
    rw [List.length_append]; omega
  have hlastE : (A ++ B)[(A ++ B).length - 1]! = B[B.length - 1]! := by
    rw [hlen, getElem!_append_right]
  have hn1 : parAtR (A ++ B) 1 ((A ++ B).length - 1) = none :=
    parAtR_none_of_zero (k := 0) (by rw [hlastE]; exact h1)
  have hn2 : parAtR (A ++ B) 2 ((A ++ B).length - 1) = none :=
    parAtR_none_of_zero (k := 1) (by rw [hlastE]; exact h2)
  have hm : m0L 3 (A ++ B) = 0 := m0L_three_zero hn1 hn2
  have hb : badRootR 3 (A ++ B) = some (A.length + p) := by
    rw [badRootR_eq (by intro h; rw [h] at hlen; simp at hlen; omega), hm, hlen]
    exact parAtR_shift ((parAtR_eq_some _ _ _ _).mpr hp)
  rw [expandRL_m0_zero 3 N (A ++ B) _ hw hb hm, List.take_length_add_append,
    List.drop_length_add_append, List.append_assoc]

/-- **A column that goes back to the head of its block copies the block.** -/
theorem expandRL_copy_block (N : Nat) (A : List (List Nat)) (d : List Nat) (D : List (List Nat))
    (x : Nat) (hw : ∀ c ∈ A ++ (d :: D ++ [[x, 0, 0]]), c.length = 3) (hd : d[0]! < x)
    (hD : ∀ col ∈ D, x ≤ col[0]!) :
    expandRL 3 N (A ++ (d :: D ++ [[x, 0, 0]]))
      = A ++ (List.replicate (N + 1) (d :: D)).flatten := by
  set B : List (List Nat) := d :: D ++ [[x, 0, 0]] with hB
  have hlen : B.length - 1 = (d :: D).length + 0 := by simp [hB]
  have hlast : B[B.length - 1]! = [x, 0, 0] := by
    rw [hlen, hB, List.cons_append, ← List.cons_append, getElem!_append_right]; rfl
  have hp : ParR B 0 0 (B.length - 1) := by
    refine ⟨by rw [hlen]; simp, ?_, fun j' h1 h2 => ?_⟩
    · rw [hlast, show B[0]! = d from rfl]; simpa using hd
    · rw [hlast]
      have hj : B[j']! = D[j' - 1]! := by
        rw [hlen] at h2
        rw [hB, List.cons_append, ← List.cons_append,
          getElem!_append_left _ _ (by simpa using h2)]
        obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
        rfl
      rw [hj]
      have hk : j' - 1 < D.length := by rw [hlen] at h2; simp at h2; omega
      have hmem : D[j' - 1]! ∈ D := by rw [getElem!_pos D _ hk]; exact List.getElem_mem _
      simpa using hD _ hmem
  rw [expandRL_append_m0_zero N A B 0 hw hp (by rw [hlast]; rfl) (by rw [hlast]; rfl),
    List.take_zero, List.nil_append, List.drop_zero, hB, List.cons_append,
    ← List.cons_append, List.dropLast_concat]

/-! ### Inside a primitive-sequence embedding -/

theorem parR0_congr (l1 l2 : List (List Nat)) (x : Nat)
    (h : ∀ j, j < l1.length → (l1[j]!)[0]! = (l2[j]!)[0]! + x) {j i : Nat}
    (hi : i < l1.length) : ParR l1 0 j i ↔ ParR l2 0 j i := by
  simp only [ParR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun j' a b => ?_⟩
    · rw [h j (by omega), h i hi] at h2; omega
    · have := h3 j' a b; rw [h j' (by omega), h i hi] at this; omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun j' a b => ?_⟩
    · rw [h j (by omega), h i hi]; omega
    · have := h3 j' a b; rw [h j' (by omega), h i hi]; omega

theorem map_embed_eq (g : Nat → List Nat) (Q : List Nat) (p N : Nat) :
    (Q.map g).take p ++ (List.replicate (N + 1) ((Q.map g).drop p).dropLast).flatten
      = (Q.take p ++ (List.replicate (N + 1) (Q.drop p).dropLast).flatten).map g := by
  simp [List.map_take, List.map_drop, List.map_dropLast, List.map_flatten, List.map_replicate]

theorem expandRL_embed_base (N : Nat) (Q : List Nat) (hc : Col 0 Q) :
    expandRL 3 N (Q.map (fun e => [e, 0, 0])) = (expandL N 0 Q).map (fun e => [e, 0, 0]) := by
  have h1 : Q.map (fun e => [e, 0, 0]) = zeroRow (zeroRow (Q.map (fun a => [a]))) := by
    simp [zeroRow, List.map_map]
  have hl1 : ∀ c ∈ Q.map (fun a => [a]), c.length = 1 := by
    intro c hc; rw [List.mem_map] at hc; obtain ⟨a, _, rfl⟩ := hc; rfl
  have hl2 : ∀ c ∈ zeroRow (Q.map (fun a => [a])), c.length = 2 := by
    intro c hc; rw [zeroRow, List.mem_map] at hc; obtain ⟨d, hd, rfl⟩ := hc
    rw [List.length_append, hl1 d hd]; rfl
  rw [h1, expandRL_zeroRow (r := 2) (by decide) N _ hl2,
    expandRL_zeroRow (r := 1) (by decide) N _ hl1, expandRL_one N Q hc]
  simp [zeroRow, List.map_map]

/-- **Expansion inside an embedding is the one-row expansion**, when the last
entry is above the embedding's level. -/
theorem expandRL_embed (N x : Nat) (A : List (List Nat)) (Q : List Nat) (hc : Col 0 Q)
    (hlast : 0 < Q[Q.length - 1]!) (hwA : ∀ c ∈ A, c.length = 3) :
    expandRL 3 N (A ++ Q.map (fun e => [x + e, 0, 0]))
      = A ++ (expandL N 0 Q).map (fun e => [x + e, 0, 0]) := by
  have hne : Q ≠ [] := by intro h; subst h; simp at hlast
  have hQ0 : Q[0]! = 0 := by
    cases Q with
    | nil => exact absurd rfl hne
    | cons a t => exact hc.1
  have hlen2 : 0 < Q.length - 1 := by
    rcases Nat.lt_or_ge 0 (Q.length - 1) with h | h
    · exact h
    · exfalso
      have : Q.length - 1 = 0 := by omega
      rw [this, hQ0] at hlast; exact absurd hlast (Nat.lt_irrefl 0)
  set g0 : Nat → List Nat := fun e => [e, 0, 0] with hg0
  set gx : Nat → List Nat := fun e => [x + e, 0, 0] with hgx
  have he0 : ∀ j, j < Q.length → ((Q.map g0)[j]!) = [Q[j]!, 0, 0] := fun j hj =>
    getElem!_map g0 Q j hj
  have hex : ∀ j, j < Q.length → ((Q.map gx)[j]!) = [x + Q[j]!, 0, 0] := fun j hj =>
    getElem!_map gx Q j hj
  have hcongr : ∀ j, j < (Q.map gx).length →
      ((Q.map gx)[j]!)[0]! = ((Q.map g0)[j]!)[0]! + x := by
    intro j hj
    rw [List.length_map] at hj
    rw [hex j hj, he0 j hj]; simp; omega
  obtain ⟨p, -, hp0⟩ := parR0_exists (Q.map g0) (j0 := 0) (i := Q.length - 1) hlen2
    (by rw [he0 0 (by omega), he0 _ (by omega), hQ0]; simpa using hlast)
  have hp0' : ParR (Q.map g0) 0 p ((Q.map g0).length - 1) := by rwa [List.length_map]
  have hpx : ParR (Q.map gx) 0 p ((Q.map gx).length - 1) := by
    rw [List.length_map]
    exact (parR0_congr _ _ x hcongr (by rw [List.length_map]; omega)).mpr hp0
  have hw0 : ∀ c ∈ [] ++ Q.map g0, c.length = 3 := by
    intro c hc; simp only [List.nil_append, List.mem_map] at hc; obtain ⟨e, _, rfl⟩ := hc; rfl
  have hwx : ∀ c ∈ A ++ Q.map gx, c.length = 3 := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hwA c h
    · rw [List.mem_map] at h; obtain ⟨e, _, rfl⟩ := h; rfl
  have hl0 : ((Q.map g0)[(Q.map g0).length - 1]!) = [Q[Q.length - 1]!, 0, 0] := by
    rw [List.length_map]; exact he0 _ (by omega)
  have hlx : ((Q.map gx)[(Q.map gx).length - 1]!) = [x + Q[Q.length - 1]!, 0, 0] := by
    rw [List.length_map]; exact hex _ (by omega)
  have hE0 := expandRL_append_m0_zero N [] (Q.map g0) p hw0 hp0'
    (by rw [hl0]; rfl) (by rw [hl0]; rfl)
  rw [List.nil_append, List.nil_append, expandRL_embed_base N Q hc, map_embed_eq] at hE0
  have hinj : Function.Injective (List.map g0) :=
    List.map_injective_iff.mpr (fun a b h => by simp [hg0] at h; exact h)
  have hE := hinj hE0
  rw [expandRL_append_m0_zero N A (Q.map gx) p hwx hpx (by rw [hlx]; rfl) (by rw [hlx]; rfl),
    map_embed_eq, hE]

/-! ### One-row expansion, written on the terms -/

/-- `n` summands `ω^X`. -/
def repT (X : Term) : Nat → Term
  | 0 => nil
  | n + 1 => cons nil X (repT X n)

/-- Whether the last summand is `ω^0 = 1`. -/
def lastOne : Term → Bool
  | nil => false
  | cons _ b t => if t == nil then b == nil else lastOne t

/-- **`expandL` on the terms.**  The last summand `ω^X` is dropped when `X = 0`,
becomes `N + 1` summands `ω^{X'}` when `X = X' + 1`, and is expanded inside
otherwise. -/
def exT (N : Nat) : Term → Term
  | nil => nil
  | cons a X Y =>
      if Y == nil then
        (if X == nil then nil
         else if lastOne X then repT (dropLastT X) (N + 1)
         else cons a (exT N X) nil)
      else cons a X (exT N Y)

theorem unread_eq_nil_iff (b : Nat) (X : Term) : unread b X = [] ↔ X = nil := by
  cases X with
  | nil => simp
  | cons a P Q => simp

theorem tw_unread (b : Nat) (X Y : Term) :
    (unread (b + 1) X ++ unread b Y).takeWhile (fun x => decide (b < x)) = unread (b + 1) X := by
  refine takeWhile_append_of_all _ _ (fun x hx => ?_) (fun x hx => ?_)
  · exact decide_eq_true (le_of_mem_unread X (b + 1) x hx)
  · cases Y with
    | nil => exact absurd hx (by simp)
    | cons c R S =>
      rw [unread_cons] at hx
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx; simp

theorem dw_unread (b : Nat) (X Y : Term) :
    (unread (b + 1) X ++ unread b Y).dropWhile (fun x => decide (b < x)) = unread b Y := by
  refine dropWhile_append_of_all _ _ (fun x hx => ?_) (fun x hx => ?_)
  · exact decide_eq_true (le_of_mem_unread X (b + 1) x hx)
  · cases Y with
    | nil => exact absurd hx (by simp)
    | cons c R S =>
      rw [unread_cons] at hx
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx; simp

theorem mem_of_lastOf : ∀ (l : List Nat) (v : Nat), lastOf l = some v → v ∈ l := by
  intro l
  induction l with
  | nil => intro v h; simp [lastOf] at h
  | cons a t ih =>
    intro v h
    cases t with
    | nil => simp [lastOf] at h; simp [h]
    | cons c r =>
      rw [lastOf_cons a _ (by simp)] at h
      exact List.mem_cons_of_mem _ (ih v h)

/-- With the last summand `1`, the matrix ends in an entry at its own level. -/
theorem unread_snoc (c : Nat) : ∀ X : Term, lastOne X = true →
    unread c X = unread c (dropLastT X) ++ [c] := by
  intro X
  induction X generalizing c with
  | nil => intro h; simp [lastOne] at h
  | cons a P Q _ ihP ihQ =>
    intro h
    by_cases hQ : Q = nil
    · subst hQ
      simp only [lastOne, beq_self_eq_true, if_true, beq_iff_eq] at h
      subst h
      simp [dropLastT]
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [lastOne, hQb, Bool.false_eq_true, if_false] at h
      rw [dropLastT, hQb, if_neg (by simp), unread_cons, unread_cons, ihQ c h]
      simp

theorem lastOf_unread (c : Nat) : ∀ X : Term, X ≠ nil →
    (lastOf (unread c X) = some c ↔ lastOne X = true) := by
  intro X
  induction X generalizing c with
  | nil => intro h; exact absurd rfl h
  | cons a P Q _ ihP ihQ =>
    intro _
    by_cases hQ : Q = nil
    · subst hQ
      by_cases hP : P = nil
      · subst hP; simp [lastOne]
      · have hPb : (P == nil) = false := by simpa using hP
        simp only [lastOne, beq_self_eq_true, if_true, hPb, Bool.false_eq_true, iff_false]
        rw [unread_cons, unread_nil, List.append_nil,
          lastOf_cons _ _ (by rwa [ne_eq, unread_eq_nil_iff])]
        intro h
        have := le_of_mem_unread P (c + 1) c (mem_of_lastOf _ _ h)
        omega
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [lastOne, hQb, Bool.false_eq_true, if_false]
      rw [unread_cons, ← List.cons_append,
        lastOf_append _ _ (by rwa [ne_eq, unread_eq_nil_iff])]
      exact ihQ c hQ

theorem flatten_rep (b : Nat) (X : Term) : ∀ n : Nat,
    (List.replicate n (b :: unread (b + 1) X)).flatten = unread b (repT X n) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, repT, unread_cons]
    rfl

/-- **`exT` is `expandL` read on the terms.** -/
theorem expandL_unread (N : Nat) : ∀ (α : Term) (b : Nat),
    expandL N b (unread b α) = unread b (exT N α) := by
  intro α
  induction α with
  | nil => intro b; rw [unread_nil, expandL_nil]; rfl
  | cons a X Y _ ihX ihY =>
    intro b
    rw [unread_cons, expandL_cons, tw_unread, dw_unread]
    by_cases hY : Y = nil
    · subst hY
      rw [if_pos (show unread b nil = [] from rfl)]
      simp only [exT, beq_self_eq_true, if_true]
      by_cases hX : X = nil
      · subst hX
        rw [if_pos (show unread (b + 1) nil = [] from rfl)]; rfl
      · have hXb : (X == nil) = false := by simpa using hX
        rw [if_neg (show ¬ unread (b + 1) X = [] by rwa [unread_eq_nil_iff])]
        simp only [hXb, Bool.false_eq_true, if_false]
        by_cases h1 : lastOne X = true
        · rw [if_pos ((lastOf_unread (b + 1) X hX).mpr h1), if_pos h1,
            unread_snoc (b + 1) X h1, List.dropLast_concat, flatten_rep]
        · rw [if_neg (fun h => h1 ((lastOf_unread (b + 1) X hX).mp h)), if_neg h1, ihX,
            unread_cons, unread_nil, List.append_nil]
    · have hYb : (Y == nil) = false := by simpa using hY
      rw [if_neg (show ¬ unread b Y = [] by rwa [unread_eq_nil_iff]), exT]
      simp only [hYb, Bool.false_eq_true, if_false]
      rw [unread_cons, ihY]

/-! ### Facts about the terms -/

theorem allNil_dropLastT' : ∀ X : Term, AllNil X → AllNil (dropLastT X) := by
  intro X
  induction X with
  | nil => intro _; trivial
  | cons a b t _ _ iht =>
    intro h
    rw [dropLastT]
    by_cases ht : t = nil
    · subst ht; simp; trivial
    · rw [if_neg (by simpa using ht)]
      exact ⟨h.1, h.2.1, iht h.2.2⟩

theorem allNil_repT (X : Term) (h : AllNil X) : ∀ n, AllNil (repT X n) := by
  intro n
  induction n with
  | zero => trivial
  | succ m ih => exact ⟨rfl, h, ih⟩

theorem allNil_exT (N : Nat) : ∀ α : Term, AllNil α → AllNil (exT N α) := by
  intro α
  induction α with
  | nil => intro _; trivial
  | cons a X Y _ ihX ihY =>
    intro h
    rw [exT]
    by_cases hY : Y = nil
    · subst hY
      simp only [beq_self_eq_true, if_true]
      by_cases hX : X = nil
      · subst hX; simp; trivial
      · have hXb : (X == nil) = false := by simpa using hX
        simp only [hXb, Bool.false_eq_true, if_false]
        split
        · exact allNil_repT _ (allNil_dropLastT' X h.2.1) _
        · exact ⟨h.1, ihX h.2.1, trivial⟩
    · have hYb : (Y == nil) = false := by simpa using hY
      simp only [hYb, Bool.false_eq_true, if_false]
      exact ⟨h.1, h.2.1, ihY h.2.2⟩

/-- Every summand is `1`. -/
def AllOne : Term → Prop
  | nil => True
  | cons _ b t => b = nil ∧ AllOne t

/-- After a summand `1` come only summands `1`: the shape of a Cantor normal
form at the top level. -/
def ZT : Term → Prop
  | nil => True
  | cons _ b t => (b = nil → AllOne t) ∧ ZT t

theorem allOne_repT : ∀ n, AllOne (repT nil n) := by
  intro n
  induction n with
  | zero => trivial
  | succ m ih => exact ⟨rfl, ih⟩

theorem zt_of_allOne : ∀ α : Term, AllOne α → ZT α := by
  intro α
  induction α with
  | nil => intro _; trivial
  | cons a b t _ _ iht => intro h; exact ⟨fun _ => h.2, iht h.2⟩

theorem zt_repT (X : Term) : ∀ n, ZT (repT X n) := by
  by_cases hX : X = nil
  · subst hX; intro n; exact zt_of_allOne _ (allOne_repT n)
  · intro n
    induction n with
    | zero => trivial
    | succ m ih => exact ⟨fun h => absurd h hX, ih⟩

theorem allOne_exT (N : Nat) : ∀ α : Term, AllOne α → AllOne (exT N α) := by
  intro α
  induction α with
  | nil => intro _; trivial
  | cons a X Y _ _ ihY =>
    intro h
    obtain ⟨hX, hY1⟩ := h
    subst hX
    rw [exT]
    by_cases hY : Y = nil
    · subst hY; simp; trivial
    · have hYb : (Y == nil) = false := by simpa using hY
      simp only [hYb, Bool.false_eq_true, if_false]
      exact ⟨rfl, ihY hY1⟩

theorem zt_exT (N : Nat) : ∀ α : Term, ZT α → ZT (exT N α) := by
  intro α
  induction α with
  | nil => intro _; trivial
  | cons a X Y _ _ ihY =>
    intro h
    rw [exT]
    by_cases hY : Y = nil
    · subst hY
      simp only [beq_self_eq_true, if_true]
      split
      · trivial
      · split
        · exact zt_repT _ _
        · exact ⟨fun _ => trivial, trivial⟩
    · have hYb : (Y == nil) = false := by simpa using hY
      simp only [hYb, Bool.false_eq_true, if_false]
      exact ⟨fun hX => allOne_exT N Y (h.1 hX), ihY h.2⟩

theorem exT_ne_nil (N : Nat) {X : Term} (hX : X ≠ nil) (hl : lastOne X = false) :
    exT N X ≠ nil := by
  cases X with
  | nil => exact absurd rfl hX
  | cons a P Q =>
    rw [exT]
    by_cases hQ : Q = nil
    · subst hQ
      simp only [lastOne, beq_self_eq_true, if_true] at hl
      simp only [beq_self_eq_true, if_true, hl, Bool.false_eq_true, if_false]
      split
      · simp [repT]
      · simp
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [hQb, Bool.false_eq_true, if_false]
      simp

theorem isFiniteT_dropLastT : ∀ X : Term, lastOne X = true →
    isFiniteT X = isFiniteT (dropLastT X) := by
  intro X
  induction X with
  | nil => intro h; simp [lastOne] at h
  | cons a P Q _ _ ihQ =>
    intro h
    by_cases hQ : Q = nil
    · subst hQ
      simp only [lastOne, beq_self_eq_true, if_true, beq_iff_eq] at h
      subst h; rfl
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [lastOne, hQb, Bool.false_eq_true, if_false] at h
      rw [dropLastT, hQb, if_neg (by simp), isFiniteT, isFiniteT, ihQ h]

theorem lastOne_of_finite : ∀ X : Term, isFiniteT X = true → X ≠ nil → lastOne X = true := by
  intro X
  induction X with
  | nil => intro _ h; exact absurd rfl h
  | cons a P Q _ _ ihQ =>
    intro h _
    rw [isFiniteT, Bool.and_eq_true] at h
    by_cases hQ : Q = nil
    · subst hQ; simp [lastOne]; simpa using h.1
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [lastOne, hQb, Bool.false_eq_true, if_false]
      exact ihQ h.2 hQ

theorem not_finite_of_not_lastOne : ∀ X : Term, X ≠ nil → lastOne X = false →
    isFiniteT X = false := by
  intro X hX hl
  by_contra h
  rw [Bool.not_eq_false] at h
  rw [lastOne_of_finite X h hX] at hl
  exact absurd hl (by simp)

theorem prSS_nil (x : Nat) : prSS x nil = [] := rfl

theorem mulUnits_dropLast (x0 y : Nat) : ∀ X : Term, lastOne X = true →
    mulUnits x0 y X = mulUnits x0 y (dropLastT X) ++ [[x0 + 1, y, 1]] := by
  intro X
  induction X with
  | nil => intro h; simp [lastOne] at h
  | cons a P Q _ _ ihQ =>
    intro h
    by_cases hQ : Q = nil
    · subst hQ
      simp only [lastOne, beq_self_eq_true, if_true, beq_iff_eq] at h
      subst h; rfl
    · have hQb : (Q == nil) = false := by simpa using hQ
      simp only [lastOne, hQb, Bool.false_eq_true, if_false] at h
      rw [dropLastT, hQb, if_neg (by simp), mulUnits, mulUnits, ihQ h, List.append_assoc]

theorem mulUnits_prefix (x0 y : Nat) : ∀ Z : Term,
    ∃ S, mulUnits x0 y Z = mulUnits x0 y (peelOne Z) ++ S := by
  intro Z
  rw [peelOne]
  split
  · induction Z with
    | nil => exact ⟨[], rfl⟩
    | cons a P Q _ _ ihQ =>
      by_cases hQ : Q = nil
      · subst hQ; exact ⟨mulUnits x0 y (cons a P nil), by simp [dropLastT]; rfl⟩
      · rename_i hfin
        rw [isFiniteT, Bool.and_eq_true] at hfin
        obtain ⟨S, hS⟩ := ihQ hfin.2
        have hQb : (Q == nil) = false := by simpa using hQ
        exact ⟨S, by rw [dropLastT, hQb, if_neg (by simp), mulUnits, mulUnits, hS,
          List.append_assoc]⟩
  · exact ⟨[], by rw [List.append_nil]⟩

/-- **Peeling the leading `1` commutes with adding a final `1`.** -/
theorem mulUnits_peel_snoc (x0 y : Nat) {X : Term} (h : lastOne X = true)
    (hne : dropLastT X ≠ nil) :
    mulUnits x0 y (peelOne X) = mulUnits x0 y (peelOne (dropLastT X)) ++ [[x0 + 1, y, 1]] := by
  rw [peelOne, peelOne, ← isFiniteT_dropLastT X h]
  split
  · rename_i hfin
    rw [isFiniteT_dropLastT X h] at hfin
    exact mulUnits_dropLast x0 y _ (lastOne_of_finite _ hfin hne)
  · exact mulUnits_dropLast x0 y X h

theorem peelOne_of_dropLast_nil {X : Term} (h : lastOne X = true) (hn : dropLastT X = nil) :
    peelOne X = nil := by
  rw [peelOne, isFiniteT_dropLastT X h, hn]; rfl

theorem peelOne_of_not_lastOne {X : Term} (hX : X ≠ nil) (h : lastOne X = false) :
    peelOne X = X := by
  rw [peelOne, not_finite_of_not_lastOne X hX h]; rfl

theorem mulUnits_repT (x0 y : Nat) (γ : Term) : ∀ n : Nat,
    mulUnits x0 y (repT γ n) = (List.replicate n ([x0 + 1, y, 1] :: prSS (x0 + 2) γ)).flatten := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => rw [repT, mulUnits, ih, List.replicate_succ, List.flatten_cons]

theorem prSS_snoc (x : Nat) {γ : Term} (h : lastOne γ = true) :
    prSS x γ = prSS x (dropLastT γ) ++ [[x, 0, 0]] := by
  rw [prSS, prSS, unread_snoc 0 γ h, List.map_append]; rfl

theorem prSS_ge (x : Nat) (γ : Term) : ∀ col ∈ prSS x γ, x ≤ col[0]! := by
  intro col hc
  rw [prSS, List.mem_map] at hc
  obtain ⟨e, _, rfl⟩ := hc
  simp

theorem lastOf_eq_getElem! : ∀ l : List Nat, l ≠ [] → lastOf l = some l[l.length - 1]! := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    cases t with
    | nil => rfl
    | cons c r =>
      rw [lastOf_cons a _ (by simp), ih (by simp)]
      simp

theorem unread_last_pos {γ : Term} (hne : γ ≠ nil) (h : lastOne γ = false) :
    0 < (unread 0 γ)[(unread 0 γ).length - 1]! := by
  have hne' : unread 0 γ ≠ [] := by rwa [ne_eq, unread_eq_nil_iff]
  have h1 := lastOf_eq_getElem! _ hne'
  rcases Nat.eq_zero_or_pos ((unread 0 γ)[(unread 0 γ).length - 1]!) with h0 | h0
  · rw [h0] at h1
    rw [(lastOf_unread 0 γ hne).mp h1] at h
    exact absurd h (by simp)
  · exact h0

/-! ### Units of the trio matrix -/

theorem list3_eq {a b c a' b' c' : Nat} (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    [a, b, c] = [a', b', c'] := by subst h1 h2 h3; rfl

theorem map_range_succ' {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun t => f (t + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem mulUnits_tail (a y : Nat) : ∀ Z : Term, ∀ col ∈ mulUnits (a + 1) (y + 1) Z,
    TailCol a y col := by
  intro Z
  induction Z with
  | nil => intro col h; simp [mulUnits] at h
  | cons _ g t _ _ iht =>
    intro col h
    rw [mulUnits, List.mem_append, List.mem_cons] at h
    rcases h with (h | h) | h
    · subst h; exact Or.inl rfl
    · rw [prSS, List.mem_map] at h
      obtain ⟨e, _, rfl⟩ := h
      exact Or.inr ⟨a + 1 + 2 + e, by omega, rfl⟩
    · exact iht col h

theorem mulUnits_asc (c x0 y : Nat) (hy : y ≠ 0) : ∀ Z : Term,
    (mulUnits x0 y Z).map (ascCol c) = mulUnits (x0 + c * 2) (y + c * 1) Z := by
  intro Z
  induction Z with
  | nil => rfl
  | cons _ g t _ _ iht =>
    rw [mulUnits, mulUnits, List.map_append, iht, List.map_cons]
    congr 2
    · simp [ascCol, hy]; omega
    · rw [prSS, prSS, List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp [ascCol]; omega

theorem addUnits_cons_split (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a X : Term) :
    ∃ U r' l', ∀ t, addUnits rp1 lastX pz i (cons a X t)
      = U ++ addUnits r' l' (X == nil) (i + 1) t := by
  by_cases hX : X = nil
  · subst hX
    cases pz with
    | true => exact ⟨[[lastX + 1, i, 0]], rp1, lastX + 1, fun t => by rw [addUnits]; rfl⟩
    | false =>
      exact ⟨[[rp1, i - 1, 0], [rp1 + 1, i, 0]], rp1, rp1 + 1, fun t => by rw [addUnits]; rfl⟩
  · have hXb : (X == nil) = false := by simpa using hX
    refine ⟨[rp1, i - 1, 0] :: bodyU X (rp1 + 1) i, rp1 + 2, rp1 + 1, fun t => ?_⟩
    rw [addUnits]
    simp only [hXb, Bool.false_eq_true, if_false]

theorem addUnits_chain (rp1 : Nat) : ∀ (n lastX i : Nat),
    addUnits rp1 lastX true i (repT nil n)
      = (List.range n).map (fun t => [lastX + 1 + t, i + t, 0]) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro lastX i
    rw [repT, addUnits]
    simp only [beq_self_eq_true, if_true]
    rw [ih, map_range_succ']
    refine congrArg₂ List.cons ?_ (List.map_congr_left (fun t _ => ?_))
    · refine list3_eq ?_ ?_ rfl <;> omega
    · refine list3_eq ?_ ?_ rfl <;> omega

theorem addUnits_ones (rp1 lastX j N : Nat) :
    addUnits rp1 lastX false (j + 1) (repT nil (N + 1))
      = (List.range (N + 1 + 1)).map (fun t => [rp1 + t, j + t, 0]) := by
  rw [repT, addUnits]
  simp only [beq_self_eq_true, if_true, Bool.false_eq_true, if_false]
  rw [addUnits_chain, map_range_succ', map_range_succ']
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
    (List.map_congr_left (fun t _ => ?_)))
  · refine list3_eq ?_ ?_ rfl <;> omega
  · refine list3_eq ?_ ?_ rfl <;> omega
  · refine list3_eq ?_ ?_ rfl <;> omega

theorem addUnits_repT (X0 : Term) (hX : X0 ≠ nil) : ∀ (n rp1 lastX : Nat) (pz : Bool) (j : Nat),
    addUnits rp1 lastX pz (j + 1) (repT X0 n)
      = ((List.range n).map (fun c => [rp1 + c * 2, j + c * 1, 0]
          :: bodyU X0 (rp1 + 1 + c * 2) (j + 1 + c * 1))).flatten := by
  have hXb : (X0 == nil) = false := by simpa using hX
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ m ih =>
    intro rp1 lastX pz j
    rw [repT, addUnits]
    simp only [hXb, Bool.false_eq_true, if_false]
    rw [show j + 1 + 1 = (j + 1) + 1 from rfl, ih, map_range_succ', List.flatten_cons]
    refine congrArg₂ (· ++ ·) (congrArg₂ List.cons ?_ ?_)
      (congrArg List.flatten (List.map_congr_left (fun c _ =>
        congrArg₂ List.cons ?_ ?_)))
    · refine list3_eq ?_ ?_ rfl <;> omega
    · refine congrArg₂ (bodyU X0) ?_ ?_ <;> omega
    · refine list3_eq ?_ ?_ rfl <;> omega
    · refine congrArg₂ (bodyU X0) ?_ ?_ <;> omega

/-! ### One step of the one-row expansion is followed by the trio matrix -/

/-- **Inside the multiply units.** -/
theorem step_mul (N x0 y : Nat) : ∀ X : Term, AllNil X → X ≠ nil → lastOne X = false →
    ∀ P : List (List Nat), Reach3 (P ++ mulUnits x0 y X) →
      Reach3 (P ++ mulUnits x0 y (exT N X)) := by
  intro X
  induction X with
  | nil => intro _ h; exact absurd rfl h
  | cons a γ t _ ihγ iht =>
    intro hA _ hl P hR
    by_cases ht : t = nil
    · subst ht
      simp only [lastOne, beq_self_eq_true, if_true, beq_eq_false_iff_ne] at hl
      have hγb : (γ == nil) = false := by simpa using hl
      rw [exT]
      simp only [beq_self_eq_true, if_true, hγb, Bool.false_eq_true, if_false]
      rw [mulUnits, mulUnits, List.append_nil] at hR
      have hw := reach3_wf hR
      split
      · rename_i h1
        rw [mulUnits_repT]
        rw [prSS_snoc (x0 + 2) h1, ← List.cons_append] at hR hw
        have hE := expandRL_copy_block N P [x0 + 1, y, 1] (prSS (x0 + 2) (dropLastT γ)) (x0 + 2)
          hw (by simp) (prSS_ge _ _)
        have := reach3_expand hR N
        rwa [hE] at this
      · rename_i h1
        have h1' : lastOne γ = false := by simpa using h1
        rw [mulUnits, mulUnits, List.append_nil]
        have hR' : Reach3 ((P ++ [[x0 + 1, y, 1]]) ++
            (unread 0 γ).map (fun e => [x0 + 2 + e, 0, 0])) := by
          rw [List.append_assoc]; exact hR
        have hwA : ∀ c ∈ P ++ [[x0 + 1, y, 1]], c.length = 3 := by
          intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hw c (List.mem_append_left _ h)
          · simp at h; subst h; rfl
        have hE := expandRL_embed N (x0 + 2) (P ++ [[x0 + 1, y, 1]]) (unread 0 γ)
          (col_unread γ hA.2.1 0) (unread_last_pos hl h1') hwA
        have := reach3_expand hR' N
        rw [hE, expandL_unread, List.append_assoc] at this
        exact this
    · have htb : (t == nil) = false := by simpa using ht
      simp only [lastOne, htb, Bool.false_eq_true, if_false] at hl
      rw [exT]
      simp only [htb, Bool.false_eq_true, if_false]
      rw [mulUnits] at hR ⊢
      rw [← List.append_assoc] at hR ⊢
      exact iht hA.2.2 ht hl _ hR

/-- **At the add units.** -/
theorem step_add (N : Nat) : ∀ α : Term, AllNil α → ZT α →
    ∀ (rp1 lastX : Nat) (pz : Bool) (j : Nat), (pz = true → AllOne α) →
    ∀ P : List (List Nat), Reach3 (P ++ addUnits rp1 lastX pz (j + 1) α) →
      Reach3 (P ++ addUnits rp1 lastX pz (j + 1) (exT N α)) := by
  intro α
  induction α with
  | nil => intro _ _ _ _ _ _ _ _ h; exact h
  | cons a X Y _ ihX ihY =>
    intro hA hZ rp1 lastX pz j hpz P hR
    by_cases hY : Y = nil
    · subst hY
      rw [exT]
      simp only [beq_self_eq_true, if_true]
      by_cases hX : X = nil
      · subst hX
        simp only [beq_self_eq_true, if_true]
        obtain ⟨U, r', l', hU⟩ := addUnits_cons_split rp1 lastX pz (j + 1) a nil
        rw [hU, show addUnits r' l' (nil == nil) (j + 1 + 1) nil = [] from rfl,
          List.append_nil] at hR
        rw [show addUnits rp1 lastX pz (j + 1) nil = [] from rfl, List.append_nil]
        exact reach3_prefix U P hR
      · have hXb : (X == nil) = false := by simpa using hX
        simp only [hXb, Bool.false_eq_true, if_false]
        have hpzf : pz = false := by
          cases pz with
          | false => rfl
          | true => exact absurd (hpz rfl).1 hX
        subst hpzf
        rw [addUnits] at hR
        simp only [hXb, Bool.false_eq_true, if_false] at hR
        rw [show addUnits (rp1 + 2) (rp1 + 1) false (j + 1 + 1) nil = [] from rfl,
          List.append_nil, Nat.add_sub_cancel, bodyU] at hR
        split
        · rename_i h1
          by_cases h0 : dropLastT X = nil
          · rw [peelOne_of_dropLast_nil h1 h0, show mulUnits (rp1 + 1) (j + 1) nil = []
              from rfl] at hR
            rw [h0]
            have := reach3_expand hR (N + 1)
            rw [expandRL_anchor_root] at this
            rw [addUnits_ones]
            exact this
          · rw [mulUnits_peel_snoc _ _ h1 h0] at hR
            have hE := expandRL_digit_unit N rp1 j P (mulUnits (rp1 + 1) (j + 1)
              (peelOne (dropLastT X))) (mulUnits_tail rp1 j _)
            have := reach3_expand hR N
            rw [show [rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: (mulUnits (rp1 + 1) (j + 1)
                (peelOne (dropLastT X)) ++ [[rp1 + 1 + 1, j + 1, 1]])
                = ([rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: mulUnits (rp1 + 1) (j + 1)
                  (peelOne (dropLastT X))) ++ [[rp1 + 2, j + 1, 1]] by simp, hE] at this
            rw [addUnits_repT _ h0]
            convert this using 3
            refine List.map_congr_left (fun c _ => ?_)
            rw [bodyU, List.map_cons, mulUnits_asc c _ _ (by omega)]
            simp [ascCol]
        · rename_i h1
          have h1' : lastOne X = false := by simpa using h1
          rw [addUnits]
          simp only [exT_ne_nil N hX h1', beq_iff_eq, if_false]
          rw [show addUnits (rp1 + 2) (rp1 + 1) false (j + 1 + 1) nil = [] from rfl,
            List.append_nil, Nat.add_sub_cancel, bodyU]
          rw [peelOne_of_not_lastOne hX h1'] at hR
          have hR' : Reach3 ((P ++ [[rp1, j, 0], [rp1 + 1, j + 1, 1]])
              ++ mulUnits (rp1 + 1) (j + 1) X) := by simpa using hR
          have h2 := step_mul N (rp1 + 1) (j + 1) X hA.2.1 hX h1' _ hR'
          obtain ⟨S, hS⟩ := mulUnits_prefix (rp1 + 1) (j + 1) (exT N X)
          rw [hS, ← List.append_assoc] at h2
          have := reach3_prefix _ _ h2
          simpa using this
    · have hYb : (Y == nil) = false := by simpa using hY
      rw [exT]
      simp only [hYb, Bool.false_eq_true, if_false]
      obtain ⟨U, r', l', hU⟩ := addUnits_cons_split rp1 lastX pz (j + 1) a X
      rw [hU] at hR ⊢
      rw [← List.append_assoc] at hR ⊢
      exact ihY hA.2.2 hZ.2 r' l' (X == nil) (j + 1)
        (fun h => hZ.1 (by simpa using h)) _ hR

/-! ### From a generator to the towers -/

/-- `ψ_0(Ω_{ε₀})`, `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)`. -/
def topE0 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0]]

/-- **`ψ_0(Ω_{ε₀})` is reachable**, by six expansions of `(0,0,0)(1,1,1)(2,2,2)`
and four cuts. -/
theorem reach3_topE0 : Reach3 topE0 := by
  have g2 : Reach3 [[0,0,0],[1,1,1],[2,2,2]] := by
    have := reach3_gen 2; exact this
  have s1 : Reach3 [[0,0,0],[1,1,1],[2,2,1]] := by
    have := reach3_expand g2 1
    rwa [show expandRL 3 1 [[0,0,0],[1,1,1],[2,2,2]] = [[0,0,0],[1,1,1],[2,2,1]] by decide]
      at this
  have s2 : Reach3 [[0,0,0],[1,1,1],[2,2,0]] := by
    have := reach3_expand s1 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,2,1]] = [[0,0,0],[1,1,1],[2,2,0],[3,3,1]]
      by decide] at this
    exact reach3_prefix [[3,3,1]] _ this
  have s3 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,1,1]] := by
    have := reach3_expand s2 2
    rwa [show expandRL 3 2 [[0,0,0],[1,1,1],[2,2,0]] = [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      by decide] at this
  have s4 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,1,0]] := by
    have := reach3_expand s3 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[4,2,1],[5,2,1]] by decide] at this
    exact reach3_prefix [[4,2,1],[5,2,1]] _ this
  have s5 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]] := by
    have := reach3_expand s4 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,0]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1]] by decide] at this
    exact reach3_prefix [[5,1,1]] _ this
  have := reach3_expand s5 1
  rwa [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]] = topE0 by decide] at this

/-- **`ψ_0(Ω_{ε₀})[n]` is the tower**: `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)⋯(n+3,0,0)`. -/
theorem expandRL_topE0 (n : Nat) :
    expandRL 3 n topE0
      = [[0,0,0],[1,1,1],[2,1,1]] ++ (List.range (n + 1)).map (fun t => [3 + t, 0, 0]) := by
  have hb : badRootR 3 topE0 = some 3 := by decide
  have hm : m0L 3 topE0 = 1 := by decide
  have ha : ∀ k, ancAtR topE0 k 3 3 = false := by
    intro k; rw [Bool.eq_false_iff, ne_eq, ancAtR_iff]
    intro h; exact absurd (tg_lt (fun _ _ h => ParR_lt h) h) (Nat.lt_irrefl 3)
  rw [expandRL_some 3 n topE0 3 hb, hm]
  simp only [show topE0.length - 1 - 3 = 1 from rfl, List.range_one, List.map_singleton,
    Nat.add_zero, ha]
  congr 1
  rw [← flatten_map_single (fun t => [3 + t, 0, 0])]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  simp [topE0, List.range_succ]

/-! ### The theorem -/

theorem omegaIndexMatrix_twr (k : Nat) :
    omegaIndexMatrix (twr (k + 3))
      = [[0,0,0],[1,1,1],[2,1,1]] ++ (List.range (k + 1)).map (fun t => [3 + t, 0, 0]) := by
  have hu : unread 0 (twr (k + 1)) = List.range (k + 1) := by
    rw [← read_range_eq_twr, unread_read _ 0 (col_range k)]
  have hne : twr (k + 1) ≠ nil := by rw [twr]; simp
  have hne2 : (twr (k + 1) == nil) = false := by simpa using hne
  rw [omegaIndexMatrix, twr, addUnits]
  simp only [show (twr (k + 2) == nil) = false by rw [twr]; simp, Bool.false_eq_true, if_false]
  rw [bodyU, peelOne, twr]
  simp only [isFiniteT, hne2, Bool.false_and, Bool.false_eq_true, if_false]
  rw [mulUnits, mulUnits, prSS, hu,
    show addUnits (0 + 2) (0 + 1) false (1 + 1) nil = [] from rfl]
  simp

/-- The one-row matrices whose trio matrix is reachable. -/
def RTrio (l : List Nat) : Prop := ZT (read 0 l) ∧ Reach3 (omegaIndexMatrix (read 0 l))

theorem rTrio_gen (n : Nat) : RTrio (List.range (n + 1)) := by
  rw [RTrio, read_range_eq_twr]
  refine ⟨⟨fun _ => trivial, trivial⟩, ?_⟩
  match n with
  | 0 =>
    have := reach3_expand (reach3_gen 1) 1
    rwa [show expandRL 3 1 ((List.range (1 + 1)).map (fun i => List.replicate 3 i))
      = omegaIndexMatrix (twr (0 + 1)) by decide] at this
  | 1 =>
    have := reach3_gen 1
    rwa [show (List.range (1 + 1)).map (fun i => List.replicate 3 i)
      = omegaIndexMatrix (twr (1 + 1)) by decide] at this
  | k + 2 =>
    have := reach3_expand reach3_topE0 k
    rwa [expandRL_topE0, ← omegaIndexMatrix_twr] at this

theorem read_expandL_exT (N : Nat) {m : List Nat} (hc : Col 0 m) :
    read 0 (expandL N 0 m) = exT N (read 0 m) := by
  conv_lhs => rw [← unread_read m 0 hc]
  rw [expandL_unread, read_unread _ (allNil_exT N _ (allNil_read 0 m)) 0]

theorem rTrio_step {m : List Nat} (hc : Col 0 m) (h : RTrio m) (N : Nat) :
    RTrio (expandL N 0 m) := by
  rw [RTrio, read_expandL_exT N hc]
  refine ⟨zt_exT N _ h.1, ?_⟩
  have := step_add N (read 0 m) (allNil_read 0 m) h.1 0 0 false 0
    (fun h => absurd h (by simp)) [] (by simpa [omegaIndexMatrix] using h.2)
  simpa [omegaIndexMatrix] using this

/-- **The trio matrix of every standard form below `ε₀` is reachable.** -/
theorem reach3_omegaIndexMatrix {α : Term} (hA : AllNil α) (hOT : OT α) :
    Reach3 (omegaIndexMatrix α) := by
  have h := reach_gen RTrio (fun hc hR N => rTrio_step hc hR N) rTrio_gen
    (col_unread α hA 0) (by rw [read_unread α hA 0]; exact hOT)
  rw [RTrio, read_unread α hA 0] at h
  exact h.2

theorem trioMatrix_allNil (α : Term) (h : AllNil α) : trioMatrix α = omegaIndexMatrix α := by
  unfold trioMatrix
  split
  · rename_i X
    have hX : X = nil := h.2.1.1
    subst hX
    rfl
  · rfl

end TrioStd

/-- **The trio matrix of `ψ_0(Ω_α)` is a standard form**, for every standard
`α < ε₀`: it is the entries of a three-row array reachable from a generator
`(0,0,0)(1,1,1)⋯(n,n,n)` by expansions. -/
theorem omegaIndexMatrix_std (α : exbE0.State) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ entriesR A = omegaIndexMatrix α.1 :=
  TrioStd.reach3_omegaIndexMatrix (allNil_of_state α) α.2.1

/-- The same for `trioMatrix`, which is `omegaIndexMatrix` below `ε₀`. -/
theorem trioMatrix_std (α : exbE0.State) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ entriesR A = trioMatrix α.1 := by
  rw [TrioStd.trioMatrix_allNil α.1 (allNil_of_state α)]
  exact omegaIndexMatrix_std α

/-- **The trio matrix as a state of `bmsL 2`**, the three-row system on the
entries. -/
def omegaIndexState (α : exbE0.State) : (bmsL 2).State :=
  ⟨omegaIndexMatrix α.1, omegaIndexMatrix_std α⟩

end Googology.Trans.BMS
