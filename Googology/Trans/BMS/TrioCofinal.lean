import Googology.Trans.BMS.TrioCof.Core
import Googology.Trans.BMS.Agree

/-!
# Trio sequences: expansion is cofinal

The trio sequences are the three-row Bashicu matrices of the `z < 2`
fragment: the matrices reachable from `(0,0,0)(1,1,1)(2,2,1)⋯(v,v,1)` by
expansion.  This file proves that among them `[ ]` is a fundamental sequence:
every member `A[k]` is below `A`, and anything standard below `A` is at or
below some `A[k]`.

The proof is koteitan/trio's `trio_cofinality`
([lean/Core.lean](https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Core.lean)),
ported unchanged into `Googology/Trans/BMS/TrioCof/` (16 modules, about
16,600 lines, no `sorry`).  It is stated there for trio's own definitions: a
trio sequence is a list of triples, `oper M n` (`M⟦n⟧`) is the expansion with
`n` copies, `ST_TS` is the set of standard forms, and the order is either
`seqlex`, the column-lexicographic order, or `<o` on the terms `Three` through
`translate`.

This file is the bridge to this library's `bmsL 2`, whose states are entry
lists and whose step is `expandRL 3`.

* `toL` turns a trio sequence into its entries.
* `expandRL_toL`: on a standard trio sequence with at least two columns,
  `expandRL 3 n (toL M) = toL (M⟦n+1⟧)` — the two expansions agree.  The
  parent relations agree on every sequence (`ParR_toL`); what needs the
  standard form is that the last column has a parent in its lowest nonzero
  row (trio's `hasParent_last_ST_TS`), which makes BM4's `m₀` equal trio's
  `srow`.
* `TrioStdL` is the trio fragment on this library's side: the least set of
  entry lists containing `trioGen v = (0,0,0)(1,1,1)(2,2,1)⋯(v,v,1)` and
  closed under `expandRL 3 n`.  `trioStdL_iff`: it is `[]` together with the
  images of trio's `ST_TS`.  `trioStdL_std`: every member is the entries of a
  standard `Arr 3`, so `trioStd` is a `Rewrite.Std` of `bmsL 2`.
* `lt_toL_iff`: the order `<` on `List (List Nat)` (lexicographic, columns
  compared lexicographically) is `seqlex`.

The results, with `<` the lexicographic order on entry lists:

* `trio_expand_lt`: `A ≠ [] → A[k] < A`;
* `trio_cofinal`: `B < A → ∃ k, B = A[k] ∨ B < A[k]`;
* `trio_fs`: the two together;
* `trioTerm_lt_iff` and `trio_cofinal_term`: the same through trio's terms
  `Three` and its order `<o`.
-/

namespace Googology.Trans.BMS.TrioCofinal

open Googology.Trans.BMS (bmsL expandRL badRootR m0L parAtR ParR AncR ancAtR entriesR)
open TrioCof (TrioSeq)

/-! ## Entries of a trio sequence -/

/-- A column as its three entries. -/
def colL (c : Nat × Nat × Nat) : List Nat := [c.1, c.2.1, c.2.2]

/-- A trio sequence as an entry list. -/
def toL (M : TrioSeq) : List (List Nat) := M.map colL

/-- An entry list as a trio sequence. -/
def ofL (l : List (List Nat)) : TrioSeq := l.map (fun c => (c.getD 0 0, c.getD 1 0, c.getD 2 0))

@[simp] theorem toL_length (M : TrioSeq) : (toL M).length = M.length := List.length_map _

theorem ofL_toL (M : TrioSeq) : ofL (toL M) = M := by
  rw [ofL, toL, List.map_map]
  conv_rhs => rw [← List.map_id M]
  exact List.map_congr_left (fun _ _ => rfl)

theorem toL_injective : Function.Injective toL := fun a b h => by
  rw [← ofL_toL a, h, ofL_toL]

theorem toL_entry (M : TrioSeq) (j k : Nat) (hk : k < 3) :
    ((toL M)[j]!)[k]! = TrioCof.entry M k j := by
  by_cases h : j < M.length
  · rw [getElem!_pos (toL M) j (by rw [toL_length]; exact h)]
    have hg : M.getD j (0, 0, 0) = M[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
    simp only [toL, List.getElem_map, TrioCof.entry, hg]
    interval_cases k <;> rfl
  · rw [getElem!_neg (toL M) j (by rw [toL_length]; exact h)]
    have hg : M.getD j (0, 0, 0) = (0, 0, 0) := List.getD_eq_default _ _ (by omega)
    simp only [TrioCof.entry, hg]
    interval_cases k <;> rfl

@[simp] theorem toL_e0 (M : TrioSeq) (j : Nat) : ((toL M)[j]!)[0]! = TrioCof.entry M 0 j :=
  toL_entry M j 0 (by omega)
@[simp] theorem toL_e1 (M : TrioSeq) (j : Nat) : ((toL M)[j]!)[1]! = TrioCof.entry M 1 j :=
  toL_entry M j 1 (by omega)
@[simp] theorem toL_e2 (M : TrioSeq) (j : Nat) : ((toL M)[j]!)[2]! = TrioCof.entry M 2 j :=
  toL_entry M j 2 (by omega)

theorem lt_len_of_entry_pos {M : TrioSeq} {k j : Nat} (h : 0 < TrioCof.entry M k j) :
    j < M.length := by
  by_contra hc
  have hg : M.getD j (0, 0, 0) = (0, 0, 0) := List.getD_eq_default _ _ (by omega)
  unfold TrioCof.entry at h
  rw [hg] at h
  split_ifs at h <;> simp at h

/-! ## The parent relations agree -/

theorem rtg_le {R : Nat → Nat → Prop} (hR : ∀ a b, R a b → a < b) {a b : Nat}
    (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hr ih => exact Nat.le_trans ih (Nat.le_of_lt (hR _ _ hr))

theorem tg_lt {R : Nat → Nat → Prop} (hR : ∀ a b, R a b → a < b) {a b : Nat}
    (h : Relation.TransGen R a b) : a < b := by
  obtain ⟨c, hac, hcb⟩ := Relation.TransGen.tail'_iff.mp h
  exact Nat.lt_of_le_of_lt (rtg_le hR hac) (hR _ _ hcb)

/-- A strict chain of a relation that stays inside the sequence is the
ancestor relation with its bounds. -/
theorem tg_iff {R : Nat → Nat → Prop} (n : Nat) (hR : ∀ a b, R a b → a < b ∧ b < n)
    (a b : Nat) :
    Relation.TransGen R a b ↔ a < b ∧ (a < n ∧ b < n ∧ Relation.ReflTransGen R a b) := by
  constructor
  · intro h
    have hab := tg_lt (fun x y hr => (hR x y hr).1) h
    obtain ⟨c, _, hcb⟩ := Relation.TransGen.tail'_iff.mp h
    have hb := (hR _ _ hcb).2
    exact ⟨hab, by omega, hb, h.to_reflTransGen⟩
  · rintro ⟨hab, -, -, h⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with he | ht
    · omega
    · exact ht

theorem nextrel0_bounds {M : TrioSeq} {a b : Nat} (h : TrioCof.nextrel0 M a b) :
    a < b ∧ b < M.length := ⟨h.2.2.1, h.2.1⟩
theorem nextrel1_bounds {M : TrioSeq} {a b : Nat} (h : TrioCof.nextrel1 M a b) :
    a < b ∧ b < M.length := ⟨h.2.2.1, h.2.1⟩
theorem nextrel2_bounds {M : TrioSeq} {a b : Nat} (h : TrioCof.nextrel2 M a b) :
    a < b ∧ b < M.length := ⟨h.2.2.1, h.2.1⟩

theorem ParR0_eq (M : TrioSeq) : ParR (toL M) 0 = TrioCof.nextrel0 M := by
  funext j i
  apply propext
  simp only [ParR, toL_e0, TrioCof.nextrel0]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hi := lt_len_of_entry_pos (show 0 < TrioCof.entry M 0 i by omega)
    exact ⟨by omega, hi, h1, h2, fun j' hj' => h3 j' hj'.1 hj'.2⟩
  · rintro ⟨_, _, h1, h2, h3⟩
    exact ⟨h1, h2, fun j' a b => h3 j' ⟨a, b⟩⟩

theorem tg0_iff (M : TrioSeq) (a b : Nat) :
    Relation.TransGen (ParR (toL M) 0) a b ↔ a < b ∧ TrioCof.le0 M a b := by
  rw [ParR0_eq]
  exact tg_iff M.length (fun _ _ h => nextrel0_bounds h) a b

theorem ParR_succ_iff (l : List (List Nat)) (k j i : Nat) :
    ParR l (k + 1) j i ↔ j < i ∧ Relation.TransGen (ParR l k) j i ∧
      (l[j]!)[k + 1]! < (l[i]!)[k + 1]! ∧
      ∀ j', j < j' → j' < i → Relation.TransGen (ParR l k) j' i →
        (l[i]!)[k + 1]! ≤ (l[j']!)[k + 1]! := Iff.rfl

theorem ParR1_eq (M : TrioSeq) : ParR (toL M) 1 = TrioCof.nextrel1 M := by
  funext j i
  apply propext
  rw [ParR_succ_iff]
  simp only [Nat.zero_add, toL_e1, TrioCof.nextrel1, tg0_iff]
  constructor
  · rintro ⟨h1, ⟨_, h2⟩, h3, h4⟩
    refine ⟨h2.1, h2.2.1, h1, h3, h2, fun j' ⟨hj', hle⟩ => ?_⟩
    have hle' := rtg_le (fun x y h => nextrel0_bounds h |>.1) hle.2.2
    rcases Nat.lt_or_ge j' i with hlt | hge
    · exact h4 j' hj' hlt ⟨hlt, hle⟩
    · rw [show j' = i by omega]
  · rintro ⟨_, _, h1, h3, h2, h4⟩
    exact ⟨h1, ⟨h1, h2⟩, h3, fun j' a _ hc => h4 j' ⟨a, hc.2⟩⟩

theorem tg1_iff (M : TrioSeq) (a b : Nat) :
    Relation.TransGen (ParR (toL M) 1) a b ↔ a < b ∧ TrioCof.le1 M a b := by
  rw [ParR1_eq]
  exact tg_iff M.length (fun _ _ h => nextrel1_bounds h) a b

theorem ParR2_eq (M : TrioSeq) : ParR (toL M) 2 = TrioCof.nextrel2 M := by
  funext j i
  apply propext
  rw [ParR_succ_iff]
  simp only [Nat.reduceAdd, toL_e2, TrioCof.nextrel2, tg1_iff]
  constructor
  · rintro ⟨h1, ⟨_, h2⟩, h3, h4⟩
    refine ⟨h2.1, h2.2.1, h1, h3, h2, fun j' ⟨hj', hle⟩ => ?_⟩
    have hle' := rtg_le (fun x y h => nextrel1_bounds h |>.1) hle.2.2
    rcases Nat.lt_or_ge j' i with hlt | hge
    · exact h4 j' hj' hlt ⟨hlt, hle⟩
    · rw [show j' = i by omega]
  · rintro ⟨_, _, h1, h3, h2, h4⟩
    exact ⟨h1, ⟨h1, h2⟩, h3, fun j' a _ hc => h4 j' ⟨a, hc.2⟩⟩

/-- **The parent relations agree**, at each of the three rows and on every
sequence: this library's `ParR` on the entries is trio's `nextR`. -/
theorem ParR_toL (M : TrioSeq) (k : Nat) (hk : k < 3) :
    ParR (toL M) k = TrioCof.nextR M k := by
  funext j i
  interval_cases k
  · rw [ParR0_eq]; rfl
  · rw [ParR1_eq]; rfl
  · rw [ParR2_eq]; rfl

theorem parAtR_toL_some (M : TrioSeq) (k : Nat) (hk : k < 3) (i j : Nat) :
    parAtR (toL M) k i = some j ↔ TrioCof.nextR M k j i := by
  rw [parAtR_eq_some, ParR_toL M k hk]

theorem not_nextR_of_zero {M : TrioSeq} {k j i : Nat} (hk : k < 3)
    (h : TrioCof.entry M k i = 0) : ¬ TrioCof.nextR M k j i := by
  intro hn
  unfold TrioCof.nextR at hn
  interval_cases k
  · have := hn.2.2.2.1; simp at hn; omega
  · have := hn.2.2.2.1; simp at hn; omega
  · have := hn.2.2.2.1; simp at hn; omega

/-! ## The expansions agree -/

theorem srow_le (M : TrioSeq) (j : Nat) : TrioCof.srow M j ≤ 2 := by
  unfold TrioCof.srow
  split_ifs <;> omega

/-- Above the lowest nonzero row the last column is `0`. -/
theorem entry_zero_of_srow_lt {M : TrioSeq} {j k : Nat} (hk : k < 3)
    (h : TrioCof.srow M j < k) : TrioCof.entry M k j = 0 := by
  unfold TrioCof.srow at h
  interval_cases k
  · omega
  · split_ifs at h with h2 h1
    · omega
    · omega
    · omega
  · split_ifs at h with h2 h1 <;> omega

theorem m0L_toL {M : TrioSeq} {i : Nat} (hi : i = M.length - 1)
    (hp : TrioCof.hasParent M (TrioCof.srow M i) i) :
    m0L 3 (toL M) = TrioCof.srow M i := by
  rw [m0L, toL_length, ← hi, Nat.findGreatest_eq_iff]
  refine ⟨srow_le M i, fun _ => ?_, fun k hk hk3 => ?_⟩
  · obtain ⟨j, hj, _⟩ := hp
    rw [Option.isSome_iff_exists]
    exact ⟨j, (parAtR_toL_some M _ (by have := srow_le M i; omega) i j).mpr hj⟩
  · rw [Option.isSome_iff_exists]
    rintro ⟨j, hj⟩
    exact not_nextR_of_zero (by omega) (entry_zero_of_srow_lt (by omega) hk)
      ((parAtR_toL_some M k (by omega) i j).mp hj)

theorem badRootR_toL {M : TrioSeq} (hlen : 1 < M.length)
    (hp : TrioCof.hasParent M (TrioCof.srow M (M.length - 1)) (M.length - 1)) :
    badRootR 3 (toL M) = some (TrioCof.parent M (TrioCof.srow M (M.length - 1)) (M.length - 1)) := by
  have hne : (toL M).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, toL_length]; omega
  rw [badRootR, hne, if_neg (by simp), m0L_toL rfl hp, toL_length]
  exact (parAtR_toL_some M _ (by have := srow_le M (M.length - 1); omega) _ _).mpr
    (TrioCof.parent_nextR hp)

theorem badRootR_toL_zero {M : TrioSeq} (hlen : 1 < M.length)
    (hz : TrioCof.entry M 0 (M.length - 1) = 0 ∧ TrioCof.entry M 1 (M.length - 1) = 0 ∧
      TrioCof.entry M 2 (M.length - 1) = 0) :
    badRootR 3 (toL M) = none := by
  have hne : (toL M).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, toL_length]; omega
  have hnone : ∀ k, k < 3 → parAtR (toL M) k (M.length - 1) = none := by
    intro k hk
    rw [Option.eq_none_iff_forall_ne_some]
    intro j hj
    refine not_nextR_of_zero hk ?_ ((parAtR_toL_some M k hk _ j).mp hj)
    interval_cases k
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  have hm : m0L 3 (toL M) = 0 := by
    rw [m0L, Nat.findGreatest_eq_zero_iff]
    intro k _ hk
    rw [toL_length, hnone k (by omega)]
    simp
  rw [badRootR, hne, if_neg (by simp), hm, toL_length]
  exact hnone 0 (by omega)

theorem toL_append (A B : TrioSeq) : toL (A ++ B) = toL A ++ toL B := List.map_append

theorem toL_take (M : TrioSeq) (j : Nat) : toL (M.take j) = (toL M).take j := List.map_take

theorem toL_flatMap {α : Type} (f : α → TrioSeq) (l : List α) :
    toL (l.flatMap f) = l.flatMap (fun a => toL (f a)) := List.map_flatMap

theorem toL_map {α : Type} (f : α → Nat × Nat × Nat) (l : List α) :
    toL (l.map f) = l.map (colL ∘ f) := List.map_map

theorem map_range_getElem! (l : List (List Nat)) (p : Nat) (hp : p ≤ l.length) :
    (List.range p).map (fun i => l[i]!) = l.take p := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact getElem!_pos l i (by simp at h1; omega)

theorem map_range_mul {α : Type} (F : Nat → α) (L : Nat) : ∀ m : Nat,
    (List.range (m * L)).map F
      = (List.range m).flatMap (fun k => (List.range L).map (fun i => F (k * L + i)))
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, List.range_add, List.map_append, map_range_mul F L m, List.range_succ,
      List.flatMap_append, List.flatMap_singleton, List.map_map]
    rfl

/-- `(j0 == j) || ancAtR …` is trio's reflexive row-`0` ancestry. -/
theorem anc0_iff {M : TrioSeq} {j0 j : Nat} (h0 : j0 < M.length) (hj : j0 ≤ j) :
    ((j0 == j) || ancAtR (toL M) 0 j0 j) = true ↔ TrioCof.le0 M j0 j := by
  rw [Bool.or_eq_true, beq_iff_eq, ancAtR_iff, AncR, tg0_iff]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact ⟨h0, h0, Relation.ReflTransGen.refl⟩
    · exact h
  · intro h
    rcases Nat.eq_or_lt_of_le hj with he | hlt
    · exact Or.inl he
    · exact Or.inr ⟨hlt, h⟩

theorem anc1_iff {M : TrioSeq} {j0 j : Nat} (h0 : j0 < M.length) (hj : j0 ≤ j) :
    ((j0 == j) || ancAtR (toL M) 1 j0 j) = true ↔ TrioCof.le1 M j0 j := by
  rw [Bool.or_eq_true, beq_iff_eq, ancAtR_iff, AncR, tg1_iff]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact ⟨h0, h0, Relation.ReflTransGen.refl⟩
    · exact h
  · intro h
    rcases Nat.eq_or_lt_of_le hj with he | hlt
    · exact Or.inl he
    · exact Or.inr ⟨hlt, h⟩

/-- **The two expansions agree** on a sequence with at least two columns
whose last column is `0` or has a parent in its lowest nonzero row.
`expandRL 3 n` writes `n + 1` copies, `M⟦n + 1⟧` too. -/
theorem expandRL_toL_of {M : TrioSeq} (n : Nat) (hlen : 1 < M.length)
    (hP : ¬ (TrioCof.entry M 0 (M.length - 1) = 0 ∧ TrioCof.entry M 1 (M.length - 1) = 0 ∧
      TrioCof.entry M 2 (M.length - 1) = 0) →
      TrioCof.hasParent M (TrioCof.srow M (M.length - 1)) (M.length - 1)) :
    expandRL 3 n (toL M) = toL (M⟦n + 1⟧) := by
  have hL : M.length - 1 ≠ 0 := by omega
  by_cases hz : TrioCof.entry M 0 (M.length - 1) = 0 ∧ TrioCof.entry M 1 (M.length - 1) = 0 ∧
      TrioCof.entry M 2 (M.length - 1) = 0
  · rw [expandRL, badRootR_toL_zero hlen hz, TrioCof.oper_eq_pred_of_zero _ hL hz,
      TrioCof.Pred, if_neg (by omega)]
    dsimp only
    exact List.map_dropLast.symm
  · have hp := hP hz
    have hm0 := m0L_toL rfl hp
    have hj0lt0 := TrioCof.nextR_index_lt (TrioCof.parent_nextR hp)
    rw [expandRL, badRootR_toL hlen hp, TrioCof.oper_bad_unfold _ hL hz hp]
    dsimp only
    -- name the pieces
    generalize hs : TrioCof.srow M (M.length - 1) = s at *
    generalize hj0 : TrioCof.parent M s (M.length - 1) = j0 at *
    have hs2 : s ≤ 2 := hs ▸ srow_le M _
    have hj0lt : j0 < M.length - 1 := hj0lt0
    rw [hm0, toL_length, toL_append, toL_take,
      ← map_range_getElem! (toL M) j0 (by rw [toL_length]; omega), map_range_mul, toL_flatMap]
    congr 1
    refine congrArg (fun f => List.flatMap f _) (funext fun k => ?_)
    dsimp only
    rw [toL_map, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left (fun i hi => ?_)
    have hi : i < M.length - 1 - j0 := List.mem_range.mp hi
    have hmod : (k * (M.length - 1 - j0) + i) % (M.length - 1 - j0) = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    have hdiv : (k * (M.length - 1 - j0) + i) / (M.length - 1 - j0) = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi,
        Nat.zero_add]
    rw [hmod, hdiv, show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, Function.comp, colL, toL_e0, toL_e1, toL_e2]
    have h0 := anc0_iff (M := M) (j0 := j0) (j := j0 + i) (by omega) (by omega)
    have h1 := anc1_iff (M := M) (j0 := j0) (j := j0 + i) (by omega) (by omega)
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
    · by_cases hsp : 0 < s
      · by_cases ha : TrioCof.le0 M j0 (j0 + i)
        · rw [if_pos (by simp [hsp, h0.mpr ha]), if_pos ha, if_pos hsp]
        · rw [if_neg (fun h => ha (h0.mp (by simp only [Bool.and_eq_true] at h; exact h.2))),
            if_neg ha]
          simp
      · rw [if_neg (by simp [hsp])]
        split_ifs <;> simp
    · by_cases hsp : 1 < s
      · by_cases ha : TrioCof.le1 M j0 (j0 + i)
        · rw [if_pos (by simp [hsp, h1.mpr ha]), if_pos ha, if_pos hsp]
        · rw [if_neg (fun h => ha (h1.mp (by simp only [Bool.and_eq_true] at h; exact h.2))),
            if_neg ha]
          simp
      · rw [if_neg (by simp [hsp])]
        split_ifs <;> simp
    · rw [if_neg (by simp; omega)]

/-- **On standard trio sequences the two expansions agree.** -/
theorem expandRL_toL {M : TrioSeq} (hM : TrioCof.ST_TS M) (hlen : 1 < M.length) (n : Nat) :
    expandRL 3 n (toL M) = toL (M⟦n + 1⟧) :=
  expandRL_toL_of n hlen (TrioCof.hasParent_last_ST_TS hM (by omega))

/-- One column expands to nothing. -/
theorem expandRL_short (l : List (List Nat)) (hl : l.length ≤ 1) (n : Nat) :
    expandRL 3 n l = [] := by
  have hb : badRootR 3 l = none := by
    rw [badRootR]
    split_ifs with he
    · rfl
    · rw [Option.eq_none_iff_forall_ne_some]
      intro j hj
      have := ParR_lt ((parAtR_eq_some _ _ _ _).mp hj)
      omega
  rw [expandRL, hb]
  dsimp only
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl

/-! ## The trio fragment of `bmsL 2` -/

/-- The generator `(0,0,0)(1,1,1)(2,2,1)⋯(v,v,1)`. -/
def trioGen (v : Nat) : List (List Nat) := (List.range (v + 1)).map (fun i => [i, i, min i 1])

theorem trioGen_eq (v : Nat) : trioGen v = toL (TrioCof.diagSeqT 0 v) := by
  rw [trioGen, toL, TrioCof.diagSeqT, List.map_map, Nat.sub_zero, List.range_eq_range']
  rfl

/-- **The trio fragment**: the least set of three-row entry lists that holds
the generators and is closed under expansion. -/
inductive TrioStdL : List (List Nat) → Prop where
  | gen (v : Nat) : TrioStdL (trioGen v)
  | step {l : List (List Nat)} (n : Nat) : TrioStdL l → TrioStdL (expandRL 3 n l)

/-- Expanding at least two columns leaves at least one. -/
theorem oper_ne_nil {M : TrioSeq} (hlen : 1 < M.length) {n : Nat} (hn : 1 ≤ n) :
    M⟦n⟧ ≠ [] := by
  have hL : M.length - 1 ≠ 0 := by omega
  have hpred : TrioCof.Pred M ≠ [] := by
    rw [TrioCof.Pred, if_neg (by omega)]
    intro h
    have := congrArg List.length h
    simp at this
    omega
  by_cases hz : TrioCof.entry M 0 (M.length - 1) = 0 ∧ TrioCof.entry M 1 (M.length - 1) = 0 ∧
      TrioCof.entry M 2 (M.length - 1) = 0
  · rw [TrioCof.oper_eq_pred_of_zero n hL hz]; exact hpred
  by_cases hp : TrioCof.hasParent M (TrioCof.srow M (M.length - 1)) (M.length - 1)
  · have hj := TrioCof.nextR_index_lt (TrioCof.parent_nextR hp)
    rw [TrioCof.oper_bad_unfold n hL hz hp]
    intro h
    rw [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
    have h0 := h.2 0 (List.mem_range.mpr (by omega))
    rw [List.map_eq_nil_iff, List.range'_eq_nil_iff] at h0
    omega
  · rw [TrioCof.oper_eq_pred_of_noParent n hL hz hp]; exact hpred

theorem toL_ne_nil_of_ST {M : TrioSeq} (hM : TrioCof.ST_TS M) : M ≠ [] := by
  induction hM with
  | diag v =>
    intro h
    have := TrioCof.diagSeqT_length v
    rw [h] at this
    simp at this
  | @oper M n hM hn ih =>
    by_cases hl : M.length - 1 = 0
    · rw [TrioCof.oper_eq_self_of_short n hl]; exact ih
    · exact oper_ne_nil (by
        have : M.length ≠ 0 := fun h0 => ih (List.length_eq_zero_iff.mp h0)
        omega) hn

/-- **The trio fragment is `[]` and trio's standard forms.** -/
theorem trioStdL_iff (l : List (List Nat)) :
    TrioStdL l ↔ l = [] ∨ ∃ M, TrioCof.ST_TS M ∧ l = toL M := by
  constructor
  · intro h
    induction h with
    | gen v => exact Or.inr ⟨_, TrioCof.ST_TS.diag v, trioGen_eq v⟩
    | @step l n _ ih =>
      rcases ih with rfl | ⟨M, hM, rfl⟩
      · exact Or.inl (expandRL_short [] (by simp) n)
      · by_cases hlen : 1 < M.length
        · exact Or.inr ⟨_, TrioCof.ST_TS.oper hM (by omega), expandRL_toL hM hlen n⟩
        · exact Or.inl (expandRL_short _ (by rw [toL_length]; omega) n)
  · rintro (rfl | ⟨M, hM, rfl⟩)
    · have := TrioStdL.step 0 (TrioStdL.gen 0)
      rwa [expandRL_short (trioGen 0) (by simp [trioGen]) 0] at this
    · induction hM with
      | diag v => rw [← trioGen_eq]; exact TrioStdL.gen v
      | @oper M n hM hn ih =>
        by_cases hlen : 1 < M.length
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [← expandRL_toL hM hlen m]
          exact TrioStdL.step m ih
        · rw [TrioCof.oper_eq_self_of_short n (by omega)]
          exact ih

/-- `(0,0,0)(1,1,1)(2,2,2)[v-1]` is the generator `v`. -/
theorem expandRL_stair2 (N : Nat) :
    expandRL 3 N [[0, 0, 0], [1, 1, 1], [2, 2, 2]] = trioGen (N + 1) := by
  have hb : badRootR 3 [[0, 0, 0], [1, 1, 1], [2, 2, 2]] = some 1 := by decide
  have hm : m0L 3 [[0, 0, 0], [1, 1, 1], [2, 2, 2]] = 2 := by decide
  rw [expandRL, hb]
  dsimp only
  rw [hm, show (List.range 1).map (fun i => [[0, 0, 0], [1, 1, 1], [2, 2, 2]][i]!)
      = [[0, 0, 0]] from rfl, trioGen, List.range_succ_eq_map (n := N + 1), List.map_cons,
    List.map_map, List.singleton_append,
    show [[0, 0, 0], [1, 1, 1], [2, 2, 2]].length - 1 - 1 = 1 from rfl, Nat.mul_one]
  congr 1
  refine List.map_congr_left (fun t _ => ?_)
  simp only [Nat.mod_one, Nat.div_one, Nat.add_zero, show List.range 3 = [0, 1, 2] from rfl,
    List.map_cons, List.map_nil, Function.comp]
  simp
  omega

/-- **Every member of the trio fragment is the entries of a standard
three-row array.** -/
theorem trioStdL_std {l : List (List Nat)} (h : TrioStdL l) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ entriesR A = l := by
  induction h with
  | gen v =>
    rcases v with _ | _ | v
    · exact ⟨Pat.stair 3 0, Pat.Std.init 0, by rw [entriesR_stair]; rfl⟩
    · exact ⟨Pat.stair 3 1, Pat.Std.init 1, by rw [entriesR_stair]; rfl⟩
    · refine ⟨BM4.expand (Pat.stair 3 2) (v + 1), Pat.Std.step _ (Pat.Std.init 2), ?_⟩
      rw [entriesR_expand (by omega), entriesR_stair]
      exact expandRL_stair2 (v + 1)
  | @step l n _ ih =>
    obtain ⟨A, hA, rfl⟩ := ih
    exact ⟨BM4.expand A n, Pat.Std.step n hA, entriesR_expand (by omega) A n⟩

/-- **The trio fragment as standard forms of `bmsL 2`.** -/
def trioStd : (bmsL 2).Std where
  Standard := fun a => TrioStdL a.1
  gen := fun v => ⟨trioGen v, trioStdL_std (TrioStdL.gen v)⟩
  gen_std := fun v => TrioStdL.gen v
  step_std := fun _ k h => TrioStdL.step k h

/-! ## The order -/

theorem colL_lt_iff (p q : Nat × Nat × Nat) : colL p < colL q ↔ TrioCof.collt p q := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨d, e, f⟩ := q
  simp only [colL, TrioCof.collt, List.cons_lt_cons_iff, List.not_lt_nil, and_false, or_false]

theorem colL_inj {p q : Nat × Nat × Nat} (h : colL p = colL q) : p = q := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨d, e, f⟩ := q
  simp only [colL, List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl, -⟩ := h
  rfl

/-- **The lexicographic order on entry lists is trio's `seqlex`.** -/
theorem lt_toL_iff : ∀ (N M : TrioSeq), toL N < toL M ↔ TrioCof.seqlex N M
  | [], [] => by simp [toL, TrioCof.seqlex]
  | [], _ :: _ => by simp [toL, TrioCof.seqlex, List.nil_lt_cons]
  | _ :: _, [] => by simp [toL, TrioCof.seqlex]
  | p :: N, q :: M => by
    rw [TrioCof.seqlex_cons_cons, ← colL_lt_iff, ← lt_toL_iff N M]
    simp only [toL, List.map_cons, List.cons_lt_cons_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨colL_inj h1, h2⟩
    · rintro (h | ⟨rfl, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h2⟩

theorem head_ST {M : TrioSeq} (hM : TrioCof.ST_TS M) (hne : M ≠ []) :
    ∃ M', M = (0, 0, 0) :: M' := by
  obtain ⟨c, M', rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := (TrioCof.blockok_ST_TS hM).1 hne
  have hz := TrioCof.z0ok_ST_TS hM 0 (by simp) h0
  obtain ⟨x, y, z⟩ := c
  simp only [List.headI_cons] at h0
  simp only [List.getD_cons_zero] at hz
  obtain ⟨hy, hz⟩ := hz
  subst h0 hy hz
  exact ⟨M', rfl⟩

/-! ## The fundamental sequence -/

/-- **Every member is below**: `A[k] < A` for a nonempty standard `A`. -/
theorem trio_expand_lt {a : List (List Nat)} (ha : TrioStdL a) (hne : a ≠ []) (k : Nat) :
    expandRL 3 k a < a := by
  rcases (trioStdL_iff a).mp ha with rfl | ⟨M, hM, rfl⟩
  · exact absurd rfl hne
  · by_cases hlen : 1 < M.length
    · rw [expandRL_toL hM hlen k, lt_toL_iff]
      have hd := TrioCof.m_step_decreases (n := k + 1) hlen (by omega)
      have hne' : M⟦k + 1⟧ ≠ M := fun h => TrioCof.Three.olt_irrefl _ (h ▸ hd)
      exact (TrioCof.olt_ST_iff_seqlex (TrioCof.ST_TS.oper hM (by omega)) hM hne').mp hd
    · rw [expandRL_short _ (by rw [toL_length]; omega)]
      obtain ⟨c, M', rfl⟩ := List.exists_cons_of_ne_nil (toL_ne_nil_of_ST hM)
      simp [toL, List.nil_lt_cons]

/-- The seqlex form of trio's cofinality, from koteitan/trio's
`argDomCore_holds`. -/
theorem seqlexCofinality : TrioCof.SeqlexCofinality :=
  TrioCof.seqlex_cofinality_of_crux
    (TrioCof.badCrux_of_asc (TrioCof.trioAscCrux_of_core TrioCof.argDomCore_holds))

/-- **Expansion is cofinal in the trio fragment**: anything standard below
`A` is at or below some `A[k]`. -/
theorem trio_cofinal {a b : List (List Nat)} (ha : TrioStdL a) (hb : TrioStdL b) (h : b < a) :
    ∃ k, b = expandRL 3 k a ∨ b < expandRL 3 k a := by
  rcases (trioStdL_iff b).mp hb with rfl | ⟨N, hN, rfl⟩
  · refine ⟨0, ?_⟩
    cases expandRL 3 0 a with
    | nil => exact Or.inl rfl
    | cons c l => exact Or.inr (List.nil_lt_cons c l)
  rcases (trioStdL_iff a).mp ha with rfl | ⟨M, hM, rfl⟩
  · exact absurd h (List.not_lt_nil _)
  rw [lt_toL_iff] at h
  by_cases hlen : 1 < M.length
  · obtain ⟨n, hn, hle⟩ := seqlexCofinality hM hN h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, ?_⟩
    rw [expandRL_toL hM hlen m, lt_toL_iff]
    rcases hle with he | hlt
    · exact Or.inl (by rw [he])
    · exact Or.inr hlt
  · exfalso
    obtain ⟨M', rfl⟩ := head_ST hM (toL_ne_nil_of_ST hM)
    obtain ⟨N', rfl⟩ := head_ST hN (toL_ne_nil_of_ST hN)
    rcases M' with _ | ⟨c, M''⟩
    · rw [TrioCof.seqlex_cons_cons] at h
      rcases h with h | ⟨_, h⟩
      · simp [TrioCof.collt] at h
      · cases N' <;> simp [TrioCof.seqlex] at h
    · simp at hlen

/-- **`[ ]` is a fundamental sequence on the trio fragment**: below `A`, and
cofinal below `A`. -/
theorem trio_fs {a : List (List Nat)} (ha : TrioStdL a) (hne : a ≠ []) :
    (∀ k, expandRL 3 k a < a) ∧
      ∀ b, TrioStdL b → b < a → ∃ k, b = expandRL 3 k a ∨ b < expandRL 3 k a :=
  ⟨trio_expand_lt ha hne, fun _ hb h => trio_cofinal ha hb h⟩

/-- The same, stated on the states of `bmsL 2` and its step. -/
theorem trioStd_cofinal (a b : (bmsL 2).State) (ha : trioStd.Standard a)
    (hb : trioStd.Standard b) (h : b.1 < a.1) :
    ∃ k, b.1 = ((bmsL 2).step a k).1 ∨ b.1 < ((bmsL 2).step a k).1 :=
  trio_cofinal ha hb h

/-! ## Through trio's terms -/

/-- The term of an entry list: trio's `translate` of the sequence. -/
def trioTerm (l : List (List Nat)) : TrioCof.Three := TrioCof.translate (ofL l)

/-- **On the trio fragment the term order is the lexicographic order.** -/
theorem trioTerm_lt_iff {a b : List (List Nat)} (ha : TrioStdL a) (hb : TrioStdL b) :
    TrioCof.Three.olt (trioTerm b) (trioTerm a) ↔ b < a := by
  rcases (trioStdL_iff a).mp ha with rfl | ⟨M, hM, rfl⟩
  · simp [trioTerm, ofL, TrioCof.translate, List.not_lt_nil]
  rcases (trioStdL_iff b).mp hb with rfl | ⟨N, hN, rfl⟩
  · obtain ⟨c, M', rfl⟩ := List.exists_cons_of_ne_nil (toL_ne_nil_of_ST hM)
    simp [trioTerm, ofL, toL, TrioCof.translate, List.nil_lt_cons]
  rw [trioTerm, trioTerm, ofL_toL, ofL_toL, lt_toL_iff]
  by_cases he : N = M
  · subst he
    constructor
    · intro h; exact absurd h (TrioCof.Three.olt_irrefl _)
    · intro h
      exact absurd ((TrioCof.olt_ST_iff_seqlex hN hN (by
        intro _; exact absurd ((lt_toL_iff N N).mpr h) (lt_irrefl _))).mpr h)
        (TrioCof.Three.olt_irrefl _)
  · exact TrioCof.olt_ST_iff_seqlex hN hM he

/-- **Cofinality through trio's terms**, the statement of koteitan/trio's
`trio_cofinality` on this library's states and step. -/
theorem trio_cofinal_term {a b : List (List Nat)} (ha : TrioStdL a) (hb : TrioStdL b)
    (h : TrioCof.Three.olt (trioTerm b) (trioTerm a)) :
    ∃ k, TrioCof.Three.ole (trioTerm b) (trioTerm (expandRL 3 k a)) := by
  obtain ⟨k, hk⟩ := trio_cofinal ha hb ((trioTerm_lt_iff ha hb).mp h)
  refine ⟨k, ?_⟩
  rcases hk with he | hlt
  · exact Or.inr (by rw [he])
  · exact Or.inl ((trioTerm_lt_iff (TrioStdL.step k ha) hb).mpr hlt)

end Googology.Trans.BMS.TrioCofinal
