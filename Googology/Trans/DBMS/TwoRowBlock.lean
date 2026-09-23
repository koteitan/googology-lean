import Googology.Trans.PSS.Expand
import Googology.Trans.BMS.Append

/-!
# Two-row DBMS: blocks

A two-row DBMS matrix is a list of **blocks**.  A block is a column `(0,0)`
followed by a pair sequence `M` whose first row is raised by one:

    blk M = (0,0) (M₀.1 + 1, M₀.2) (M₁.1 + 1, M₁.2) ⋯

The DBMS generator `(0,0)(1,0)(2,1)⋯(n,n-1)` is the block of the pair sequence
generator `(0,0)(1,1)⋯(n-1,n-1)`.  This file says how two-row expansion
(`expand2L`, which is `BM4.expand` by `entries2_expand`) acts on blocks.

* `expand2L_append`: a list that starts with a column whose first entry is `0`
  starts a block, and expansion does not look in front of it.  This is
  `BMS/Append.lean`'s `expandRL_append` read through `expandRL_two`.
* The parents under the raise: `ParL_shift`, `AncL_shift`, `ParL1_blk`.  The
  extra column `(0,0)` in front is a row-`0` ancestor of everything and never
  a row-`1` parent that `M` did not already have, as long as a positive second
  entry of `M` always has a row-`1` parent — which holds for every standard
  pair sequence (`parAt1_ne_none`).
* `expand2L_blk_some`: if `M` has a bad root, the block expands as `M` does:
  `(blk M)[N] = blk (M[N])`.
* `expand2L_blk_none`: if it has none, `M` ends in `(0,0)`, `M[N]` drops that
  column, and the block is repeated: `(blk M)[N] = blk (M[N])` written `N + 1`
  times.
-/

namespace Googology.Trans.DBMS

open Googology.Trans.BMS Googology.Trans.PSS

/-! ### Expansion only looks at the last block, with two rows -/

/-- Both rows of a pair as a column. -/
def colOf (x : ℕ × ℕ) : List ℕ := [x.1, x.2]

theorem map_colOf_injective : Function.Injective (List.map colOf) :=
  List.map_injective_iff.mpr (fun a b h => by
    simp only [colOf, List.cons.injEq, and_true] at h
    exact Prod.ext h.1 h.2)

theorem expand2L_append (N : ℕ) (P Q : List (ℕ × ℕ)) (hQ : Q ≠ []) (h0 : (Q[0]!).1 = 0) :
    expand2L N (P ++ Q) = P ++ expand2L N Q := by
  obtain ⟨q, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
  have h0' : ((Q'.map colOf |>.cons (colOf q))[0]!)[0]! = 0 := by
    show (colOf q)[0]! = 0
    simpa [colOf] using h0
  have h := expandRL_append 2 N (P.map colOf) ((q :: Q').map colOf) h0' (by simp)
  rw [← List.map_append] at h
  have e1 := expandRL_two N (P ++ q :: Q')
  have e2 := expandRL_two N (q :: Q')
  change expandRL 2 N ((P ++ q :: Q').map colOf) = (expand2L N (P ++ q :: Q')).map colOf at e1
  change expandRL 2 N ((q :: Q').map colOf) = (expand2L N (q :: Q')).map colOf at e2
  rw [e1, e2, ← List.map_append] at h
  exact map_colOf_injective h

/-! ### Shifting the first row -/

/-- The first row raised by one. -/
def shc (x : ℕ × ℕ) : ℕ × ℕ := (x.1 + 1, x.2)

/-- A pair sequence with its first row raised by one. -/
def sh (M : List (ℕ × ℕ)) : List (ℕ × ℕ) := M.map shc

/-- A block: `(0,0)` and then the pair sequence raised by one. -/
def blk (M : List (ℕ × ℕ)) : List (ℕ × ℕ) := (0, 0) :: sh M

@[simp] theorem blk_length (M : List (ℕ × ℕ)) : (blk M).length = M.length + 1 := by
  simp [blk, sh]

theorem blk_getElem_succ (M : List (ℕ × ℕ)) {k : ℕ} (hk : k < M.length) :
    (blk M)[k + 1]! = shc (M[k]!) := by
  show (sh M)[k]! = _
  rw [sh, getElem!_pos _ k (by simpa using hk), getElem!_pos M k hk, List.getElem_map]

theorem blk_getElem_succ_snd (M : List (ℕ × ℕ)) (k : ℕ) :
    ((blk M)[k + 1]!).2 = (M[k]!).2 := by
  by_cases hk : k < M.length
  · rw [blk_getElem_succ M hk]; rfl
  · show ((sh M)[k]!).2 = _
    rw [getElem!_neg (sh M) k (by simpa [sh] using hk), getElem!_neg M k hk]

theorem blk_getElem_zero (M : List (ℕ × ℕ)) : (blk M)[0]! = (0, 0) := rfl

theorem blk_fst (M : List (ℕ × ℕ)) :
    (blk M).map Prod.fst = 0 :: (M.map Prod.fst).map (· + 1) := by
  simp [blk, sh, shc, List.map_map, Function.comp_def]

theorem shift_getElem (m : List ℕ) {k : ℕ} (hk : k < m.length) :
    (0 :: m.map (· + 1))[k + 1]! = m[k]! + 1 := by
  show (m.map (· + 1))[k]! = _
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos m k hk]
  simp

/-! ### Parents and ancestors under the shift -/

theorem ParL_shift (m : List ℕ) {i : ℕ} (hi : i < m.length) (j : ℕ) :
    ParL (0 :: m.map (· + 1)) (j + 1) (i + 1) ↔ ParL m j i := by
  unfold ParL
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hj : j < m.length := by omega
    rw [shift_getElem m hj, shift_getElem m hi] at h2
    refine ⟨by omega, by omega, fun j' a b => ?_⟩
    have := h3 (j' + 1) (by omega) (by omega)
    rw [shift_getElem m hi, shift_getElem m (by omega)] at this
    omega
  · rintro ⟨h1, h2, h3⟩
    have hj : j < m.length := by omega
    rw [shift_getElem m hj, shift_getElem m hi]
    refine ⟨by omega, by omega, fun j' a b => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
    rw [shift_getElem m (by omega)]
    have := h3 k (by omega) (by omega)
    omega

theorem AncL_lt' {l : List ℕ} {a b : ℕ} (h : AncL l a b) : a < b := by
  induction h with
  | single hp => exact hp.1
  | tail _ hp ih => exact lt_trans ih hp.1

theorem AncL_shift (m : List ℕ) {i : ℕ} (hi : i < m.length) (j : ℕ) :
    AncL (0 :: m.map (· + 1)) (j + 1) (i + 1) ↔ AncL m j i := by
  constructor
  · intro h
    have key : ∀ b, Relation.TransGen (ParL (0 :: m.map (· + 1))) (j + 1) b →
        ∀ i, b = i + 1 → i < m.length → AncL m j i := by
      intro b hb
      induction hb with
      | single hp =>
        intro i hib hi
        subst hib
        exact Relation.TransGen.single ((ParL_shift m hi j).mp hp)
      | @tail c b hac hcb ih =>
        intro i hib hi
        subst hib
        have hlt : j + 1 < c := AncL_lt' hac
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have hc : c' < m.length := by have := hcb.1; omega
        exact Relation.TransGen.tail (ih c' rfl hc) ((ParL_shift m hi c').mp hcb)
    exact key _ h i rfl hi
  · intro h
    revert hi
    induction h with
    | single hp => intro hi; exact Relation.TransGen.single ((ParL_shift m hi j).mpr hp)
    | @tail c b _ hcb ih =>
      intro hi
      have hc : c < m.length := by have := hcb.1; omega
      exact Relation.TransGen.tail (ih hc) ((ParL_shift m hi c).mpr hcb)

theorem ancAtB_shift (m : List ℕ) {i : ℕ} (hi : i < m.length) (j : ℕ) :
    ancAtB (0 :: m.map (· + 1)) (j + 1) (i + 1) = ancAtB m j i := by
  rw [Bool.eq_iff_iff, ancAtB_iff, ancAtB_iff]
  exact AncL_shift m hi j

theorem ParL1_blk (M : List (ℕ × ℕ)) {i : ℕ} (hi : i < M.length) (j : ℕ) :
    ParL1 (blk M) (j + 1) (i + 1) ↔ ParL1 M j i := by
  have hi' : i < (M.map Prod.fst).length := by simpa using hi
  unfold ParL1
  rw [blk_fst, blk_getElem_succ_snd, blk_getElem_succ_snd, AncL_shift _ hi' j]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, h2, h3, fun j' a b hc => ?_⟩
    have := h4 (j' + 1) (by omega) (by omega) ((AncL_shift _ hi' j').mpr hc)
    rwa [blk_getElem_succ_snd] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, h2, h3, fun j' a b hc => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
    rw [blk_getElem_succ_snd]
    exact h4 k (by omega) (by omega) ((AncL_shift _ hi' k).mp hc)


/-! ### The bad root of a block -/

theorem badRootL_ne_nil {l : List (ℕ × ℕ)} {pb : ℕ × Bool} (h : badRootL l = some pb) :
    l ≠ [] := by
  rintro rfl
  simp [badRootL] at h

theorem badRootL_lt {l : List (ℕ × ℕ)} {p : ℕ} {b : Bool} (h : badRootL l = some (p, b)) :
    p < l.length - 1 := by
  have hne := badRootL_ne_nil h
  rw [badRootL, if_neg (by simpa using hne)] at h
  cases h1 : parAt1 l (l.length - 1) with
  | some q =>
    rw [h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact ((parAt1_eq_some _ _ _).mp h1).1
  | none =>
    rw [h1] at h
    cases h2 : parAt (l.map Prod.fst) (l.length - 1) with
    | some q =>
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ((parAt_eq_some _ _ _).mp h2).1
    | none => rw [h2] at h; exact absurd h (by simp)

theorem blk_isEmpty (M : List (ℕ × ℕ)) : (blk M).isEmpty = false := rfl

theorem parAt1_blk_none {M : List (ℕ × ℕ)} {n : ℕ} (h : (M[n]!).2 = 0) :
    parAt1 (blk M) (n + 1) = none := by
  cases h' : parAt1 (blk M) (n + 1) with
  | none => rfl
  | some j =>
    exfalso
    have hp := ((parAt1_eq_some _ _ _).mp h').2.2.1
    rw [blk_getElem_succ_snd, h] at hp
    omega

/-- **A bad root of `M` is one to the right in its block.** -/
theorem badRootL_blk_some {M : List (ℕ × ℕ)}
    (hpos : ∀ i, 0 < (M[i]!).2 → parAt1 M i ≠ none) {p : ℕ} {b : Bool}
    (h : badRootL M = some (p, b)) : badRootL (blk M) = some (p + 1, b) := by
  have hne := badRootL_ne_nil h
  have hn : M.length - 1 < M.length := by
    have := List.length_pos_of_ne_nil hne; omega
  have hl : (blk M).length - 1 = (M.length - 1) + 1 := by
    rw [blk_length]; have := List.length_pos_of_ne_nil hne; omega
  have hn' : M.length - 1 < (M.map Prod.fst).length := by simpa using hn
  rw [badRootL, if_neg (by simpa using hne)] at h
  rw [badRootL, blk_isEmpty, if_neg (by simp), hl]
  cases h1 : parAt1 M (M.length - 1) with
  | some q =>
    rw [h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : parAt1 (blk M) (M.length - 1 + 1) = some (q + 1) :=
      (parAt1_eq_some _ _ _).mpr ((ParL1_blk M hn q).mpr ((parAt1_eq_some _ _ _).mp h1))
    rw [this]
  | none =>
    rw [h1] at h
    have hs : (M[M.length - 1]!).2 = 0 := by
      by_contra hc
      exact hpos _ (by omega) h1
    rw [parAt1_blk_none hs]
    cases h2 : parAt (M.map Prod.fst) (M.length - 1) with
    | some q =>
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : parAt ((blk M).map Prod.fst) (M.length - 1 + 1) = some (q + 1) := by
        rw [blk_fst, parAt_eq_some, ParL_shift _ hn' q, ← parAt_eq_some]
        exact h2
      simp only [this]
    | none => rw [h2] at h; exact absurd h (by simp)

/-- **With no bad root, the whole block is the bad part.** -/
theorem badRootL_blk_none {M : List (ℕ × ℕ)} (hne : M ≠ [])
    (hpos : ∀ i, 0 < (M[i]!).2 → parAt1 M i ≠ none)
    (h : badRootL M = none) : badRootL (blk M) = some (0, false) := by
  have hn : M.length - 1 < M.length := by
    have := List.length_pos_of_ne_nil hne; omega
  have hl : (blk M).length - 1 = (M.length - 1) + 1 := by
    rw [blk_length]; have := List.length_pos_of_ne_nil hne; omega
  have hn' : M.length - 1 < (M.map Prod.fst).length := by simpa using hn
  rw [badRootL, if_neg (by simpa using hne)] at h
  rw [badRootL, blk_isEmpty, if_neg (by simp), hl]
  cases h1 : parAt1 M (M.length - 1) with
  | some q => rw [h1] at h; exact absurd h (by simp)
  | none =>
    rw [h1] at h
    have hs : (M[M.length - 1]!).2 = 0 := by
      by_contra hc
      exact hpos _ (by omega) h1
    rw [parAt1_blk_none hs]
    cases h2 : parAt (M.map Prod.fst) (M.length - 1) with
    | some q => rw [h2] at h; exact absurd h (by simp)
    | none =>
      have hle := parAux_none _ _ _ h2
      have : parAt ((blk M).map Prod.fst) (M.length - 1 + 1) = some 0 := by
        rw [blk_fst, parAt_eq_some]
        refine ⟨by omega, ?_, fun j' a b => ?_⟩
        · rw [shift_getElem _ hn']
          show 0 < _
          omega
        · obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
          rw [shift_getElem _ hn', shift_getElem _ (by omega)]
          have := hle k (by omega)
          omega
      simp only [this]

/-! ### Expansion of a block -/

/-- **When `M` has a bad root, the block expands as `M` does**, raised by
one. -/
theorem expand2L_blk_some {M : List (ℕ × ℕ)}
    (hpos : ∀ i, 0 < (M[i]!).2 → parAt1 M i ≠ none) {p : ℕ} {b : Bool}
    (h : badRootL M = some (p, b)) (N : ℕ) :
    expand2L N (blk M) = blk (expand2L N M) := by
  have hp := badRootL_lt h
  have hs : (blk M).length - 1 - (p + 1) = M.length - 1 - p := by rw [blk_length]; omega
  have hlast : (blk M).length - 1 = M.length - 1 + 1 := by rw [blk_length]; omega
  rw [expand2L, badRootL_blk_some hpos h, expand2L, h]
  dsimp only
  rw [hs, hlast]
  show _ = (0, 0) :: (sh _)
  rw [sh, List.range_succ_eq_map, List.map_cons, List.cons_append]
  simp only [List.map_append, List.map_map]
  congr 1
  congr 1
  · refine List.map_congr_left (fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    exact blk_getElem_succ M (by omega)
  · refine List.map_congr_left (fun t _ => ?_)
    have hsp : 0 < M.length - 1 - p := by omega
    have hk : p + t % (M.length - 1 - p) < M.length := by
      have := Nat.mod_lt t hsp; omega
    have hk' : p + t % (M.length - 1 - p) < (M.map Prod.fst).length := by simpa using hk
    rw [show p + 1 + t % (M.length - 1 - p) = (p + t % (M.length - 1 - p)) + 1 by omega,
      blk_getElem_succ M hk, blk_getElem_succ M (by omega), blk_getElem_succ M (by omega),
      blk_fst, ancAtB_shift _ hk' p,
      show (p + 1 == p + t % (M.length - 1 - p) + 1) = (p == p + t % (M.length - 1 - p)) by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; omega]
    simp only [Function.comp_apply]
    split
    · simp only [shc, Prod.mk.injEq, and_true, Nat.add_sub_add_right]
      omega
    · rfl

/-- **When `M` has no bad root, the block is repeated**: `M` loses its last
column, and the block of what is left is written `N + 1` times. -/
theorem expand2L_blk_none {M : List (ℕ × ℕ)} (hne : M ≠ [])
    (hpos : ∀ i, 0 < (M[i]!).2 → parAt1 M i ≠ none)
    (h : badRootL M = none) (N : ℕ) :
    expand2L N (blk M) = repN (N + 1) (blk (expand2L N M)) := by
  have hM : expand2L N M = M.dropLast := by rw [expand2L, h]
  rw [hM, expand2L, badRootL_blk_none hne hpos h]
  dsimp only
  rw [List.range_zero, List.map_nil, List.nil_append,
    show (blk M).length - 1 - 0 = M.length by rw [blk_length]; omega]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, Nat.zero_add]
  rw [map_range_mod M.length (fun i => (blk M)[i]!) (N + 1)]
  congr 1
  have h1 : (List.range M.length).map (fun i => (blk M)[i]!)
      = ((List.range (blk M).length).map (fun i => (blk M)[i]!)).dropLast := by
    rw [map_range_dropLast, blk_length, Nat.add_sub_cancel]
  rw [h1, listEta, blk, blk, List.dropLast_cons_of_ne_nil (by simpa [sh] using hne), sh, sh,
    List.map_dropLast]

/-! ### Lists of blocks -/

/-- A list of blocks, one after another. -/
def blocks (Ms : List (List (ℕ × ℕ))) : List (ℕ × ℕ) := Ms.flatMap blk

@[simp] theorem blocks_nil : blocks [] = [] := rfl

theorem blocks_cons (M : List (ℕ × ℕ)) (Ms : List (List (ℕ × ℕ))) :
    blocks (M :: Ms) = blk M ++ blocks Ms := by simp [blocks]

theorem blocks_append (Ms Ms' : List (List (ℕ × ℕ))) :
    blocks (Ms ++ Ms') = blocks Ms ++ blocks Ms' := by simp [blocks]

theorem blocks_singleton (M : List (ℕ × ℕ)) : blocks [M] = blk M := by simp [blocks]

theorem repN_blocks (X : List (ℕ × ℕ)) : ∀ n, repN n (blk X) = blocks (List.replicate n X)
  | 0 => rfl
  | n + 1 => by
    rw [repN, repN_blocks X n, List.replicate_succ', blocks_append, blocks_singleton]

/-- **Expanding a list of blocks expands the last one.** -/
theorem expand2L_blocks_last (N : ℕ) (Ms : List (List (ℕ × ℕ))) (M : List (ℕ × ℕ)) :
    expand2L N (blocks (Ms ++ [M])) = blocks Ms ++ expand2L N (blk M) := by
  rw [blocks_append, blocks_singleton]
  exact expand2L_append N _ _ (by simp [blk]) rfl

end Googology.Trans.DBMS
