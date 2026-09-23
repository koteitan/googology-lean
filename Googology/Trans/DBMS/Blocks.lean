import Googology.Trans.BMS.Append
import Googology.Trans.DBMS.Entries
import Googology.Rank

/-!
# DBMS at every number of rows: blocks and the rank

A DBMS standard form, at any number of rows, is a list of **blocks**.  A block
is a zero column followed by a matrix `M` whose row-`0` entries are raised by
one:

    blkR r M = (0,…,0) (M₀ with row 0 + 1) (M₁ with row 0 + 1) ⋯

The matrix `M` is **rooted**: its first column is zero, and a column whose
row-`0` entry is `0` is a zero column.  This file proves, for every number of
rows:

* `expandRL_blkR_ne`, `expandRL_blkR_zero`: expanding a block is expanding its
  rooted content `M`.  If the last column of `M` is not zero,
  `(blkR M)[N] = blkR (M[N])`; if it is zero, the block without its last
  column is written `N + 1` times.  The extra zero column in front is a row-`0`
  ancestor of everything and never a parent in rows `1, 2, …`
  (`not_ParR_blkR_zero`).
* `rooted_expandRL`: a rooted matrix stays rooted under expansion.
* `rkL_append`: the rank of the rule on all matrices (`bmsAllL`) adds up over
  blocks: `rank (P ++ Q) = rank P + rank Q` when `Q` starts with a column whose
  row-`0` entry is `0`.
* `rkL_blkR`: the rank of a block is `ω ^ (rank of its content)`.
* `dblocks_of_state`, `rank_dbmsL_eq_sum`: every standard form of DBMS with
  `r + 1` rows is `blkR M₀ ++ ⋯ ++ blkR Mₖ` with each `Mᵢ` in the content
  system `CReach` (the rule of BM4 started from `cgen`), and its rank is

      ω ^ rank(M₀) + ω ^ rank(M₁) + ⋯ + ω ^ rank(Mₖ).

So the rank of DBMS with `r + 1` rows is determined by the rank of the rule of
BM4 on the matrices of `CReach r`.  With two rows the content generators are
the pair-sequence generators `(0,0)(1,1)⋯(n-1,n-1)`, which is the block
decomposition of `TwoRowBlock.lean`.  With three rows they are
`(0,0,0)(1,1,0)(2,2,1)⋯(n-1,n-1,n-2)`; from `n = 3` on these are not standard
forms of three-row BMS.  `ThreeRow.lean` computes the rank of the content for
`n = 3` (`rkL_cgen_three`); for `n ≤ 2` the generators are two-row generators
with a row of zeros underneath, and their values are not restated there; for
`n ≥ 4` it is open.

The ranks here are ranks of the rule on all matrices (`bmsAllL`); on a DBMS
standard form it is the rank of DBMS itself (`rank_dbmsL_eq_rkL`).  The
converse of `dblocks_of_state` — which lists of blocks are standard — is not
proved.
-/

namespace Googology.Trans.DBMS

open Googology.Trans.BMS

/-! ### Columns and blocks -/

/-- A column with its row-`0` entry raised by one. -/
def up0 (v : List Nat) : List Nat := (v[0]! + 1) :: v.tail

/-- The zero column. -/
def zcol (r : Nat) : List Nat := List.replicate r 0

/-- A column all of whose entries are `0`. -/
def IsZ (v : List Nat) : Prop := ∀ k : Nat, v[k]! = 0

/-- A block: the zero column, then `M` with its row-`0` entries raised by one. -/
def blkR (r : Nat) (M : List (List Nat)) : List (List Nat) := zcol r :: M.map up0

/-- **Rooted**: the first column is zero, and every column whose row-`0` entry
is `0` is zero. -/
def Rooted (M : List (List Nat)) : Prop :=
  IsZ (M[0]!) ∧ ∀ i : Nat, (M[i]!)[0]! = 0 → IsZ (M[i]!)

@[simp] theorem up0_get0 (v : List Nat) : (up0 v)[0]! = v[0]! + 1 := rfl

theorem up0_get_succ (v : List Nat) (k : Nat) : (up0 v)[k + 1]! = v[k + 1]! := by
  cases v with
  | nil => rfl
  | cons a t => rfl

theorem up0_length {v : List Nat} (h : v ≠ []) : (up0 v).length = v.length := by
  cases v with
  | nil => exact absurd rfl h
  | cons a t => simp [up0]

theorem zcol_get (r k : Nat) : (zcol r)[k]! = 0 := by
  rw [zcol]
  by_cases h : k < r
  · rw [getElem!_pos _ k (by simpa using h)]; simp
  · rw [getElem!_neg _ k (by simpa using h)]; rfl

theorem isZ_zcol (r : Nat) : IsZ (zcol r) := zcol_get r

theorem isZ_nil : IsZ ([] : List Nat) := fun _ => rfl


@[simp] theorem blkR_length (r : Nat) (M : List (List Nat)) :
    (blkR r M).length = M.length + 1 := by simp [blkR]

theorem blkR_get0 (r : Nat) (M : List (List Nat)) : (blkR r M)[0]! = zcol r := rfl

theorem blkR_get_succ (r : Nat) (M : List (List Nat)) {i : Nat} (h : i < M.length) :
    (blkR r M)[i + 1]! = up0 (M[i]!) := by
  show (M.map up0)[i]! = _
  rw [getElem!_pos _ i (by simpa using h), getElem!_pos M i h, List.getElem_map]

theorem getElem!_default_of_ge (l : List (List Nat)) {i : Nat} (h : l.length ≤ i) :
    l[i]! = [] := getElem!_neg l i (by omega)

/-! ### Parents live inside the list -/

theorem ParR_lt_len {l : List (List Nat)} : ∀ {k j i : Nat}, ParR l k j i → i < l.length := by
  intro k
  induction k with
  | zero =>
    intro j i h
    by_contra hc
    have h2 := h.2.1
    rw [getElem!_default_of_ge l (i := i) (by omega)] at h2
    exact absurd h2 (by simp)
  | succ m ih =>
    intro j i h
    obtain ⟨b, _, hb⟩ := Relation.TransGen.tail'_iff.mp h.2.1
    exact ih hb

theorem transGen_lt {R : Nat → Nat → Prop} (hlt : ∀ a b, R a b → a < b) {a b : Nat}
    (h : Relation.TransGen R a b) : a < b := by
  induction h with
  | single h => exact hlt _ _ h
  | tail _ h ih => exact lt_trans ih (hlt _ _ h)

/-- A relation that commutes with the shift by one has a transitive closure
that does too, as long as it goes up. -/
theorem transGen_shift {R R' : Nat → Nat → Prop} (h : ∀ a b, R (a + 1) (b + 1) ↔ R' a b)
    (hlt : ∀ a b, R a b → a < b) (a b : Nat) :
    Relation.TransGen R (a + 1) (b + 1) ↔ Relation.TransGen R' a b := by
  constructor
  · have key : ∀ x y, Relation.TransGen R x y → 1 ≤ x →
        Relation.TransGen R' (x - 1) (y - 1) := by
      intro x y hxy
      induction hxy with
      | @single y hs =>
        intro hx
        have hy := hlt _ _ hs
        refine Relation.TransGen.single ((h _ _).mp ?_)
        rwa [show x - 1 + 1 = x from by omega, show y - 1 + 1 = y from by omega]
      | @tail c y hxc hs ih =>
        intro hx
        have hc := transGen_lt hlt hxc
        have hy := hlt _ _ hs
        refine Relation.TransGen.tail (ih hx) ((h _ _).mp ?_)
        rwa [show c - 1 + 1 = c from by omega, show y - 1 + 1 = y from by omega]
    intro hab
    simpa using key _ _ hab (by omega)
  · intro hab
    induction hab with
    | single hs => exact Relation.TransGen.single ((h _ _).mpr hs)
    | tail _ hs ih => exact Relation.TransGen.tail ih ((h _ _).mpr hs)

/-! ### The parents of a block -/

/-- **Inside a block the parents are those of its content**, in every row. -/
theorem ParR_blkR_succ (r : Nat) (M : List (List Nat)) :
    ∀ k j i, ParR (blkR r M) k (j + 1) (i + 1) ↔ ParR M k j i := by
  intro k
  induction k with
  | zero =>
    intro j i
    by_cases hi : j < i ∧ i < M.length
    · rw [ParR, ParR, blkR_get_succ r M hi.2, blkR_get_succ r M (by omega), up0_get0, up0_get0]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, by omega, fun j' a b => ?_⟩
        have := h3 (j' + 1) (by omega) (by omega)
        rw [blkR_get_succ r M (by omega), up0_get0] at this
        omega
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, by omega, fun j' a b => ?_⟩
        have := h3 (j' - 1) (by omega) (by omega)
        rw [show j' = (j' - 1) + 1 from by omega, blkR_get_succ r M (by omega), up0_get0]
        omega
    · constructor
      · intro h
        have h1 := ParR_lt_len h
        have h2 := ParR_lt h
        simp at h1
        exact absurd ⟨by omega, by omega⟩ hi
      · intro h; exact absurd ⟨ParR_lt h, ParR_lt_len h⟩ hi
  | succ m ih =>
    have hTG := transGen_shift (R := ParR (blkR r M) m) (R' := ParR M m) ih
      (fun _ _ h => ParR_lt h)
    intro j i
    by_cases hi : j < i ∧ i < M.length
    · rw [ParR, ParR, blkR_get_succ r M hi.2, blkR_get_succ r M (by omega), up0_get_succ,
        up0_get_succ, hTG]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨by omega, h2, h3, fun j' a b hc => ?_⟩
        have := h4 (j' + 1) (by omega) (by omega) ((hTG j' i).mpr hc)
        rwa [blkR_get_succ r M (by omega), up0_get_succ] at this
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨by omega, h2, h3, fun j' a b hc => ?_⟩
        have hj : j' = (j' - 1) + 1 := by omega
        rw [hj] at hc
        rw [hj, blkR_get_succ r M (by omega), up0_get_succ]
        exact h4 (j' - 1) (by omega) (by omega) ((hTG _ i).mp hc)
    · constructor
      · intro h
        have h1 := ParR_lt_len h
        have h2 := ParR_lt h
        simp at h1
        exact absurd ⟨by omega, by omega⟩ hi
      · intro h; exact absurd ⟨ParR_lt h, ParR_lt_len h⟩ hi

theorem AncR_blkR_succ (r : Nat) (M : List (List Nat)) (k a b : Nat) :
    AncR (blkR r M) k (a + 1) (b + 1) ↔ AncR M k a b :=
  transGen_shift (ParR_blkR_succ r M k) (fun _ _ h => ParR_lt h) a b

/-- A row-`0` parent exists as soon as some earlier column is smaller in
row `0`. -/
theorem exists_ParR0 (l : List (List Nat)) :
    ∀ d j i, i - j = d → j < i → (l[j]!)[0]! < (l[i]!)[0]! → ∃ p, ParR l 0 p i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j i hd hji hv
    by_cases hall : ∀ j', j < j' → j' < i → (l[i]!)[0]! ≤ (l[j']!)[0]!
    · exact ⟨j, hji, hv, hall⟩
    · push Not at hall
      obtain ⟨j', h1, h2, h3⟩ := hall
      exact ih (i - j') (by omega) j' i rfl h2 h3

theorem ParR_row0_lt {l : List (List Nat)} : ∀ {k j i : Nat}, ParR l k j i →
    (l[j]!)[0]! < (l[i]!)[0]! := by
  intro k
  induction k with
  | zero => intro j i h; exact h.2.1
  | succ m ih =>
    intro j i h
    have hT := h.2.1
    clear h
    induction hT with
    | single hs => exact ih hs
    | tail _ hs ih2 => exact lt_trans ih2 (ih hs)

theorem AncR_row0_lt {l : List (List Nat)} {k j i : Nat} (h : AncR l k j i) :
    (l[j]!)[0]! < (l[i]!)[0]! := by
  induction h with
  | single hs => exact ParR_row0_lt hs
  | tail _ hs ih => exact lt_trans ih (ParR_row0_lt hs)

/-- A row-`k` ancestor is a row-`0` ancestor. -/
theorem AncR_zero_of {l : List (List Nat)} : ∀ {k j i : Nat}, AncR l k j i → AncR l 0 j i := by
  intro k
  induction k with
  | zero => intro j i h; exact h
  | succ m ih =>
    intro j i h
    induction h with
    | single hs => exact ih hs.2.1
    | tail _ hs ih2 => exact Relation.TransGen.trans ih2 (ih hs.2.1)

/-- In a rooted matrix a column that is not zero in row `0` descends, in row
`0`, from a zero column. -/
theorem exists_zero_anc {M : List (List Nat)} (hM : Rooted M) :
    ∀ i, i < M.length → (M[i]!)[0]! ≠ 0 → ∃ z, AncR M 0 z i ∧ IsZ (M[z]!) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hne
    have h00 : (M[0]!)[0]! = 0 := hM.1 0
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact absurd h00 hne
      · exact h
    obtain ⟨p, hp⟩ := exists_ParR0 M (i - 0) 0 i rfl hi0 (by omega)
    by_cases hp0 : (M[p]!)[0]! = 0
    · exact ⟨p, Relation.TransGen.single hp, hM.2 p hp0⟩
    · obtain ⟨z, hz, hZ⟩ := ih p (ParR_lt hp) (by have := ParR_lt hp; omega) hp0
      exact ⟨z, Relation.TransGen.tail hz hp, hZ⟩

/-- **The zero column in front of a block is never a parent in rows
`1, 2, …`.** -/
theorem not_ParR_blkR_zero (r : Nat) {M : List (List Nat)} (hM : Rooted M) :
    ∀ k i, ¬ ParR (blkR r M) (k + 1) 0 i := by
  intro k
  induction k with
  | zero =>
    intro i h
    have hlen := ParR_lt_len h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [blkR_length] at hlen
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < M.length := by omega
    rw [blkR_get0, zcol_get, blkR_get_succ r M hi', up0_get_succ] at h3
    simp only [Nat.zero_add] at h3
    have hne : (M[i']!)[0]! ≠ 0 := fun h0 => by
      have := hM.2 i' h0 1
      omega
    obtain ⟨z, hz, hZ⟩ := exists_zero_anc hM i' hi' hne
    have hz' : z < i' := transGen_lt (fun _ _ h => ParR_lt h) hz
    have := h4 (z + 1) (by omega) (by omega) ((AncR_blkR_succ r M 0 z i').mpr hz)
    rw [blkR_get_succ r M hi', up0_get_succ, blkR_get_succ r M (by omega), up0_get_succ] at this
    simp only [Nat.zero_add] at this
    rw [hZ 1] at this
    omega
  | succ m ih =>
    intro i h
    obtain ⟨b, hb, _⟩ := Relation.TransGen.head'_iff.mp h.2.1
    exact ih b hb

/-! ### Expanding a block -/

/-- With a last column that is not zero, the zero column in front is not a
parent of the last column in any row. -/
theorem not_ParR_blkR_zero_last (r : Nat) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) :
    ∀ k, ¬ ParR (blkR r M) k 0 M.length := by
  have hpos : 0 < M.length := List.length_pos_iff.mpr hne
  intro k
  cases k with
  | succ k => exact not_ParR_blkR_zero r hM k _
  | zero =>
    rintro ⟨h1, h2, h3⟩
    have hl0 : (M[M.length - 1]!)[0]! ≠ 0 := fun h0 => hlast (hM.2 _ h0)
    by_cases hn : M.length = 1
    · exact hlast (by rw [hn]; exact hM.1)
    · have := h3 1 (by omega) (by omega)
      rw [show M.length = (M.length - 1) + 1 from by omega, blkR_get_succ r M (by omega),
        blkR_get_succ r M hpos, up0_get0, up0_get0, hM.1 0] at this
      omega

theorem parAtR_blkR_last (r : Nat) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) (k : Nat) :
    parAtR (blkR r M) k M.length = (parAtR M k (M.length - 1)).map (· + 1) := by
  have hpos : 0 < M.length := List.length_pos_iff.mpr hne
  have hn : M.length = (M.length - 1) + 1 := by omega
  cases h : parAtR M k (M.length - 1) with
  | none =>
    rw [Option.map_none]
    by_contra hc
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hc
    have hp := (parAtR_eq_some _ _ _ _).mp hj
    cases j with
    | zero => exact not_ParR_blkR_zero_last r hM hne hlast k hp
    | succ j =>
      rw [hn, ParR_blkR_succ] at hp
      rw [(parAtR_eq_some _ _ _ _).mpr hp] at h
      exact absurd h (by simp)
  | some p =>
    rw [Option.map_some, parAtR_eq_some, hn, ParR_blkR_succ]
    exact (parAtR_eq_some _ _ _ _).mp h

theorem m0L_blkR (r : Nat) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) :
    m0L r (blkR r M) = m0L r M := by
  rw [m0L, m0L, blkR_length, Nat.add_sub_cancel]
  exact findGreatest_congr (r - 1) (fun k _ => by
    rw [parAtR_blkR_last r hM hne hlast k, Option.isSome_map])

theorem badRootR_blkR (r : Nat) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) :
    badRootR r (blkR r M) = (badRootR r M).map (· + 1) := by
  have hne' : ¬ (blkR r M).isEmpty = true := by simp [blkR]
  have hneM : ¬ M.isEmpty = true := by simpa [List.isEmpty_iff] using hne
  rw [badRootR, badRootR, if_neg hne', if_neg hneM, blkR_length, Nat.add_sub_cancel,
    m0L_blkR r hM hne hlast]
  exact parAtR_blkR_last r hM hne hlast _

theorem blkR_dropLast (r : Nat) {M : List (List Nat)} (hne : M ≠ []) :
    blkR r M.dropLast = (blkR r M).dropLast := by
  rw [blkR, blkR, List.dropLast_cons_of_ne_nil (by simpa using hne), List.map_dropLast]

theorem up0_map_range (r' : Nat) (f g : Nat → Nat) (h0 : g 0 = f 0 + 1)
    (hs : ∀ k, g (k + 1) = f (k + 1)) :
    (List.range (r' + 1)).map g = up0 ((List.range (r' + 1)).map f) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, up0]
  simp only [List.map_map, List.tail_cons]
  refine congrArg₂ _ ?_ (List.map_congr_left (fun k _ => hs k))
  rw [h0]
  rfl

theorem blkR_append (r : Nat) (A B : List (List Nat)) :
    blkR r (A ++ B) = blkR r A ++ B.map up0 := by
  simp [blkR]

theorem blkR_map_range (r : Nat) (M : List (List Nat)) {p : Nat} (hp : p ≤ M.length) :
    blkR r ((List.range p).map (fun i => M[i]!))
      = (List.range (p + 1)).map (fun i => (blkR r M)[i]!) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, blkR, List.map_map]
  congr 1
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < p := List.mem_range.mp hi
  exact (blkR_get_succ r M (by omega)).symm

/-- **Expanding a block whose content does not end in a zero column is
expanding the content.** -/
theorem expandRL_blkR_ne (r N : Nat) (hr : 0 < r) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) :
    expandRL r N (blkR r M) = blkR r (expandRL r N M) := by
  have hpos : 0 < M.length := List.length_pos_iff.mpr hne
  cases hb : badRootR r M with
  | none =>
    rw [expandRL, badRootR_blkR r hM hne hlast, hb, Option.map_none]
    conv_rhs => rw [expandRL, hb]
    exact (blkR_dropLast r hne).symm
  | some p =>
    have hp : p + 1 < M.length := badRootR_lt hb
    rw [expandRL, badRootR_blkR r hM hne hlast, hb, Option.map_some]
    conv_rhs => rw [expandRL, hb]
    dsimp only
    rw [blkR_append, blkR_map_range r M (by omega), List.map_map]
    congr 1
    rw [blkR_length, Nat.add_sub_cancel, show M.length - (p + 1) = M.length - 1 - p from by omega,
      m0L_blkR r hM hne hlast]
    refine List.map_congr_left (fun t _ => ?_)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hs : 0 < M.length - 1 - p := by omega
    have hx : p + t % (M.length - 1 - p) < M.length := by
      have := Nat.mod_lt t hs; omega
    have e1 : (blkR (r' + 1) M)[p + 1 + t % (M.length - 1 - p)]!
        = up0 (M[p + t % (M.length - 1 - p)]!) := by
      rw [show p + 1 + t % (M.length - 1 - p) = (p + t % (M.length - 1 - p)) + 1 from by omega]
      exact blkR_get_succ _ M hx
    have e2 : (blkR (r' + 1) M)[p + 1]! = up0 (M[p]!) := blkR_get_succ _ M (by omega)
    have e3 : (blkR (r' + 1) M)[M.length]! = up0 (M[M.length - 1]!) := by
      conv_lhs => rw [show M.length = (M.length - 1) + 1 from by omega]
      exact blkR_get_succ _ M (by omega)
    have e4 : ∀ k, ancAtR (blkR (r' + 1) M) k (p + 1) (p + 1 + t % (M.length - 1 - p))
        = ancAtR M k p (p + t % (M.length - 1 - p)) := by
      intro k
      rw [Bool.eq_iff_iff, ancAtR_iff, ancAtR_iff,
        show p + 1 + t % (M.length - 1 - p) = (p + t % (M.length - 1 - p)) + 1 from by omega]
      exact AncR_blkR_succ _ M k p _
    have e5 : (p + 1 == p + 1 + t % (M.length - 1 - p)) = (p == p + t % (M.length - 1 - p)) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; omega
    simp only [Function.comp, e1, e2, e3, e4, e5]
    refine up0_map_range r' _ _ ?_ ?_
    · simp only [up0_get0]
      split
      · rw [Nat.add_sub_add_right]; ring
      · rfl
    · intro k
      simp only [up0_get_succ]

theorem dropLast_eq_map_range {α : Type} [Inhabited α] (l : List α) :
    l.dropLast = (List.range (l.length - 1)).map (fun i => l[i]!) := by
  conv_lhs => rw [← listEta l.dropLast]
  rw [List.length_dropLast]
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < l.length - 1 := List.mem_range.mp hi
  rw [getElem!_pos l.dropLast i (by rw [List.length_dropLast]; exact hi'),
    getElem!_pos l i (by omega), List.getElem_dropLast]

theorem blkR_col_len (r : Nat) (hr : 0 < r) {M : List (List Nat)}
    (hlen : ∀ v ∈ M, v.length = r) : ∀ v ∈ blkR r M, v.length = r := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · rw [h, zcol, List.length_replicate]
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    rw [up0_length (fun he => by rw [he] at hw; have := hlen [] hw; simp at this; omega)]
    exact hlen w hw

/-- **Expanding a block whose content ends in a zero column repeats the block
without that column.** -/
theorem expandRL_blkR_zero (r N : Nat) (hr : 0 < r) {M : List (List Nat)}
    (hlen : ∀ v ∈ M, v.length = r) (hne : M ≠ []) (hlast : IsZ (M[M.length - 1]!)) :
    expandRL r N (blkR r M) = repN (N + 1) (blkR r M.dropLast) := by
  have hpos : 0 < M.length := List.length_pos_iff.mpr hne
  have eL : (blkR r M)[M.length]! = up0 (M[M.length - 1]!) := by
    conv_lhs => rw [show M.length = (M.length - 1) + 1 from by omega]
    exact blkR_get_succ _ M (by omega)
  have hm : m0L r (blkR r M) = 0 := by
    rw [m0L, blkR_length, Nat.add_sub_cancel, Nat.findGreatest_eq_zero_iff]
    intro k hk _ hsome
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
    have hp := (parAtR_eq_some _ _ _ _).mp hj
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := hp.2.2.1
    rw [eL, up0_get_succ, hlast (k' + 1)] at this
    omega
  have hb : badRootR r (blkR r M) = some 0 := by
    have hne' : ¬ (blkR r M).isEmpty = true := by simp [blkR]
    rw [badRootR, if_neg hne', hm, blkR_length, Nat.add_sub_cancel, parAtR_eq_some]
    refine ⟨hpos, ?_, fun j' h1 h2 => ?_⟩
    · rw [blkR_get0, zcol_get, eL, up0_get0]; omega
    · rw [eL, up0_get0, hlast 0, show j' = (j' - 1) + 1 from by omega,
        blkR_get_succ r M (by omega), up0_get0]
      omega
  rw [expandRL_of_m0_zero r N (blkR r M) 0 hb hm (blkR_col_len r hr hlen),
    List.range_zero, List.map_nil, List.nil_append, blkR_dropLast r hne,
    dropLast_eq_map_range]
  simp

/-- **`[0]` removes the last column**, on any matrix whose columns have the
height of the rule. -/
theorem expandRL_zero (r : Nat) (l : List (List Nat)) (hlen : ∀ v ∈ l, v.length = r) :
    expandRL r 0 l = l.dropLast := by
  cases hb : badRootR r l with
  | none => rw [expandRL, hb]
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    rw [expandRL, hb]
    dsimp only
    rw [dropLast_eq_map_range]
    have e : l.length - 1 = p + (l.length - 1 - p) := by omega
    conv_rhs => rw [e, List.range_add, List.map_append, List.map_map]
    rw [Nat.zero_add, Nat.one_mul]
    congr 1
    refine List.map_congr_left (fun t ht => ?_)
    have ht' : t < l.length - 1 - p := List.mem_range.mp ht
    rw [Nat.mod_eq_of_lt ht', Nat.div_eq_of_lt ht']
    simp only [Nat.zero_mul, Nat.add_zero, ite_self, Function.comp]
    rw [← hlen (l[p + t]!) (getElem!_mem l _ (by omega))]
    exact listEta _

/-- **One more copy**: `M[N + 1]` is `M[N]` followed by the columns of one
more copy of the bad part. -/
theorem expandRL_succ_append (r N : Nat) (l : List (List Nat)) {p : Nat}
    (hb : badRootR r l = some p) :
    ∃ X, X ≠ [] ∧ expandRL r (N + 1) l = expandRL r N l ++ X := by
  have hp : p + 1 < l.length := badRootR_lt hb
  rw [expandRL, expandRL, hb]
  dsimp only
  refine ⟨_, ?_, by
    rw [show (N + 1 + 1) * (l.length - 1 - p) = (N + 1) * (l.length - 1 - p) + (l.length - 1 - p)
      from by ring, List.range_add, List.map_append, List.append_assoc]⟩
  simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  omega

/-- A rooted matrix whose last column is not zero has a bad root. -/
theorem badRootR_isSome (r : Nat) {M : List (List Nat)} (hM : Rooted M)
    (hne : M ≠ []) (hlast : ¬ IsZ (M[M.length - 1]!)) : ∃ p, badRootR r M = some p := by
  have hpos : 0 < M.length := List.length_pos_iff.mpr hne
  have hl0 : (M[M.length - 1]!)[0]! ≠ 0 := fun h0 => hlast (hM.2 _ h0)
  have hn1 : 0 < M.length - 1 := by
    by_contra hc
    exact hlast (by rw [show M.length - 1 = 0 from by omega]; exact hM.1)
  obtain ⟨q, hq⟩ := exists_ParR0 M _ 0 (M.length - 1) rfl hn1 (by rw [hM.1 0]; omega)
  have h0 : (parAtR M 0 (M.length - 1)).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨q, (parAtR_eq_some _ _ _ _).mpr hq⟩
  have hspec : (parAtR M (m0L r M) (M.length - 1)).isSome = true :=
    Nat.findGreatest_spec (P := fun k => (parAtR M k (M.length - 1)).isSome = true)
      (Nat.zero_le (r - 1)) h0
  have hneM : ¬ M.isEmpty = true := by simpa [List.isEmpty_iff] using hne
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hspec
  exact ⟨p, by rw [badRootR, if_neg hneM]; exact hp⟩

/-! ### Rooted matrices stay rooted -/

theorem getElem!_dropLast' (l : List (List Nat)) (i : Nat) :
    (l.dropLast)[i]! = if i < l.length - 1 then l[i]! else [] := by
  split
  · rename_i h
    rw [getElem!_pos l.dropLast i (by rw [List.length_dropLast]; exact h),
      getElem!_pos l i (by omega), List.getElem_dropLast]
  · rename_i h
    exact getElem!_neg _ i (by rw [List.length_dropLast]; exact h)

theorem getElem!_map_range_nat (r : Nat) (f : Nat → Nat) (k : Nat) :
    ((List.range r).map f)[k]! = if k < r then f k else 0 := by
  split
  · rename_i h; exact getElem!_map_range r f h
  · rename_i h; exact getElem!_neg _ k (by simpa using h)

theorem badRootR_ParR {r : Nat} {l : List (List Nat)} {p : Nat} (hb : badRootR r l = some p) :
    ParR l (m0L r l) p (l.length - 1) := by
  rw [badRootR] at hb
  split at hb
  · exact absurd hb (by simp)
  · exact (parAtR_eq_some _ _ _ _).mp hb

theorem ancAtR_zero_of {l : List (List Nat)} {k p x : Nat} (h : ancAtR l k p x = true) :
    ancAtR l 0 p x = true :=
  (ancAtR_iff _ _ _ _).mpr (AncR_zero_of ((ancAtR_iff _ _ _ _).mp h))

/-- **Expansion keeps a matrix rooted.** -/
theorem rooted_expandRL (r N : Nat) {M : List (List Nat)} (hM : Rooted M) :
    Rooted (expandRL r N M) := by
  cases hb : badRootR r M with
  | none =>
    rw [expandRL, hb]
    dsimp only
    refine ⟨?_, fun i hi => ?_⟩
    · rw [getElem!_dropLast']
      split
      · exact hM.1
      · exact isZ_nil
    · rw [getElem!_dropLast'] at hi ⊢
      split
      · rw [if_pos (by assumption)] at hi; exact hM.2 i hi
      · exact isZ_nil
  | some p =>
    have hp : p + 1 < M.length := badRootR_lt hb
    have hs : 0 < M.length - 1 - p := by omega
    have hpar := badRootR_ParR hb
    have hδ : (M[p]!)[0]! < (M[M.length - 1]!)[0]! := ParR_row0_lt hpar
    rw [expandRL, hb]
    dsimp only
    -- the entries of the output
    have hG : ∀ i, i < p → ((List.range p).map (fun i => M[i]!) ++
        (List.range ((N + 1) * (M.length - 1 - p))).map (fun t =>
          (List.range r).map (fun k =>
            if decide (k < m0L r M) && ((p == p + t % (M.length - 1 - p))
                || ancAtR M k p (p + t % (M.length - 1 - p))) then
              (M[p + t % (M.length - 1 - p)]!)[k]!
                + (t / (M.length - 1 - p)) * ((M[M.length - 1]!)[k]! - (M[p]!)[k]!)
            else (M[p + t % (M.length - 1 - p)]!)[k]!)))[i]! = M[i]! := by
      intro i hi
      rw [getElem!_append_left _ _ (by simpa using hi), getElem!_map_range _ _ hi]
    -- a column of a copy
    have hC : ∀ t : Nat, (∀ k : Nat, ((List.range r).map (fun k =>
            if decide (k < m0L r M) && ((p == p + t % (M.length - 1 - p))
                || ancAtR M k p (p + t % (M.length - 1 - p))) then
              (M[p + t % (M.length - 1 - p)]!)[k]!
                + (t / (M.length - 1 - p)) * ((M[M.length - 1]!)[k]! - (M[p]!)[k]!)
            else (M[p + t % (M.length - 1 - p)]!)[k]!))[k]! = 0) ∨
          ((List.range r).map (fun k =>
            if decide (k < m0L r M) && ((p == p + t % (M.length - 1 - p))
                || ancAtR M k p (p + t % (M.length - 1 - p))) then
              (M[p + t % (M.length - 1 - p)]!)[k]!
                + (t / (M.length - 1 - p)) * ((M[M.length - 1]!)[k]! - (M[p]!)[k]!)
            else (M[p + t % (M.length - 1 - p)]!)[k]!))[0]! ≠ 0 := by
      intro t
      by_cases h0 : ((List.range r).map (fun k =>
            if decide (k < m0L r M) && ((p == p + t % (M.length - 1 - p))
                || ancAtR M k p (p + t % (M.length - 1 - p))) then
              (M[p + t % (M.length - 1 - p)]!)[k]!
                + (t / (M.length - 1 - p)) * ((M[M.length - 1]!)[k]! - (M[p]!)[k]!)
            else (M[p + t % (M.length - 1 - p)]!)[k]!))[0]! = 0
      · refine Or.inl (fun k => ?_)
        rw [getElem!_map_range_nat] at h0 ⊢
        split
        · rename_i hk
          rw [if_pos (by omega)] at h0
          have hx0 : (M[p + t % (M.length - 1 - p)]!)[0]! = 0 := by
            split at h0 <;> omega
          have hZ := hM.2 _ hx0
          split
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
            have hc0 : (decide (0 < m0L r M) && ((p == p + t % (M.length - 1 - p))
                || ancAtR M 0 p (p + t % (M.length - 1 - p)))) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
              refine ⟨by omega, ?_⟩
              rcases hc.2 with h | h
              · exact Or.inl h
              · exact Or.inr (ancAtR_zero_of h)
            rw [if_pos hc0, hx0, Nat.zero_add] at h0
            rw [hZ k, Nat.zero_add]
            rcases Nat.mul_eq_zero.mp h0 with hq | hq
            · rw [hq, Nat.zero_mul]
            · omega
          · exact hZ k
        · rfl
      · exact Or.inr h0
    refine ⟨?_, fun i hi => ?_⟩
    · cases p with
      | succ q => rw [hG 0 (by omega)]; exact hM.1
      | zero =>
        rw [List.range_zero, List.map_nil, List.nil_append,
          getElem!_map_range _ _ (show 0 < (N + 1) * (M.length - 1 - 0) from
            Nat.mul_pos (Nat.succ_pos N) hs)]
        intro k
        rw [getElem!_map_range_nat]
        split
        · simp only [Nat.zero_mod, Nat.zero_div, Nat.zero_mul, Nat.add_zero, ite_self]
          exact hM.1 k
        · rfl
    · by_cases hip : i < p
      · rw [hG i hip] at hi ⊢; exact hM.2 i hi
      · obtain ⟨t, rfl⟩ : ∃ t, i = p + t := ⟨i - p, by omega⟩
        have hlenG : ((List.range p).map (fun i => M[i]!)).length = p := by simp
        have key : ∀ (G C : List (List Nat)), G.length = p → (G ++ C)[p + t]! = C[t]! := by
          intro G C h; rw [← h]; exact getElem!_append_right G C t
        rw [key _ _ hlenG] at hi ⊢
        by_cases ht : t < (N + 1) * (M.length - 1 - p)
        · rw [getElem!_map_range _ _ ht] at hi ⊢
          rcases hC t with h | h
          · exact h
          · exact absurd hi h
        · rw [getElem!_neg _ t (by simpa using ht)]
          exact isZ_nil

/-! ### Two ordinal facts -/

section OrdinalFacts

open Ordinal Order

theorem iSup_succ_mul_nat (x : Ordinal.{0}) (hx : 0 < x) :
    ⨆ N : Nat, succ (x * ((N + 1 : Nat) : Ordinal)) = x * ω := by
  refine le_antisymm (Ordinal.iSup_le (fun N => succ_le_of_lt ?_)) ?_
  · exact (mul_lt_mul_iff_of_pos_left hx).mpr (Ordinal.natCast_lt_omega0 _)
  · rw [← Ordinal.iSup_mul_natCast]
    refine Ordinal.iSup_le (fun n => le_trans ?_ (Ordinal.le_iSup
      (fun N : Nat => succ (x * ((N + 1 : Nat) : Ordinal))) n))
    refine le_trans ?_ (le_succ _)
    exact mul_le_mul_right (by exact_mod_cast Nat.le_succ n) x

theorem iSup_succ_opow (a : Nat → Ordinal.{0}) (hmono : ∀ N, a N < a (N + 1)) :
    ⨆ N, succ (ω ^ a N) = ω ^ (⨆ N, succ (a N)) := by
  have h1 : ⨆ N, succ (a N) = ⨆ N, a N := by
    refine le_antisymm (Ordinal.iSup_le (fun N => le_trans (succ_le_of_lt (hmono N))
      (Ordinal.le_iSup a (N + 1)))) (Ordinal.iSup_le (fun N => le_trans (le_succ _)
      (Ordinal.le_iSup (fun N => succ (a N)) N)))
  have h2 : ⨆ N, succ (ω ^ a N) = ⨆ N, ω ^ a N := by
    refine le_antisymm (Ordinal.iSup_le (fun N => le_trans (succ_le_of_lt
      ((opow_lt_opow_iff_right one_lt_omega0).mpr (hmono N)))
      (Ordinal.le_iSup (fun N => ω ^ a N) (N + 1)))) (Ordinal.iSup_le (fun N => le_trans
      (le_succ _) (Ordinal.le_iSup (fun N => succ (ω ^ a N)) N)))
  rw [h1, h2]
  exact ((isNormal_opow one_lt_omega0).map_iSup (Ordinal.bddAbove_of_small)).symm

end OrdinalFacts

/-! ### The rank on all matrices -/

section Rank

open Ordinal Order

/-- The rank of the rule on all matrices with `r + 1` rows (`bmsAllL r`), as a
function on lists; `0` on a list whose columns do not all have `r + 1`
entries. -/
noncomputable def rkL (r : Nat) (l : List (List Nat)) : Ordinal.{0} :=
  if h : ∀ v ∈ l, v.length = r + 1 then
    @IsWellFounded.rank (bmsAllL r).State (bmsAllL r).Rel ⟨bmsAllL_wf r⟩ ⟨l, h⟩
  else 0

/-- Columns of height `r + 1`. -/
def Valid (r : Nat) (l : List (List Nat)) : Prop := ∀ v ∈ l, v.length = r + 1

theorem rkL_eq {r : Nat} (s : AllLState r) :
    rkL r s.1 = @IsWellFounded.rank (bmsAllL r).State (bmsAllL r).Rel ⟨bmsAllL_wf r⟩ s := by
  rw [rkL, dif_pos s.2]

theorem valid_expandRL {r : Nat} {l : List (List Nat)} (h : Valid r l) (N : Nat) :
    Valid r (expandRL (r + 1) N l) := expandRL_col_len (r + 1) N l h

theorem rkL_nil (r : Nat) : rkL r [] = 0 := by
  haveI : IsWellFounded (bmsAllL r).State (bmsAllL r).Rel := ⟨bmsAllL_wf r⟩
  rw [rkL_eq (⟨[], by simp⟩ : AllLState r)]
  exact Rewrite.rank_halted rfl

theorem rkL_step {r : Nat} {l : List (List Nat)} (h : Valid r l) (hne : l ≠ []) :
    rkL r l = ⨆ N : Nat, succ (rkL r (expandRL (r + 1) N l)) := by
  haveI : IsWellFounded (bmsAllL r).State (bmsAllL r).Rel := ⟨bmsAllL_wf r⟩
  rw [rkL_eq (⟨l, h⟩ : AllLState r),
    @Rewrite.rank_eq_iSup_nat (bmsAllL r) ⟨bmsAllL_wf r⟩ (⟨l, h⟩ : AllLState r) hne]
  congr 1
  funext N
  rw [rkL_eq (⟨_, valid_expandRL h N⟩ : AllLState r)]
  rfl

theorem rkL_lt {r : Nat} {l : List (List Nat)} (h : Valid r l) (hne : l ≠ []) (N : Nat) :
    rkL r (expandRL (r + 1) N l) < rkL r l := by
  rw [rkL_step h hne]
  exact lt_of_lt_of_le (lt_succ _)
    (Ordinal.le_iSup (fun N : Nat => succ (rkL r (expandRL (r + 1) N l))) N)

theorem rel_of_ne {r : Nat} (s : AllLState r) (hne : s.1 ≠ []) (N : Nat) :
    (bmsAllL r).Rel ((bmsAllL r).step s N) s := ⟨hne, N, rfl⟩

/-- **The rank adds up over blocks**: a list that starts with a column whose
row-`0` entry is `0` is expanded without looking in front of it. -/
theorem rkL_append (r : Nat) : ∀ (Q : AllLState r) (P : List (List Nat)), Valid r P →
    (Q.1 = [] ∨ (Q.1[0]!)[0]! = 0) → rkL r (P ++ Q.1) = rkL r P + rkL r Q.1 := by
  intro Q
  induction Q using WellFounded.induction (bmsAllL_wf r) with
  | _ Q ih =>
    intro P hP h0
    by_cases hQ : Q.1 = []
    · rw [hQ, List.append_nil, rkL_nil, add_zero]
    · have h0' : (Q.1[0]!)[0]! = 0 := h0.resolve_left hQ
      have hPQ : Valid r (P ++ Q.1) := by
        intro v hv
        rcases List.mem_append.mp hv with h | h
        · exact hP v h
        · exact Q.2 v h
      rw [rkL_step hPQ (by simp [hQ]), rkL_step Q.2 hQ, add_iSup]
      congr 1
      funext N
      rw [expandRL_append (r + 1) N P Q.1 h0' hQ, Order.succ_eq_add_one, Order.succ_eq_add_one,
        ← add_assoc]
      congr 1
      exact ih ((bmsAllL r).step Q N) (rel_of_ne Q hQ N) P hP
        (head_expandRL (r + 1) N (Nat.succ_pos r) Q.1 h0')

theorem rkL_append' {r : Nat} {P Q : List (List Nat)} (hP : Valid r P) (hQ : Valid r Q)
    (h0 : Q = [] ∨ (Q[0]!)[0]! = 0) : rkL r (P ++ Q) = rkL r P + rkL r Q :=
  rkL_append r ⟨Q, hQ⟩ P hP h0

theorem valid_repN {r : Nat} {B : List (List Nat)} (hB : Valid r B) :
    ∀ n, Valid r (repN n B) := by
  intro n
  induction n with
  | zero => intro v hv; simp [repN] at hv
  | succ n ih =>
    intro v hv
    rw [repN] at hv
    rcases List.mem_append.mp hv with h | h
    · exact ih v h
    · exact hB v h

theorem rkL_repN {r : Nat} {B : List (List Nat)} (hB : Valid r B)
    (h0 : B = [] ∨ (B[0]!)[0]! = 0) : ∀ n : Nat, rkL r (repN n B) = rkL r B * (n : Ordinal) := by
  intro n
  induction n with
  | zero => rw [repN, rkL_nil, Nat.cast_zero, mul_zero]
  | succ n ih =>
    rw [repN, rkL_append' (valid_repN hB n) hB h0, ih, Nat.cast_succ, mul_add_one]

/-- A proper prefix has a smaller rank: `[0]` removes the last column. -/
theorem rkL_lt_append {r : Nat} (P : List (List Nat)) :
    ∀ (n : Nat) (X : List (List Nat)), X.length = n → X ≠ [] → Valid r (P ++ X) →
      rkL r P < rkL r (P ++ X) := by
  intro n
  induction n with
  | zero => intro X hX hne; exact absurd (List.length_eq_zero_iff.mp hX) hne
  | succ n ih =>
    intro X hX hne hv
    have hdrop : expandRL (r + 1) 0 (P ++ X) = P ++ X.dropLast := by
      rw [expandRL_zero (r + 1) _ hv, List.dropLast_append_of_ne_nil hne]
    have hlt := rkL_lt hv (by simp [hne]) 0
    rw [hdrop] at hlt
    by_cases hX' : X.dropLast = []
    · rwa [hX', List.append_nil] at hlt
    · refine lt_trans (ih X.dropLast (by rw [List.length_dropLast]; omega) hX' ?_) hlt
      rw [← hdrop]
      exact valid_expandRL hv 0

theorem expandRL_single (r N : Nat) (v : List Nat) : expandRL r N [v] = [] := by
  have hb : badRootR r [v] = none := by
    rw [badRootR, if_neg (by simp)]
    cases h : parAtR [v] (m0L r [v]) ([v].length - 1) with
    | none => rfl
    | some j =>
      have := ParR_lt ((parAtR_eq_some _ _ _ _).mp h)
      simp at this
  rw [expandRL, hb]
  rfl

theorem badRootR_none_of_isZ (r : Nat) {M : List (List Nat)} (hlast : IsZ (M[M.length - 1]!)) :
    badRootR r M = none := by
  rw [badRootR]
  split
  · rfl
  · cases h : parAtR M (m0L r M) (M.length - 1) with
    | none => rfl
    | some j =>
      have hp := (parAtR_eq_some _ _ _ _).mp h
      have := ParR_row0_lt hp
      rw [hlast 0] at this
      omega

/-- **The rank of a block is `ω` to the rank of its content.** -/
theorem rkL_blkR (r : Nat) : ∀ (M : AllLState r), Rooted M.1 →
    rkL r (blkR (r + 1) M.1) = ω ^ rkL r M.1 := by
  intro M
  induction M using WellFounded.induction (bmsAllL_wf r) with
  | _ M ih =>
    intro hM
    have hvB : Valid r (blkR (r + 1) M.1) := blkR_col_len (r + 1) (Nat.succ_pos r) M.2
    by_cases hne : M.1 = []
    · rw [rkL_step hvB (by simp [blkR])]
      rw [hne, rkL_nil, opow_zero]
      simp only [blkR, List.map_nil, expandRL_single, rkL_nil, Order.succ_eq_add_one, zero_add]
      exact ciSup_const
    · have hpos : 0 < M.1.length := List.length_pos_iff.mpr hne
      by_cases hlast : IsZ (M.1[M.1.length - 1]!)
      · -- the content ends in a zero column
        have hM' : Valid r M.1.dropLast := by
          rw [← expandRL_zero (r + 1) _ M.2]; exact valid_expandRL M.2 0
        have hstep : ∀ N, expandRL (r + 1) N M.1 = M.1.dropLast := by
          intro N; rw [expandRL, badRootR_none_of_isZ (r + 1) hlast]
        have hroot' : Rooted M.1.dropLast := by
          rw [← hstep 0]; exact rooted_expandRL (r + 1) 0 hM
        have ihM := ih ((bmsAllL r).step M 0) (rel_of_ne M hne 0)
          (by show Rooted (expandRL (r + 1) 0 M.1); rw [hstep 0]; exact hroot')
        change rkL r (blkR (r + 1) (expandRL (r + 1) 0 M.1)) = ω ^ rkL r (expandRL (r + 1) 0 M.1)
          at ihM
        rw [hstep 0] at ihM
        have hvB' : Valid r (blkR (r + 1) M.1.dropLast) :=
          blkR_col_len (r + 1) (Nat.succ_pos r) hM'
        rw [rkL_step hvB (by simp [blkR]), rkL_step M.2 hne]
        simp only [hstep]
        rw [ciSup_const, opow_succ]
        simp only [expandRL_blkR_zero (r + 1) _ (Nat.succ_pos r) M.2 hne hlast]
        simp only [rkL_repN hvB' (Or.inr (by rw [blkR_get0, zcol_get])), ihM]
        exact iSup_succ_mul_nat _ (opow_pos _ omega0_pos)
      · -- the content ends in a column that is not zero
        obtain ⟨p, hb⟩ := badRootR_isSome (r + 1) hM hne hlast
        have ihN : ∀ N, rkL r (blkR (r + 1) (expandRL (r + 1) N M.1))
            = ω ^ rkL r (expandRL (r + 1) N M.1) := fun N =>
          ih ((bmsAllL r).step M N) (rel_of_ne M hne N) (rooted_expandRL (r + 1) N hM)
        rw [rkL_step hvB (by simp [blkR]), rkL_step M.2 hne]
        simp only [expandRL_blkR_ne (r + 1) _ (Nat.succ_pos r) hM hne hlast, ihN]
        refine iSup_succ_opow _ (fun N => ?_)
        obtain ⟨X, hX, he⟩ := expandRL_succ_append (r + 1) N M.1 hb
        rw [he]
        exact rkL_lt_append _ X.length X rfl hX (by rw [← he]; exact valid_expandRL M.2 _)

end Rank

/-! ### DBMS standard forms are lists of blocks -/

section DBMSBlocks

open Ordinal Order
open Googology.Notation.DBMS

/-- The content of the DBMS generator with `r + 1` rows and `n + 1` columns:
column `i` holds `i` in row `0` and `i + 1 - k` in row `k ≥ 1`.  With three
rows: `(0,0,0)(1,1,0)(2,2,1)(3,3,2)⋯`. -/
def cgen (r n : Nat) : List (List Nat) :=
  (List.range n).map (fun i => (List.range (r + 1)).map (fun k => if k = 0 then i else i + 1 - k))

/-- The content system: the rule of BM4 started from `cgen`. -/
inductive CReach (r : Nat) : List (List Nat) → Prop
  | gen (n : Nat) : CReach r (cgen r n)
  | step {M : List (List Nat)} (N : Nat) : CReach r M → CReach r (expandRL (r + 1) N M)

theorem entriesR_dstair_blkR (r n : Nat) :
    entriesR (dstair (r + 1) n) = blkR (r + 1) (cgen r n) := by
  rw [entriesR_dstair, show List.range (n + 1) = 0 :: (List.range n).map Nat.succ from
    List.range_succ_eq_map, List.map_cons, blkR, cgen, List.map_map, List.map_map]
  congr 1
  · simp [zcol, List.map_const']
  · refine List.map_congr_left (fun i _ => ?_)
    exact up0_map_range r _ _ (by simp) (fun k => by simp)

theorem valid_cgen (r n : Nat) : Valid r (cgen r n) := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  simp

theorem rooted_cgen (r n : Nat) : Rooted (cgen r n) := by
  have hcol : ∀ i : Nat, ((cgen r n)[i]!)[0]! = 0 → IsZ ((cgen r n)[i]!) := by
    intro i hi
    by_cases h : i < n
    · rw [cgen, getElem!_map_range _ _ h] at hi ⊢
      rw [getElem!_map_range_nat] at hi
      simp only [Nat.succ_pos, if_true] at hi
      intro k
      rw [getElem!_map_range_nat]
      split
      · simp only [hi]
        split <;> omega
      · rfl
    · rw [getElem!_neg _ i (by simpa [cgen] using h)]
      exact isZ_nil
  refine ⟨?_, hcol⟩
  by_cases h : 0 < n
  · exact hcol 0 (by
      rw [cgen, getElem!_map_range _ _ h, getElem!_map_range_nat]
      simp)
  · rw [getElem!_neg _ 0 (by simpa [cgen] using h)]
    exact isZ_nil

theorem CReach.rooted {r : Nat} {M : List (List Nat)} (h : CReach r M) : Rooted M := by
  induction h with
  | gen n => exact rooted_cgen r n
  | step N _ ih => exact rooted_expandRL (r + 1) N ih

theorem CReach.valid {r : Nat} {M : List (List Nat)} (h : CReach r M) : Valid r M := by
  induction h with
  | gen n => exact valid_cgen r n
  | step N _ ih => exact valid_expandRL ih N

/-- **A list of blocks with contents in the content system.** -/
def DBlocks (r : Nat) (l : List (List Nat)) : Prop :=
  ∃ Ms : List (List (List Nat)), (∀ M ∈ Ms, CReach r M) ∧ l = (Ms.map (blkR (r + 1))).flatten

theorem repN_blkR (r n : Nat) (X : List (List Nat)) :
    repN n (blkR r X) = ((List.replicate n X).map (blkR r)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repN, ih, List.replicate_succ', List.map_append, List.flatten_append]
    simp

theorem expandRL_nil (r N : Nat) : expandRL r N [] = [] := by
  rw [expandRL]
  have : badRootR r [] = none := by simp [badRootR]
  rw [this]
  rfl

theorem dblocks_expand {r : Nat} {l : List (List Nat)} (h : DBlocks r l) (N : Nat) :
    DBlocks r (expandRL (r + 1) N l) := by
  obtain ⟨Ms, hMs, rfl⟩ := h
  rcases List.eq_nil_or_concat Ms with h0 | ⟨Ms', M, rfl⟩
  · subst h0
    exact ⟨[], by simp, by simp [expandRL_nil]⟩
  · rw [List.concat_eq_append] at hMs ⊢
    have hM : CReach r M := hMs M (by simp)
    have hMs' : ∀ M' ∈ Ms', CReach r M' := fun M' h => hMs M' (by simp [h])
    rw [List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton,
      expandRL_append (r + 1) N _ _ (by rw [blkR_get0, zcol_get]) (by simp [blkR])]
    by_cases hne : M = []
    · subst hne
      refine ⟨Ms', hMs', ?_⟩
      simp only [blkR, List.map_nil, expandRL_single, List.append_nil]
    · by_cases hlast : IsZ (M[M.length - 1]!)
      · rw [expandRL_blkR_zero (r + 1) N (Nat.succ_pos r) hM.valid hne hlast, repN_blkR]
        refine ⟨Ms' ++ List.replicate (N + 1) M.dropLast, fun M' h => ?_, by simp⟩
        rcases List.mem_append.mp h with h | h
        · exact hMs' M' h
        · rw [List.eq_of_mem_replicate h, ← expandRL_zero (r + 1) M hM.valid]
          exact CReach.step 0 hM
      · rw [expandRL_blkR_ne (r + 1) N (Nat.succ_pos r) hM.rooted hne hlast]
        refine ⟨Ms' ++ [expandRL (r + 1) N M], fun M' h => ?_, by simp⟩
        rcases List.mem_append.mp h with h | h
        · exact hMs' M' h
        · rw [List.mem_singleton.mp h]; exact CReach.step N hM

/-- **Every standard form of DBMS with `r + 1` rows is a list of blocks whose
contents lie in the content system.** -/
theorem dblocks_of_state {r : Nat} (l : (dbmsL r).State) : DBlocks r l.1 := by
  obtain ⟨A, hA, hl⟩ := l.2
  rw [← hl]
  clear hl
  induction hA with
  | init n => exact ⟨[cgen r n], fun M h => by rw [List.mem_singleton.mp h]; exact CReach.gen n,
      by rw [entriesR_dstair_blkR]; simp⟩
  | step N _ ih =>
    rw [entriesR_expand (Nat.succ_pos r)]
    exact dblocks_expand ih N

/-- The rank of a list of blocks is the sum, in order, of `ω` to the ranks of
the contents. -/
theorem rkL_blocks (r : Nat) : ∀ Ms : List (List (List Nat)), (∀ M ∈ Ms, CReach r M) →
    rkL r ((Ms.map (blkR (r + 1))).flatten) = (Ms.map (fun M => ω ^ rkL r M)).sum := by
  intro Ms
  induction Ms with
  | nil => intro _; simp [rkL_nil]
  | cons M Ms ih =>
    intro h
    have hM : CReach r M := h M (by simp)
    have hMs : ∀ M' ∈ Ms, CReach r M' := fun M' hm => h M' (by simp [hm])
    have hvalid : ∀ Ns : List (List (List Nat)), (∀ M' ∈ Ns, CReach r M') →
        Valid r ((Ns.map (blkR (r + 1))).flatten) := by
      intro Ns hNs v hv
      obtain ⟨B, hB, hvB⟩ := List.mem_flatten.mp hv
      obtain ⟨M', hM', rfl⟩ := List.mem_map.mp hB
      exact blkR_col_len (r + 1) (Nat.succ_pos r) (hNs M' hM').valid v hvB
    rw [List.map_cons, List.flatten_cons, List.map_cons, List.sum_cons,
      rkL_append' (blkR_col_len (r + 1) (Nat.succ_pos r) hM.valid) (hvalid Ms hMs) ?_,
      ih hMs, rkL_blkR r ⟨M, hM.valid⟩ hM.rooted]
    cases Ms with
    | nil => exact Or.inl rfl
    | cons M' Ms' =>
      refine Or.inr ?_
      simp only [List.map_cons, List.flatten_cons]
      rw [getElem!_append_left _ _ (by simp [blkR]), blkR_get0, zcol_get]

/-- DBMS on the entries sits inside the rule on all matrices, step for step. -/
def dbmsLToAll (r : Nat) : StepHom (dbmsL r) (bmsAllL r) where
  map := (dbmsLSim r).map
  reindex := id
  map_step := fun _ _ => rfl
  map_halted := fun _ h => h

theorem rank_dbmsL_eq_rkL (r : Nat) (l : (dbmsL r).State) :
    Rewrite.rank (dbmsL_wf r) l = rkL r l.1 := by
  haveI : IsWellFounded (dbmsL r).State (dbmsL r).Rel := ⟨dbmsL_wf r⟩
  haveI : IsWellFounded (bmsAllL r).State (bmsAllL r).Rel := ⟨bmsAllL_wf r⟩
  rw [Rewrite.rank_def, show rkL r l.1 = rkL r ((dbmsLToAll r).map l).1 from rfl,
    rkL_eq ((dbmsLToAll r).map l)]
  exact ((dbmsLToAll r).rank_map (fun k => ⟨k, rfl⟩) (fun _ => Iff.rfl) l).symm

/-- **The rank of DBMS with `r + 1` rows, block by block.**  A standard form is
`blkR M₀ ++ ⋯ ++ blkR Mₖ` with every `Mᵢ` in the content system, and its rank is
`ω ^ rank(M₀) + ⋯ + ω ^ rank(Mₖ)`, where `rank` is the rank of the rule of BM4
on all matrices. -/
theorem rank_dbmsL_eq_sum (r : Nat) (l : (dbmsL r).State) :
    ∃ Ms : List (List (List Nat)), (∀ M ∈ Ms, CReach r M) ∧
      l.1 = (Ms.map (blkR (r + 1))).flatten ∧
      Rewrite.rank (dbmsL_wf r) l = (Ms.map (fun M => ω ^ rkL r M)).sum := by
  obtain ⟨Ms, hMs, hl⟩ := dblocks_of_state l
  exact ⟨Ms, hMs, hl, by rw [rank_dbmsL_eq_rkL, hl, rkL_blocks r Ms hMs]⟩

/-- **The generators**: the rank of the DBMS generator with `r + 1` rows and
`n + 1` columns is `ω` to the rank of its content `cgen r n`. -/
theorem rkL_dstair (r n : Nat) :
    rkL r (entriesR (dstair (r + 1) n)) = ω ^ rkL r (cgen r n) := by
  rw [entriesR_dstair_blkR]
  exact rkL_blkR r ⟨cgen r n, valid_cgen r n⟩ (rooted_cgen r n)

end DBMSBlocks

end Googology.Trans.DBMS
