import Googology.Trans.BMS.ZeroRow
import Googology.Trans.DBMS.Entries
import Googology.Rank

/-!
# DBMS: `r + 1` rows inside `r + 2` rows

`Trans/BMS/ZeroRow.lean` puts BMS with `r + 1` rows inside BMS with `r + 2`
rows, by writing a row of zeros underneath.  This file does the same for DBMS.

The rule is BM4's in both systems, so `expandRL_zeroRow` (a row of zeros
underneath changes nothing) is already the step.  What is new is the
generators.  The DBMS generator with `s` rows and `n + 1` columns has `i - k`
in column `i`, row `k` (`dsE s n`).  With a row of zeros underneath it is a
DBMS standard form with `s + 1` rows:

* for `n ≤ s` it **is** the generator with `s + 1` rows, since `i - s = 0`
  for `i ≤ n` (`zeroRow_dsE_of_le`);
* for `n ≥ s` it is the generator with `s + 1` rows and `s + 2` columns
  expanded at `n - s` (`expandRL_dsE`).  Its last column is
  `(s + 1, s, …, 1)`; in every row the parent is the column before it,
  `(s, s - 1, …, 0)`, so the bad root is that column, the bad part is that one
  column, and the ascension is `1` above row `s` and `0` in row `s`:

      (0,…)(1,…)⋯(s, s-1, …, 1, 0)(s+1, s, …, 2, 0)⋯(s+N, …, N+1, 0)

So the zero row of a standard form is standard, by induction over
reachability (`exists_dstd_zeroRow`), and `dbmsL_homSucc` is a `StepHom`
from `dbmsL r` to `dbmsL (r + 1)` with no renumbering.  It is one to one
(`dbmsL_homSucc_injective`), keeps the rank (`rank_dbmsL_homSucc`), and is not
onto (`dbmsToSucc_not_surjective`: the generator `(0,0)(1,0)(2,1)` has a
nonzero bottom entry).
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS

/-! ### The generators on the entries -/

/-- The entries of the DBMS generator with `s` rows and `n + 1` columns. -/
def dsE (s n : Nat) : List (List Nat) :=
  (List.range (n + 1)).map (fun i => (List.range s).map (fun k => i - k))

theorem entriesR_dstair_eq_dsE (s n : Nat) : entriesR (dstair s n) = dsE s n :=
  entriesR_dstair s n

@[simp] theorem dsE_length (s n : Nat) : (dsE s n).length = n + 1 := by
  rw [dsE, List.length_map, List.length_range]

theorem dsE_getElem_col {s n i : Nat} (hi : i ≤ n) :
    (dsE s n)[i]! = (List.range s).map (fun k => i - k) := by
  rw [dsE, getElem!_pos _ i (by rw [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range]

theorem dsE_getElem {s n i k : Nat} (hi : i ≤ n) (hk : k < s) :
    ((dsE s n)[i]!)[k]! = i - k := by
  rw [dsE_getElem_col hi, getElem!_pos _ k (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

/-- A column `i ≤ s` of the generator ends in `0` at row `s`. -/
theorem col_succ_of_le {s i : Nat} (hi : i ≤ s) :
    (List.range (s + 1)).map (fun k => i - k) = (List.range s).map (fun k => i - k) ++ [0] := by
  rw [List.range_succ, List.map_append, List.map_singleton, show i - s = 0 by omega]

/-- **Up to `s + 1` columns, the generator with a row of zeros underneath is
the generator with one row more.** -/
theorem zeroRow_dsE_of_le {s n : Nat} (hn : n ≤ s) : zeroRow (dsE s n) = dsE (s + 1) n := by
  rw [dsE, dsE, zeroRow_map]
  refine List.map_congr_left (fun i hi => ?_)
  have : i ≤ s := by have := List.mem_range.mp hi; omega
  rw [col_succ_of_le this]

/-! ### The generator with `s + 2` columns -/

/-- In the generator with `s + 1` rows and `s + 2` columns, column `s` is the
parent of the last column in every row. -/
theorem parR_dsE (s : Nat) : ∀ k, k ≤ s → ParR (dsE (s + 1) (s + 1)) k s (s + 1) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [ParR]
    refine ⟨by omega, ?_, fun j' a b => by omega⟩
    rw [dsE_getElem (by omega) (by omega), dsE_getElem (by omega) (by omega)]
    omega
  | succ m ih =>
    intro hk
    rw [ParR]
    refine ⟨by omega, Relation.TransGen.single (ih (by omega)), ?_, fun j' a b _ => by omega⟩
    rw [dsE_getElem (by omega) (by omega), dsE_getElem (by omega) (by omega)]
    omega

theorem m0L_dsE (s : Nat) : m0L (s + 1) (dsE (s + 1) (s + 1)) = s := by
  have hsome : (parAtR (dsE (s + 1) (s + 1)) s
      ((dsE (s + 1) (s + 1)).length - 1)).isSome = true := by
    rw [dsE_length, show s + 1 + 1 - 1 = s + 1 from rfl, Option.isSome_iff_exists]
    exact ⟨s, (parAtR_eq_some _ _ _ _).mpr (parR_dsE s s (Nat.le_refl s))⟩
  have hle : s ≤ m0L (s + 1) (dsE (s + 1) (s + 1)) :=
    Nat.le_findGreatest (by omega) hsome
  have hge : m0L (s + 1) (dsE (s + 1) (s + 1)) ≤ s := Nat.findGreatest_le _
  omega

theorem badRootR_dsE (s : Nat) : badRootR (s + 1) (dsE (s + 1) (s + 1)) = some s := by
  rw [badRootR, if_neg (by
      rw [List.isEmpty_iff, ← List.length_eq_zero_iff, dsE_length]
      omega),
    m0L_dsE s, dsE_length, show s + 1 + 1 - 1 = s + 1 from rfl, parAtR_eq_some]
  exact parR_dsE s s (Nat.le_refl s)

/-- **The generator with `s + 1` rows and `s + 2` columns expands at `N` to
the generator with `s` rows and `s + N + 1` columns, with a row of zeros
underneath.** -/
theorem expandRL_dsE (s N : Nat) :
    expandRL (s + 1) N (dsE (s + 1) (s + 1)) = zeroRow (dsE s (s + N)) := by
  rw [expandRL, badRootR_dsE s]
  dsimp only
  rw [dsE_length, m0L_dsE s, show s + 1 + 1 - 1 - s = 1 by omega,
    show s + 1 + 1 - 1 = s + 1 from rfl, Nat.mul_one]
  conv_rhs => rw [dsE, zeroRow_map, show s + N + 1 = s + (N + 1) by omega, List.range_add,
    List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left (fun i hi => ?_)
    have hi' : i < s := List.mem_range.mp hi
    rw [dsE_getElem_col (by omega), col_succ_of_le (by omega)]
  · refine List.map_congr_left (fun t _ => ?_)
    simp only [Nat.mod_one, Nat.div_one, Nat.add_zero, Function.comp_apply]
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · refine List.map_congr_left (fun k hk0 => ?_)
      have hk : k < s := List.mem_range.mp hk0
      rw [if_pos (by simp [hk])]
      rw [dsE_getElem (by omega) (by omega), dsE_getElem (by omega) (by omega),
        show s + 1 - k - (s - k) = 1 by omega, Nat.mul_one]
      omega
    · rw [if_neg (by simp), dsE_getElem (by omega) (by omega), Nat.sub_self]

/-! ### The zero row of a standard form is standard -/

/-- **A DBMS standard form with a row of zeros underneath is a DBMS standard
form with one row more.** -/
theorem exists_dstd_zeroRow (r : Nat) : ∀ A : Arr (r + 1), DStd (r + 1) A →
    ∃ B : Arr (r + 2), DStd (r + 2) B ∧ entriesR B = zeroRow (entriesR A) := by
  intro A hA
  induction hA with
  | init n =>
    rw [entriesR_dstair_eq_dsE]
    by_cases hn : n ≤ r + 1
    · exact ⟨dstair (r + 2) n, DStd.init n, by
        rw [entriesR_dstair_eq_dsE, zeroRow_dsE_of_le hn]⟩
    · refine ⟨expand (dstair (r + 2) (r + 2)) (n - (r + 1)), DStd.step _ (DStd.init _), ?_⟩
      rw [entriesR_expand (by omega), entriesR_dstair_eq_dsE,
        show r + 2 = (r + 1) + 1 from rfl, expandRL_dsE (r + 1) (n - (r + 1)),
        show r + 1 + (n - (r + 1)) = n by omega]
  | @step A0 N _ ih =>
    obtain ⟨B, hB, hE⟩ := ih
    refine ⟨expand B N, DStd.step N hB, ?_⟩
    rw [entriesR_expand (by omega), hE,
      expandRL_zeroRow (r := r + 1) (by omega) N (entriesR A0) (entriesR_col_len A0),
      entriesR_expand (by omega)]

/-! ### The systems -/

/-- **DBMS with `r + 1` rows sits inside DBMS with `r + 2` rows**, by writing
a row of zeros underneath.  The brackets are not renumbered. -/
def dbmsL_homSucc (r : Nat) : StepHom (dbmsL r) (dbmsL (r + 1)) where
  map := fun l => ⟨zeroRow l.1, by
    obtain ⟨A, hA, hE⟩ := l.2
    obtain ⟨B, hB, hEB⟩ := exists_dstd_zeroRow r A hA
    exact ⟨B, hB, by rw [hEB, hE]⟩⟩
  reindex := id
  map_step := fun l N => Subtype.ext (by
    obtain ⟨A, _, hE⟩ := l.2
    exact (expandRL_zeroRow (r := r + 1) (by omega) N l.1
      (by rw [← hE]; exact entriesR_col_len A)).symm)
  map_halted := fun l h => (zeroRow_nil_iff l.1).mp h

@[simp] theorem dbmsL_homSucc_map_val (r : Nat) (l : (dbmsL r).State) :
    ((dbmsL_homSucc r).map l).1 = zeroRow l.1 := rfl

/-- **It is one to one.** -/
theorem dbmsL_homSucc_injective (r : Nat) {a b : (dbmsL r).State}
    (h : (dbmsL_homSucc r).map a = (dbmsL_homSucc r).map b) : a = b := by
  have h' : zeroRow a.1 = zeroRow b.1 := congrArg Subtype.val h
  exact Subtype.ext
    (List.map_injective_iff.mpr (fun x y hxy => List.append_cancel_right hxy) h')

/-- **It keeps the rank**: the embedding has exactly the steps the source has. -/
theorem rank_dbmsL_homSucc (r : Nat) (a : (dbmsL r).State) :
    Rewrite.rank (dbmsL_wf (r + 1)) ((dbmsL_homSucc r).map a)
      = Rewrite.rank (dbmsL_wf r) a := by
  haveI : IsWellFounded (dbmsL r).State (dbmsL r).Rel := ⟨dbmsL_wf r⟩
  haveI : IsWellFounded (dbmsL (r + 1)).State (dbmsL (r + 1)).Rel := ⟨dbmsL_wf (r + 1)⟩
  rw [Rewrite.rank_def, Rewrite.rank_def]
  exact StepHom.rank_map (dbmsL_homSucc r) (fun k => ⟨k, rfl⟩)
    (fun s => (zeroRow_nil_iff s.1).symm) a

/-! ### The cells of the translation table, in the shape of `TransGoals` -/

theorem dbmsToSucc_preserves : ∀ (i : Nat) (a b : (dbmsL i).State), True → True →
    (dbmsL i).Rel b a → (dbmsL (i + 1)).Rel ((dbmsL_homSucc i).map b) ((dbmsL_homSucc i).map a) :=
  fun i a b _ _ h => (dbmsL_homSucc i).toSim.map_rel a b h

theorem dbmsToSucc_commutes : ∃ ρ : Nat → Nat → Nat, ∀ i,
    (∀ (a : (dbmsL i).State) k, True → True ∧
      (dbmsL_homSucc i).map ((dbmsL i).step a k)
        = (dbmsL (i + 1)).step ((dbmsL_homSucc i).map a) (ρ i k)) ∧
    (∀ a, True → (dbmsL (i + 1)).halted ((dbmsL_homSucc i).map a) → (dbmsL i).halted a) :=
  ⟨fun i => (dbmsL_homSucc i).reindex, fun i =>
    ⟨fun a k _ => ⟨trivial, (dbmsL_homSucc i).map_step a k⟩,
     fun a _ h => (dbmsL_homSucc i).map_halted a h⟩⟩

theorem dbmsToSucc_injective : ∀ (i : Nat) (a b : (dbmsL i).State), True → True →
    (dbmsL_homSucc i).map a = (dbmsL_homSucc i).map b → a = b :=
  fun i _ _ _ _ h => dbmsL_homSucc_injective i h

theorem dbmsToSucc_rank : ∀ i, ∃ (hR : (dbmsL i).WF) (hQ : (dbmsL (i + 1)).WF),
    ∀ a, True → Rewrite.rank hQ ((dbmsL_homSucc i).map a) = Rewrite.rank hR a :=
  fun i => ⟨dbmsL_wf i, dbmsL_wf (i + 1), fun a _ => rank_dbmsL_homSucc i a⟩

/-- **It is not onto**: the generator `(0,0)(1,0)(2,1)` of two-row DBMS has
`1` in its bottom row, and every column of an image ends in `0`. -/
theorem dbmsToSucc_not_surjective :
    ¬ ∀ (i : Nat) (c : (dbmsL (i + 1)).State), ∃ a : (dbmsL i).State,
      True ∧ (dbmsL_homSucc i).map a = c := by
  intro h
  obtain ⟨a, -, ha⟩ := h 0 ((dbmsLStd 1).gen 2)
  have hv : zeroRow a.1 = dsE 2 2 := congrArg Subtype.val ha
  have hm : [2, 1] ∈ zeroRow a.1 := by rw [hv]; decide
  obtain ⟨d, -, hd⟩ := List.mem_map.mp hm
  have := congrArg List.getLast? hd
  simp at this

/-! ### The whole hierarchy -/

/-- **`r + 1` rows sit inside `r + d + 1`**, by writing `d` rows of zeros
underneath. -/
def dbmsL_simAdd (r : Nat) : ∀ d : Nat, Sim (dbmsL r) (dbmsL (r + d))
  | 0 => Sim.refl _
  | d + 1 => (dbmsL_simAdd r d).comp (dbmsL_homSucc (r + d)).toSim

/-- And that is what the map does. -/
theorem dbmsL_simAdd_map (r : Nat) : ∀ (d : Nat) (l : (dbmsL r).State),
    ((dbmsL_simAdd r d).map l).1 = zeroRow^[d] l.1 := by
  intro d
  induction d with
  | zero => intro l; rfl
  | succ m ih =>
    intro l
    rw [Function.iterate_succ_apply', ← ih l]
    rfl

/-- **So the number of rows only goes up.** -/
def dbmsL_simLe {r s : Nat} (h : r ≤ s) : Sim (dbmsL r) (dbmsL s) :=
  Nat.add_sub_cancel' h ▸ dbmsL_simAdd r (s - r)

end Googology.Trans.DBMS
