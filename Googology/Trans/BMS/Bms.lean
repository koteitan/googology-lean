import Googology.Trans.BMS.Entries
import Googology.Trans.BMS.Prim

/-!
# One-row Bashicu matrices, translated

This closes the chain.  `BMS/Entries.lean` matches `BM4.expand` on `BM4.Arr 1`
against `expandL`; `BMS/Prim.lean` translates `expandL` into the extended
Buchholz system.  What is left is that a standard array's entries are a matrix
whose term is a standard form, which `std_entries` proves by induction over
reachability: the generator `(0)(1)⋯(n)` reads as the tower
`ψ_0(ψ_0(⋯ψ_0(0)⋯))`, and expansion keeps both properties.

So `bmsHom` is a `StepHom` from `Notation.BMS.bms 1` into `prim`, with no
renumbering, and composing gives:

* `bmsOrdEval` — each one-row matrix names a countable ordinal, the value of
  the term its entries read as, and expansion lowers it;
* `bms_one_terminates` — one-row matrices terminate.

The second is already known from `Notation.BMS.bms_terminates`, but by a
different route: that one comes from the labelling proof for any number of
rows, this one from the well-ordering of extended Buchholz's ψ.  The first is
new here — `Notation.BMS.bmsEval` gives the rank of the expansion relation,
which is an ordinal but not a named one.
-/

namespace Googology.Trans.BMS

open BM4 Pat
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### The generators -/

/-- The tower `ψ_0(ψ_0(⋯ψ_0(0)⋯))`. -/
def twr : Nat → Term
  | 0 => nil
  | k + 1 => psi nil (twr k)

theorem chain_range' : ∀ (k s b prev : Nat), b ≤ s → s ≤ prev + 1 →
    Chain b prev (List.range' s k) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; exact trivial
  | succ m ih =>
    intro s b prev h1 h2
    rw [List.range'_succ]
    exact ⟨h1, h2, ih (s + 1) b s (by omega) (by omega)⟩

/-- The generator `(0)(1)⋯(n)` is a matrix. -/
theorem col_range (n : Nat) : Col 0 (List.range (n + 1)) := by
  rw [List.range_eq_range', List.range'_succ]
  exact ⟨rfl, chain_range' n 1 0 0 (by omega) (by omega)⟩

/-- A run of consecutive entries reads as a tower. -/
theorem read_range' : ∀ (k b : Nat), read b (List.range' b k) = twr k := by
  intro k
  induction k with
  | zero => intro b; rw [List.range'_zero, read_nil, twr]
  | succ m ih =>
    intro b
    have hall : ∀ x ∈ List.range' (b + 1) m, decide (b < x) = true := by
      intro x hx
      exact decide_eq_true (by have := List.left_le_of_mem_range' hx; omega)
    rw [List.range'_succ, read_cons, takeWhile_all _ hall, dropWhile_all _ hall,
      read_nil, ih (b + 1), twr]

theorem descAll_twr : ∀ k : Nat, DescAll (twr k) := by
  intro k
  induction k with
  | zero => exact trivial
  | succ m ih => exact ⟨ih, trivial, rfl⟩

theorem allNil_twr : ∀ k : Nat, AllNil (twr k) := by
  intro k
  induction k with
  | zero => exact trivial
  | succ m ih => exact ⟨rfl, ih, trivial⟩

/-- The generator's term is a standard form. -/
theorem OT_read_range (n : Nat) : OT (read 0 (List.range (n + 1))) := by
  rw [List.range_eq_range', read_range']
  exact OT_of_desc _ (allNil_twr _) (descAll_twr _)

theorem entries_stair (n : Nat) : entries (stair 1 n) = List.range (n + 1) := by
  rw [entries, show (stair 1 n).len = n + 1 from rfl]
  exact List.map_id _

/-! ### Standard arrays -/

/-- **Every standard one-row array is a matrix whose term is a standard
form.** -/
theorem std_entries : ∀ A : Arr 1, Pat.Std 1 A →
    Col 0 (entries A) ∧ OT (read 0 (entries A)) := by
  intro A h
  induction h with
  | init n => rw [entries_stair]; exact ⟨col_range n, OT_read_range n⟩
  | step N _ ih =>
    rw [entries_expand' _ N ih.1]
    exact prim_step_ok ⟨_, ih⟩ N

/-! ### The translation -/

/-- A standard one-row array, as a state of the primitive sequence system. -/
def toEntries (A : (Googology.Notation.BMS.bms 1).State) : PrimState :=
  ⟨entries A.1, std_entries A.1 A.2⟩

/-- **Reading the entries is a translation** from one-row Bashicu matrices to
the primitive sequence system, and the brackets are not renumbered. -/
def bmsHom : StepHom (Googology.Notation.BMS.bms 1) prim where
  map := toEntries
  reindex := id
  map_step := fun A N => Subtype.ext (entries_expand' A.1 N (std_entries A.1 A.2).1)
  map_halted := fun A h => by
    have hL := entries_length A.1
    rw [show entries A.1 = [] from h] at hL
    exact hL.symm

/-- **A one-row Bashicu matrix names a countable ordinal**: the value of the
extended Buchholz term its entries read as.  Expansion lowers it. -/
noncomputable def bmsOrdEval :
    Eval (Googology.Notation.BMS.bms 1) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim bmsHom.toSim primEval

theorem bmsOrdEval_val (A : (Googology.Notation.BMS.bms 1).State) :
    bmsOrdEval.val A = (read 0 (entries A.1)).val := rfl

/-- **The ordinal is below `ε₀`.** -/
theorem bmsOrdEval_lt_e0 (A : (Googology.Notation.BMS.bms 1).State) :
    bmsOrdEval.val A < te0.val :=
  val_lt_val (std_entries A.1 A.2).2 OT_te0 (read_lt_e0 0 _)

/-- **Expansion lowers the ordinal**, stated without the wrapper. -/
theorem bms_one_val_lt {A B : (Googology.Notation.BMS.bms 1).State}
    (h : (Googology.Notation.BMS.bms 1).Rel B A) :
    (read 0 (entries B.1)).val < (read 0 (entries A.1)).val :=
  bmsOrdEval.val_lt A B h

/-- **One-row Bashicu matrices terminate**, by the translation rather than by
the labelling proof. -/
theorem bms_one_terminates : (Googology.Notation.BMS.bms 1).Terminates :=
  bmsHom.toSim.terminates (primHom.toSim.wf exbOT_wf)


end Googology.Trans.BMS
