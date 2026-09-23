import Googology.Trans.DBMS.Tables

/-!
# One-row DBMS on the entries

A standard form of DBMS is a matrix.  A state of `dbms 1` is an array `Arr 1`,
and an array has a total column map, so it also holds values outside the
matrix.  `Trans/DBMS/Tables.lean` shows two standard arrays, `stA` and `stB`,
that are the same matrix `(0)` and differ only there.  So `dbms 1` has more
states than there are standard forms.

This file gives one-row DBMS with the matrices as its states, as
`Trans/BMS/Prim.lean` and `Trans/BMS/Pair.lean` do for BMS.

* `dbmsL1`: a state is the list of entries of a standard one-row DBMS array;
  the step is `expandL`, and a state halts when it is the empty list.
  `dbmsL1Std` names the generators `(0)(1)⋯(n)`.
* `dbmsToL1`: the entries, as a `StepHom` from `dbms 1` onto `dbmsL1`.  Two
  arrays go to the same state exactly when they are the same matrix
  (`dbmsToL1_map_eq_iff`).  The rank is kept (`rank_dbmsToL1`), and so is the
  ordinal (`dbmsOrdEval_val_eq`).
* `dbmsL1Prim`: `dbmsL1` → primitive sequences, the identity on the lists.  It
  is one to one and onto (`dbmsL1Prim_injective`, `dbmsL1Prim_surjective`),
  because the standard one-row DBMS matrices are the standard one-row BMS
  matrices (`dstd_entries_iff`).  `dbmsL1EquivPrim` says the two systems are
  the same system.
* `dbmsL1OrdEval`: the ordinal of a matrix.  It is one to one
  (`dbmsL1OrdEval_injective`), onto the ordinals below `ε₀`
  (`dbmsL1Ord_image`), equal to the rank (`rank_dbmsL1_eq_val`) and
  order-preserving for the dictionary order (`dbmsL1OrdEval_lt_iff`).
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### The system -/

/-- The state of one-row DBMS on the entries: the entries of a standard
one-row DBMS array. -/
def DbmsState1 : Type := {l : List Nat // DReach l}

/-- A state is a one-row matrix whose term is a standard form. -/
theorem DbmsState1.ok (l : DbmsState1) : Col 0 l.1 ∧ OT (read 0 l.1) :=
  (dstd_entries_iff l.1).mp l.2

theorem dbmsL1_step_ok (l : DbmsState1) (N : Nat) : DReach (expandL N 0 l.1) :=
  dreach_expandL l.ok.1 l.2 N

/-- **One-row DBMS on the entries.**  The step is `expandL`, a function that
runs. -/
def dbmsL1 : Rewrite where
  State := DbmsState1
  step := fun l N => ⟨expandL N 0 l.1, dbmsL1_step_ok l N⟩
  halted := fun l => l.1 = []

@[simp] theorem dbmsL1_step_val (l : DbmsState1) (N : Nat) :
    ((dbmsL1.step l N) : DbmsState1).1 = expandL N 0 l.1 := rfl

@[simp] theorem dbmsL1_halted_iff (l : DbmsState1) : dbmsL1.halted l ↔ l.1 = [] := Iff.rfl

/-- The generators `(0)(1)⋯(n)`. -/
def dbmsL1Std : dbmsL1.Std where
  Standard := fun _ => True
  gen := fun n => ⟨List.range (n + 1), dreach_range n⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-! ### From the arrays: the entries -/

/-- The entries of a standard one-row DBMS array, as a state of `dbmsL1`. -/
def toL1 (A : (dbms 1).State) : DbmsState1 := ⟨entries A.1, A.1, A.2, rfl⟩

/-- **The entries are a translation** from `dbms 1` onto `dbmsL1`, bracket for
bracket. -/
def dbmsToL1 : StepHom (dbms 1) dbmsL1 where
  map := toL1
  reindex := id
  map_step := fun A N => Subtype.ext (entries_expand' A.1 N (dstd_entries A.1 A.2).1)
  map_halted := fun A h => by
    have hL := entries_length A.1
    rw [show entries A.1 = [] from h] at hL
    exact hL.symm

/-- **Two arrays go to the same state exactly when they are the same
matrix.** -/
theorem dbmsToL1_map_eq_iff (A B : (dbms 1).State) :
    dbmsToL1.map A = dbmsToL1.map B ↔ entries A.1 = entries B.1 :=
  Subtype.ext_iff

/-- **Every state of `dbmsL1` is the matrix of a standard array.** -/
theorem dbmsToL1_surjective (l : DbmsState1) : ∃ A, dbmsToL1.map A = l := by
  obtain ⟨A, hA, hl⟩ := l.2
  exact ⟨⟨A, hA⟩, Subtype.ext hl⟩

/-- The generators go to the generators. -/
theorem dbmsToL1_gen (n : Nat) :
    dbmsToL1.map ((dbmsStd 1).gen n) = dbmsL1Std.gen n :=
  Subtype.ext (entries_dstair n)

theorem dbmsToL1_halted_iff (A : (dbms 1).State) :
    (dbms 1).halted A ↔ dbmsL1.halted (dbmsToL1.map A) := by
  show A.1.len = 0 ↔ entries A.1 = []
  exact entries_eq_nil_iff.symm

/-! ### The same system as the primitive sequences -/

/-- A state of `dbmsL1` as a primitive sequence: the same list. -/
def l1ToPrim (l : DbmsState1) : PrimState := ⟨l.1, l.ok⟩

/-- A primitive sequence as a state of `dbmsL1`: the same list. -/
def primToL1 (l : PrimState) : DbmsState1 := ⟨l.1, (dstd_entries_iff l.1).mpr l.2⟩

/-- **`dbmsL1` → primitive sequences**, the identity on the lists. -/
def dbmsL1Prim : StepHom dbmsL1 prim where
  map := l1ToPrim
  reindex := id
  map_step := fun _ _ => rfl
  map_halted := fun _ h => h

/-- Primitive sequences → `dbmsL1`, the identity on the lists. -/
def primDbmsL1 : StepHom prim dbmsL1 where
  map := primToL1
  reindex := id
  map_step := fun _ _ => rfl
  map_halted := fun _ h => h

/-- **One-row DBMS on the entries and the primitive sequence system are the
same system.** -/
def dbmsL1EquivPrim : Equiv dbmsL1 prim where
  toFun := dbmsL1Prim.toSim
  invFun := primDbmsL1.toSim
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem dbmsL1Prim_injective {a b : DbmsState1} (h : dbmsL1Prim.map a = dbmsL1Prim.map b) :
    a = b :=
  Subtype.ext (congrArg (fun x : PrimState => x.1) h)

theorem dbmsL1Prim_surjective (c : PrimState) : dbmsL1Prim.map (primToL1 c) = c := rfl

/-- The entries of a standard array, read as a primitive sequence, are what
`dbmsHom` gives. -/
theorem dbmsL1Prim_toL1 (A : (dbms 1).State) :
    dbmsL1Prim.map (dbmsToL1.map A) = dbmsHom.map A :=
  rfl

/-! ### Well-foundedness and the rank -/

/-- **One-row DBMS on the entries is well founded.** -/
theorem dbmsL1_wf : dbmsL1.WF := dbmsL1Prim.toSim.wf prim_wf

/-- **And terminates.** -/
theorem dbmsL1_terminates : dbmsL1.Terminates := dbmsL1.terminates_of_wf dbmsL1_wf

instance instIsWellFoundedDbmsL1 : IsWellFounded dbmsL1.State dbmsL1.Rel := ⟨dbmsL1_wf⟩

/-- The rank of a matrix is the rank of it as a primitive sequence. -/
theorem rank_dbmsL1Prim (l : DbmsState1) :
    IsWellFounded.rank prim.Rel (dbmsL1Prim.map l) = IsWellFounded.rank dbmsL1.Rel l :=
  dbmsL1Prim.rank_map (fun k => ⟨k, rfl⟩) (fun _ => Iff.rfl) l

/-- **The entries keep the rank**: an array has the rank of its matrix. -/
theorem rank_dbmsToL1 (A : (dbms 1).State) :
    IsWellFounded.rank dbmsL1.Rel (dbmsToL1.map A) = IsWellFounded.rank (dbms 1).Rel A :=
  dbmsToL1.rank_map (fun k => ⟨k, rfl⟩) dbmsToL1_halted_iff A

/-! ### The ordinal of a matrix -/

/-- **A one-row DBMS matrix names a countable ordinal**, and expansion lowers
it. -/
noncomputable def dbmsL1OrdEval :
    Eval dbmsL1 (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim dbmsL1Prim.toSim primEval

theorem dbmsL1OrdEval_val (l : DbmsState1) :
    dbmsL1OrdEval.val l = (read 0 l.1).val := rfl

/-- **An array names the ordinal of its matrix.** -/
theorem dbmsOrdEval_val_eq (A : (dbms 1).State) :
    dbmsOrdEval.val A = dbmsL1OrdEval.val (dbmsToL1.map A) := rfl

/-- **Distinct matrices name distinct ordinals.** -/
theorem dbmsL1OrdEval_injective {a b : DbmsState1}
    (h : dbmsL1OrdEval.val a = dbmsL1OrdEval.val b) : a = b :=
  Subtype.ext (read_inj a.ok.1 b.ok.1 (val_inj_of_OT a.ok.2 b.ok.2 h))

/-- **The matrices name exactly the ordinals below `ε₀`.** -/
theorem dbmsL1Ord_image :
    {α | ∃ a, dbmsL1Std.Standard a ∧ dbmsL1OrdEval.val a = α} = Set.Iio Ord.eps0 := by
  ext α
  constructor
  · rintro ⟨a, -, rfl⟩
    exact val_read_lt_eps0 a.ok.2
  · intro h
    obtain ⟨l, hc, hOT, hv⟩ := exists_matrix_of_lt_eps0 h
    exact ⟨⟨l, (dstd_entries_iff l).mpr ⟨hc, hOT⟩⟩, trivial, hv⟩

/-- **The rank of a matrix is the ordinal it names.** -/
theorem rank_dbmsL1_eq_val (l : DbmsState1) :
    IsWellFounded.rank dbmsL1.Rel l = dbmsL1OrdEval.val l := by
  rw [← rank_dbmsL1Prim]
  exact rank_prim_eq_val (dbmsL1Prim.map l)

/-- **The dictionary order on the matrices is the order of the ordinals.** -/
theorem dbmsL1OrdEval_lt_iff (a b : DbmsState1) :
    a.1 < b.1 ↔ dbmsL1OrdEval.val a < dbmsL1OrdEval.val b :=
  primEval_lt_iff (dbmsL1Prim.map a) (dbmsL1Prim.map b)

end Googology.Trans.DBMS
