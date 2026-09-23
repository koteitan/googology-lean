import Googology.Goals.Basic
import Googology.Notation.Y
import Googology.Trans

/-!
# The goal records of this library

One `def` per record, and the list `audit` of all their lines (section 7.6 of
`spec.md`).  `test/GoalsAudit.lean` prints it, and `scripts/check_readme.py`
compares it with the tables of `README.md` and `README-ja.md`.

A record names its README row by its labels.  The parameters of a record are
part of each statement, and Lean cannot tell whether they are the intended
ones; the docstring of each record says what they are.

The first part of the file holds the small definitions and lemmas that put
existing theorems into the shape a record asks for.
-/

namespace Googology.Goals

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ## Bridges -/

section Bridges

open Googology.Trans.BMS Googology.Trans.PSS

/-- BMS with `r + 1` rows runs on the entries: `entriesR_expand` says the
step is `expandRL`. -/
def bmsRuns (r : Nat) : Runs (Notation.BMS.bms (r + 1)) where
  Code := List (List Nat)
  enc := fun A => entriesR A.1
  run := fun l k => expandRL (r + 1) k l
  halt := List.isEmpty
  enc_step := fun A k => entriesR_expand (Nat.succ_pos r) A.1 k
  halt_iff := fun A => by
    show (entriesR A.1).isEmpty = true ↔ A.1.len = 0
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff, entriesR_length]
  source := "Trans.BMS.entriesR_expand: entriesR (BM4.expand A N) = expandRL (r + 1) N (entriesR A); \
BM4.expand is the rule of koteitan/bms-elem-pattern"

/-- DBMS with `r + 1` rows runs on the entries, as BMS does. -/
def dbmsRuns (r : Nat) : Runs (Notation.DBMS.dbms (r + 1)) where
  Code := List (List Nat)
  enc := fun A => entriesR A.1
  run := fun l k => expandRL (r + 1) k l
  halt := List.isEmpty
  enc_step := fun A k => entriesR_expand (Nat.succ_pos r) A.1 k
  halt_iff := fun A => by
    show (entriesR A.1).isEmpty = true ↔ A.1.len = 0
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff, entriesR_length]
  source := "Trans.BMS.entriesR_expand: entriesR (BM4.expand A N) = expandRL (r + 1) N (entriesR A); \
DBMS expands by BM4.expand"

/-- The Y sequence runs on lists. -/
def yRuns : Runs Notation.Y.ySys where
  Code := List Nat
  enc := fun s => s.1
  run := Notation.Y.expand
  halt := List.isEmpty
  enc_step := fun _ _ => rfl
  halt_iff := fun _ => List.isEmpty_iff
  source := "Notation.Y.expand transcribes script.js of Naruyoko/YNySequence (revision 2de1397); \
test/YCheck.lean checks it against the official program on 213 expansions"

/-- Extended Buchholz's ψ runs on terms: one step is `fs X (idx X n)`. -/
def exbRuns : Runs exbOT where
  Code := Term
  enc := fun A => A.1
  run := fun X n => fs X (idx X n)
  halt := fun X => X == nil
  enc_step := fun _ _ => rfl
  halt_iff := fun _ => beq_iff_eq
  source := "Notation.ExBuchholz.Term.fs: the fundamental sequences of p進大好きbot's notation \
for extended Buchholz's ψ; exbOT.step is fs at idx"

/-- The standard arrays inside all arrays. -/
def bmsIncl (r : Nat) : Incl (Notation.BMS.bms r) (Notation.BMS.bmsAll r) where
  map := Subtype.val
  map_inj := fun _ _ h => Subtype.ext h
  map_step := fun _ _ => rfl
  map_halted := fun _ => Iff.rfl

/-- The DBMS standard arrays inside all arrays. -/
def dbmsIncl (r : Nat) : Incl (Notation.DBMS.dbms r) (Notation.BMS.bmsAll r) where
  map := Subtype.val
  map_inj := fun _ _ h => Subtype.ext h
  map_step := fun _ _ => rfl
  map_halted := fun _ => Iff.rfl

/-- The standard Y sequences inside the legal ones. -/
def yIncl : Incl Notation.Y.ySys Notation.Y.yLegal where
  map := Notation.Y.stdSim.map
  map_inj := fun _ _ h => Subtype.ext (congrArg (fun x : Notation.Y.yLegal.State => x.1) h)
  map_step := fun _ _ => rfl
  map_halted := fun _ => Iff.rfl

/-- Primitive sequences name distinct ordinals. -/
theorem primEval_injective {a b : PrimState} (h : primEval.val a = primEval.val b) : a = b :=
  Subtype.ext (read_inj a.2.1 b.2.1 (val_inj_of_OT a.2.2 b.2.2 h))

/-- The ordinals of primitive sequences are the ordinals below `ε₀`. -/
theorem primEval_image :
    {α | ∃ a, primStd.Standard a ∧ primEval.val a = α} = Set.Iio Ord.eps0 := by
  ext α
  constructor
  · rintro ⟨a, -, rfl⟩
    exact val_read_lt_eps0 a.2.2
  · intro h
    obtain ⟨l, hc, hOT, hv⟩ := exists_matrix_of_lt_eps0 h
    exact ⟨⟨l, hc, hOT⟩, trivial, hv⟩

/-- The ordinals of pair sequences are the ordinals below `ψ_0(Ω_ω)`. -/
theorem pairOrd_image :
    {α | ∃ a, pairStd.Standard a ∧ pairOrdEval.val a = α} = Set.Iio (val psiOmegaOmega) := by
  rw [← range_pairOrd]
  ext α
  exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, trivial, h⟩⟩

/-- The ordinals of one-row DBMS are the ordinals below `ε₀`. -/
theorem dbmsOrd_image :
    {α | ∃ a, (Notation.DBMS.dbmsStd 1).Standard a ∧ Trans.DBMS.dbmsOrdEval.val a = α}
      = Set.Iio Ord.eps0 := by
  ext α
  constructor
  · rintro ⟨a, -, rfl⟩
    show _ < Ord.eps0
    rw [← val_te0]
    exact Trans.DBMS.dbmsOrdEval_lt_e0 a
  · intro h
    obtain ⟨a, ha⟩ := Trans.DBMS.exists_dbms_of_lt_eps0 h
    exact ⟨a, trivial, ha⟩

/-- The ordinals of the countable standard forms are the ordinals below
`ψ_0(Λ)`. -/
theorem exbOT_image :
    {α | ∃ a, exbOTStd.Standard a ∧ val (a : exbOT.State).1 = α} = Set.Iio (Ord.psi Lam 0) := by
  ext α
  constructor
  · rintro ⟨a, -, rfl⟩
    exact (lt_tW_iff_val_lt_psi_Lam a.2.1).mp a.2.2
  · intro h
    obtain ⟨X, ⟨hX, hv⟩, -⟩ := existsUnique_OT_of_lt_psi_Lam h
    have hlt : val X < Ord.psi Lam 0 := hv ▸ h
    exact ⟨⟨X, hX, (lt_tW_iff_val_lt_psi_Lam hX).mpr hlt⟩, trivial, hv⟩

/-- A step keeps a standard form below `ψ_0(Ω_ω)` standard and below it. -/
theorem step_psiOmegaOmega_ok {X : Term} (hOT : OT X) (hlt : X < psiOmegaOmega) (n : Nat) :
    OT (fs X (idx X n)) ∧ fs X (idx X n) < psiOmegaOmega := by
  have htW := lt_tW_of_lt_psiOmegaOmega hlt
  by_cases h : X = nil
  · subst h
    rw [show fs nil (idx nil n) = nil from by rw [fs]]
    exact ⟨rfl, hlt⟩
  · exact ⟨(step_ok hOT htW n).1, lt_trans (step_lt hOT htW h n) hlt⟩

/-- Extended Buchholz's ψ on the standard forms below `ψ_0(Ω_ω)`: the target
of the pair sequences. -/
def exbPair : Rewrite where
  State := {X : Term // OT X ∧ X < psiOmegaOmega}
  step := fun A n => ⟨fs A.1 (idx A.1 n), step_psiOmegaOmega_ok A.2.1 A.2.2 n⟩
  halted := fun A => A.1 = nil

theorem OT_psiOmegaOmega : OT psiOmegaOmega := by decide

theorem pairOrdTerm_lt (l : PairState) : pairOrdTerm l.1 < psiOmegaOmega := by
  have hm : pairOrdEval.val l ∈ Set.Iio (val psiOmegaOmega) :=
    range_pairOrd ▸ Set.mem_range_self l
  have hv : val (pairOrdTerm l.1) < val psiOmegaOmega := by
    rw [val_pairOrdTerm l.2]
    exact hm
  exact (lt_iff_val_lt (OT_pairOrdTerm l.2) OT_psiOmegaOmega).mpr hv

/-- A pair sequence goes to the term of its ordinal, `0` or `1 + pairTerm M`. -/
def pairToExb (l : PairState) : exbPair.State :=
  ⟨pairOrdTerm l.1, OT_pairOrdTerm l.2, pairOrdTerm_lt l⟩

theorem pairToExb_injective {a b : PairState} (h : pairToExb a = pairToExb b) : a = b := by
  have hv : val (pairOrdTerm a.1) = val (pairOrdTerm b.1) :=
    congrArg (fun x : exbPair.State => val x.1) h
  rw [val_pairOrdTerm a.2, val_pairOrdTerm b.2] at hv
  exact pairOrd_injective hv

theorem pairToExb_surjective (c : exbPair.State) : ∃ a, pairToExb a = c := by
  have hv : val c.1 ∈ Set.range pairOrdEval.val := by
    rw [range_pairOrd]
    exact val_lt_val c.2.1 OT_psiOmegaOmega c.2.2
  obtain ⟨a, ha⟩ := hv
  refine ⟨a, Subtype.ext (val_inj_of_OT (OT_pairOrdTerm a.2) c.2.1 ?_)⟩
  show val (pairOrdTerm a.1) = _
  rw [val_pairOrdTerm a.2]
  exact ha

/-- The trio matrix of `ψ_0(Ω_α)` by `omegaIndexMatrix`, and `[]` on every
other term. -/
def omegaIndexOf : Term → List (List Nat)
  | .cons .nil (.cons α .nil .nil) .nil => omegaIndexMatrix α
  | _ => []

theorem omegaIndexOf_col_len (X : Term) : ∀ c ∈ omegaIndexOf X, c.length = 2 + 1 := by
  unfold omegaIndexOf
  split
  · exact fun c hc => (WF3_omegaIndexMatrix _ c hc).1
  · intro c hc
    exact absurd hc (by simp)

/-- Extended Buchholz's ψ → trio sequences, as a map into all three-row
matrices on the entries. -/
def exbToTrio (A : exbOT.State) : (bmsAllL 2).State :=
  ⟨omegaIndexOf A.1, omegaIndexOf_col_len A.1⟩

/-- The terms `ψ_0(Ω_α)` with `α < ε₀`: where `exbToTrio` is about. -/
def TrioDom (A : exbOT.State) : Prop :=
  ∃ α, OT α ∧ α < te0 ∧ A.1 = psi nil (psi α nil)

end Bridges

/-! ## The first table: notations -/

open Googology.Notation.BMS Googology.Notation.DBMS Googology.Notation.Y

/-- BMS, `r + 1` rows for every `r`, on the standard arrays. -/
def bmsNotation : NotationGoals (fun r => bms (r + 1)) (fun r => bmsStd (r + 1)) where
  labelEn := "BMS"
  labelJa := "BMS"
  expansion := some bmsRuns
  wf := .proved fun r => (bmsStd (r + 1)).wf_of_wf (bms_wf (r + 1))

/-- BMS on every array, standard or not. -/
def bmsNonStd : NonStdGoals bms bmsAll where
  labelEn := "BMS"
  labelJa := "BMS"
  incl := fun r => ⟨bmsIncl r⟩
  wf := .proved bmsAll_wf

/-- DBMS, `r + 1` rows for every `r`, on its standard arrays. -/
def dbmsNotation : NotationGoals (fun r => dbms (r + 1)) (fun r => dbmsStd (r + 1)) where
  labelEn := "DBMS"
  labelJa := "DBMS"
  expansion := some dbmsRuns
  wf := .proved fun r => (dbmsStd (r + 1)).wf_of_wf (dbms_wf (r + 1))

/-- DBMS on every array. -/
def dbmsNonStd : NonStdGoals dbms bmsAll where
  labelEn := "DBMS"
  labelJa := "DBMS"
  incl := fun r => ⟨dbmsIncl r⟩
  wf := .proved bmsAll_wf

/-- The Y sequence on its standard forms. -/
def yNotation : NotationGoals (fun _ : Unit => ySys) (fun _ => yStd) where
  labelEn := "Y sequence"
  labelJa := "Y 数列"
  expansion := some fun _ => yRuns
  wf := .proved fun _ => yStd.wf_of_wf ySys_wf

/-- The Y sequence on every legal sequence. -/
def yNonStd : NonStdGoals (fun _ : Unit => ySys) (fun _ => yLegal) where
  labelEn := "Y sequence"
  labelJa := "Y 数列"
  incl := fun _ => ⟨yIncl⟩
  wf := .proved fun _ => yLegal_wf

/-- Extended Buchholz's ψ on the countable standard forms. -/
def exbNotation : NotationGoals (fun _ : Unit => exbOT) (fun _ => exbOTStd) where
  labelEn := "extended Buchholz's ψ"
  labelJa := "拡張ブーフホルツ ψ"
  expansion := some fun _ => exbRuns
  wf := .proved fun _ => exbOTStd.wf_of_wf exbOT_wf

/-! ## The second table: translations into the ordinals -/

open Googology.Trans.BMS Googology.Trans.DBMS Googology.Trans.PSS

/-- One row of "BMS with at most 2 rows": the primitive sequences on the
entries, the ordinal of the reading, onto the ordinals below `ε₀`, with the
dictionary order on the entries. -/
def bmsOneRowOrd : OrdGoals (fun _ : Unit => prim) (fun _ => primStd)
    (fun _ => primEval.val) (fun _ => Set.Iio Ord.eps0) (fun _ => primLt) where
  labelEn := "BMS with at most 2 rows"
  labelJa := "2 行以下の BMS"
  injective := .proved fun _ _ _ _ _ h => primEval_injective h
  surjective := .proved fun _ => primEval_image
  decreasing := .proved fun _ a b _ _ h => primEval.val_lt a b h
  rank := .proved fun _ => ⟨primStd.wf_of_wf prim_wf, fun a ha => by
    rw [Rewrite.Std.rank_eq primStd prim_wf a ha]
    exact (rank_prim_eq_val a).symm⟩
  order := .proved fun _ a b _ _ => primEval_lt_iff a b

/-- Two rows of "BMS with at most 2 rows": the pair sequences on the entries,
`1 + val` of the term by pss-proof's `Trans`, onto the ordinals below
`ψ_0(Ω_ω)`, with the lexicographic order of pss-proof. -/
def bmsTwoRowOrd : OrdGoals (fun _ : Unit => pairL) (fun _ => pairStd)
    (fun _ => pairOrdEval.val) (fun _ => Set.Iio (val psiOmegaOmega)) (fun _ => PairLt) where
  labelEn := "BMS with at most 2 rows"
  labelJa := "2 行以下の BMS"
  injective := .proved fun _ _ _ _ _ h => pairOrd_injective h
  surjective := .proved fun _ => pairOrd_image
  decreasing := .proved fun _ a b _ _ h => pairOrdEval.val_lt a b h
  rank := .proved fun _ => ⟨pairStd.wf_of_wf pairL_wf, fun a ha => by
    rw [Rewrite.Std.rank_eq pairStd pairL_wf a ha]
    exact (rank_pairL_eq a).symm⟩
  order := .proved fun _ a b _ _ => ltPS_iff_pairOrd_lt a b

/-- One-row DBMS: the ordinal of the reading of the entries, onto the
ordinals below `ε₀`, with the dictionary order on the entries.  It is not
injective on the arrays: `dbmsOrdEval_not_injective`. -/
def dbmsOneRowOrd : OrdGoals (fun _ : Unit => dbms 1) (fun _ => dbmsStd 1)
    (fun _ => dbmsOrdEval.val) (fun _ => Set.Iio Ord.eps0)
    (fun _ A B => entries A.1 < entries B.1) where
  labelEn := "one-row DBMS"
  labelJa := "1 行の DBMS"
  injective := .refuted fun h =>
    dbmsOrdEval_not_injective fun a b hab => h () a b trivial trivial hab
  surjective := .proved fun _ => dbmsOrd_image
  decreasing := .proved fun _ a b _ _ h => dbmsOrdEval.val_lt a b h
  rank := .proved fun _ => ⟨(dbmsStd 1).wf_of_wf (dbms_wf 1), fun a ha => by
    rw [Rewrite.Std.rank_eq (dbmsStd 1) (dbms_wf 1) a ha]
    exact (rank_dbms_eq_val a).symm⟩
  order := .proved fun _ a b _ _ => dbmsOrdEval_lt_iff a b

/-- Extended Buchholz's ψ: the value of a countable standard form, onto the
ordinals below `ψ_0(Λ)`, with the term order. -/
def exbOrd : OrdGoals (fun _ : Unit => exbOT) (fun _ => exbOTStd)
    (fun _ A => val A.1) (fun _ => Set.Iio (Ord.psi Lam 0)) (fun _ A B => A.1 < B.1) where
  labelEn := "extended Buchholz's ψ"
  labelJa := "拡張ブーフホルツ ψ"
  injective := .proved fun _ a b _ _ h => Subtype.ext (val_inj_of_OT a.2.1 b.2.1 h)
  surjective := .proved fun _ => exbOT_image
  decreasing := .proved fun _ a b _ _ h => exbOTEval.val_lt a b h
  rank := .proved fun _ => ⟨exbOTStd.wf_of_wf exbOT_wf, fun a ha => by
    rw [Rewrite.Std.rank_eq exbOTStd exbOT_wf a ha]
    exact (rank_exbOT_eq_val a).symm⟩
  order := .proved fun _ a b _ _ => lt_iff_val_lt a.2.1 b.2.1

/-! ## The third table: translations between notations -/

/-- Primitive sequences → pair sequences: a row of zeros underneath. -/
def primToPair : TransGoals (fun _ : Unit => prim) (fun _ => pairL) (fun _ _ => True)
    (fun _ => primHomPair.map) where
  sourceEn := "primitive sequences"
  sourceJa := "原始数列"
  targetEn := "pair sequences"
  targetJa := "ペア数列"
  preserves := .proved fun _ a b _ _ h => primHomPair.toSim.map_rel a b h
  commutes := .proved ⟨fun _ => primHomPair.reindex, fun _ =>
    ⟨fun a k _ => ⟨trivial, primHomPair.map_step a k⟩,
     fun a _ h => primHomPair.map_halted a h⟩⟩
  injective := .proved fun _ _ _ _ _ h => primHomPair_injective h
  surjective := .todo
  rank := .proved fun _ => ⟨prim_wf, pairL_wf, fun a _ => rank_toPairS a⟩

/-- Primitive sequences → extended Buchholz's ψ: the reading, onto the
standard forms below `ψ_0(Ω)` (`exbE0`). -/
def primToExb : TransGoals (fun _ : Unit => prim) (fun _ => exbE0) (fun _ _ => True)
    (fun _ => primHomE0.map) where
  sourceEn := "primitive sequences"
  sourceJa := "原始数列"
  targetEn := "extended Buchholz's ψ"
  targetJa := "拡張ブーフホルツ ψ"
  preserves := .proved fun _ a b _ _ h => primHomE0.toSim.map_rel a b h
  commutes := .proved ⟨fun _ => primHomE0.reindex, fun _ =>
    ⟨fun a k _ => ⟨trivial, primHomE0.map_step a k⟩,
     fun a _ h => primHomE0.map_halted a h⟩⟩
  injective := .proved fun _ a b _ _ h => by
    rw [← primEquivE0.left_inv a, ← primEquivE0.left_inv b]
    exact congrArg primEquivE0.invFun.map h
  surjective := .proved fun _ c => ⟨primEquivE0.invFun.map c, trivial, primEquivE0.right_inv c⟩
  rank := .proved fun _ => ⟨prim_wf, primEquivE0.wf_iff.mp prim_wf,
    fun a _ => rank_primHomE0 a⟩

/-- Pair sequences → extended Buchholz's ψ: the term of the ordinal, onto the
standard forms below `ψ_0(Ω_ω)` (`exbPair`). -/
def pairToExbGoals : TransGoals (fun _ : Unit => pairL) (fun _ => exbPair) (fun _ _ => True)
    (fun _ => pairToExb) where
  sourceEn := "pair sequences"
  sourceJa := "ペア数列"
  targetEn := "extended Buchholz's ψ"
  targetJa := "拡張ブーフホルツ ψ"
  preserves := .todo
  commutes := .todo
  injective := .proved fun _ _ _ _ _ h => pairToExb_injective h
  surjective := .proved fun _ c => (pairToExb_surjective c).imp fun _ h => ⟨trivial, h⟩
  rank := .todo

/-- BMS `r` rows → BMS `r + 1` rows: a row of zeros underneath, on the
entries.  `bmsL r` has `r + 1` rows. -/
def bmsToSucc : TransGoals bmsL (fun r => bmsL (r + 1)) (fun _ _ => True)
    (fun r => (bmsL_homSucc r).map) where
  sourceEn := "BMS, `r` rows"
  sourceJa := "BMS `r` 行"
  targetEn := "BMS, `r+1` rows"
  targetJa := "BMS `r+1` 行"
  preserves := .proved fun i a b _ _ h => (bmsL_homSucc i).toSim.map_rel a b h
  commutes := .proved ⟨fun i => (bmsL_homSucc i).reindex, fun i =>
    ⟨fun a k _ => ⟨trivial, (bmsL_homSucc i).map_step a k⟩,
     fun a _ h => (bmsL_homSucc i).map_halted a h⟩⟩
  injective := .todo
  surjective := .todo
  rank := .proved fun i => ⟨bmsL_wf i, bmsL_wf (i + 1), fun a _ => rank_zeroRow i a⟩

/-- One-row DBMS → primitive sequences: the entries.  It is not injective on
the arrays: `dbmsHom_not_injective`. -/
def dbmsToPrim : TransGoals (fun _ : Unit => dbms 1) (fun _ => prim) (fun _ _ => True)
    (fun _ => dbmsHom.map) where
  sourceEn := "one-row DBMS"
  sourceJa := "1 行の DBMS"
  targetEn := "primitive sequences"
  targetJa := "原始数列"
  preserves := .proved fun _ a b _ _ h => dbmsHom.toSim.map_rel a b h
  commutes := .proved ⟨fun _ => dbmsHom.reindex, fun _ =>
    ⟨fun a k _ => ⟨trivial, dbmsHom.map_step a k⟩,
     fun a _ h => dbmsHom.map_halted a h⟩⟩
  injective := .refuted fun h =>
    dbmsHom_not_injective fun a b hab => h () a b trivial trivial hab
  surjective := .todo
  rank := .proved fun _ => ⟨dbms_wf 1, prim_wf, fun a _ => rank_dbmsHom a⟩

/-- DBMS `r` rows → BMS `r` rows: the array itself, into all arrays. -/
def dbmsToBms : TransGoals dbms bmsAll (fun _ _ => True) (fun r => (dbmsSim r).map) where
  sourceEn := "DBMS, `r` rows"
  sourceJa := "DBMS `r` 行"
  targetEn := "BMS, `r` rows"
  targetJa := "BMS `r` 行"
  preserves := .proved fun i a b _ _ h => (dbmsSim i).map_rel a b h
  commutes := .todo
  injective := .todo
  surjective := .todo
  rank := .todo

/-- Extended Buchholz's ψ → trio sequences: `omegaIndexMatrix`, transcribed
from koteitan/trio, on the terms `ψ_0(Ω_α)` with `α < ε₀`, into all
three-row matrices. -/
def exbToTrioGoals : TransGoals (fun _ : Unit => exbOT) (fun _ => bmsAllL 2)
    (fun _ => TrioDom) (fun _ => exbToTrio) where
  sourceEn := "extended Buchholz's ψ"
  sourceJa := "拡張ブーフホルツ ψ"
  targetEn := "trio sequences"
  targetJa := "トリオ数列"
  preserves := .todo
  commutes := .todo
  injective := .todo
  surjective := .todo
  rank := .todo

/-! ## The audit -/

/-- Every line of every record. -/
def audit : List AuditLine :=
  bmsNotation.lines (toString ``Googology.Goals.bmsNotation) ++
  bmsNonStd.lines (toString ``Googology.Goals.bmsNonStd) ++
  dbmsNotation.lines (toString ``Googology.Goals.dbmsNotation) ++
  dbmsNonStd.lines (toString ``Googology.Goals.dbmsNonStd) ++
  yNotation.lines (toString ``Googology.Goals.yNotation) ++
  yNonStd.lines (toString ``Googology.Goals.yNonStd) ++
  exbNotation.lines (toString ``Googology.Goals.exbNotation) ++
  bmsOneRowOrd.lines (toString ``Googology.Goals.bmsOneRowOrd) ++
  bmsTwoRowOrd.lines (toString ``Googology.Goals.bmsTwoRowOrd) ++
  dbmsOneRowOrd.lines (toString ``Googology.Goals.dbmsOneRowOrd) ++
  exbOrd.lines (toString ``Googology.Goals.exbOrd) ++
  primToPair.lines (toString ``Googology.Goals.primToPair) ++
  primToExb.lines (toString ``Googology.Goals.primToExb) ++
  pairToExbGoals.lines (toString ``Googology.Goals.pairToExbGoals) ++
  bmsToSucc.lines (toString ``Googology.Goals.bmsToSucc) ++
  dbmsToPrim.lines (toString ``Googology.Goals.dbmsToPrim) ++
  dbmsToBms.lines (toString ``Googology.Goals.dbmsToBms) ++
  exbToTrioGoals.lines (toString ``Googology.Goals.exbToTrioGoals)

end Googology.Goals
