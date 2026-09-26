/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Finish.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Finish.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Backfill
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopTotality

set_option backward.do.legacy false

/-! Numerical correctness of the actual column-finishing stages. Geometry
must still establish that their row validation and parent readiness hold. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem finish_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem finish_bind_error {α β : Type} (e : Error) (f : α → Result β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem finish_pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem finish_throw_eq {α : Type} (e : Error) :
    (throw e : Result α) = Except.error e := rfl

def FinishedColumn (mountain : Mountain) (column : Column) : Prop :=
  ∃ upper rest, column.toList.reverse = upper :: rest ∧ upper.value = 1 ∧
    Backfilled mountain upper rest ∧ PositiveReal (upper :: rest)

def ColumnShape (cells : List Cell) (column : Column) : Prop :=
  cells.map Cell.row = column.toList.map Cell.row ∧
    cells.map Cell.left = column.toList.map Cell.left

private theorem shape_reverse {sorted : List Cell} {upper seed : Cell}
    {rest output : List Cell} (hrev : sorted.reverse = upper :: rest)
    (hseed : SameShape upper seed) (hshape : List.Forall₂ SameShape rest output) :
    ColumnShape sorted (seed :: output).reverse.toArray := by
  have hsh : List.Forall₂ SameShape (upper :: rest) (seed :: output) := .cons hseed hshape
  constructor
  · have he := congrArg List.reverse (shapes_rows hsh)
    rw [← hrev] at he
    simpa only [List.toList_toArray, List.map_reverse, List.reverse_reverse] using he
  · have he := congrArg List.reverse (shapes_lefts hsh)
    rw [← hrev] at he
    simpa only [List.toList_toArray, List.map_reverse, List.reverse_reverse] using he

private theorem finished_reverse {mountain : Mountain} {seed : Cell} {output : List Cell}
    (hseed : seed.value = 1) (hfilled : Backfilled mountain seed output)
    (hpositive : PositiveReal output) :
    FinishedColumn mountain (seed :: output).reverse.toArray := by
  refine ⟨seed, output, by simp, hseed, hfilled, ?_⟩
  intro cell hmem hreal
  rcases List.mem_cons.mp hmem with he | he
  · subst cell; simp [hseed]
  · exact hpositive cell he hreal

/-- Totality of the numerical stage from actual readable positive parents,
with preservation of every row and stored left endpoint. -/
theorem finishSorted_correct {mountain : Mountain} {sorted : List Cell}
    {upper : Cell} {rest : List Cell} (hrev : sorted.reverse = upper :: rest)
    (hreal : upper.row ≠ 0) (hready : BackfillReady mountain upper rest) :
    ∃ column, finishSorted mountain sorted = .ok column ∧
      ColumnShape sorted column ∧ FinishedColumn mountain column := by
  let seed : Cell := ⟨upper.row, 1, upper.left⟩
  obtain ⟨output, hrun, hshape, hfilled, hpositive⟩ := hready.run seed rfl (by change 0 < (1 : Nat); omega)
  refine ⟨(seed :: output).reverse.toArray, ?_, shape_reverse hrev ⟨rfl, rfl⟩ hshape,
    finished_reverse rfl hfilled hpositive⟩
  have hr : backfill mountain ⟨upper.row, 1, upper.left⟩ rest = .ok output := hrun
  simp [finishSorted, hrev, hreal, hr, seed]

/-- Unconditional soundness of every successful numerical-stage execution. -/
theorem finishSorted_success_spec {mountain : Mountain} {sorted : List Cell}
    {column : Column} (h : finishSorted mountain sorted = .ok column) :
    ColumnShape sorted column ∧ FinishedColumn mountain column := by
  cases hrev : sorted.reverse with
  | nil => simp [finishSorted, hrev] at h
  | cons upper rest =>
    by_cases hz : upper.row = 0
    · simp [finishSorted, hrev, hz] at h
    · let seed : Cell := ⟨upper.row, 1, upper.left⟩
      cases hr : backfill mountain seed rest with
      | error e =>
        dsimp only [seed] at hr
        simp [finishSorted, hrev, hz, hr] at h
      | ok output =>
        have hr' : backfill mountain ⟨upper.row, 1, upper.left⟩ rest = .ok output := hr
        have he : column = (seed :: output).reverse.toArray := by
          simpa [finishSorted, hrev, hz, hr', seed] using h.symm
        subst column
        obtain ⟨hshape, hfilled, hpositive⟩ := backfill_success_spec
          (show 0 < seed.value by change 0 < (1 : Nat); omega) hr
        exact ⟨shape_reverse hrev ⟨rfl, rfl⟩ hshape,
          finished_reverse rfl hfilled hpositive⟩

/-- The full sorting/checking/finishing function cannot return a column with
incorrect backfill equations, altered sorted geometry, or nonpositive real
values. This makes no claim that every supplied list passes its checks. -/
theorem finish_success_spec {mountain : Mountain} {cells : List Cell} {column : Column}
    (h : finish mountain cells = .ok column) :
    ColumnShape (cells.mergeSort (fun a b => decide (a.row ≤ b.row))) column ∧
      FinishedColumn mountain column := by
  cases hv : validateColumnRows (cells.mergeSort (fun a b => decide (a.row ≤ b.row))) with
  | error e => simp [finish, hv] at h
  | ok resultUnit =>
    cases resultUnit
    exact finishSorted_success_spec (by simpa [finish, hv] using h)

/-- The real validation loop succeeds once a first phantom and distinct
adjacent row labels are supplied by geometry. -/
theorem validateColumnRows_correct {first : Cell} {rest : List Cell}
    (hfirst : first.row = 0)
    (hdistinct : ∀ pair ∈ (first :: rest).zip (first :: rest).tail,
      pair.1.row ≠ pair.2.row) :
    validateColumnRows (first :: rest) = .ok () := by
  have hs : Succeeds (validateColumnRows (first :: rest)) := by
    unfold validateColumnRows
    simp only [hfirst, ne_eq, not_true_eq_false, ↓reduceIte]
    apply succeeds_bind
    · apply succeeds_forIn
      intro pair hp state
      have hn := hdistinct pair hp
      simp only [hn, ↓reduceIte]
      exact succeeds_pure _
    · intro result
      exact succeeds_pure _
  obtain ⟨result, hresult⟩ := hs
  cases result
  exact hresult

/-- Pure local input conditions sufficient for the complete actual finisher.
The list is sorted by the program itself; geometry must supply the phantom,
non-overlap, a real top, and the actual readable parents. -/
def FinishReady (mountain : Mountain) (cells : List Cell) : Prop :=
  let sorted := cells.mergeSort (fun a b => decide (a.row ≤ b.row))
  ∃ first tail upper rest,
    sorted = first :: tail ∧ sorted.reverse = upper :: rest ∧
    first.row = 0 ∧ upper.row ≠ 0 ∧
    (∀ pair ∈ sorted.zip sorted.tail, pair.1.row ≠ pair.2.row) ∧
    BackfillReady mountain upper rest

theorem finish_correct {mountain : Mountain} {cells : List Cell}
    (ready : FinishReady mountain cells) :
    ∃ column, finish mountain cells = .ok column ∧
      ColumnShape (cells.mergeSort (fun a b => decide (a.row ≤ b.row))) column ∧
      FinishedColumn mountain column := by
  obtain ⟨first, tail, upper, rest, hsorted, hreverse, hfirst, hreal, hdistinct, hparents⟩ := ready
  have hv : validateColumnRows
      (cells.mergeSort (fun a b => decide (a.row ≤ b.row))) = .ok () := by
    rw [hsorted]
    exact validateColumnRows_correct hfirst (by simpa only [hsorted] using hdistinct)
  obtain ⟨column, hc, hshape, hfinished⟩ := finishSorted_correct hreverse hreal hparents
  exact ⟨column, by simpa [finish, hv] using hc, hshape, hfinished⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.finishSorted_correct
#print axioms OmegaY.Expansion.finish_success_spec
#print axioms OmegaY.Expansion.validateColumnRows_correct
#print axioms OmegaY.Expansion.finish_correct
