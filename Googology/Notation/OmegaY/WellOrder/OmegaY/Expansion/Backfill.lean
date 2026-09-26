/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Backfill.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Backfill.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Build

set_option backward.do.legacy false

/-!
# Correctness of the actual numerical backfill

The readiness predicate below states only local facts about the supplied
finite list: the phantom is terminal and every parent actually read exists
with positive value. It does not assume that backfill succeeds, that the
copied graph is canonical, or that expansion is well-founded.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem backfill_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem backfill_bind_error {α β : Type} (e : Error) (f : α → Result β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem backfill_pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem backfill_throw_eq {α : Type} (e : Error) :
    (throw e : Result α) = Except.error e := rfl

/-- Row and stored left endpoint, independent of numerical value. -/
def SameShape (a b : Cell) : Prop := a.row = b.row ∧ a.left = b.left

def PositiveReal (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, cell.row ≠ 0 → 0 < cell.value

/-- Exactly the references needed while moving down a fixed finite column.
No condition is imposed on the phantom's auxiliary incoming leg. -/
inductive BackfillReady (mountain : Mountain) : Cell → List Cell → Prop
  | nil (upper : Cell) : BackfillReady mountain upper []
  | phantom (upper lower : Cell) (hrow : lower.row = 0) :
      BackfillReady mountain upper [lower]
  | next {upper lower : Cell} {rest : List Cell} {ref : Ref} {parent : Cell}
      (hrow : lower.row ≠ 0)
      (hleft : upper.left = some ref)
      (hparent : lookup mountain ref = .ok parent)
      (hpositive : 0 < parent.value)
      (tail : BackfillReady mountain lower rest) :
      BackfillReady mountain upper (lower :: rest)

/-- The exact numerical parent-sum equations on the finished downward list. -/
inductive Backfilled (mountain : Mountain) : Cell → List Cell → Prop
  | nil (upper : Cell) : Backfilled mountain upper []
  | phantom (upper lower : Cell) (hrow : lower.row = 0) (hvalue : lower.value = 0) :
      Backfilled mountain upper [lower]
  | next {upper lower : Cell} {rest : List Cell} {ref : Ref} {parent : Cell}
      (hrow : lower.row ≠ 0)
      (hleft : upper.left = some ref)
      (hparent : lookup mountain ref = .ok parent)
      (hpositive : 0 < parent.value)
      (hvalue : lower.value = upper.value + parent.value)
      (tail : Backfilled mountain lower rest) :
      Backfilled mountain upper (lower :: rest)

/-- A positive seed value can replace an unfinished seed. All original rows
and left endpoints are preserved and every numerical equation is verified. -/
theorem BackfillReady.run {mountain : Mountain} {upper : Cell} {cells : List Cell}
    (ready : BackfillReady mountain upper cells) :
    ∀ seed : Cell, seed.left = upper.left → 0 < seed.value →
      ∃ result, backfill mountain seed cells = .ok result ∧
        List.Forall₂ SameShape cells result ∧ Backfilled mountain seed result ∧
        PositiveReal result := by
  induction ready with
  | nil upper =>
      intro seed _ _
      exact ⟨[], rfl, .nil, .nil seed, by simp [PositiveReal]⟩
  | phantom upper lower hrow =>
      intro seed _ _
      let output : Cell := ⟨lower.row, 0, lower.left⟩
      refine ⟨[output], ?_, .cons ⟨rfl, rfl⟩ .nil,
        .phantom seed output hrow rfl, ?_⟩
      · simp [backfill, hrow, output]
      · intro cell hmem hreal
        have he : cell = output := List.mem_singleton.mp hmem
        subst cell
        exact False.elim (hreal hrow)
  | @next upper lower rest ref parent hrow hleft hparent hpositive tail ih =>
      intro seed hseed hseedpositive
      let output : Cell := ⟨lower.row, seed.value + parent.value, lower.left⟩
      have houtputpositive : 0 < output.value := by dsimp [output]; omega
      obtain ⟨result, hrun, hshape, hfilled, hvalues⟩ :=
        ih output rfl houtputpositive
      have hseedleft : seed.left = some ref := hseed.trans hleft
      refine ⟨output :: result, ?_, .cons ⟨rfl, rfl⟩ hshape,
        .next hrow hseedleft hparent hpositive rfl hfilled, ?_⟩
      · have hnzero : parent.value ≠ 0 := by omega
        simpa [backfill, hrow, leftOf, hseedleft, hparent, hnzero, output] using
          congrArg (fun xs : List Cell => Except.ok (output :: xs)) rfl ▸
            (show (do let xs ← backfill mountain output rest
                      pure (output :: xs)) = .ok (output :: result) by simp [hrun])
      · intro cell hmem hreal
        rcases List.mem_cons.mp hmem with he | he
        · subst cell; exact houtputpositive
        · exact hvalues cell he hreal

theorem backfill_correct {mountain : Mountain} {upper : Cell} {cells : List Cell}
    (ready : BackfillReady mountain upper cells) (hpositive : 0 < upper.value) :
    ∃ result, backfill mountain upper cells = .ok result ∧
      List.Forall₂ SameShape cells result ∧ Backfilled mountain upper result ∧
      PositiveReal result := ready.run upper rfl hpositive

theorem Backfilled.exact_difference {mountain : Mountain} {upper lower : Cell}
    {rest : List Cell} (h : Backfilled mountain upper (lower :: rest))
    (hreal : lower.row ≠ 0) :
    ∃ ref parent, upper.left = some ref ∧ lookup mountain ref = .ok parent ∧
      0 < parent.value ∧ lower.value - parent.value = upper.value := by
  cases h with
  | phantom _ _ hrow _ => exact False.elim (hreal hrow)
  | next _ hleft hparent hpositive hvalue _ =>
      exact ⟨_, _, hleft, hparent, hpositive, by omega⟩

theorem shapes_rows {source output : List Cell}
    (h : List.Forall₂ SameShape source output) :
    source.map Cell.row = output.map Cell.row := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, h.1, ih]

theorem shapes_lefts {source output : List Cell}
    (h : List.Forall₂ SameShape source output) :
    source.map Cell.left = output.map Cell.left := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, h.2, ih]

/-- Every successful execution satisfies the specification, even without a
readiness certificate.  Positivity follows from the actual runtime guards. -/
theorem backfill_success_spec {mountain : Mountain} {upper : Cell}
    {cells result : List Cell} (hpositive : 0 < upper.value)
    (hsuccess : backfill mountain upper cells = .ok result) :
    List.Forall₂ SameShape cells result ∧ Backfilled mountain upper result ∧
      PositiveReal result := by
  induction cells generalizing upper result with
  | nil =>
      have he : result = [] := by simpa [backfill] using hsuccess.symm
      subst result
      exact ⟨.nil, .nil _, by simp [PositiveReal]⟩
  | cons lower rest ih =>
      by_cases hrow : lower.row = 0
      · cases rest with
        | nil =>
          have he : result = [⟨lower.row, 0, lower.left⟩] := by
            simpa [backfill, hrow] using hsuccess.symm
          subst result
          refine ⟨.cons ⟨rfl, rfl⟩ .nil, .phantom _ _ hrow rfl, ?_⟩
          intro cell hc hr
          have he := List.mem_singleton.mp hc
          subst cell
          exact False.elim (hr hrow)
        | cons next tail => simp [backfill, hrow] at hsuccess
      · cases hl : upper.left with
        | none => simp [backfill, hrow, leftOf, hl] at hsuccess
        | some ref =>
          cases hp : lookup mountain ref with
          | error e => simp [backfill, hrow, leftOf, hl, hp] at hsuccess
          | ok parent =>
            by_cases hz : parent.value = 0
            · simp [backfill, hrow, leftOf, hl, hp, hz] at hsuccess
            · let next : Cell := ⟨lower.row, upper.value + parent.value, lower.left⟩
              cases ht : backfill mountain next rest with
              | error e =>
                  dsimp only [next] at ht
                  simp [backfill, hrow, leftOf, hl, hp, hz, ht] at hsuccess
              | ok output =>
                  dsimp only [next] at ht
                  have he : result = next :: output := by
                    simpa [backfill, hrow, leftOf, hl, hp, hz, ht, next] using hsuccess.symm
                  subst result
                  have hnext : 0 < next.value := by dsimp [next]; omega
                  obtain ⟨hs, hf, hv⟩ := ih hnext ht
                  refine ⟨.cons ⟨rfl, rfl⟩ hs,
                    .next hrow hl hp (Nat.pos_of_ne_zero hz) rfl hf, ?_⟩
                  intro cell hc hr
                  rcases List.mem_cons.mp hc with he | he
                  · subst cell; exact hnext
                  · exact hv cell he hr

end OmegaY.Expansion

#print axioms OmegaY.Expansion.backfill_correct
#print axioms OmegaY.Expansion.Backfilled.exact_difference
#print axioms OmegaY.Expansion.backfill_success_spec
