import Googology.Notation.ExBuchholz.Closure
import Googology.Notation.ExBuchholz.Mono

/-!
# The expansion system on the countable standard forms

`exb` in `FS.lean` reads the fundamental sequence as an expansion system on
every term.  Well-foundedness is a statement about the countable standard
forms, so this file restricts the state to them.

What the restriction needs is that one step keeps a term standard and below
`Ω` — Buchholz's Lemma 3.3 for the extended system — and `Closure.lean`
derives that from the Bachmann property.  So everything here is stated with
`Bachmann` as a hypothesis.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- Numerals are standard forms. -/
theorem OT_numeral (n : Nat) : OT (numeral n) := OT_repeatPrin (by decide) n

/-- So is every index the expansion system uses. -/
theorem OT_idx (X : Term) (n : Nat) : OT (idx X n) := by
  rw [idx]
  split
  · exact rfl
  · exact OT_numeral n

/-- One step keeps a countable standard form standard and countable. -/
theorem step_ok (HB : Bachmann) {X : Term} (hOT : OT X) (hlt : X < tW) (n : Nat) :
    OT (fs X (idx X n)) ∧ fs X (idx X n) < tW := by
  by_cases h : X = nil
  · subst h
    rw [show fs nil (idx nil n) = nil from by rw [fs]]
    exact ⟨rfl, nil_lt_cons _ _ _⟩
  · exact ⟨OTFS_of_Bachmann HB X _ hOT (idx_lt_dom hOT hlt h n) (OT_idx X n),
      lt_trans (step_lt hOT hlt h n) hlt⟩

/-- Extended Buchholz terms as an expansion system on the countable standard
forms: one step is the fundamental sequence at the numeral `n`. -/
def exbOT (HB : Bachmann) : Rewrite where
  State := {X : Term // OT X ∧ X < tW}
  step := fun A n => ⟨fs A.1 (idx A.1 n), step_ok HB A.2.1 A.2.2 n⟩
  halted := fun A => A.1 = nil

theorem exbOT_Rel_lt (HB : Bachmann) {A B : (exbOT HB).State}
    (h : (exbOT HB).Rel B A) : OTLt B.1 A.1 := by
  obtain ⟨hne, n, hn⟩ := h
  refine ⟨B.2.1, A.2.1, ?_⟩
  rw [show B.1 = fs A.1 (idx A.1 n) from congrArg Subtype.val hn]
  exact step_lt A.2.1 A.2.2 hne n

/-- **One expansion step is well founded on the countable standard forms.** -/
theorem exbOT_wf (HB : Bachmann) : (exbOT HB).WF :=
  Subrelation.wf (fun {_ _} h => exbOT_Rel_lt HB h) (InvImage.wf _ OTLt_wf)

/-- **Extended Buchholz terms terminate.**  Supplied by
`Rewrite.terminates_of_wf`. -/
theorem exbOT_terminates (HB : Bachmann) : (exbOT HB).Terminates :=
  (exbOT HB).terminates_of_wf (exbOT_wf HB)

end Googology.Notation.ExBuchholz.Term
