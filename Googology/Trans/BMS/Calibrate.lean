import Googology.Trans.BMS.Commute

/-!
# What the one-row reading reaches

`BMS/ExBuchholz.lean` says the reading uses no subscript but `0`, and that
what it produces is below `ψ_0(Ω)`.  This file says those two are the same
condition, and that the reading reaches everything below `ψ_0(Ω)`.

`lt_e0_iff_allNil`: a standard form is below `ψ_0(Ω)` exactly when all its
subscripts are `0`.  One direction is arithmetic on the term order; the other
needs the standard-form condition, and this is where it earns its keep.  A
term like `ψ_0(ψ_0(ψ_1(1)))` is below `ψ_0(Ω)` and uses the subscript `1`, but
it is not a standard form: `G_0` of its argument holds `ψ_1(1)`, which is not
below that argument.  The proof turns that into an induction — if the argument
reached `ψ_0(Ω)` it would hold `Ω` or more, and `G_0` puts that below the
argument, which is itself below `Ω`.

`exists_read`: every standard form below `ψ_0(Ω)` is `read 0 l` for a matrix
`l`.  Together with `unread_read` the reading is a bijection between one-row
matrices and the terms below `ψ_0(Ω)`, and `read_expandL` carries expansion to
`[ ]`.  So one row is settled both ways: nothing below `ψ_0(Ω)` is missed, and
nothing above it is named.
-/

namespace Googology.Trans.BMS
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem eq_nil_of_lt_t1 {a : Term} (h : a < t1) : a = nil := by
  cases a with
  | nil => rfl
  | cons c d u =>
    exfalso
    rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp h) with h2 | h2
    · exact not_lt_nil c h2
    · exact not_lt_nil d h2.2

theorem OT_head {a b t : Term} (h : OT (cons a b t)) : OT (psi a b) := by
  simp only [OT, isOT, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, trivial⟩, rfl⟩

theorem mem_G_head (d u : Term) : d ∈ G nil (cons nil d u) := by
  rw [G, if_pos (nil_le nil)]
  exact List.mem_append_left _ List.mem_cons_self

/-- **A standard form below `ψ_0(Ω)` uses no subscript but `0`.** -/
theorem allNil_of_OT_lt_e0 : ∀ X : Term, OT X → X < te0 → AllNil X := by
  intro X
  induction hn : size X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    cases X with
    | nil => intro _ _; exact trivial
    | cons a b t =>
      intro hOT hlt
      have hpsi : psi a b < psi nil tW := cons_lt_psi_iff.mp hlt
      obtain ⟨ha, hbtW⟩ : a = nil ∧ b < tW := by
        rcases psi_lt_psi_iff.mp hpsi with h | h
        · exact absurd h (not_lt_nil a)
        · exact h
      subst ha
      have hbe0 : b < te0 := by
        rcases lt_trichotomy b te0 with h | h | h
        · exact h
        · exfalso
          have hmem : tW ∈ G nil b := by rw [h]; exact mem_G_head tW nil
          exact absurd (lt_trans (OT_G_lt (OT_head hOT) tW hmem) hbtW) (lt_irrefl tW)
        · exfalso
          cases b with
          | nil => exact not_lt_nil te0 h
          | cons c d u =>
            have hc : c = nil := by
              rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hbtW) with h2 | h2
              · exact eq_nil_of_lt_t1 h2
              · exact absurd h2.2 (not_lt_nil d)
            subst hc
            have hdW : tW ≤ d := by
              rcases cons_lt_cons_iff.mp h with h1 | ⟨h1, _⟩
              · rcases psi_lt_psi_iff.mp h1 with h2 | h2
                · exact absurd h2 (not_lt_nil nil)
                · exact le_of_lt h2.2
              · injection h1 with _ h2 _
                exact le_iff_lt_or_eq.mpr (Or.inr h2)
            have hdb : d < cons nil d u := OT_G_lt (OT_head hOT) d (mem_G_head d u)
            exact absurd (lt_of_le_of_lt' hdW (lt_trans hdb hbtW)) (lt_irrefl tW)
      refine ⟨rfl, ?_, ?_⟩
      · exact ih (size b) (by subst hn; simp only [size_cons]; omega) b rfl (OT_snd hOT) hbe0
      · exact ih (size t) (by subst hn; simp only [size_cons]; omega) t rfl (OT_tail hOT)
          (lt_trans (tail_lt t nil b hOT) hlt)

theorem allNil_lt_tW : ∀ X : Term, AllNil X → X < tW := by
  intro X
  cases X with
  | nil => intro _; exact nil_lt_cons _ _ _
  | cons a b t =>
    intro h
    obtain ⟨ha, _, _⟩ := h
    subst ha
    exact cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _)))

/-- **A term with no subscript but `0` is below `ψ_0(Ω)`.** -/
theorem allNil_lt_e0 : ∀ X : Term, AllNil X → X < te0 := by
  intro X
  cases X with
  | nil => intro _; exact nil_lt_cons _ _ _
  | cons a b t =>
    intro h
    obtain ⟨ha, hb, _⟩ := h
    subst ha
    exact cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, allNil_lt_tW b hb⟩))

/-- **Below `ψ_0(Ω)` is exactly where the subscripts are all `0`.** -/
theorem lt_e0_iff_allNil {X : Term} (h : OT X) : X < te0 ↔ AllNil X :=
  ⟨allNil_of_OT_lt_e0 X h, allNil_lt_e0 X⟩

/-- Writing a term back gives a matrix. -/
theorem col_unread : ∀ (X : Term), AllNil X → ∀ b : Nat, Col b (unread b X) := by
  intro X
  induction X with
  | nil => intro _ b; rw [unread_nil]; exact trivial
  | cons a P Q _ ihP ihQ =>
    intro h b
    obtain ⟨ha, hP, hQ⟩ := h
    subst ha
    rw [unread_cons]
    refine ⟨rfl, chain_append _ b b
      (chain_of_col (ihP hP (b + 1)) (by omega) (by omega)) (Nat.le_refl b) _ (ihQ hQ b)⟩

/-- **Every standard form below `ψ_0(Ω)` is read off a one-row matrix.**  With
`read_expandL` and `unread_read` this pins the one-row translation down: the
reading is a bijection between one-row matrices and the terms below `ψ_0(Ω)`,
and it carries expansion to `[ ]`. -/
theorem exists_read {X : Term} (h : OT X) (hlt : X < te0) :
    ∃ l : List Nat, Col 0 l ∧ read 0 l = X := by
  have hA := allNil_of_OT_lt_e0 X h hlt
  exact ⟨unread 0 X, col_unread X hA 0, read_unread X hA 0⟩


end Googology.Trans.BMS
