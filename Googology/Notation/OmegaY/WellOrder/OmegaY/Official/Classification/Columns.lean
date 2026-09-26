/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Columns.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Assemble

set_option backward.do.legacy false

/-!
# Every copied column comes from one `copyColumn`

In the splice branch of `Official.expandDiagram`, every column `X ≥ x₀` of the result
`R` was produced by `copyColumn` for one source column `x` of one block `i`, with
`X = x + w·i`, and the result read by that call is the prefix `R.extract 0 X`
(`expandDiagram_splice`).
-/

namespace OmegaY.Official.Classification

open Canonical Official

theorem forIn_except_inv_mem {α β ε : Type} (P : β → Prop) (xs : List α)
    (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a ∈ xs, ∀ b s, P b → f a b = .ok s →
      P (match s with | .done b => b | .yield b => b)) :
    ∀ (b r : β), P b → forIn xs b f = .ok r → P r := by
  induction xs with
  | nil =>
      intro b r hb h
      simp only [List.forIn_nil] at h
      cases h
      exact hb
  | cons a as ih =>
      intro b r hb h
      simp only [List.forIn_cons] at h
      cases hfa : f a b with
      | error e => simp [hfa] at h; cases h
      | ok s =>
          have hs := hf a (by simp) b s hb hfa
          rw [hfa] at h
          cases s with
          | done b' => simp only [bind, Except.bind] at h; cases h; exact hs
          | yield b' =>
              simp only [bind, Except.bind] at h
              exact ih (fun a' ha' => hf a' (by simp [ha'])) b' r hs h

/-- The context of the call that produced column `X` of the result. -/
def ctxAt (M R : Mountain) (x i cr w x0 X : Nat) : Context :=
  ⟨M, R.extract 0 X, x, i, cr, w, x0⟩

/-- The invariant of the copying loops. -/
def ColumnsInv (M : Mountain) (copies cr w x0 : Nat) (τ : Row) (R : Mountain) : Prop :=
  AgreeBelow M R x0 ∧ x0 ≤ R.size ∧ ∀ X (hX : X < R.size), x0 ≤ X →
    ∃ i x, i < copies + 1 ∧ x ∈ blockColumns cr x0 copies i ∧ X = x + w * i ∧
      copyColumn (ctxAt M R x i cr w x0 X) τ = .ok R[X]

theorem ColumnsInv.push {M : Mountain} {copies cr w x0 : Nat} {τ : Row} {R : Mountain}
    (hI : ColumnsInv M copies cr w x0 τ R) {i x : Nat} (hi : i < copies + 1)
    (hx : x ∈ blockColumns cr x0 copies i) (hsize : R.size = x + w * i) {col : Column}
    (hcol : copyColumn ⟨M, R, x, i, cr, w, x0⟩ τ = .ok col) :
    ColumnsInv M copies cr w x0 τ (R.push col) := by
  obtain ⟨hA, hle, hall⟩ := hI
  refine ⟨hA.push hle col, by simp only [Array.size_push]; omega, ?_⟩
  intro X hX hX0
  simp only [Array.size_push] at hX
  by_cases hlt : X < R.size
  · obtain ⟨i', x', hi', hx', hX', hc⟩ := hall X hlt hX0
    refine ⟨i', x', hi', hx', hX', ?_⟩
    have hext : (R.push col).extract 0 X = R.extract 0 X := by
      apply Array.ext
      · simp; omega
      · intro j h1 h2
        simp only [Array.getElem_extract]
        rw [Array.getElem_push_lt (by simp at h1; omega)]
    have hget : (R.push col)[X]'(by simp; omega) = R[X] := Array.getElem_push_lt hlt
    simp only [ctxAt, hext, hget]
    exact hc
  · have hXe : X = R.size := by omega
    subst hXe
    refine ⟨i, x, hi, hx, hsize, ?_⟩
    have hext : (R.push col).extract 0 R.size = R := by
      apply Array.ext
      · simp
      · intro j h1 h2
        simp only [Array.getElem_extract]
        rw [Array.getElem_push_lt (by simp at h1; omega)]
        simp
    have hget : (R.push col)[R.size]'(by simp) = col := Array.getElem_push_eq
    simp only [ctxAt, hext, hget]
    exact hcol

/-- The splice branch of `expandDiagram`, with the origin of every copied column. -/
theorem expandDiagram_splice {values : List Nat} {copies : Nat} {R M : Mountain}
    (h : Official.expandDiagram values copies = .ok R) (hM : build values = .ok M)
    {col : Column} {t : Cell} (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t)
    (hne : ¬ (official t.row = 0 ∨ copies = 0)) {root : Ref} (hl : t.left = some root) :
    root.column < M.size - 1 ∧
      ColumnsInv M copies root.column (M.size - 1 - root.column) (M.size - 1)
        (official t.row) R := by
  unfold Official.expandDiagram at h
  simp only [hM, Official.liftE, Except.mapError, bind, Except.bind, pure, Except.pure] at h
  have hvne : ¬ values.isEmpty = true := by
    intro he
    have : values = [] := List.isEmpty_iff.mp he
    subst this
    have h' : build [] = .ok #[] := rfl
    rw [h'] at hM
    cases hM
    simp at hcol
  rw [if_neg hvne] at h
  have hc : Expansion.columnAt M (M.size - 1) = .ok col := by
    simp [Expansion.columnAt, hcol]
  have htop : Expansion.top col = .ok t := by
    simp [Expansion.top, ht]
  have hleft : Expansion.leftOf t = .ok root := by
    simp [Expansion.leftOf, hl]
  simp only [hc, htop, hleft] at h
  rw [if_neg hne] at h
  by_cases hcr : root.column < M.size - 1
  · rw [if_neg (not_not.mpr hcr)] at h
    refine ⟨hcr, ?_⟩
    split at h
    · cases h
    · rename_i v hv
      cases h
      refine forIn_except_inv_mem
        (P := ColumnsInv M copies root.column (M.size - 1 - root.column) (M.size - 1)
          (official t.row)) _ _ ?_ _ _ ?_ hv
      · intro i hi s st hP hst
        split at hst
        · cases hst
        · rename_i v' hv'
          cases hst
          refine forIn_except_inv_mem
            (P := ColumnsInv M copies root.column (M.size - 1 - root.column) (M.size - 1)
              (official t.row)) _ _ ?_ _ _ hP hv'
          intro x hx s2 st2 hP2 hst2
          split at hst2
          · simp [throw, throwThe, MonadExceptOf.throw] at hst2
          · rename_i hsize
            split at hst2
            · cases hst2
            · rename_i c hcopy
              cases hst2
              exact hP2.push (List.mem_range.mp hi) hx (by omega) hcopy
      · refine ⟨fun c hc' => by simp [hc'], by simp, ?_⟩
        intro X hX hX0
        simp at hX
        omega
  · rw [if_pos hcr] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

end OmegaY.Official.Classification
