import Googology.Notation.SSOSS.CutShape
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Ordinal translation map below (0,0,2)

The standard 0/1 sequences (`Standard`) with the one-step expansion relation `Rel`
form an ordinal notation whose value map `o` is
* decreasing along `Rel`,
* cofinal (every `β < o a` is bounded by some one-step expansion of `a`),
* equal to the well-founded rank of `Rel` on standard sequences.
-/

namespace Googology.Notation.SSOSS
namespace Below002

/-- One-step expansion: `Rel b a` means `b` is obtained from `a` in one step.
A final `0` is erased; a positive final entry is expanded by `Seq.fs a k`, `k ≥ 1`. -/
def Rel (b a : List ℕ) : Prop :=
  (a ≠ [] ∧ Seq.entry a a.length = 0 ∧ b = a.dropLast) ∨
  (0 < Seq.entry a a.length ∧ ∃ k, 1 ≤ k ∧ b = Seq.fs a k)

/-- The standard sequences. -/
def Std : Type := {S : List ℕ // Standard S}

/-- `Rel` restricted to standard sequences. -/
def StdRel (b a : Std) : Prop := Rel b.1 a.1

theorem eq_dropLast_append {a : List ℕ} (h : a ≠ []) :
    a = a.dropLast ++ [Seq.entry a a.length] := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  congr 2
  rw [List.getLast_eq_getElem]
  simp [Seq.entry, List.getElem?_eq_getElem (show a.length - 1 < a.length by
    have := List.length_pos_of_ne_nil h; omega)]

/-- 1. Closure: one-step expansions of standard sequences are standard. -/
theorem closure {a b : List ℕ} (ha : Standard a) (h : Rel b a) : Standard b := by
  rcases h with ⟨hne, h0, rfl⟩ | ⟨hpos, k, hk, rfl⟩
  · have e := eq_dropLast_append hne
    rw [h0] at e
    rw [e] at ha
    exact Standard.erase ha
  · exact Standard.expand ha hpos k hk

/-- 2. Decreasing. -/
theorem decreasing {a b : List ℕ} (ha : Standard a) (h : Rel b a) : o b < o a := by
  rcases h with ⟨hne, h0, rfl⟩ | ⟨hpos, k, hk, rfl⟩
  · have e := eq_dropLast_append hne
    rw [h0] at e
    conv_rhs => rw [e, o_append_zero]
    exact Order.lt_succ _
  · exact o_fs_lt_of_standard ha hpos k hk

/-- 3. Cofinal. -/
theorem cofinal {a : List ℕ} (ha : Standard a) :
    ∀ β < o a, ∃ b, Rel b a ∧ β ≤ o b := by
  intro β hβ
  by_cases hpos : 0 < Seq.entry a a.length
  · rw [o_fs_sup_of_standard ha hpos] at hβ
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have : (⨆ n : ℕ, o (Seq.fs a (n + 1))) ≤ β :=
      Ordinal.iSup_le fun n => (hcon _ (Or.inr ⟨hpos, n + 1, by omega, rfl⟩)).le
    exact absurd hβ (not_lt.2 this)
  · have h0 : Seq.entry a a.length = 0 := by omega
    have hne : a ≠ [] := by
      rintro rfl
      simp [o] at hβ
    refine ⟨a.dropLast, Or.inl ⟨hne, h0, rfl⟩, ?_⟩
    have e := eq_dropLast_append hne
    rw [h0] at e
    rw [e, o_append_zero] at hβ
    exact Order.lt_succ_iff.1 hβ

/-- 4. Well-foundedness of `Rel` on standard sequences. -/
theorem wf : WellFounded StdRel :=
  (InvImage.wf (fun S : Std => o S.1) Ordinal.lt_wf).mono
    fun _ a h => decreasing a.2 h

instance : IsWellFounded Std StdRel := ⟨wf⟩

/-- The rank of `Rel` on standard sequences:
`rank a = ⨆ (b standard, Rel b a), rank b + 1`. -/
noncomputable def rank (a : Std) : Ordinal.{0} := IsWellFounded.rank StdRel a

theorem rank_eq_sup (a : Std) :
    rank a = ⨆ b : {b : Std // StdRel b a}, Order.succ (rank b) :=
  IsWellFounded.rank_eq StdRel a

/-- 5. Rank: the value map equals the rank. -/
theorem rank_eq (a : Std) : o a.1 = rank a := by
  induction a using wf.induction with
  | _ a ih =>
    rw [rank_eq_sup]
    apply le_antisymm
    · refine le_of_forall_lt fun β hβ => ?_
      obtain ⟨b, hb, hle⟩ := cofinal a.2 β hβ
      let b' : Std := ⟨b, closure a.2 hb⟩
      have hb' : StdRel b' a := hb
      calc β ≤ o b := hle
        _ < Order.succ (rank b') := by
          rw [← ih b' hb']; exact Order.lt_succ _
        _ ≤ _ := Ordinal.le_iSup (fun x : {b : Std // StdRel b a} => Order.succ (rank x.1))
              ⟨b', hb'⟩
    · refine Ordinal.iSup_le fun ⟨b, hb⟩ => ?_
      rw [← ih b hb]
      exact Order.succ_le_of_lt (decreasing a.2 hb)

end Below002
end Googology.Notation.SSOSS
