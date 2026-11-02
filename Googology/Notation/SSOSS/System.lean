import Googology.Rank
import Googology.Notation.SSOSS.MainBelow002

/-!
# SSOSS below (0,0,2) as an expansion system

`ssossSys` is the expansion of Kanrokoti's 強2階探索表記 (rev 76153) on lists of
naturals: `step a k = Seq.fs a (k + 1)` is the sequence part of `a[k]`, which
uses `f(k) = k + 1` copies of the bad part, and the empty list halts.  A final
`0` is dropped, whatever the bracket.

`ssossStd` takes as standard forms the source's `Standard`: the generators
`(0,0,1,…,1)` closed under expansion.  `standard_iff_reach` says it is the least
set that holds the generators and is closed under `step`, the standard forms of
chapter 1 of `spec.md`.  These are the sequences below `(0,0,2)`.

The theorems at the end put `Below002.decreasing`, `Below002.cofinal`,
`Below002.wf` and `Below002.rank_eq` into the form of the library.
-/

namespace Googology.Notation.SSOSS

open Ordinal

/-- The expansion system: lists of naturals, `step a k = Seq.fs a (k + 1)`,
and the empty list halts. -/
def ssossSys : Rewrite where
  State := List ℕ
  step := fun a k => Seq.fs a (k + 1)
  halted := fun a => a = []

/-- The generators `(0,0)` followed by `n` ones. -/
def gen (n : ℕ) : List ℕ := [0, 0] ++ List.replicate n 1

-- Expansions from the rev 76153 handover, computed by the compiled code:
-- `ssossSys.step a k = Seq.fs a (k + 1)`.
#guard Seq.fs [0,0,1] 2 = [0,0,0,0]
#guard Seq.fs [0,0,1,0,1] 2 = [0,0,1,0,0,1,0,0]
#guard Seq.fs [0,0,1,1,0,1] 2 = [0,0,1,1,0,0,1,1,0,0]
#guard Seq.fs [0,0,1,1,1] 3 = [0,0,1,1,0,1,1,0,1,1,0]
#guard Seq.fs [0,0,2] 2 = [0,0,1,1]
#guard Seq.fs [0,0,1,0] 4 = [0,0,1]

theorem fs_nil (k : ℕ) : Seq.fs [] k = [] := by simp [Seq.fs]

theorem fs_of_entry_zero {a : List ℕ} (hne : a ≠ []) (h0 : Seq.entry a a.length = 0)
    (k : ℕ) : Seq.fs a k = a.dropLast := by
  have : a.isEmpty = false := by cases a <;> simp_all
  simp [Seq.fs, this, h0]

theorem entry_append_zero (S : List ℕ) : Seq.entry (S ++ [0]) (S ++ [0]).length = 0 := by
  simp [Seq.entry]

theorem fs_append_zero (S : List ℕ) (k : ℕ) : Seq.fs (S ++ [0]) k = S := by
  rw [fs_of_entry_zero (by simp) (entry_append_zero S)]
  simp

/-- One step of `ssossSys` is the source's one-step relation `Below002.Rel`. -/
theorem rel_iff (a b : List ℕ) : ssossSys.Rel b a ↔ Below002.Rel b a := by
  constructor
  · rintro ⟨hne, k, rfl⟩
    by_cases h0 : Seq.entry a a.length = 0
    · exact Or.inl ⟨hne, h0, fs_of_entry_zero hne h0 _⟩
    · exact Or.inr ⟨Nat.pos_of_ne_zero h0, k + 1, by omega, rfl⟩
  · rintro (⟨hne, h0, rfl⟩ | ⟨hpos, k, hk, rfl⟩)
    · exact ⟨hne, 0, (fs_of_entry_zero hne h0 1).symm⟩
    · have hne : a ≠ [] := by
        rintro rfl
        simp [Seq.entry] at hpos
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact ⟨hne, j, rfl⟩

theorem rel_eq : ssossSys.Rel = Below002.Rel :=
  funext fun b => funext fun a => propext (rel_iff a b)

/-- The standard forms: the source's `Standard`, with the generators `gen`. -/
def ssossStd : ssossSys.Std where
  Standard := Standard
  gen := gen
  gen_std := Standard.tower
  step_std := fun s k hs => by
    by_cases he : s = []
    · subst he
      show Standard (Seq.fs [] (k + 1))
      rw [fs_nil]
      exact standard_nil
    · exact Below002.closure hs ((rel_iff s _).1 ⟨he, k, rfl⟩)

/-- `Standard` is the least set that holds the generators and is closed under
`step`. -/
theorem standard_iff_reach (a : List ℕ) :
    Standard a ↔ ∀ P : List ℕ → Prop, (∀ n, P (gen n)) →
      (∀ s k, P s → P (ssossSys.step s k)) → P a := by
  constructor
  · intro ha P hg hs
    induction ha with
    | tower n => exact hg n
    | expand _ _ k hk ih =>
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact hs _ j ih
    | @erase S _ ih =>
      have := hs _ 0 ih
      simpa [ssossSys, fs_append_zero] using this
  · intro h
    exact h Standard ssossStd.gen_std ssossStd.step_std

/-- Well-foundedness on the standard forms. -/
theorem ssossStd_wf : ssossStd.WF := by
  show WellFounded (fun b a : {s // Standard s} => ssossSys.Rel b.1 a.1)
  rw [rel_eq]
  exact Below002.wf

/-- One step makes `o` strictly smaller. -/
theorem ssoss_decreasing (a b : List ℕ) (ha : Standard a) (h : ssossSys.Rel b a) :
    o b < o a :=
  Below002.decreasing ha ((rel_iff a b).1 h)

/-- Every ordinal below `o a` is at most `o b` for a one-step expansion `b`. -/
theorem ssoss_cofinal (a : List ℕ) (ha : Standard a) :
    ∀ β < o a, ∃ b, Standard b ∧ ssossSys.Rel b a ∧ β ≤ o b := by
  intro β hβ
  obtain ⟨b, hb, hle⟩ := Below002.cofinal ha β hβ
  exact ⟨b, Below002.closure ha hb, (rel_iff a b).2 hb, hle⟩

theorem rank_congr {α : Type} {r s : α → α → Prop} (e : r = s)
    [IsWellFounded α r] [IsWellFounded α s] (x : α) :
    IsWellFounded.rank r x = IsWellFounded.rank s x := by
  subst e
  rfl

/-- `o` is the rank of one step on the standard forms. -/
theorem ssoss_rank (a : List ℕ) (ha : Standard a) :
    o a = ssossStd.rank ssossStd_wf a ha := by
  haveI : IsWellFounded {s // Standard s} (fun b a => ssossSys.Rel b.1 a.1) := ⟨ssossStd_wf⟩
  have e : (fun b a : {s // Standard s} => ssossSys.Rel b.1 a.1) = Below002.StdRel := by
    funext b a
    exact propext (rel_iff a.1 b.1)
  haveI : IsWellFounded {s // Standard s} Below002.StdRel := ⟨Below002.wf⟩
  rw [Below002.rank_eq ⟨a, ha⟩]
  exact (rank_congr e ⟨a, ha⟩).symm

end Googology.Notation.SSOSS
