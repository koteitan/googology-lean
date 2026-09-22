import Googology.Trans.BMS.Agree

/-!
# Expansion on every matrix

`Notation/BMS/Any.lean` puts the rule on every array, standard or not, as
`bmsAll`.  This file does the same on the entries, where the step runs.

Every matrix is the entries of an array — `ofListR` builds one and
`entriesR_ofListR` reads it back, as long as the columns all have the right
height, which `expandRL_col_len` says expansion preserves.  So `bmsAllL r` is
the rule on every matrix with `r + 1` rows, it terminates, it is well founded,
and it carries the rank of its own expansion.

`bmsLSim` includes the standard matrices in it, and `Trans/DBMS/Entries.lean`
includes the DBMS ones.  Neither inclusion needs anything proved: the step is
the same `expandRL` on both sides.
-/

namespace Googology.Trans.BMS

open BM4

theorem getElem!_mem {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_pos l i h]
  exact List.getElem_mem h

/-- The array with these columns. -/
def ofListR (r : Nat) (l : List (List Nat)) : Arr r := ⟨l.length, fun i k => (l[i]!)[k]!⟩

theorem entriesR_ofListR (r : Nat) (l : List (List Nat)) (h : ∀ c ∈ l, c.length = r) :
    entriesR (ofListR r l) = l := by
  rw [entriesR, show (ofListR r l).len = l.length from rfl]
  refine Eq.trans (List.map_congr_left (fun i hi => ?_)) (listEta l)
  show (List.range r).map (fun k => (l[i]!)[k]!) = l[i]!
  rw [← h (l[i]!) (getElem!_mem l i (List.mem_range.mp hi))]
  exact listEta (l[i]!)

theorem badRootR_lt {r : Nat} {l : List (List Nat)} {p : Nat}
    (h : badRootR r l = some p) : p + 1 < l.length := by
  rw [badRootR] at h
  by_cases he : l.isEmpty
  · rw [if_pos he] at h; exact absurd h (by simp)
  · rw [if_neg he] at h
    have := ParR_lt ((parAtR_eq_some l (m0L r l) (l.length - 1) p).mp h)
    have hne : l ≠ [] := by simpa [List.isEmpty_iff] using he
    have : 0 < l.length := List.length_pos_iff.mpr hne
    omega

/-- Expansion keeps every column the same height. -/
theorem expandRL_col_len (r N : Nat) (l : List (List Nat)) (h : ∀ c ∈ l, c.length = r) :
    ∀ c ∈ expandRL r N l, c.length = r := by
  rw [expandRL]
  cases hb : badRootR r l with
  | none =>
    dsimp only
    exact fun c hc => h c (List.dropLast_sublist l |>.subset hc)
  | some p =>
    dsimp only
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h1
      exact h _ (getElem!_mem l i (by have := badRootR_lt hb; have := List.mem_range.mp hi; omega))
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h2
      rw [List.length_map, List.length_range]

/-! ### The system -/

/-- The state: a matrix with `r + 1` rows, standard or not. -/
abbrev AllLState (r : Nat) : Type := {l : List (List Nat) // ∀ c ∈ l, c.length = r + 1}

/-- **Expansion on every matrix with `r + 1` rows.**  This is `bmsAll` written
on the entries, and unlike it the step runs. -/
def bmsAllL (r : Nat) : Rewrite where
  State := AllLState r
  step := fun l N => ⟨expandRL (r + 1) N l.1, expandRL_col_len (r + 1) N l.1 l.2⟩
  halted := fun l => l.1 = []

/-- **It terminates.** -/
theorem bmsAllL_terminates (r : Nat) : (bmsAllL r).Terminates := by
  intro f hf
  choose k hk using hf
  let g : Nat → Arr (r + 1) :=
    fun n => Nat.rec (ofListR (r + 1) (f 0).1) (fun m B => expand B (k m)) n
  have hgf : ∀ n, entriesR (g n) = (f n).1 := by
    intro n
    induction n with
    | zero => exact entriesR_ofListR (r + 1) (f 0).1 (f 0).2
    | succ m ih =>
      show entriesR (expand (g m) (k m)) = (f (m + 1)).1
      rw [entriesR_expand (Nat.succ_pos r), ih]
      exact (congrArg Subtype.val (hk m)).symm
  obtain ⟨n, hn⟩ :=
    Googology.Notation.BMS.bmsAll_terminates (r + 1) g (fun n => ⟨k n, rfl⟩)
  refine ⟨n, ?_⟩
  show (f n).1 = []
  rw [← hgf n, entriesR]
  have hl : (g n).len = 0 := hn
  rw [hl, List.range_zero, List.map_nil]

/-- **And is well founded.** -/
theorem bmsAllL_wf (r : Nat) : (bmsAllL r).WF := Rewrite.wf_of_terminates (bmsAllL_terminates r)

/-- So it carries the rank of its own expansion. -/
noncomputable def bmsAllLEval (r : Nat) :
    Eval (bmsAllL r) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (bmsAllL_wf r)

theorem entriesR_col_len {r : Nat} (A : Arr (r + 1)) :
    ∀ c ∈ entriesR A, c.length = r + 1 := by
  intro c hc
  rw [entriesR] at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  rw [List.length_map, List.length_range]

/-- The standard matrices sit inside all matrices. -/
def bmsLSim (r : Nat) : Sim (bmsL r) (bmsAllL r) where
  map := fun l => ⟨l.1, by
    obtain ⟨A, _, hA⟩ := l.2
    rw [← hA]
    exact entriesR_col_len A⟩
  map_rel := by
    rintro a b ⟨hna, k, rfl⟩
    exact ⟨hna, k, rfl⟩

end Googology.Trans.BMS
